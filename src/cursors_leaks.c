/*-------------------------------------------------------------------------
 *
 * cursors_leak.c
 *
 *			  detection unclosed cursors code
 *
 * by Pavel Stehule 2013-2022
 *
 *-------------------------------------------------------------------------
 */

#include "plpgsql_check.h"
#include "plpgsql_check_builtins.h"

#include "storage/proc.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/memutils.h"

bool plpgsql_check_cursors_leaks = true;
bool plpgsql_check_cursors_leaks_strict = false;
int plpgsql_check_cursors_leaks_level = WARNING;


#define MAX_NAMES_PER_STATEMENT			20

typedef struct
{
	int			stmtid;
	int			rec_level;
	char	   *curname;
} CursorTrace;

typedef struct
{
	Oid			fn_oid;
	TransactionId fn_xmin;
} FunctionTraceKey;

typedef struct
{
	FunctionTraceKey key;

	int			ncursors;
	int			cursors_size;
	CursorTrace *cursors_traces;
} FunctionTrace;

MemoryContextCallback contextCallback;


static LocalTransactionId traces_lxid = InvalidLocalTransactionId;
static HTAB *traces = NULL;
static MemoryContext traces_mcxt = NULL;

static void func_setup(PLpgSQL_execstate *estate, PLpgSQL_function *func, void **plugin2_info);
static void func_end(PLpgSQL_execstate *estate, PLpgSQL_function *func, void **plugin2_info);
static void stmt_end(PLpgSQL_execstate *estate, PLpgSQL_stmt *stmt, void **plugin2_info);

static plpgsql_check_plugin2 cursors_leaks_plugin2 = { func_setup, NULL, func_end, NULL,
													   NULL, stmt_end, NULL, NULL, NULL, NULL, NULL, NULL };

static FunctionTrace *
get_function_trace(PLpgSQL_function *func)
{
	bool		found;
	FunctionTrace *ftrace;
	FunctionTraceKey key;

	if (traces == NULL || traces_lxid != MyProc->lxid)
	{
		HASHCTL		ctl;

		traces_mcxt = AllocSetContextCreate(TopTransactionContext,
										    "plpgsql_check - trace cursors",
										    ALLOCSET_DEFAULT_SIZES);

		memset(&ctl, 0, sizeof(ctl));
		ctl.keysize = sizeof(FunctionTraceKey);
		ctl.entrysize = sizeof(FunctionTrace);
		ctl.hcxt = traces_mcxt;

		traces = hash_create("plpgsql_checj - cursors leaks detection",
							 FUNCS_PER_USER,
							 &ctl,
							 HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);

		traces_lxid = MyProc->lxid;
	}

	key.fn_oid = func->fn_oid;
	key.fn_xmin = func->fn_xmin;

	ftrace = (FunctionTrace *) hash_search(traces,
										  (void *) &key,
										  HASH_ENTER,
										  &found);

	if (!found)
	{
		ftrace->key.fn_oid = func->fn_oid;
		ftrace->key.fn_xmin = func->fn_xmin;
		ftrace->ncursors = 0;
		ftrace->cursors_size = 0;
		ftrace->cursors_traces = NULL;
	}

	return ftrace;
}


static void
func_setup(PLpgSQL_execstate *estate, PLpgSQL_function *func, void **plugin2_info)
{
	FunctionTrace *ftrace;

	if (plpgsql_check_cursors_leaks)
	{
		ftrace = get_function_trace(func);

		*plugin2_info = ftrace;
	}
	else
		*plugin2_info = NULL;
}

static void
func_end(PLpgSQL_execstate *estate,
				PLpgSQL_function *func,
				void **plugin2_info)
{
	FunctionTrace *ftrace = *plugin2_info;
	int			i;

	if (!ftrace || traces_lxid != MyProc->lxid)
		return;

	for (i = 0; i < ftrace->ncursors; i++)
	{
		CursorTrace *ct = &ftrace->cursors_traces[i];

		/*
		 * Iterate over traced cursors. Remove slots for tracing
		 * immediately, when traced cursor is closed already.
		 */
		if (ct->curname && ct->rec_level == func->use_count)
		{
			if (SPI_cursor_find(ct->curname))
			{
				if (plpgsql_check_cursors_leaks_strict)
				{
					char	*context;

					context = GetErrorContextStack();

					ereport(plpgsql_check_cursors_leaks_level,
							errcode(ERRCODE_INVALID_CURSOR_STATE),
							errmsg("cursor is not closed"),
							errdetail("%s", context));
					pfree(context);

					pfree(ct->curname);
					ct->stmtid = -1;
					ct->curname = NULL;
				}
			}
			else
			{
				pfree(ct->curname);
				ct->stmtid = -1;
				ct->curname = NULL;
			}
		}
	}
}

static void
stmt_end(PLpgSQL_execstate *estate, PLpgSQL_stmt *stmt, void **plugin2_info)
{
	FunctionTrace *ftrace = *plugin2_info;

	if (!ftrace)
		return;

	if (traces_lxid != MyProc->lxid)
	{
		ftrace = get_function_trace(estate->func);
		*plugin2_info = ftrace;
	}

	if (stmt->cmd_type == PLPGSQL_STMT_OPEN)
	{
		int			i;
		int			cursors_for_current_stmt = 0;
		int			free_slot = -1;
		PLpgSQL_var *curvar;

		for (i = 0; i < ftrace->ncursors; i++)
		{
			CursorTrace *ct = &ftrace->cursors_traces[i];

			if (ct->curname && ct->stmtid == stmt->stmtid)
			{
				if (SPI_cursor_find(ct->curname))
				{
					if (estate->func->use_count == 1 && !plpgsql_check_cursors_leaks_strict)
					{
						char	*context;

						context = GetErrorContextStack();

						ereport(plpgsql_check_cursors_leaks_level,
								errcode(ERRCODE_INVALID_CURSOR_STATE),
								errmsg("cursor is not closed"),
								errdetail("%s", context));

						pfree(context);

						pfree(ct->curname);
						ct->stmtid = -1;
						ct->curname = NULL;
					}
					else
					{
						cursors_for_current_stmt += 1;
					}
				}
				else
				{
					pfree(ct->curname);
					ct->stmtid = -1;
					ct->curname = NULL;
				}
			}

			if (ct->stmtid == -1 && free_slot == -1)
				free_slot = i;
		}

		curvar = (PLpgSQL_var *) (estate->datums[((PLpgSQL_stmt_open *) stmt)->curvar]);
		Assert(!curvar->isnull);

		if (cursors_for_current_stmt < MAX_NAMES_PER_STATEMENT)
		{
			MemoryContext oldcxt;
			char	   *curname;
			CursorTrace *ct = NULL;

			oldcxt = MemoryContextSwitchTo(traces_mcxt);

			curname = TextDatumGetCString(curvar->value);

			if (free_slot != -1)
				ct = &ftrace->cursors_traces[free_slot];
			else
			{
				if (ftrace->ncursors == ftrace->cursors_size)
				{
					if (ftrace->cursors_size > 0)
					{
						ftrace->cursors_size += 10;
						ftrace->cursors_traces = repalloc_array(ftrace->cursors_traces,
																CursorTrace,
																ftrace->cursors_size);
					}
					else
					{
						ftrace->cursors_size = 10;
						ftrace->cursors_traces = palloc_array(CursorTrace,
														  ftrace->cursors_size);
					}
				}

				ct = &ftrace->cursors_traces[ftrace->ncursors++];
			}

			ct->stmtid = stmt->stmtid;
			ct->rec_level = estate->func->use_count;
			ct->curname = curname;

			MemoryContextSwitchTo(oldcxt);
		}
	}
}

void
plpgsql_check_cursors_leaks_init(void)
{
	plpgsql_check_register_pldbgapi2_plugin(&cursors_leaks_plugin2);
}