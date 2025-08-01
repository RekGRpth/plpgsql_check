/*-------------------------------------------------------------------------
 *
 * catalog.c
 *
 *			  routines for working with Postgres's catalog and caches
 *
 * by Pavel Stehule 2013-2025
 *
 *-------------------------------------------------------------------------
 */

#include "plpgsql_check.h"

#include "catalog/pg_extension.h"
#include "catalog/pg_language.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/extension.h"
#include "commands/proclang.h"
#include "utils/builtins.h"
#include "utils/catcache.h"
#include "utils/fmgroids.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/regproc.h"

#include "catalog/pg_proc.h"
#include "utils/syscache.h"

/*
 * Pre pg 18 doesn't support system cache for pg_extension,
 * we need to manipulate with table on low level.
 */
#if PG_VERSION_NUM < 180000

#include "access/genam.h"

#include "access/htup_details.h"
#include "access/table.h"
#include "catalog/indexing.h"
#include "utils/rel.h"

#endif

static Oid	plpgsql_check_PLpgSQLlanguageId = InvalidOid;

/*
 * Prepare metadata necessary for plpgsql_check
 */
void
plpgsql_check_get_function_info(plpgsql_check_info *cinfo)
{
	Form_pg_proc proc;
	char		functyptype;

	proc = (Form_pg_proc) GETSTRUCT(cinfo->proctuple);

	functyptype = get_typtype(proc->prorettype);

	cinfo->trigtype = PLPGSQL_NOT_TRIGGER;
	cinfo->is_procedure = proc->prokind == PROKIND_PROCEDURE;

	/*
	 * Disallow pseudotype result  except for TRIGGER, RECORD, VOID, or
	 * polymorphic
	 */
	if (functyptype == TYPTYPE_PSEUDO)
	{
		/* we assume OPAQUE with no arguments means a trigger */
		if (proc->prorettype == TRIGGEROID)
			cinfo->trigtype = PLPGSQL_DML_TRIGGER;
		else if (proc->prorettype == EVENT_TRIGGEROID)
			cinfo->trigtype = PLPGSQL_EVENT_TRIGGER;
		else if (proc->prorettype != RECORDOID &&
				 proc->prorettype != VOIDOID &&
				 !IsPolymorphicType(proc->prorettype))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("PL/pgSQL functions cannot return type %s",
							format_type_be(proc->prorettype))));
	}


	cinfo->volatility = proc->provolatile;
	cinfo->rettype = proc->prorettype;
}

char *
plpgsql_check_get_src(HeapTuple procTuple)
{
	Datum		prosrcdatum;
	bool		isnull;

	prosrcdatum = SysCacheGetAttr(PROCOID, procTuple,
								  Anum_pg_proc_prosrc, &isnull);
	if (isnull)
		elog(ERROR, "null prosrc");

	return TextDatumGetCString(prosrcdatum);
}

/*
 * Process necessary checking before code checking
 *     a) disallow other than plpgsql check function,
 *     b) when function is trigger function, then reloid must be defined
 */
void
plpgsql_check_precheck_conditions(plpgsql_check_info *cinfo)
{
	Form_pg_proc proc;
	char	   *funcname;

	proc = (Form_pg_proc) GETSTRUCT(cinfo->proctuple);
	funcname = format_procedure(cinfo->fn_oid);

	/*
	 * The plpgsql_check can be loaded by shared_proload_libraries. That means
	 * so in init time the access to system catalog can be impossible. So
	 * plpgsql_check_PLpgSQLlanguageId should be initialized here.
	 */
	if (!OidIsValid(plpgsql_check_PLpgSQLlanguageId))
		plpgsql_check_PLpgSQLlanguageId = get_language_oid("plpgsql", false);

	/* used language must be plpgsql */
	if (proc->prolang != plpgsql_check_PLpgSQLlanguageId)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("%s is not a plpgsql function", funcname)));

	/* profiler doesn't require trigger data check */
	if (!cinfo->show_profile)
	{
		/* dml trigger needs valid relid, others not */
		if (cinfo->trigtype == PLPGSQL_DML_TRIGGER)
		{
			if (!OidIsValid(cinfo->relid))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("missing trigger relation"),
						 errhint("Trigger relation oid must be valid")));
		}
		else
		{
			if (OidIsValid(cinfo->relid))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("function is not trigger"),
						 errhint("Trigger relation oid must not be valid for non dml trigger function.")));
		}
	}

	pfree(funcname);
}

#if PG_VERSION_NUM < 160000

/*
 * plpgsql_check_get_extension_schema - given an extension OID, fetch its extnamespace
 *
 * Returns InvalidOid if no such extension.
 */
static Oid
get_extension_schema(Oid ext_oid)
{
	Oid			result;
	Relation	rel;
	SysScanDesc scandesc;
	HeapTuple	tuple;
	ScanKeyData entry[1];

	rel = table_open(ExtensionRelationId, AccessShareLock);

	ScanKeyInit(&entry[0],
				Anum_pg_extension_oid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(ext_oid));

	scandesc = systable_beginscan(rel, ExtensionOidIndexId, true,
								  NULL, 1, entry);

	tuple = systable_getnext(scandesc);

	/* We assume that there can be at most one matching tuple */
	if (HeapTupleIsValid(tuple))
		result = ((Form_pg_extension) GETSTRUCT(tuple))->extnamespace;
	else
		result = InvalidOid;

	systable_endscan(scandesc);

	table_close(rel, AccessShareLock);

	return result;
}

#endif

#if PG_VERSION_NUM < 180000

/*
 * get_extension_version - given an extension OID, look up the version
 *
 * Returns a palloc'd string, or NULL if no such extension.
 */
char *
get_extension_version(Oid ext_oid)
{
	char	   *result;
	Relation	rel;
	SysScanDesc scandesc;
	HeapTuple	tuple;
	ScanKeyData entry[1];

	rel = table_open(ExtensionRelationId, AccessShareLock);

	ScanKeyInit(&entry[0],
				Anum_pg_extension_oid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(ext_oid));

	scandesc = systable_beginscan(rel, ExtensionOidIndexId, true,
								  NULL, 1, entry);

	tuple = systable_getnext(scandesc);

	/* We assume that there can be at most one matching tuple */
	if (HeapTupleIsValid(tuple))
	{
		Datum		datum;
		bool		isnull;

		datum = heap_getattr(tuple, Anum_pg_extension_extversion,
							 RelationGetDescr(rel), &isnull);

		if (isnull)
			elog(ERROR, "extversion is null");

		result = text_to_cstring(DatumGetTextPP(datum));
	}
	else
		result = NULL;

	systable_endscan(scandesc);

	table_close(rel, AccessShareLock);

	return result;
}

#else

/*
 * Returns a palloc'd string, or NULL if no such extension.
 * Use extension syscache from PostgreSQL 18+
 */
char *
get_extension_version2(Oid ext_oid)
{
	HeapTuple	extTuple;
	Datum		extversiondatum;
	char	   *result;
	bool		isnull;

	extTuple = SearchSysCache1(EXTENSIONOID, ObjectIdGetDatum(ext_oid));
	if (!HeapTupleIsValid(extTuple))
		elog(ERROR, "cache lookup failed for extension %u", ext_oid);

	extversiondatum = SysCacheGetAttr(EXTENSIONOID, extTuple,
									  Anum_pg_extension_extversion, &isnull);

	if (isnull)
		elog(ERROR, "extversion is null");

	result = TextDatumGetCString(extversiondatum);

	ReleaseSysCache(extTuple);

	return result;
}

#endif

/*
 * Returns oid of pragma function. It is used for elimination
 * pragma function from volatility tests.
 */
Oid
plpgsql_check_pragma_func_oid(void)
{
	Oid			result = InvalidOid;
	Oid			extoid;

	extoid = get_extension_oid("plpgsql_check", true);

	if (OidIsValid(extoid))
	{
		CatCList   *catlist;
		Oid			schemaoid;
		int			i;

		schemaoid = get_extension_schema(extoid);

		/* Search syscache by name only */
		catlist = SearchSysCacheList1(PROCNAMEARGSNSP, CStringGetDatum("plpgsql_check_pragma"));

		for (i = 0; i < catlist->n_members; i++)
		{
			HeapTuple	proctup = &catlist->members[i]->tuple;
			Form_pg_proc procform = (Form_pg_proc) GETSTRUCT(proctup);

			/* Consider only procs in specified namespace */
			if (procform->pronamespace != schemaoid)
				continue;

			result = procform->oid;
			break;
		}

		ReleaseSysCacheList(catlist);
	}

	return result;
}

/*
 * Returns true, if function specified by oid is plpgsql function.
 */
bool
plpgsql_check_is_plpgsql_function(Oid foid)
{
	HeapTuple	procTuple;
	Form_pg_proc procStruct;
	bool		result;

	procTuple = SearchSysCache1(PROCOID, ObjectIdGetDatum(foid));
	if (!HeapTupleIsValid(procTuple))
		return false;

	procStruct = (Form_pg_proc) GETSTRUCT(procTuple);

	/*
	 * The plpgsql_check can be loaded by shared_proload_libraries. That means
	 * so in init time the access to system catalog can be impossible. So
	 * plpgsql_check_PLpgSQLlanguageId should be initialized here.
	 */
	if (!OidIsValid(plpgsql_check_PLpgSQLlanguageId))
		plpgsql_check_PLpgSQLlanguageId = get_language_oid("plpgsql", false);

	result = procStruct->prolang == plpgsql_check_PLpgSQLlanguageId;

	ReleaseSysCache(procTuple);

	return result;
}

/*
 * plpgsql_check_get_op_namespace
 *	  returns the name space of the operator with the given opno
 */
Oid
plpgsql_check_get_op_namespace(Oid opno)
{
	HeapTuple	tp;

	tp = SearchSysCache1(OPEROID, ObjectIdGetDatum(opno));
	if (HeapTupleIsValid(tp))
	{
		Form_pg_operator optup = (Form_pg_operator) GETSTRUCT(tp);

		ReleaseSysCache(tp);
		return optup->oprnamespace;
	}
	else
		return InvalidOid;
}
