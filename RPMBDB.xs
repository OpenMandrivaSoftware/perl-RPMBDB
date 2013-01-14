#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include <sys/utsname.h>
#include <sys/select.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <unistd.h>
#include <libintl.h>
#include <glob.h>
#include <stdbool.h>
#include <magic.h>

#undef Fflush
#undef Mkdir
#undef Stat
#undef Fstat

#define _RPMEVR_INTERNAL
#define _RPMPS_INTERNAL
#define _RPMDB_INTERNAL
#define _RPMTAG_INTERNAL
#define WITH_DB

#define	_RPMVSF_NODIGESTS	\
  ( RPMVSF_NOSHA1HEADER |	\
    RPMVSF_NOMD5HEADER |	\
    RPMVSF_NOSHA1 |		\
    RPMVSF_NOMD5 )

#define	_RPMVSF_NOSIGNATURES	\
  ( RPMVSF_NODSAHEADER |	\
    RPMVSF_NORSAHEADER |	\
    RPMVSF_NODSA |		\
    RPMVSF_NORSA )

#define	_RPMVSF_NOHEADER	\
  ( RPMVSF_NOSHA1HEADER |	\
    RPMVSF_NOMD5HEADER |	\
    RPMVSF_NODSAHEADER |	\
    RPMVSF_NORSAHEADER )

#define	_RPMVSF_NOPAYLOAD	\
  ( RPMVSF_NOSHA1 |		\
    RPMVSF_NOMD5 |		\
    RPMVSF_NODSA |		\
    RPMVSF_NORSA )

#include <rpmcli.h>
#include <rpmio.h>
#include <rpmtag.h>
#include <rpmdb.h>
#include <pkgio.h>
#include <rpmcb.h>
#include <rpmte.h>
#include <rpmps.h>
#include <rpmlog.h>

#if BYTE_ORDER == LITTLE_ENDIAN
#define bswap32(x) htobe32(x)
#elif __BYTE_ORDER == BIG_ENDIAN
#define bswap32(x) htole32(x)
#endif

static int
bdb_log_archive(DB_ENV *dbenv, char ***list, uint32_t flags) {
  int ret;
  if ((ret = dbenv->log_archive(dbenv, list, flags)) != 0)
    dbenv->err(dbenv, ret, "DB_ENV->log_archive");
  return ret;
}

static int
bdb_log_lsn_reset(DB_ENV *dbenv) {
  int ret = 0;
  char **list = NULL;
  /* Reset log sequence numbers to allow for moving to new environment */
  if(!(ret = dbenv->log_archive(dbenv, &list, DB_ARCH_DATA|DB_ARCH_ABS))) {
    char **p = list;
    for(; *p; p++)
      if(!ret)
	ret = dbenv->lsn_reset(dbenv, *p, 0);
    _free(list);
  }
  return ret;
}

/* This should be mostly working..
 * TODO:
 * Cleanup
 * Better error checking
 */

static int
rpmdb_convert(const char *prefix, int dbtype, int swap, int rebuild) {
  rpmts tsCur = NULL;
  int xx, i;
  const char *dbpath = NULL;
  const char *__dbi_txn = NULL;
  const char *_dbi_tags = NULL;
  const char *_dbi_config = NULL;
  const char *_dbi_config_Packages = NULL;
  const char *fn = NULL, *fn2 = NULL;
  const char *tmppath = NULL;
  glob_t gl = { .gl_pathc = 0, .gl_pathv = NULL, .gl_offs = 0 };
  struct stat st;

  unsetenv("TMPDIR");
  rpmReadConfigFiles(NULL, NULL);

  dbpath = rpmExpand("%{?_dbpath}", NULL);
  __dbi_txn = rpmExpand("%{__dbi_txn}", NULL);
  _dbi_tags = rpmExpand("%{_dbi_tags}", NULL);
  _dbi_config = rpmExpand("%{_dbi_config}", NULL);
  _dbi_config_Packages = rpmExpand("%{_dbi_config_Packages}", NULL);
  addMacro(NULL, "__dbi_txn", NULL, "create nofsync mpool txn thread thread_count=64", -1);

  /* (ugly) clear any existing locks */
  fn = rpmGetPath(prefix && prefix[0] ? prefix : "", dbpath, "/", "__db.*", NULL);
  xx = Glob(fn, 0, NULL, &gl);
  for (i = 0; i < (int)gl.gl_pathc; i++)
    xx = Unlink(gl.gl_pathv[i]);
  fn = _free(fn);
  Globfree(&gl);

  tsCur = rpmtsCreate();
  rpmtsSetRootDir(tsCur, prefix && prefix[0] ? prefix : NULL);

  /* To try make upgrades smooth, we've tried to prevent the new configuration
   * with possibly incompatible configuration from being dropped in during the
   * upgrade. Now that the rpm upgrade has finished we'll make sure to switch
   * to this new configuration before performing the conversion.
   */
  fn2 = rpmGetPath(prefix && prefix[0] ? prefix : "", "%{_dbpath}", "/DB_CONFIG.rpmnew", NULL);
  if (!Stat(fn2, &st) && st.st_size) {
    fn = rpmGetPath(prefix && prefix[0] ? prefix : "", "%{_dbpath}", "/DB_CONFIG", NULL);
    if (!Stat(fn, &st)) {
      /* if empty configuration, we'll just remove it */
      if (!st.st_size)
	Unlink(fn);
      else {
	/* if non-empty configuration exists, we'll rename it */
	fn2 = rpmGetPath(prefix && prefix[0] ? prefix : "", "%{_dbpath}", "/DB_CONFIG.rpmsave", NULL);
	Rename(fn, fn2);
	fn2 = _free(fn2);
      }
    }
    Rename(fn2, fn);
    fn = _free(fn);
  }
  fn2 = _free(fn2);

  if(!rpmtsOpenDB(tsCur, O_RDONLY)) {
    if(dbtype == 1) {
      addMacro(NULL, "_dbi_tags", NULL, "Packages:Name:Basenames:Group:Requirename:Providename:Conflictname:Triggername:Dirnames:Requireversion:Provideversion:Installtid:Sigmd5:Sha1header:Filedigests:Depends:Pubkeys", -1);
      addMacro(NULL, "_dbi_config", NULL, "%{_dbi_htconfig}", -1);
      addMacro(NULL, "_dbi_config_Packages", NULL, "%{_dbi_htconfig} lockdbfd", -1);
    }

    rpmts tsNew = rpmtsCreate();
    rpmdb rdbNew = NULL;
    DB_ENV *dbenvNew = NULL;
    struct stat sb;

    fn = rpmGetPath("%{_dbpath}", NULL);
    tmppath = tempnam(fn, "rpmdb_convert.XXXXXX");
    fn = _free(fn);
    addMacro(NULL, "_dbpath", NULL, tmppath, -1);
    rpmtsSetRootDir(tsNew, prefix && prefix[0] ? prefix : NULL);
    if(!rpmtsOpenDB(tsNew, O_RDWR)) {
      DBC *dbcpCur = NULL, *dbcpNew = NULL;
      rdbNew = rpmtsGetRdb(tsNew);
      dbenvNew = rdbNew->db_dbenv;
      dbiIndex dbiCur = dbiOpen(rpmtsGetRdb(tsCur), RPMDBI_PACKAGES, 0);
      dbiIndex dbiNew = dbiOpen(rdbNew, RPMDBI_PACKAGES, 0);
      DB_TXN *txnidNew = dbiTxnid(dbiNew);

      if(!(xx = dbiCopen(dbiCur, NULL, NULL, 0)) && !(xx = dbiCopen(dbiNew, txnidNew, &dbcpNew, DB_WRITECURSOR))) {
	DB * _dbN = (DB *) dbiNew->dbi_db;
	DB * _dbO = (DB *) dbiCur->dbi_db;
	DBT key, data;
	DB_TXN *txnidCur = dbiTxnid(dbiCur);
	uint32_t nkeys = 0;

	memset(&key, 0, sizeof(key));
	memset(&data, 0, sizeof(data));

	/* Acquire a cursor for the database. */
	if ((xx = _dbO->cursor(_dbO, NULL, &dbcpCur, 0)) != 0)
	  _dbO->err(_dbO, xx, "DB->cursor");

	if(!(xx = _dbO->stat(_dbO, txnidCur, &dbiCur->dbi_stats, 0))) {

	  switch(_dbO->type) {
	    case DB_BTREE:
	    case DB_RECNO: {
		DB_BTREE_STAT *db_stat = dbiCur->dbi_stats;
		nkeys = db_stat->bt_nkeys;
	      }
	      break;
	    case DB_HASH: {
		DB_HASH_STAT *db_stat = dbiCur->dbi_stats;
		nkeys = db_stat->hash_nkeys;
	      }
	      break;
	    case DB_QUEUE: {
		DB_QUEUE_STAT *db_stat = dbiCur->dbi_stats;
		nkeys = db_stat->qs_nkeys;
	      }
	      break;
	    case DB_UNKNOWN:
	    default:
	      xx = -1;
	      break;
	  }


	  if(!xx) {
	    uint32_t i = 0;
	    int doswap = -1;
	    float pct = 0;
	    uint8_t tmp;
	    /* 
	     * Older rpm places number of keys as first entry of hash database,
	     * so any package placed at beginning of it will be "missing" from
	     * rpmdb...
	     */
	    if (dbtype == 1){
	      key.data = &i;
	      data.data = &nkeys;
	      key.size = data.size = sizeof(uint32_t);
	      xx = _dbN->put(_dbN, NULL, &key, &data, 0);
	    }
	    while ((xx = dbcpCur->c_get(dbcpCur, &key, &data, DB_NEXT)) == 0) {
	      tmp = pct;
	      pct = (100*(float)++i/nkeys) + 0.5;
	      /* TODO: callbacks for status output? */
	      if(tmp < (int)(pct+0.5)) {
		fprintf(stderr, "\rconverting %s%s/Packages: %u/%u %d%%", prefix && prefix[0] ? prefix : "", tmppath, i, nkeys, (int)pct);
	      }
	      fflush(stdout);
	      if(i == 1 && !*(uint32_t*)key.data)
		    continue;

	      if(__builtin_expect(doswap, 1) < 0) {
		if((htole32(*(uint32_t*)key.data) > 10000000 && swap < 0) ||
		    (htole32(*(uint32_t*)key.data) < 10000000 && swap > 0))
		  doswap = 1;
		else
		  doswap = 0;
	      }
	      if(__builtin_expect(doswap, 1)) {
		if(swap)
		  *(uint32_t*)key.data = bswap32(*(uint32_t*)key.data);
	      }
	      xx = _dbN->put(_dbN, NULL, &key, &data, 0);

	    }
	    fprintf(stderr, "\n");
	    if(!(xx = dbiCclose(dbiNew, dbcpNew, 0)) && !(xx = dbiCclose(dbiCur, dbcpCur, 0)) &&
		rebuild) {
	      xx = rpmtsCloseDB(tsCur);

	      rpmVSFlags vsflags = rpmExpandNumeric("%{_vsflags_rebuilddb}");
	      if (rpmcliQueryFlags & VERIFY_DIGEST)
		vsflags |= _RPMVSF_NODIGESTS;
	      if (rpmcliQueryFlags & VERIFY_SIGNATURE)
		vsflags |= _RPMVSF_NOSIGNATURES;
	      rpmtsSetVSFlags(tsNew, vsflags);

	      {
		size_t dbix;
		fprintf(stderr, "rebuilding rpmdb:\n");
		fflush(stdout);
		for (dbix = 0; dbix < rdbNew->db_ndbi; dbix++) {
		  tagStore_t dbiTags = &rdbNew->db_tags[dbix];

		  /* Remove configured secondary indices. */
		  switch (dbiTags->tag) {
		    case RPMDBI_AVAILABLE:
		    case RPMDBI_ADDED:
		    case RPMDBI_REMOVED:
		    case RPMDBI_DEPCACHE:
		    case RPMDBI_BTREE:
		    case RPMDBI_HASH:
		    case RPMDBI_QUEUE:
		    case RPMDBI_RECNO:
		      fprintf(stderr, "skipping %s:\t%d%%\n", (dbiTags->str != NULL ? dbiTags->str : tagName(dbiTags->tag)),
			  (int)(100*((float)dbix/rdbNew->db_ndbi)));
		    case RPMDBI_PACKAGES:
		    case RPMDBI_SEQNO:
		      continue;
		      break;
		    default:
		      fn = rpmGetPath(rdbNew->db_root, rdbNew->db_home, "/",
			  (dbiTags->str != NULL ? dbiTags->str : tagName(dbiTags->tag)),
			  NULL);
		      fprintf(stderr, "%s:\t", fn);
		      if (!Stat(fn, &sb))
			xx = Unlink(fn);
		      fn = _free(fn);
		      break;
		  }
		  /* TODO: signal handler? */

		  /* Open (and re-create) each index. */
		  (void) dbiOpen(rdbNew, dbiTags->tag, rdbNew->db_flags);
		  fprintf(stderr, "%d%%\n", (int)(100*((float)dbix/rdbNew->db_ndbi)));
		  fflush(stdout);
		}

		/* Unreference header used by associated secondary index callbacks. */
		(void) headerFree(rdbNew->db_h);
		rdbNew->db_h = NULL;

		/* Reset the Seqno counter to the maximum primary key */
		rpmlog(RPMLOG_DEBUG, "rpmdb: max. primary key %u\n",
		    (unsigned)rdbNew->db_maxkey);
		fn = rpmGetPath(rdbNew->db_root, rdbNew->db_home, "/Seqno", NULL);
		if (!Stat(fn, &sb))
		  xx = Unlink(fn);
		fprintf(stderr, "%s:\t", fn);
		(void) dbiOpen(rdbNew, RPMDBI_SEQNO, rdbNew->db_flags);
		fprintf(stderr, "100%%\n");

		fn = _free(fn);

		/* Remove no longer required transaction logs */
		if(!(xx = bdb_log_archive(dbenvNew, NULL, DB_ARCH_REMOVE)))
		  xx = bdb_log_lsn_reset(dbenvNew);
		xx = rpmtsCloseDB(tsNew);
	      }
	    }
	  }
	}
      }
      if(!xx) {
	const char *dest = NULL;
	size_t dbix;
	
	if(!rpmtsOpenDB(tsNew, O_RDONLY)) {
	  rdbNew = rpmtsGetRdb(tsNew);
	  for (dbix = 0; dbix < rdbNew->db_ndbi; dbix++) {
	    tagStore_t dbiTags = &rdbNew->db_tags[dbix];
	    fn = rpmGetPath(rdbNew->db_root, rdbNew->db_home, "/", dbiTags->str, NULL);
	    dest = rpmGetPath(rdbNew->db_root, dbpath, "/", dbiTags->str, NULL);
	    if(!Stat(dest, &sb))
	      xx = Unlink(dest);
	    if(!Stat(fn, &sb)) {
	      xx = Rename(fn, dest);
	    }
	    fn = _free(fn);
	    dest = _free(dest);
	  }
	  dest = rpmGetPath(rdbNew->db_root, NULL);
	  xx = rpmtsCloseDB(tsNew);

	  /* (ugly) cleanup */
	  fn = rpmGetPath(dest, tmppath, "/", "*", NULL);
	  xx = Glob(fn, 0, NULL, &gl);
	  for (i = 0; i < (int)gl.gl_pathc; i++)
	    xx = Unlink(gl.gl_pathv[i]);
	  fn = _free(fn);
	  Globfree(&gl);

	  fn = rpmGetPath(dest, dbpath, "/log/", "*", NULL);
	  xx = Glob(fn, 0, NULL, &gl);
	  for (i = 0; i < (int)gl.gl_pathc; i++)
	    xx = Unlink(gl.gl_pathv[i]);
	  fn = _free(fn);
	  Globfree(&gl);

	  fn = rpmGetPath(dest, tmppath, "/log/", "*", NULL);
	  xx = Glob(fn, 0, NULL, &gl);
	  for (i = 0; i < (int)gl.gl_pathc; i++)
	    xx = Unlink(gl.gl_pathv[i]);
	  fn = _free(fn);
	  Globfree(&gl);

	  fn = rpmGetPath(dest, dbpath, "/tmp/", "*", NULL);
	  xx = Glob(fn, 0, NULL, &gl);
	  for (i = 0; i < (int)gl.gl_pathc; i++)
	    xx = Unlink(gl.gl_pathv[i]);
	  fn = _free(fn);
	  Globfree(&gl);

	  /* remove indices no longer used */
	  fn = rpmGetPath(dest, dbpath, "Provideversion", NULL);
	  if(!Stat(fn, &sb))
	    xx = Unlink(fn);
	  fn = _free(fn);
 	  fn = rpmGetPath(dest, dbpath, "Requireversion", NULL);
	  if(!Stat(fn, &sb))
	    xx = Unlink(fn);
	  fn = _free(fn);

	  /* clear locks */
	  fn = rpmGetPath(prefix && prefix[0] ? prefix : "", dbpath, "/", "__db.*", NULL);
	  xx = Glob(fn, 0, NULL, &gl);
	  for (i = 0; i < (int)gl.gl_pathc; i++)
	    xx = Unlink(gl.gl_pathv[i]);
	  fn = _free(fn);
	  Globfree(&gl);

	  fn = rpmGetPath(dest, tmppath, "/log", NULL);
	  xx = Rmdir(fn);
	  fn = _free(fn);
	  fn = rpmGetPath(dest, tmppath, NULL);
	  xx = Rmdir(fn);
	  fn = _free(fn);

	  _free(dest);
	}
      }
    }
    tsNew = rpmtsFree(tsNew);
  }
  tsCur = rpmtsFree(tsCur);
  addMacro(NULL, "_dbpath", NULL, dbpath, -1);
  addMacro(NULL, "__dbi_txn", NULL, __dbi_txn, -1);
  addMacro(NULL, "_dbi_tags", NULL, _dbi_tags, -1);
  addMacro(NULL, "_dbi_config", NULL, _dbi_config, -1);
  addMacro(NULL, "_dbi_config_Packages", NULL, _dbi_config_Packages, -1);

  _free(dbpath);
  _free(__dbi_txn);
  _free(_dbi_tags);
  _free(_dbi_config);
  _free(_dbi_config_Packages);
  _free(tmppath);
  return xx;
}

MODULE = RPMBDB            PACKAGE = RPMBDB       PREFIX = BDB_
void
BDB_info(prefix=NULL)
  char *prefix
  PREINIT:
  rpmts ts = NULL;
  int xx, empty = 1;
  const char *dbpath = NULL;
  struct stat sb;
  PPCODE:
  dbpath = rpmGetPath(prefix ? prefix : "", "%{?_dbpath}", NULL);
  if (Stat(dbpath, &sb) >= 0) {
    ts = rpmtsCreate();
    rpmtsSetRootDir(ts, prefix);
    if ((rpmtsOpenDB(ts, O_RDONLY)) == 0) {
      rpmdb db = rpmtsGetRdb(ts);
      dbiIndex dbi = dbiOpen(db, RPMDBI_PACKAGES, 0);
      DB *bdb = dbi->dbi_db;
      DBC *dbcp = NULL;
      DBT key, data;

      switch(bdb->type) {
	case DB_BTREE:
	  XPUSHs(sv_2mortal(newSVpvs("btree")));
	  break;
	case DB_RECNO:
	  XPUSHs(sv_2mortal(newSVpvs("recno")));
	  break;
	case DB_HASH:
	  XPUSHs(sv_2mortal(newSVpvs("hash")));
	  break;
	case DB_QUEUE:
	  XPUSHs(sv_2mortal(newSVpvs("queue")));
	  break;
	case DB_UNKNOWN:
	default:
	  XPUSHs(&PL_sv_undef);
	  break;
      }
      /* Acquire a cursor for the database. */
      if ((xx = bdb->cursor(bdb, NULL, &dbcp, 0)) != 0) {
	bdb->err(bdb, xx, "DB->cursor");
	empty = 2;
      }
      if (empty != 2) {
	/* Re-initialize the key/data pair. */
	memset(&key, 0, sizeof(key));
	memset(&data, 0, sizeof(data));
	while ((xx = dbcp->c_get(dbcp, &key, &data, DB_NEXT)) == 0) {
	  if (!*(uint32_t*)key.data)
	    continue;
	  if (htole32(*(uint32_t*)key.data) > 10000000)
	    XPUSHs(sv_2mortal(newSVpvs("bigendian")));
	  else
	    XPUSHs(sv_2mortal(newSVpvs("littleendian")));
	  empty = 0;
	  break;

	}
      }
      if (empty)
	XPUSHs(&PL_sv_undef);
      xx = dbiCclose(dbi, dbcp, 0);

    }
    ts = rpmtsFree(ts);
  }
  _free(dbpath);

int
BDB_convert(prefix=NULL, dbtype=NULL, swap=0, rebuild=0)
  char *prefix
  char *dbtype
  int swap  
  int rebuild
  PREINIT:
  int type = 0;
  CODE:
  if(dbtype && !strcmp(dbtype, "hash"))
    type = 1;
  else if(dbtype && !strcmp(dbtype, "btree"))
    type = 0;
  else if(dbtype)
    croak("Unsupported database type: %s\n", dbtype);
  RETVAL = rpmdb_convert(prefix, type, swap, rebuild) == 0;
  OUTPUT:
  RETVAL
