import os
import re
import sqlite3 as _sqlite3
import threading
import time


_connection_log_emitted = False
_perf_seq = 0
_pg_pool = None
_pool_lock = threading.Lock()
_request_state = threading.local()


def _db_perf_enabled():
    return os.environ.get("DB_PERF_LOG", "").strip().lower() in ("1", "true", "yes", "on")


def _next_perf_seq():
    global _perf_seq
    _perf_seq += 1
    return _perf_seq


def _trim_sql(sql, limit=180):
    compact = re.sub(r"\s+", " ", str(sql or "")).strip()
    if len(compact) <= limit:
        return compact
    return compact[: limit - 3] + "..."


def _log_perf(event, **fields):
    if not _db_perf_enabled():
        return
    payload = " ".join([f"{key}={fields[key]}" for key in sorted(fields)])
    print(f"[db-perf] event={event} {payload}".strip(), flush=True)


def _request_depth():
    return int(getattr(_request_state, "depth", 0) or 0)


def _request_conn_wrapper():
    return getattr(_request_state, "conn_wrapper", None)


def _set_request_conn_wrapper(conn_wrapper):
    _request_state.conn_wrapper = conn_wrapper


def _clear_request_conn_wrapper():
    if hasattr(_request_state, "conn_wrapper"):
        delattr(_request_state, "conn_wrapper")


def _is_request_active():
    return _request_depth() > 0


def _pool_bounds():
    minconn = int(os.environ.get("PG_POOL_MIN", "1") or 1)
    maxconn = int(os.environ.get("PG_POOL_MAX", "8") or 8)
    if minconn < 1:
        minconn = 1
    if maxconn < minconn:
        maxconn = minconn
    return minconn, maxconn


def _get_postgres_pool(dsn):
    global _pg_pool
    if _pg_pool is not None:
        return _pg_pool
    with _pool_lock:
        if _pg_pool is not None:
            return _pg_pool
        try:
            from psycopg2.pool import ThreadedConnectionPool
        except Exception as exc:
            raise RuntimeError(
                "DATABASE_URL está definida pero psycopg2 no está instalado. "
                "Añade psycopg2-binary a requirements.txt"
            ) from exc
        minconn, maxconn = _pool_bounds()
        _pg_pool = ThreadedConnectionPool(minconn, maxconn, dsn)
        return _pg_pool


def _env_database_url():
    value = os.environ.get("DATABASE_URL", "").strip()
    return value


def is_postgres_enabled():
    return bool(_env_database_url())


def _normalize_insert_or_ignore(sql):
    pattern = re.compile(r"INSERT\s+OR\s+IGNORE\s+INTO", re.IGNORECASE)
    if not pattern.search(sql):
        return sql

    normalized = pattern.sub("INSERT INTO", sql)
    if "ON CONFLICT" in normalized.upper():
        return normalized

    stripped = normalized.rstrip()
    if stripped.endswith(";"):
        return stripped[:-1] + " ON CONFLICT DO NOTHING;"
    return normalized + " ON CONFLICT DO NOTHING"


def _normalize_time_functions(sql):
    sql = re.sub(r"datetime\s*\(\s*'now'\s*\)", "CURRENT_TIMESTAMP", sql, flags=re.IGNORECASE)
    sql = re.sub(r"date\s*\(\s*'now'\s*\)", "CURRENT_DATE", sql, flags=re.IGNORECASE)
    return sql


def _normalize_create_table(sql):
    # SQLite-style autoincrement primary key to PostgreSQL serial identity.
    return re.sub(r"\bid\s+INTEGER\s+PRIMARY\s+KEY\b", "id BIGSERIAL PRIMARY KEY", sql, flags=re.IGNORECASE)


def _normalize_placeholders(sql):
    # This project uses positional SQLite placeholders everywhere.
    return sql.replace("?", "%s")


def _translate_sql(sql):
    out = sql
    out = _normalize_insert_or_ignore(out)
    out = _normalize_time_functions(out)
    out = _normalize_create_table(out)
    out = _normalize_placeholders(out)
    return out


def _is_read_query(sql):
    head = str(sql or '').lstrip().upper()
    return head.startswith('SELECT') or head.startswith('WITH')


def _is_transient_pg_error(exc):
    text = str(exc or '').lower()
    transient_markers = [
        'server closed the connection unexpectedly',
        'ssl syscall error',
        'could not receive data from server',
        'connection not open',
        'connection already closed',
        'eof detected',
        'terminating connection',
        'connection reset by peer',
        'broken pipe',
        "can't assign requested address",
    ]
    return any(marker in text for marker in transient_markers)


def _parse_pragma_table_info(sql):
    m = re.match(r"\s*PRAGMA\s+table_info\s*\(\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*\)\s*;?\s*$", sql, flags=re.IGNORECASE)
    return m.group(1) if m else None


class PostgresCursor:
    def __init__(self, conn_wrapper, raw_cursor):
        self._conn_wrapper = conn_wrapper
        self._raw = raw_cursor
        self._buffer = None
        self._lastrowid_value = None
        self._lastrowid_pending = False
        self._last_query_seq = None
        self._last_query_sql = ""
        self._last_query_started_at = None

    def execute(self, sql, params=None):
        params = params or ()
        table_name = _parse_pragma_table_info(sql)
        if table_name:
            self._buffer = self._build_pragma_table_info_rows(table_name)
            self._lastrowid_value = None
            self._lastrowid_pending = False
            return self

        translated = _translate_sql(sql)
        self._buffer = None
        self._lastrowid_value = None
        self._lastrowid_pending = False
        query_seq = _next_perf_seq()
        started_at = time.perf_counter()
        try:
            self._raw.execute(translated, params)
        except Exception as exc:
            if not (_is_read_query(translated) and _is_transient_pg_error(exc)):
                raise
            if not self._conn_wrapper._reconnect_cursor(self):
                raise
            self._raw.execute(translated, params)
        elapsed_ms = (time.perf_counter() - started_at) * 1000.0
        self._last_query_seq = query_seq
        self._last_query_sql = translated
        self._last_query_started_at = started_at
        _log_perf(
            "execute",
            engine="postgres",
            query_id=query_seq,
            duration_ms=f"{elapsed_ms:.3f}",
            params=len(params),
            sql=_trim_sql(translated),
        )

        if translated.lstrip().upper().startswith("INSERT"):
            self._lastrowid_pending = True

        return self

    def executemany(self, sql, seq_of_params):
        translated = _translate_sql(sql)
        self._buffer = None
        self._lastrowid_value = None
        self._lastrowid_pending = False
        batch = list(seq_of_params)
        query_seq = _next_perf_seq()
        started_at = time.perf_counter()
        self._raw.executemany(translated, batch)
        elapsed_ms = (time.perf_counter() - started_at) * 1000.0
        self._last_query_seq = query_seq
        self._last_query_sql = translated
        self._last_query_started_at = started_at
        _log_perf(
            "executemany",
            engine="postgres",
            query_id=query_seq,
            duration_ms=f"{elapsed_ms:.3f}",
            batch_size=len(batch),
            sql=_trim_sql(translated),
        )
        return self

    def fetchone(self):
        if self._buffer is not None:
            if not self._buffer:
                return None
            return self._buffer.pop(0)
        started_at = time.perf_counter()
        row = self._raw.fetchone()
        elapsed_ms = (time.perf_counter() - started_at) * 1000.0
        _log_perf(
            "fetchone",
            engine="postgres",
            query_id=self._last_query_seq or 0,
            duration_ms=f"{elapsed_ms:.3f}",
            has_row=1 if row is not None else 0,
            sql=_trim_sql(self._last_query_sql),
        )
        return row

    def fetchall(self):
        if self._buffer is not None:
            rows = self._buffer
            self._buffer = []
            return rows
        started_at = time.perf_counter()
        rows = self._raw.fetchall()
        elapsed_ms = (time.perf_counter() - started_at) * 1000.0
        _log_perf(
            "fetchall",
            engine="postgres",
            query_id=self._last_query_seq or 0,
            duration_ms=f"{elapsed_ms:.3f}",
            rowcount=len(rows),
            sql=_trim_sql(self._last_query_sql),
        )
        return rows

    @property
    def rowcount(self):
        return self._raw.rowcount

    @property
    def lastrowid(self):
        if self._lastrowid_pending:
            self._refresh_lastrowid()
            self._lastrowid_pending = False
        return self._lastrowid_value

    @lastrowid.setter
    def lastrowid(self, value):
        self._lastrowid_value = value
        self._lastrowid_pending = False

    def close(self):
        self._raw.close()

    def _refresh_lastrowid(self):
        probe = None
        try:
            probe = self._conn_wrapper._raw.cursor()
            probe.execute("SAVEPOINT copilot_lastrowid")
            try:
                probe.execute("SELECT LASTVAL()")
                row = probe.fetchone()
                self._lastrowid_value = int(row[0]) if row and row[0] is not None else None
            finally:
                # Ensure any LASTVAL error does not poison the caller transaction.
                probe.execute("ROLLBACK TO SAVEPOINT copilot_lastrowid")
                probe.execute("RELEASE SAVEPOINT copilot_lastrowid")
        except Exception:
            self._lastrowid_value = None
        finally:
            if probe is not None:
                try:
                    probe.close()
                except Exception:
                    pass

    def _build_pragma_table_info_rows(self, table_name):
        cur = self._conn_wrapper._raw.cursor()
        cur.execute(
            """
            SELECT c.column_name, c.data_type, c.is_nullable, c.column_default,
                   EXISTS (
                       SELECT 1
                       FROM information_schema.table_constraints tc
                       JOIN information_schema.key_column_usage kcu
                         ON tc.constraint_name = kcu.constraint_name
                        AND tc.table_schema = kcu.table_schema
                      WHERE tc.constraint_type = 'PRIMARY KEY'
                        AND tc.table_schema = 'public'
                        AND tc.table_name = c.table_name
                        AND kcu.column_name = c.column_name
                   ) AS is_pk
            FROM information_schema.columns c
            WHERE c.table_schema = 'public' AND c.table_name = %s
            ORDER BY c.ordinal_position
            """,
            (table_name,),
        )
        rows = cur.fetchall()
        cur.close()

        pragma_rows = []
        for idx, row in enumerate(rows):
            col_name, data_type, is_nullable, col_default, is_pk = row
            pragma_rows.append(
                (
                    idx,
                    col_name,
                    str(data_type or ""),
                    0 if str(is_nullable).upper() == "YES" else 1,
                    col_default,
                    1 if is_pk else 0,
                )
            )
        return pragma_rows


class PostgresConnection:
    def __init__(self, raw_conn, pool=None, managed_by_request=False):
        self._raw = raw_conn
        self._pool = pool
        self._managed_by_request = managed_by_request
        self._returned = False

    def cursor(self):
        return PostgresCursor(self, self._raw.cursor())

    def commit(self):
        self._raw.commit()

    def rollback(self):
        self._raw.rollback()

    def close(self):
        if self._managed_by_request:
            return
        if self._returned:
            return
        try:
            self._raw.rollback()
        except Exception:
            pass
        if self._pool is not None:
            self._pool.putconn(self._raw, close=True)
        else:
            self._raw.close()
        self._returned = True

    def _reconnect_cursor(self, pg_cursor):
        if self._pool is None:
            return False
        try:
            try:
                pg_cursor._raw.close()
            except Exception:
                pass
            try:
                self._pool.putconn(self._raw, close=True)
            except Exception:
                pass
            self._raw = self._pool.getconn()
            self._returned = False
            pg_cursor._raw = self._raw.cursor()
            return True
        except Exception:
            return False


class SqliteCompatModule:
    def __init__(self):
        self.Error = Exception

    def begin_request(self):
        _request_state.depth = _request_depth() + 1

    def end_request(self):
        depth = _request_depth()
        if depth <= 0:
            return
        depth -= 1
        _request_state.depth = depth
        if depth > 0:
            return

        conn_wrapper = _request_conn_wrapper()
        if conn_wrapper is None:
            _clear_request_conn_wrapper()
            return

        _clear_request_conn_wrapper()
        if is_postgres_enabled():
            try:
                conn_wrapper._raw.rollback()
            except Exception:
                pass
            if conn_wrapper._pool is not None and not conn_wrapper._returned:
                conn_wrapper._pool.putconn(conn_wrapper._raw, close=True)
                conn_wrapper._returned = True
            return

        try:
            conn_wrapper.close()
        except Exception:
            pass

    def connect(self, db_path):
        global _connection_log_emitted
        if is_postgres_enabled():
            dsn = _env_database_url()
            request_conn = _request_conn_wrapper() if _is_request_active() else None
            if request_conn is not None:
                if getattr(request_conn._raw, 'closed', 0):
                    _clear_request_conn_wrapper()
                else:
                    _log_perf("reuse", engine="postgres", scope="request")
                    return request_conn

            pool = _get_postgres_pool(dsn)
            started_at = time.perf_counter()
            raw = pool.getconn()
            elapsed_ms = (time.perf_counter() - started_at) * 1000.0
            _log_perf("connect", engine="postgres", duration_ms=f"{elapsed_ms:.3f}")
            if not _connection_log_emitted:
                print("Using PostgreSQL", flush=True)
                print("First connection opened with PostgreSQL", flush=True)
                _connection_log_emitted = True
            conn_wrapper = PostgresConnection(raw, pool=pool, managed_by_request=_is_request_active())
            if _is_request_active():
                _set_request_conn_wrapper(conn_wrapper)
            return conn_wrapper

        if not _connection_log_emitted:
            print("Using SQLite", flush=True)
            print("First connection opened with SQLite", flush=True)
            _connection_log_emitted = True
        started_at = time.perf_counter()
        conn = _sqlite3.connect(str(db_path))
        elapsed_ms = (time.perf_counter() - started_at) * 1000.0
        _log_perf("connect", engine="sqlite", duration_ms=f"{elapsed_ms:.3f}")
        return conn


sqlite3_compat = SqliteCompatModule()
