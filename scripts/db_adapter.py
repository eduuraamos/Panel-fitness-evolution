import os
import re
import sqlite3 as _sqlite3


_connection_log_emitted = False


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


def _parse_pragma_table_info(sql):
    m = re.match(r"\s*PRAGMA\s+table_info\s*\(\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*\)\s*;?\s*$", sql, flags=re.IGNORECASE)
    return m.group(1) if m else None


class PostgresCursor:
    def __init__(self, conn_wrapper, raw_cursor):
        self._conn_wrapper = conn_wrapper
        self._raw = raw_cursor
        self._buffer = None
        self.lastrowid = None

    def execute(self, sql, params=None):
        params = params or ()
        table_name = _parse_pragma_table_info(sql)
        if table_name:
            self._buffer = self._build_pragma_table_info_rows(table_name)
            self.lastrowid = None
            return self

        translated = _translate_sql(sql)
        self._buffer = None
        self.lastrowid = None
        self._raw.execute(translated, params)

        if translated.lstrip().upper().startswith("INSERT"):
            self._refresh_lastrowid()

        return self

    def executemany(self, sql, seq_of_params):
        translated = _translate_sql(sql)
        self._buffer = None
        self.lastrowid = None
        self._raw.executemany(translated, seq_of_params)
        return self

    def fetchone(self):
        if self._buffer is not None:
            if not self._buffer:
                return None
            return self._buffer.pop(0)
        return self._raw.fetchone()

    def fetchall(self):
        if self._buffer is not None:
            rows = self._buffer
            self._buffer = []
            return rows
        return self._raw.fetchall()

    @property
    def rowcount(self):
        return self._raw.rowcount

    def close(self):
        self._raw.close()

    def _refresh_lastrowid(self):
        try:
            probe = self._conn_wrapper._raw.cursor()
            probe.execute("SELECT LASTVAL()")
            row = probe.fetchone()
            probe.close()
            self.lastrowid = int(row[0]) if row and row[0] is not None else None
        except Exception:
            self.lastrowid = None

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
    def __init__(self, raw_conn):
        self._raw = raw_conn

    def cursor(self):
        return PostgresCursor(self, self._raw.cursor())

    def commit(self):
        self._raw.commit()

    def rollback(self):
        self._raw.rollback()

    def close(self):
        self._raw.close()


class SqliteCompatModule:
    def __init__(self):
        self.Error = Exception

    def connect(self, db_path):
        global _connection_log_emitted
        if is_postgres_enabled():
            dsn = _env_database_url()
            try:
                import psycopg2
            except Exception as exc:
                raise RuntimeError(
                    "DATABASE_URL está definida pero psycopg2 no está instalado. "
                    "Añade psycopg2-binary a requirements.txt"
                ) from exc
            raw = psycopg2.connect(dsn)
            if not _connection_log_emitted:
                print("Using PostgreSQL", flush=True)
                print("First connection opened with PostgreSQL", flush=True)
                _connection_log_emitted = True
            return PostgresConnection(raw)

        if not _connection_log_emitted:
            print("Using SQLite", flush=True)
            print("First connection opened with SQLite", flush=True)
            _connection_log_emitted = True
        return _sqlite3.connect(str(db_path))


sqlite3_compat = SqliteCompatModule()
