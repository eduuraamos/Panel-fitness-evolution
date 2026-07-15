#!/usr/bin/env python3
"""Migra los datos de data/foods.db (SQLite) a PostgreSQL.

La migración reutiliza el bootstrap existente del servidor y el adaptador
centralizado de base de datos para mantener un único camino de conexión.
"""
from __future__ import annotations

import argparse
import os
import sqlite3 as source_sqlite3
import time
import traceback
from pathlib import Path

from db_adapter import is_postgres_enabled, sqlite3_compat as dest_sqlite3
from food_schema import rebuild_foods_search_index
import serve_foods as app_schema


BASE_DIR = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE_DB = BASE_DIR / "data" / "foods.db"

TABLES_TO_MIGRATE = [
    "brands",
    "foods",
    "exercises",
    "routines",
    "diets",
    "clients",
    "app_settings",
    "routine_items",
    "routine_days",
    "diet_meals",
    "diet_day_config",
    "diet_supplements",
    "diet_items",
    "payment_plans",
    "client_diet_history",
    "client_training_history",
    "client_fasting_weights",
    "client_daily_steps",
    "client_reviews",
]

SEQUENCE_TABLES = [
    "categories",
    "brands",
    "exercise_categories",
    "foods",
    "exercises",
    "routines",
    "diets",
    "clients",
    "routine_items",
    "routine_days",
    "diet_meals",
    "diet_day_config",
    "diet_supplements",
    "diet_items",
    "payment_plans",
    "client_diet_history",
    "client_training_history",
    "client_fasting_weights",
    "client_daily_steps",
    "client_reviews",
]


def _quote_table_name(name):
    return '"' + name.replace('"', '""') + '"'


def _table_columns(conn, table_name):
    cur = conn.cursor()
    cur.execute(f"PRAGMA table_info({table_name})")
    rows = cur.fetchall()
    return [row[1] for row in rows], rows


def _count_rows(conn, table_name):
    cur = conn.cursor()
    cur.execute(f"SELECT COUNT(*) FROM {table_name}")
    return int(cur.fetchone()[0] or 0)


def _table_exists(conn, table_name):
    cols, _ = _table_columns(conn, table_name)
    return bool(cols)


def _bootstrap_destination_schema(dest_conn):
    print('[1/6] Bootstrapping destination schema...', flush=True)
    app_schema.ensure_brand_column(dest_conn)
    app_schema.ensure_exercises_table(dest_conn)
    app_schema.ensure_routines_table(dest_conn)
    app_schema.ensure_diets_table(dest_conn)
    app_schema.ensure_clients_table(dest_conn)
    app_schema.ensure_payment_plans_table(dest_conn)
    app_schema.ensure_client_history_tables(dest_conn)
    app_schema.ensure_fasting_weights_table(dest_conn)
    app_schema.ensure_client_daily_steps_table(dest_conn)
    app_schema.ensure_client_reviews_table(dest_conn)
    app_schema.ensure_diet_builder_tables(dest_conn)
    app_schema.ensure_app_settings_table(dest_conn)
    print('[1/6] Schema bootstrap complete', flush=True)


ALLOW_EXTRA_ROWS_TABLES = {
    'categories',
    'exercise_categories',
}

FORENSIC_INSERT_LOG = True


def _select_rows(source_conn, table_name, columns):
    select_sql = f"SELECT {', '.join(columns)} FROM {table_name}"
    if 'id' in columns:
        select_sql += ' ORDER BY id'
    source_cur = source_conn.cursor()
    source_cur.execute(select_sql)
    return source_cur.fetchall()


def _migrate_named_table(source_conn, dest_conn, table_name):
    print(f'[2/6] Migrating lookup table: {table_name} (start)', flush=True)
    source_columns, _ = _table_columns(source_conn, table_name)
    if 'id' not in source_columns or 'name' not in source_columns:
        raise RuntimeError(f'{table_name} requiere columnas id y name')

    rows = _select_rows(source_conn, table_name, ['id', 'name'])
    dest_before = _count_rows(dest_conn, table_name)

    dest_cur = dest_conn.cursor()
    dest_cur.execute(f"SELECT id, name FROM {table_name}")
    existing = dest_cur.fetchall()
    id_by_name = {str(name): int(id_val) for id_val, name in existing if name is not None}
    used_ids = {int(id_val) for id_val, _name in existing}

    id_map = {}
    for source_id, name in rows:
        source_id_i = int(source_id)
        name_text = str(name or '').strip()
        if not name_text:
            continue

        existing_id = id_by_name.get(name_text)
        if existing_id is not None:
            id_map[source_id_i] = int(existing_id)
            continue

        if source_id_i in used_ids:
            dest_cur.execute(
                f"INSERT INTO {table_name}(name) VALUES(?) ON CONFLICT(name) DO NOTHING",
                (name_text,),
            )
            dest_cur.execute(f"SELECT id FROM {table_name} WHERE name = ?", (name_text,))
            row = dest_cur.fetchone()
            if not row:
                raise RuntimeError(f'No se pudo resolver id para {table_name}.{name_text}')
            new_id = int(row[0])
            id_by_name[name_text] = new_id
            used_ids.add(new_id)
            id_map[source_id_i] = new_id
            continue

        dest_cur.execute(
            f"INSERT INTO {table_name}(id, name) VALUES(?, ?) ON CONFLICT(id) DO UPDATE SET name = excluded.name",
            (source_id_i, name_text),
        )
        id_by_name[name_text] = source_id_i
        used_ids.add(source_id_i)
        id_map[source_id_i] = source_id_i

    dest_conn.commit()

    if is_postgres_enabled() and table_name in SEQUENCE_TABLES:
        seq_cur = dest_conn.cursor()
        seq_cur.execute(
            f"""
            SELECT setval(
                pg_get_serial_sequence('{table_name}', 'id'),
                COALESCE((SELECT MAX(id) FROM {table_name}), 1),
                EXISTS(SELECT 1 FROM {table_name})
            )
            """
        )
        dest_conn.commit()

    dest_after = _count_rows(dest_conn, table_name)
    matched = len(rows) == dest_after
    if table_name in ALLOW_EXTRA_ROWS_TABLES:
        matched = dest_after >= len(rows)

    result = {
        'table': table_name,
        'source': len(rows),
        'before': dest_before,
        'after': dest_after,
        'migrated': max(0, dest_after - dest_before),
        'matched': matched,
    }
    print(
        f"[2/6] Migrating lookup table: {table_name} (done) "
        f"source={result['source']} before={result['before']} after={result['after']}",
        flush=True,
    )
    return result, id_map


def _copy_table(source_conn, dest_conn, table_name, row_transform=None):
    print(f'[3/6] Migrating table: {table_name} (start)', flush=True)
    if not _table_exists(source_conn, table_name):
        print(f'Skipping {table_name}: source table not found', flush=True)
        return {
            'table': table_name,
            'source': 0,
            'before': None,
            'after': None,
            'migrated': 0,
            'matched': True,
            'skipped': True,
        }

    if not _table_exists(dest_conn, table_name):
        source_count = _count_rows(source_conn, table_name)
        print(f'Skipping {table_name}: destination table not found', flush=True)
        return {
            'table': table_name,
            'source': source_count,
            'before': None,
            'after': None,
            'migrated': 0,
            'matched': True,
            'skipped': True,
        }

    source_columns, source_info = _table_columns(source_conn, table_name)
    dest_columns, _ = _table_columns(dest_conn, table_name)

    common_columns = [column for column in source_columns if column in dest_columns]
    if not common_columns:
        source_count = _count_rows(source_conn, table_name)
        dest_count = _count_rows(dest_conn, table_name) if _table_exists(dest_conn, table_name) else None
        print(f'Skipping {table_name}: no common columns', flush=True)
        return {
            'table': table_name,
            'source': source_count,
            'before': dest_count,
            'after': dest_count,
            'migrated': 0,
            'matched': True,
            'skipped': True,
        }

    pk_columns = [row[1] for row in source_info if int(row[5] or 0) > 0 and row[1] in common_columns]
    if not pk_columns:
        pk_columns = [common_columns[0]]

    rows = _select_rows(source_conn, table_name, common_columns)
    print(f"[3/6] {table_name}: rows to process={len(rows)}", flush=True)
    if row_transform:
        rows = [row_transform(dict(zip(common_columns, row))) for row in rows]
        rows = [tuple(row[column] for column in common_columns) for row in rows]

    dest_before = _count_rows(dest_conn, table_name)
    if rows:
        placeholders = ', '.join(['?'] * len(common_columns))
        column_sql = ', '.join(common_columns)
        conflict_target = ', '.join(pk_columns)
        update_columns = [column for column in common_columns if column not in pk_columns]
        if update_columns:
            update_sql = ', '.join([f'{column}=excluded.{column}' for column in update_columns])
            upsert_sql = (
                f"INSERT INTO {table_name} ({column_sql}) VALUES ({placeholders}) "
                f"ON CONFLICT({conflict_target}) DO UPDATE SET {update_sql}"
            )
        else:
            upsert_sql = (
                f"INSERT INTO {table_name} ({column_sql}) VALUES ({placeholders}) "
                f"ON CONFLICT({conflict_target}) DO NOTHING"
            )
        ignore_sql = (
            f"INSERT INTO {table_name} ({column_sql}) VALUES ({placeholders}) "
            "ON CONFLICT DO NOTHING"
        )
        dest_cur = dest_conn.cursor()
        if table_name == 'diet_items':
            print(
                "[3/6] diet_items: possible waits on INSERT/ON CONFLICT and FK checks (diet_id, food_id)",
                flush=True,
            )
        row_errors = 0
        for idx, row in enumerate(rows, start=1):
            started = time.monotonic()
            before_row_count = _count_rows(dest_conn, table_name)
            if FORENSIC_INSERT_LOG:
                print(f"[FORENSIC] {table_name} row={idx} sql={upsert_sql}", flush=True)
                print(f"[FORENSIC] {table_name} row={idx} params={row}", flush=True)
            try:
                dest_cur.execute(upsert_sql, row)
                if FORENSIC_INSERT_LOG:
                    print(
                        f"[FORENSIC] {table_name} row={idx} upsert_rowcount={dest_cur.rowcount}",
                        flush=True,
                    )
                dest_conn.commit()
                if FORENSIC_INSERT_LOG:
                    print(f"[FORENSIC] {table_name} row={idx} commit=ok", flush=True)
            except Exception:
                if FORENSIC_INSERT_LOG:
                    print(f"[FORENSIC] {table_name} row={idx} upsert_exception_start", flush=True)
                    print(traceback.format_exc(), flush=True)
                    print(f"[FORENSIC] {table_name} row={idx} rollback=start", flush=True)
                dest_conn.rollback()
                if FORENSIC_INSERT_LOG:
                    print(f"[FORENSIC] {table_name} row={idx} rollback=done", flush=True)
                try:
                    # Covers rows that collide on non-PK UNIQUE constraints.
                    if FORENSIC_INSERT_LOG:
                        print(f"[FORENSIC] {table_name} row={idx} fallback_sql={ignore_sql}", flush=True)
                        print(f"[FORENSIC] {table_name} row={idx} fallback_params={row}", flush=True)
                    dest_cur.execute(ignore_sql, row)
                    if FORENSIC_INSERT_LOG:
                        print(
                            f"[FORENSIC] {table_name} row={idx} fallback_rowcount={dest_cur.rowcount}",
                            flush=True,
                        )
                    dest_conn.commit()
                    if FORENSIC_INSERT_LOG:
                        print(f"[FORENSIC] {table_name} row={idx} fallback_commit=ok", flush=True)
                except Exception as row_exc:
                    if FORENSIC_INSERT_LOG:
                        print(f"[FORENSIC] {table_name} row={idx} fallback_exception={row_exc}", flush=True)
                        print(traceback.format_exc(), flush=True)
                        print(f"[FORENSIC] {table_name} row={idx} rollback_after_fallback=start", flush=True)
                    dest_conn.rollback()
                    if FORENSIC_INSERT_LOG:
                        print(f"[FORENSIC] {table_name} row={idx} rollback_after_fallback=done", flush=True)
                    row_errors += 1
                    if row_errors <= 5:
                        print(
                            f"[3/6] {table_name}: row {idx} skipped after error: {row_exc}",
                            flush=True,
                        )
            finally:
                after_row_count = _count_rows(dest_conn, table_name)
                inserted_delta = after_row_count - before_row_count
                if FORENSIC_INSERT_LOG:
                    print(
                        f"[FORENSIC] {table_name} row={idx} inserted_delta={inserted_delta} "
                        f"count_before={before_row_count} count_after={after_row_count}",
                        flush=True,
                    )
            elapsed = time.monotonic() - started
            if table_name == 'diet_items' and elapsed >= 3.0:
                print(
                    f"[3/6] diet_items: row {idx} took {elapsed:.1f}s (possible lock/wait on INSERT/FK)",
                    flush=True,
                )

            if idx % 100 == 0:
                print(f"[3/6] {table_name}: processed {idx}/{len(rows)}", flush=True)
        if row_errors:
            print(f"[3/6] {table_name}: total row errors={row_errors}", flush=True)

    if is_postgres_enabled() and table_name in SEQUENCE_TABLES:
        seq_cur = dest_conn.cursor()
        seq_cur.execute(
            f"""
            SELECT setval(
                pg_get_serial_sequence('{table_name}', 'id'),
                COALESCE((SELECT MAX(id) FROM {table_name}), 1),
                EXISTS(SELECT 1 FROM {table_name})
            )
            """
        )
        dest_conn.commit()

    dest_after = _count_rows(dest_conn, table_name)
    matched = len(rows) == dest_after
    if table_name in ALLOW_EXTRA_ROWS_TABLES:
        matched = dest_after >= len(rows)

    result = {
        'table': table_name,
        'source': len(rows),
        'before': dest_before,
        'after': dest_after,
        'migrated': max(0, dest_after - dest_before),
        'matched': matched,
        'skipped': False,
    }
    print(
        f"[3/6] Migrating table: {table_name} (done) "
        f"source={result['source']} before={result['before']} after={result['after']}",
        flush=True,
    )
    return result


def _rebuild_food_search(dest_conn):
    print('[4/6] Rebuilding foods_search index (start)', flush=True)
    cur = dest_conn.cursor()
    rebuild_foods_search_index(cur)
    dest_conn.commit()
    print('[4/6] Rebuilding foods_search index (done)', flush=True)


def migrate(source_db_path):
    if not is_postgres_enabled():
        raise SystemExit('DATABASE_URL no está definida. Ejecuta la migración contra PostgreSQL.')

    source_path = Path(source_db_path)
    if not source_path.exists():
        raise SystemExit(f'No existe la base SQLite de origen: {source_path}')

    print('Migration started', flush=True)
    print(f'Source SQLite: {source_path}', flush=True)
    print('Connecting to destination PostgreSQL...', flush=True)
    source_conn = source_sqlite3.connect(str(source_path))
    dest_conn = dest_sqlite3.connect(os.environ.get('DATABASE_URL', ''))
    print('Destination PostgreSQL connection ready', flush=True)

    try:
        try:
            _bootstrap_destination_schema(dest_conn)
        except Exception as exc:
            raise RuntimeError(f'Error during schema bootstrap: {exc}') from exc

        summary = []
        try:
            category_summary, category_id_map = _migrate_named_table(source_conn, dest_conn, 'categories')
        except Exception as exc:
            raise RuntimeError(f'Error migrating lookup table categories: {exc}') from exc
        summary.append(category_summary)
        try:
            exercise_category_summary, exercise_category_id_map = _migrate_named_table(source_conn, dest_conn, 'exercise_categories')
        except Exception as exc:
            raise RuntimeError(f'Error migrating lookup table exercise_categories: {exc}') from exc
        summary.append(exercise_category_summary)

        def _foods_row_transform(row):
            category_id = row.get('category_id')
            if category_id is not None:
                try:
                    category_id_i = int(category_id)
                except Exception:
                    category_id_i = None
                if category_id_i is not None:
                    row['category_id'] = category_id_map.get(category_id_i, category_id_i)
            return row

        def _exercises_row_transform(row):
            for key in ('exercise_category_id', 'exercise_category_id_2'):
                value = row.get(key)
                if value is None:
                    continue
                try:
                    value_i = int(value)
                except Exception:
                    continue
                row[key] = exercise_category_id_map.get(value_i, value_i)
            return row

        for table_name in TABLES_TO_MIGRATE:
            try:
                if table_name == 'foods':
                    summary.append(_copy_table(source_conn, dest_conn, table_name, row_transform=_foods_row_transform))
                elif table_name == 'exercises':
                    summary.append(_copy_table(source_conn, dest_conn, table_name, row_transform=_exercises_row_transform))
                else:
                    summary.append(_copy_table(source_conn, dest_conn, table_name))
            except Exception as exc:
                raise RuntimeError(f'Error migrating table {table_name}: {exc}') from exc

        try:
            _rebuild_food_search(dest_conn)
        except Exception as exc:
            raise RuntimeError(f'Error rebuilding foods_search index: {exc}') from exc

        print('[5/6] Verifying row counts (start)', flush=True)
        source_foods_search = _count_rows(source_conn, 'foods_search')
        dest_foods_search = _count_rows(dest_conn, 'foods_search')
        summary.append({
            'table': 'foods_search',
            'source': source_foods_search,
            'before': None,
            'after': dest_foods_search,
            'migrated': dest_foods_search,
            'matched': source_foods_search == dest_foods_search,
            'skipped': False,
        })
        print('[5/6] Verifying row counts (done)', flush=True)

        mismatches = [row for row in summary if not row.get('skipped', False) and not row['matched']]
        print('[6/6] Final summary', flush=True)
        print('Migración finalizada')
        for row in summary:
            status = 'omitida' if row.get('skipped', False) else 'ok'
            before_text = '' if row['before'] is None else f", before={row['before']}"
            print(
                f"- {row['table']}: source={row['source']}{before_text}, after={row['after']}, "
                f"migrated={row['migrated']}, status={status}"
            )
        if mismatches:
            print('Verificación fallida en:', ', '.join(row['table'] for row in mismatches))
            raise SystemExit(1)
        print('Verificación correcta: los conteos coinciden con SQLite')
    except Exception as exc:
        dest_conn.rollback()
        print(f'Migration failed: {exc}', flush=True)
        raise
    finally:
        source_conn.close()
        dest_conn.close()


def parse_args():
    parser = argparse.ArgumentParser(description='Migrar data/foods.db de SQLite a PostgreSQL')
    parser.add_argument('--source-db', default=str(DEFAULT_SOURCE_DB), help='Ruta de la base SQLite de origen')
    return parser.parse_args()


if __name__ == '__main__':
    args = parse_args()
    migrate(args.source_db)
