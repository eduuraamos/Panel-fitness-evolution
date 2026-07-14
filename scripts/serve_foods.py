#!/usr/bin/env python3
"""Servidor HTTP simple para gestionar alimentos y ejercicios (UI + JSON API).
"""
from http.server import HTTPServer, BaseHTTPRequestHandler
from db_adapter import sqlite3_compat as sqlite3
from food_schema import (
    ensure_catalog_schema,
    ensure_default_food_categories as bootstrap_default_food_categories,
    ensure_exercise_schema as bootstrap_exercise_schema,
    rebuild_foods_search_index as catalog_rebuild_foods_search_index,
    refresh_food_search_row as catalog_refresh_food_search_row,
    supports_foods_search_fts,
)
import html
import os
import re
import calendar
import base64
import uuid
import mimetypes
import socket
import urllib.parse
import json
import unicodedata
import io
import time
import hmac
import hashlib
from difflib import SequenceMatcher

from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib import colors
from reportlab.lib.utils import ImageReader

BASE_DIR = os.path.dirname(os.path.dirname(__file__))
STATIC_DIR = "static"
DATA_DIR = os.environ.get("DATA_DIR", os.path.join(BASE_DIR, "data"))
DB_PATH = os.path.join(DATA_DIR, "foods.db")
STATIC_BASE_DIR = os.path.join(os.path.dirname(__file__), STATIC_DIR)
UPLOADS_DIR = os.environ.get("UPLOADS_DIR", os.path.join(DATA_DIR, "uploads"))
UPLOADS_FOODS_DIR = os.path.join(UPLOADS_DIR, "foods")
HOST = "0.0.0.0"
PORT = int(os.environ.get("PORT", "8005"))
CLIENT_PORTAL_SECRET = os.environ.get("CLIENT_PORTAL_SECRET", "nutrition-app-client-portal")
CLIENT_PORTAL_COOKIE = "client_portal_session"
CLIENT_PORTAL_SESSION_TTL_SECONDS = 60 * 60 * 24 * 30
ADMIN_PORTAL_SECRET = os.environ.get("ADMIN_PORTAL_SECRET", "nutrition-app-admin-portal")
ADMIN_PORTAL_COOKIE = "admin_portal_session"
ADMIN_PORTAL_SESSION_TTL_SECONDS = 60 * 60 * 24 * 30
ADMIN_PORTAL_USERNAME = os.environ.get("ADMIN_PORTAL_USERNAME", "admin")
ADMIN_PORTAL_PASSWORD = os.environ.get("ADMIN_PORTAL_PASSWORD", "change-me-now")

# migrations
_schema_checked = False

DEFAULT_FOOD_CATEGORIES = [
    'Carnes', 'Pescados', 'Huevos', 'Lácteos', 'Arroz', 'Pasta', 'Patata/Batata',
    'Frutas', 'Verduras', 'Legumbres', 'Frutos secos', 'Aceites', 'Grasas saludables',
    'Salsas', 'Embutidos', 'Bebidas', 'Dulces', 'Suplementos'
]

DEFAULT_DIET_INSTRUCTIONS_TEMPLATE = (
    "Hidratacion: bebe al menos 2 litros de agua al dia.\n"
    "Horarios: intenta mantener horarios regulares y evita saltarte comidas.\n"
    "Coccion: prioriza plancha, horno, vapor o airfryer, reduciendo fritos.\n"
    "Adherencia: si un alimento no te encaja, usa una opcion similar y manten cantidades.\n"
    "Constancia: revisa sensaciones, energia y digestion para ajustar con tu entrenador."
)

SPANISH_MONTHS = [
    'ENERO', 'FEBRERO', 'MARZO', 'ABRIL', 'MAYO', 'JUNIO',
    'JULIO', 'AGOSTO', 'SEPTIEMBRE', 'OCTUBRE', 'NOVIEMBRE', 'DICIEMBRE'
]


def normalize_text(value):
    text = unicodedata.normalize('NFKD', str(value or ''))
    text = ''.join(ch for ch in text if not unicodedata.combining(ch))
    text = text.lower().strip()
    return re.sub(r'\s+', ' ', text)


def parse_numeric_input(value, default=0.0):
    text = str(value or '').strip()
    if not text:
        return float(default)
    # Accept localized decimals (e.g. 12,5) and values with units (e.g. "12 g").
    text = text.replace(',', '.')
    m = re.search(r'[-+]?\d+(?:\.\d+)?', text)
    if not m:
        return float(default)
    try:
        return float(m.group(0))
    except Exception:
        return float(default)


def parse_gluten_input(value):
    if value is None:
        return None
    text = str(value).strip().lower()
    if text == '':
        return None
    if text in ('1', 'true', 'yes', 'si', 'con'):
        return 1
    if text in ('0', 'false', 'no', 'sin'):
        return 0
    return None


def query_terms(query):
    return [t for t in re.findall(r'[a-z0-9]+', normalize_text(query)) if t]


def build_fts_query(query):
    terms = query_terms(query)
    if not terms:
        return ''
    return ' '.join([f'"{t}"*' for t in terms])


def _coerce_schema_connection(conn_or_path=None):
    if conn_or_path is None:
        conn_or_path = DB_PATH
    if hasattr(conn_or_path, 'cursor'):
        return conn_or_path, False
    return sqlite3.connect(conn_or_path), True


def rebuild_foods_search_index(cur):
    catalog_rebuild_foods_search_index(cur)


def refresh_food_search_row(cur, food_id):
    catalog_refresh_food_search_row(cur, food_id)


def ensure_brand_column(conn_or_path=None):
    global _schema_checked
    if _schema_checked:
        return
    conn, should_close = _coerce_schema_connection(conn_or_path)
    ensure_catalog_schema(conn)
    cur = conn.cursor()
    cur.execute("PRAGMA table_info(foods)")
    cols = [r[1] for r in cur.fetchall()]
    if 'brand' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN brand TEXT")
            conn.commit()
        except Exception:
            pass
    if 'photo_path' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN photo_path TEXT")
            conn.commit()
        except Exception:
            pass
    if 'nutrition_mode' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN nutrition_mode TEXT DEFAULT 'per100'")
            conn.commit()
        except Exception:
            pass
    if 'per100_unit' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN per100_unit TEXT DEFAULT 'g'")
            conn.commit()
        except Exception:
            pass
    if 'barcode' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN barcode TEXT")
            conn.commit()
        except Exception:
            pass
    if 'keywords' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN keywords TEXT")
            conn.commit()
        except Exception:
            pass
    if 'is_active' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN is_active INTEGER DEFAULT 1")
            cur.execute("UPDATE foods SET is_active = 1 WHERE is_active IS NULL")
            conn.commit()
        except Exception:
            pass
    if 'is_verified' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN is_verified INTEGER DEFAULT 0")
            cur.execute("UPDATE foods SET is_verified = 0 WHERE is_verified IS NULL")
            conn.commit()
        except Exception:
            pass
    if 'has_gluten' not in cols:
        try:
            cur.execute("ALTER TABLE foods ADD COLUMN has_gluten INTEGER")
            conn.commit()
        except Exception:
            pass

    try:
        rebuild_foods_search_index(cur)
        conn.commit()
    except Exception:
        pass

    if should_close:
        conn.close()
    _schema_checked = True


def ensure_exercises_table(conn_or_path=None):
    bootstrap_exercise_schema(conn_or_path or DB_PATH)


def ensure_routines_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS routines (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        description TEXT,
        created_at TEXT NOT NULL
    )
    """
    )
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS routine_items (
        id INTEGER PRIMARY KEY,
        routine_id INTEGER NOT NULL,
        day_name TEXT NOT NULL,
        exercise_id INTEGER,
        sets_text TEXT,
        reps_text TEXT,
        notes TEXT,
        sort_order INTEGER DEFAULT 0,
        FOREIGN KEY(routine_id) REFERENCES routines(id),
        FOREIGN KEY(exercise_id) REFERENCES exercises(id)
    )
    """
    )
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS routine_days (
        id INTEGER PRIMARY KEY,
        routine_id INTEGER NOT NULL,
        day_index INTEGER NOT NULL,
        day_name TEXT NOT NULL,
        day_type TEXT NOT NULL DEFAULT 'train',
        UNIQUE(routine_id, day_index),
        FOREIGN KEY(routine_id) REFERENCES routines(id)
    )
    """
    )
    conn.commit()

    cur.execute("PRAGMA table_info(routines)")
    routine_cols = [r[1] for r in cur.fetchall()]
    if 'is_template' not in routine_cols:
        cur.execute("ALTER TABLE routines ADD COLUMN is_template INTEGER DEFAULT 1")
        cur.execute("UPDATE routines SET is_template = 1 WHERE is_template IS NULL")
        conn.commit()
    if 'client_name' not in routine_cols:
        cur.execute("ALTER TABLE routines ADD COLUMN client_name TEXT")
        conn.commit()

    cur.execute("PRAGMA table_info(routine_items)")
    routine_item_cols = [r[1] for r in cur.fetchall()]
    if 'day_index' not in routine_item_cols:
        cur.execute("ALTER TABLE routine_items ADD COLUMN day_index INTEGER")
        conn.commit()

    default_days = ['Lunes', 'Martes', 'Miércoles', 'Jueves', 'Viernes', 'Sábado', 'Domingo']
    for idx, day_name in enumerate(default_days):
        cur.execute(
            "UPDATE routine_items SET day_index = ? WHERE day_index IS NULL AND day_name = ?",
            (idx, day_name),
        )
    conn.commit()
    if should_close:
        conn.close()


def get_default_routine_days():
    return [
        (0, 'Lunes', 'train'),
        (1, 'Martes', 'train'),
        (2, 'Miércoles', 'train'),
        (3, 'Jueves', 'train'),
        (4, 'Viernes', 'train'),
        (5, 'Sábado', 'rest'),
        (6, 'Domingo', 'rest'),
    ]


def ensure_routine_days_for_routine(routine_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    for day_index, day_name, day_type in get_default_routine_days():
        cur.execute(
            "INSERT OR IGNORE INTO routine_days(routine_id, day_index, day_name, day_type) VALUES(?,?,?,?)",
            (routine_id, day_index, day_name, day_type),
        )
    conn.commit()
    conn.close()


def get_routine_days(routine_id):
    ensure_routine_days_for_routine(routine_id)
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT day_index, day_name, day_type FROM routine_days WHERE routine_id = ? ORDER BY day_index",
        (routine_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def ensure_diets_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS diets (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        description TEXT,
        client_instructions TEXT,
        is_template INTEGER DEFAULT 1,
        client_diet_name TEXT,
        client_weight_kg REAL DEFAULT 0,
        client_name TEXT,
        client_height_cm REAL DEFAULT 0,
        client_age INTEGER DEFAULT 0,
        created_at TEXT NOT NULL
    )
    """
    )
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS diet_items (
        id INTEGER PRIMARY KEY,
        diet_id INTEGER NOT NULL,
        food_id INTEGER NOT NULL,
        quantity TEXT,
        note TEXT,
        FOREIGN KEY(diet_id) REFERENCES diets(id),
        FOREIGN KEY(food_id) REFERENCES foods(id)
    )
    """
    )
    conn.commit()
    cur.execute("PRAGMA table_info(diets)")
    diet_cols = [r[1] for r in cur.fetchall()]
    if 'client_weight_kg' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN client_weight_kg REAL DEFAULT 0")
    if 'is_template' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN is_template INTEGER DEFAULT 1")
        cur.execute("UPDATE diets SET is_template = 1 WHERE is_template IS NULL")
    if 'client_diet_name' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN client_diet_name TEXT")
    if 'client_name' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN client_name TEXT")
    if 'client_height_cm' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN client_height_cm REAL DEFAULT 0")
    if 'client_age' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN client_age INTEGER DEFAULT 0")
    if 'client_instructions' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN client_instructions TEXT")
    if 'display_number' not in diet_cols:
        cur.execute("ALTER TABLE diets ADD COLUMN display_number INTEGER")
    cur.execute("UPDATE diets SET display_number = id WHERE display_number IS NULL")
    cur.execute("PRAGMA table_info(diet_items)")
    cols = [r[1] for r in cur.fetchall()]
    if 'day_of_week' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN day_of_week TEXT")
    if 'meal_time' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN meal_time TEXT")
    if 'meal_id' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN meal_id INTEGER")
    if 'quantity_grams' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN quantity_grams REAL DEFAULT 100")
    if 'quantity_units' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN quantity_units REAL DEFAULT 1")
    if 'option_group' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN option_group INTEGER DEFAULT 1")
    cur.execute("UPDATE diet_items SET option_group = 1 WHERE option_group IS NULL OR option_group NOT IN (1,2)")
    conn.commit()
    if should_close:
        conn.close()


def ensure_app_settings_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS app_settings (
        key TEXT PRIMARY KEY,
        value TEXT
    )
    """
    )
    cur.execute(
        "INSERT OR IGNORE INTO app_settings(key, value) VALUES(?, ?)",
        ('diet_instructions_template', DEFAULT_DIET_INSTRUCTIONS_TEMPLATE),
    )
    cur.execute(
        "INSERT OR IGNORE INTO app_settings(key, value) VALUES(?, ?)",
        ('admin_portal_username', str(ADMIN_PORTAL_USERNAME or 'admin').strip() or 'admin'),
    )
    cur.execute(
        "INSERT OR IGNORE INTO app_settings(key, value) VALUES(?, ?)",
        ('admin_portal_password_hash', hash_admin_password(str(ADMIN_PORTAL_PASSWORD or 'change-me-now'))),
    )
    conn.commit()
    if should_close:
        conn.close()


def get_app_setting(key, default_value=''):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT value FROM app_settings WHERE key = ?", (key,))
    row = cur.fetchone()
    conn.close()
    if not row:
        return default_value
    return row[0] if row[0] is not None else default_value


def set_app_setting(key, value):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "INSERT INTO app_settings(key, value) VALUES(?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (key, value),
    )
    conn.commit()
    conn.close()


def get_diet_instructions_template():
    value = get_app_setting('diet_instructions_template', DEFAULT_DIET_INSTRUCTIONS_TEMPLATE)
    return (value or '').strip() or DEFAULT_DIET_INSTRUCTIONS_TEMPLATE


def ensure_clients_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS clients (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        phone TEXT,
        email TEXT,
        birthdate TEXT,
        height_cm REAL DEFAULT 0,
        weight_kg REAL DEFAULT 0,
        objectives TEXT,
        plan_start_date TEXT,
        plan_end_date TEXT,
        plan_amount REAL DEFAULT 0,
        plan_notes TEXT,
        created_at TEXT NOT NULL
    )
    """
    )
    conn.commit()
    cur.execute("PRAGMA table_info(clients)")
    cols = [r[1] for r in cur.fetchall()]
    if 'plan_start_date' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN plan_start_date TEXT")
    if 'plan_end_date' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN plan_end_date TEXT")
    if 'plan_amount' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN plan_amount REAL DEFAULT 0")
    if 'plan_notes' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN plan_notes TEXT")
    if 'email' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN email TEXT")
    if 'client_access_code' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN client_access_code TEXT")
    if 'client_password_hash' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN client_password_hash TEXT")
    if 'daily_steps_goal' not in cols:
        cur.execute("ALTER TABLE clients ADD COLUMN daily_steps_goal INTEGER DEFAULT 0")
    cur.execute(
        "UPDATE clients SET client_access_code = ('C' || CAST(id AS TEXT)) WHERE COALESCE(TRIM(client_access_code), '') = ''"
    )
    cur.execute("CREATE INDEX IF NOT EXISTS idx_clients_email ON clients(email)")
    conn.commit()
    if should_close:
        conn.close()


def ensure_payment_plans_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS payment_plans (
        id INTEGER PRIMARY KEY,
        client_id INTEGER NOT NULL,
        start_date TEXT NOT NULL,
        end_date TEXT NOT NULL,
        amount REAL DEFAULT 0,
        notes TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )
    """
    )
    conn.commit()
    if should_close:
        conn.close()


def ensure_client_history_tables(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS client_diet_history (
        id INTEGER PRIMARY KEY,
        client_id INTEGER NOT NULL,
        diet_id INTEGER NOT NULL,
        start_date TEXT,
        end_date TEXT,
        is_active INTEGER DEFAULT 1,
        notes TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY(client_id) REFERENCES clients(id),
        FOREIGN KEY(diet_id) REFERENCES diets(id)
    )
    """
    )
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS client_training_history (
        id INTEGER PRIMARY KEY,
        client_id INTEGER NOT NULL,
        exercise_id INTEGER,
        training_name TEXT,
        start_date TEXT,
        end_date TEXT,
        is_active INTEGER DEFAULT 1,
        notes TEXT,
        created_at TEXT NOT NULL,
        FOREIGN KEY(client_id) REFERENCES clients(id),
        FOREIGN KEY(exercise_id) REFERENCES exercises(id)
    )
    """
    )
    conn.commit()
    cur.execute("PRAGMA table_info(client_diet_history)")
    cols = [r[1] for r in cur.fetchall()]
    if 'template_diet_id' not in cols:
        cur.execute("ALTER TABLE client_diet_history ADD COLUMN template_diet_id INTEGER")
    cur.execute("PRAGMA table_info(client_training_history)")
    training_cols = [r[1] for r in cur.fetchall()]
    if 'routine_id' not in training_cols:
        cur.execute("ALTER TABLE client_training_history ADD COLUMN routine_id INTEGER")
    if 'template_routine_id' not in training_cols:
        cur.execute("ALTER TABLE client_training_history ADD COLUMN template_routine_id INTEGER")

    # Backfill: routines already assigned as client copies before template flag existed.
    cur.execute(
        """
        UPDATE routines
        SET is_template = 0
        WHERE id IN (
            SELECT DISTINCT routine_id
            FROM client_training_history
            WHERE COALESCE(template_routine_id, 0) > 0 AND COALESCE(routine_id, 0) > 0
        )
        """
    )
    conn.commit()
    if should_close:
        conn.close()


def ensure_fasting_weights_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS client_fasting_weights (
        id INTEGER PRIMARY KEY,
        client_id INTEGER NOT NULL,
        date_text TEXT NOT NULL,
        weight_kg REAL NOT NULL,
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL,
        UNIQUE(client_id, date_text),
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )
    """
    )
    cur.execute("CREATE INDEX IF NOT EXISTS idx_fasting_weights_client_date ON client_fasting_weights(client_id, date_text)")
    conn.commit()
    if should_close:
        conn.close()


def ensure_client_daily_steps_table(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS client_daily_steps (
        id INTEGER PRIMARY KEY,
        client_id INTEGER NOT NULL,
        date_text TEXT NOT NULL,
        steps INTEGER NOT NULL,
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL,
        UNIQUE(client_id, date_text),
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )
    """
    )
    cur.execute("CREATE INDEX IF NOT EXISTS idx_client_daily_steps_client_date ON client_daily_steps(client_id, date_text)")
    conn.commit()
    if should_close:
        conn.close()


def get_fasting_weight_slots():
    from datetime import date
    today = date.today()
    slots = []
    for delta in range(-2, 6):
        month_raw = today.month + delta
        year = today.year + ((month_raw - 1) // 12)
        month = ((month_raw - 1) % 12) + 1
        slots.append((year, month))
    return slots


def get_client_fasting_weights_map(client_id, start_date_text, end_date_text):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT date_text, weight_kg
        FROM client_fasting_weights
        WHERE client_id = ? AND date_text >= ? AND date_text <= ?
        ORDER BY date_text
        """,
        (int(client_id), start_date_text, end_date_text),
    )
    rows = cur.fetchall()
    conn.close()
    out = {}
    for date_text, weight_kg in rows:
        out[str(date_text)] = float(weight_kg or 0)
    return out


def get_client_daily_steps_goal(client_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT COALESCE(daily_steps_goal, 0) FROM clients WHERE id = ?", (int(client_id),))
    row = cur.fetchone()
    conn.close()
    if not row:
        return 0
    try:
        return int(row[0] or 0)
    except Exception:
        return 0


def get_client_daily_steps_map(client_id, start_date_text, end_date_text):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT date_text, steps
        FROM client_daily_steps
        WHERE client_id = ? AND date_text >= ? AND date_text <= ?
        ORDER BY date_text
        """,
        (int(client_id), start_date_text, end_date_text),
    )
    rows = cur.fetchall()
    conn.close()
    out = {}
    for date_text, steps in rows:
        out[str(date_text)] = int(steps or 0)
    return out


def upsert_client_fasting_weight(client_id, date_text, weight_kg):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    if weight_kg is None:
        cur.execute(
            "DELETE FROM client_fasting_weights WHERE client_id = ? AND date_text = ?",
            (int(client_id), date_text),
        )
    else:
        cur.execute(
            """
            INSERT INTO client_fasting_weights(client_id, date_text, weight_kg, created_at, updated_at)
            VALUES(?,?,?,datetime('now'),datetime('now'))
            ON CONFLICT(client_id, date_text)
            DO UPDATE SET weight_kg = excluded.weight_kg, updated_at = datetime('now')
            """,
            (int(client_id), date_text, float(weight_kg)),
        )
    conn.commit()
    conn.close()


def upsert_client_daily_steps(client_id, date_text, steps):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    if steps is None:
        cur.execute(
            "DELETE FROM client_daily_steps WHERE client_id = ? AND date_text = ?",
            (int(client_id), date_text),
        )
    else:
        cur.execute(
            """
            INSERT INTO client_daily_steps(client_id, date_text, steps, created_at, updated_at)
            VALUES(?,?,?,datetime('now'),datetime('now'))
            ON CONFLICT(client_id, date_text)
            DO UPDATE SET steps = excluded.steps, updated_at = datetime('now')
            """,
            (int(client_id), date_text, int(steps)),
        )
    conn.commit()
    conn.close()


def render_fasting_weights_panel(client_id, panel_id='fasting-weight-panel', include_client_id=True):
    slots = get_fasting_weight_slots()
    first_year, first_month = slots[0]
    last_year, last_month = slots[-1]
    start_date_text = f"{first_year:04d}-{first_month:02d}-01"
    last_day = calendar.monthrange(last_year, last_month)[1]
    end_date_text = f"{last_year:04d}-{last_month:02d}-{last_day:02d}"
    weights_map = get_client_fasting_weights_map(client_id, start_date_text, end_date_text)

    month_columns = []
    for year, month in slots:
        max_day = calendar.monthrange(year, month)[1]
        rows = []
        for day in range(1, max_day + 1):
            date_key = f"{year:04d}-{month:02d}-{day:02d}"
            value = weights_map.get(date_key)
            value_text = '' if value is None else f"{value:.2f}".replace('.', ',')
            rows.append(
                f'<label class="fw-row fw-day-row" data-date="{date_key}">'
                f'<span>{day}:</span>'
                f'<input class="fw-input" type="text" inputmode="decimal" data-date="{date_key}" value="{html.escape(value_text)}" placeholder="-" />'
                '</label>'
            )
        month_columns.append(
            '<div class="fw-month">'
            f'<div class="fw-month-title">{SPANISH_MONTHS[month - 1]}</div>'
            f'<div class="fw-month-days">{"".join(rows)}</div>'
            '</div>'
        )

    client_payload = f"client_id: {int(client_id)}," if include_client_id else ''
    return f'''
    <div class="fw-wrap" id="{panel_id}">
        <div class="fw-head">Peso corporal en ayunas</div>
        <div class="fw-grid">{"".join(month_columns)}</div>
        <div class="fw-foot">Editable por ti y por el cliente. Se guarda automáticamente al salir del campo.</div>
    </div>
    <script>
    (function() {{
        const root = document.getElementById('{panel_id}');
        if (!root) return;
        const inputs = Array.from(root.querySelectorAll('.fw-input'));
        const dayRows = Array.from(root.querySelectorAll('.fw-day-row'));

        function parseIsoDate(dateText) {{
            const parts = String(dateText || '').split('-');
            if (parts.length !== 3) return null;
            const y = Number(parts[0]);
            const m = Number(parts[1]);
            const d = Number(parts[2]);
            if (!Number.isFinite(y) || !Number.isFinite(m) || !Number.isFinite(d)) return null;
            return new Date(y, m - 1, d);
        }}

        function isMonday(dateText) {{
            const dt = parseIsoDate(dateText);
            if (!dt) return false;
            return dt.getDay() === 1;
        }}

        function formatWeight(n) {{
            return Number(n || 0).toFixed(2).replace('.', ',');
        }}

        function formatPct(p) {{
            const sign = p > 0 ? '+' : '';
            return sign + Number(p || 0).toFixed(2).replace('.', ',') + '%';
        }}

        function renderWeeklyMeans() {{
            root.querySelectorAll('.fw-mean-row').forEach((el) => el.remove());
            const rowByDate = new Map();
            const valueByDate = new Map();

            dayRows.forEach((row) => {{
                const dateText = row.dataset.date;
                if (!dateText) return;
                rowByDate.set(dateText, row);
                const input = row.querySelector('.fw-input');
                if (!input) return;
                const parsed = normalizeWeight(input.value);
                if (!parsed.invalid && !parsed.empty) valueByDate.set(dateText, parsed.value);
            }});

            const orderedDates = Array.from(rowByDate.keys()).sort();
            let previousMonday = null;
            let previousAverage = null;

            for (const dateText of orderedDates) {{
                if (!isMonday(dateText)) continue;
                if (!previousMonday) {{
                    previousMonday = dateText;
                    continue;
                }}

                const weekDates = orderedDates.filter((d) => d >= previousMonday && d <= dateText);
                const values = weekDates
                    .map((d) => valueByDate.get(d))
                    .filter((v) => Number.isFinite(v));

                if (!values.length) {{
                    previousMonday = dateText;
                    continue;
                }}

                const avg = values.reduce((a, b) => a + b, 0) / values.length;
                let pctText = '(s/d)';
                let pctClass = 'neutral';
                if (previousAverage && previousAverage > 0) {{
                    const pct = ((avg - previousAverage) / previousAverage) * 100;
                    pctText = '(' + formatPct(pct) + ')';
                    pctClass = pct < 0 ? 'down' : (pct > 0 ? 'up' : 'neutral');
                }}

                const meanRow = document.createElement('div');
                meanRow.className = 'fw-row fw-mean-row';
                meanRow.innerHTML = '<span>M:</span><strong class="fw-mean-value ' + pctClass + '">' + formatWeight(avg) + ' <em>' + pctText + '</em></strong>';
                const anchor = rowByDate.get(dateText);
                if (anchor && anchor.parentNode) anchor.insertAdjacentElement('afterend', meanRow);

                previousAverage = avg;
                previousMonday = dateText;
            }}
        }}

        function normalizeWeight(raw) {{
            const text = String(raw || '').trim();
            if (!text) return {{ empty: true, value: null, text: '' }};
            const cleaned = text.replace(',', '.');
            const n = Number(cleaned);
            if (!Number.isFinite(n) || n <= 0 || n > 400) return {{ invalid: true }};
            return {{ empty: false, value: n, text: n.toFixed(2).replace('.', ',') }};
        }}
        async function saveInput(input) {{
            const parsed = normalizeWeight(input.value);
            if (parsed.invalid) {{
                input.classList.add('is-error');
                return;
            }}
            input.classList.remove('is-error');
            input.value = parsed.text;
            input.classList.add('is-saving');
            try {{
                const res = await fetch('/api/client_fasting_weight', {{
                    method: 'PUT',
                    headers: {{ 'Content-Type': 'application/json' }},
                    body: JSON.stringify({{
                        {client_payload}
                        date: input.dataset.date,
                        weight_kg: parsed.empty ? '' : parsed.value
                    }})
                }});
                if (!res.ok) throw new Error('save failed');
                input.classList.remove('is-saving');
                input.classList.add('is-saved');
                renderWeeklyMeans();
                setTimeout(() => input.classList.remove('is-saved'), 650);
            }} catch (_e) {{
                input.classList.remove('is-saving');
                input.classList.add('is-error');
            }}
        }}
        inputs.forEach((input) => {{
            input.addEventListener('blur', () => saveInput(input));
            input.addEventListener('keydown', (ev) => {{
                if (ev.key === 'Enter') {{
                    ev.preventDefault();
                    input.blur();
                }}
            }});
            input.addEventListener('input', () => input.classList.remove('is-error'));
        }});
        renderWeeklyMeans();
    }})();
    </script>
    '''


def render_client_daily_steps_panel(client_id, panel_id='client-steps-panel', include_client_id=True, daily_goal=0):
    slots = get_fasting_weight_slots()
    first_year, first_month = slots[0]
    last_year, last_month = slots[-1]
    start_date_text = f"{first_year:04d}-{first_month:02d}-01"
    last_day = calendar.monthrange(last_year, last_month)[1]
    end_date_text = f"{last_year:04d}-{last_month:02d}-{last_day:02d}"
    steps_map = get_client_daily_steps_map(client_id, start_date_text, end_date_text)

    month_columns = []
    for year, month in slots:
        max_day = calendar.monthrange(year, month)[1]
        rows = []
        for day in range(1, max_day + 1):
            date_key = f"{year:04d}-{month:02d}-{day:02d}"
            value = steps_map.get(date_key)
            value_text = '' if value is None else str(int(value))
            rows.append(
                f'<label class="fw-row" data-date="{date_key}">'
                f'<span>{day}:</span>'
                f'<input class="fw-steps-input" type="text" inputmode="numeric" data-date="{date_key}" value="{html.escape(value_text)}" placeholder="-" />'
                '</label>'
            )
        month_columns.append(
            '<div class="fw-month">'
            f'<div class="fw-month-title">{SPANISH_MONTHS[month - 1]}</div>'
            f'<div class="fw-month-days">{"".join(rows)}</div>'
            '</div>'
        )

    goal_value = int(daily_goal or 0)
    goal_label = f"{goal_value} pasos" if goal_value > 0 else 'Sin objetivo'
    client_payload = f"client_id: {int(client_id)}," if include_client_id else ''
    return f'''
    <div class="fw-wrap" id="{panel_id}">
        <div class="fw-head">Pasos diarios</div>
        <div class="fw-grid">{"".join(month_columns)}</div>
        <div class="fw-foot"><strong>Objetivo diario:</strong> {html.escape(goal_label)}</div>
        <div class="fw-foot">Editable por ti y por el cliente. Se guarda automáticamente al salir del campo.</div>
    </div>
    <script>
    (function() {{
        const root = document.getElementById('{panel_id}');
        if (!root) return;
        const inputs = Array.from(root.querySelectorAll('.fw-steps-input'));
        const dailyGoal = {goal_value};

        function normalizeSteps(raw) {{
            const text = String(raw || '').trim();
            if (!text) return {{ empty: true, value: null, text: '' }};
            const digits = text.replace(/[^0-9]/g, '');
            if (!digits) return {{ invalid: true }};
            const value = Number(digits);
            if (!Number.isFinite(value) || value < 0 || value > 100000) return {{ invalid: true }};
            return {{ empty: false, value, text: String(Math.round(value)) }};
        }}

        function applyGoalStatus(input, parsed) {{
            input.classList.remove('goal-met', 'goal-missed');
            if (!parsed || parsed.invalid || parsed.empty) return;
            if (!dailyGoal || dailyGoal <= 0) return;
            if (parsed.value >= dailyGoal) {{
                input.classList.add('goal-met');
            }} else {{
                input.classList.add('goal-missed');
            }}
        }}

        async function saveInput(input) {{
            const parsed = normalizeSteps(input.value);
            if (parsed.invalid) {{
                input.classList.add('is-error');
                input.classList.remove('goal-met', 'goal-missed');
                return;
            }}
            input.classList.remove('is-error');
            input.value = parsed.text;
            applyGoalStatus(input, parsed);
            input.classList.add('is-saving');
            try {{
                const res = await fetch('/api/client_daily_steps', {{
                    method: 'PUT',
                    headers: {{ 'Content-Type': 'application/json' }},
                    body: JSON.stringify({{
                        {client_payload}
                        date: input.dataset.date,
                        steps: parsed.empty ? '' : parsed.value
                    }})
                }});
                if (!res.ok) throw new Error('save failed');
                input.classList.remove('is-saving');
                input.classList.add('is-saved');
                setTimeout(() => input.classList.remove('is-saved'), 650);
            }} catch (_e) {{
                input.classList.remove('is-saving');
                input.classList.add('is-error');
            }}
        }}

        inputs.forEach((input) => {{
            input.addEventListener('blur', () => saveInput(input));
            input.addEventListener('keydown', (ev) => {{
                if (ev.key === 'Enter') {{
                    ev.preventDefault();
                    input.blur();
                }}
            }});
            input.addEventListener('input', () => {{
                input.classList.remove('is-error');
                const parsed = normalizeSteps(input.value);
                applyGoalStatus(input, parsed);
            }});

            const parsed = normalizeSteps(input.value);
            applyGoalStatus(input, parsed);
        }});
    }})();
    </script>
    '''


# helpers
def get_foods():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT f.id, f.name, f.brand, c.name as category, f.calories, f.protein, f.carbs, f.fats, f.serving_size, "
        "COALESCE(f.photo_path, ''), COALESCE(f.nutrition_mode, 'per100'), COALESCE(f.per100_unit, 'g'), COALESCE(f.is_verified, 0), f.has_gluten "
        "FROM foods f LEFT JOIN categories c ON f.category_id = c.id "
        "ORDER BY COALESCE(c.name, 'Sin categoría'), f.name"
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_categories():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT id, name FROM categories ORDER BY name")
    rows = cur.fetchall()
    conn.close()
    return rows


def ensure_default_food_categories(conn_or_path=DB_PATH):
    bootstrap_default_food_categories(conn_or_path)


def get_brands():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT id, name FROM brands ORDER BY name")
    rows = cur.fetchall()
    conn.close()
    return rows


def get_exercises():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT e.id, e.name, e.muscle_group, e.equipment, e.difficulty, e.notes, ec.name, COALESCE(e.video_url, ''), COALESCE(e.machine_url, ''), COALESCE(ec2.name, '') "
        "FROM exercises e "
        "LEFT JOIN exercise_categories ec ON e.exercise_category_id = ec.id "
        "LEFT JOIN exercise_categories ec2 ON e.exercise_category_id_2 = ec2.id "
        "ORDER BY e.id"
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_exercise_categories():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT id, name FROM exercise_categories ORDER BY name")
    rows = cur.fetchall()
    conn.close()
    return rows


def get_routines(templates_only=True):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    if templates_only:
        cur.execute(
            "SELECT id, name, description, created_at FROM routines WHERE COALESCE(is_template, 1) = 1 ORDER BY id DESC"
        )
    else:
        cur.execute("SELECT id, name, description, created_at FROM routines ORDER BY id DESC")
    rows = cur.fetchall()
    conn.close()
    return rows


def get_routine_by_id(routine_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, description, created_at, COALESCE(is_template, 1), COALESCE(client_name, '') FROM routines WHERE id = ?",
        (routine_id,),
    )
    row = cur.fetchone()
    conn.close()
    return row


def get_routine_series_totals(routine_id):
    items = get_routine_items(routine_id)
    exercises = {e[0]: e for e in get_exercises()}
    totals = {}

    for item in items:
        exercise_id = item[3]
        series_count = int(round(parse_numeric_input(item[5], 0)))
        if series_count <= 0:
            continue

        exercise = exercises.get(exercise_id)
        group_candidates = []
        if exercise:
            for raw_group in (exercise[6] or '', exercise[9] or '', exercise[2] or ''):
                label = str(raw_group or '').strip()
                if label and label not in group_candidates:
                    group_candidates.append(label)
        if not group_candidates:
            group_candidates = ['Sin grupo muscular']

        for group_name in group_candidates:
            totals[group_name] = totals.get(group_name, 0) + series_count

    return sorted(totals.items(), key=lambda row: normalize_text(row[0]))


def render_routine_series_summary_html(routine_id):
    totals = get_routine_series_totals(routine_id)
    if not totals:
        return (
            '<section class="section-card routine-summary-card">'
            '<h3>📊 Series por grupo muscular</h3>'
            '<p style="color:#6d7480;margin:0;">Aún no hay series registradas en esta rutina.</p>'
            '</section>'
        )

    rows_html = ''.join([
        f'<tr><td>{html.escape(group_name)}</td><td>{series_count}</td></tr>'
        for group_name, series_count in totals
    ])
    return (
        '<section class="section-card routine-summary-card">'
        '<h3>📊 Series por grupo muscular</h3>'
        '<table class="routine-summary-table">'
        '<thead><tr><th>Grupo muscular</th><th>Series</th></tr></thead>'
        f'<tbody>{rows_html}</tbody>'
        '</table>'
        '</section>'
    )


def get_routine_items(routine_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT ri.id, ri.routine_id, ri.day_name, ri.exercise_id, e.name, COALESCE(ri.sets_text, ''), COALESCE(ri.reps_text, ''), COALESCE(ri.notes, ''), COALESCE(ri.sort_order, 0), COALESCE(ri.day_index, -1) "
        "FROM routine_items ri LEFT JOIN exercises e ON ri.exercise_id = e.id "
        "WHERE ri.routine_id = ? ORDER BY ri.sort_order, ri.id",
        (routine_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_diets():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, description, created_at, COALESCE(client_weight_kg, 0), COALESCE(display_number, id) "
        "FROM diets ORDER BY COALESCE(display_number, id), id"
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def ensure_diet_display_number_column():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("PRAGMA table_info(diets)")
    cols = [r[1] for r in cur.fetchall()]
    if 'display_number' not in cols:
        cur.execute("ALTER TABLE diets ADD COLUMN display_number INTEGER")
        cur.execute("UPDATE diets SET display_number = id WHERE display_number IS NULL")
        conn.commit()
    conn.close()


def get_clients():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, phone, COALESCE(email, ''), birthdate, COALESCE(height_cm, 0), COALESCE(weight_kg, 0), COALESCE(objectives, ''), COALESCE(plan_start_date, ''), COALESCE(plan_end_date, ''), COALESCE(plan_amount, 0), COALESCE(plan_notes, ''), created_at FROM clients ORDER BY id"
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_client_by_id(client_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, phone, COALESCE(email, ''), birthdate, COALESCE(height_cm, 0), COALESCE(weight_kg, 0), COALESCE(objectives, ''), COALESCE(plan_start_date, ''), COALESCE(plan_end_date, ''), COALESCE(plan_amount, 0), COALESCE(plan_notes, ''), created_at FROM clients WHERE id = ?",
        (int(client_id),),
    )
    row = cur.fetchone()
    conn.close()
    return row


def normalize_login_identifier(value):
    text = str(value or '').strip()
    return re.sub(r'\s+', '', text).lower()


def normalize_phone(value):
    return re.sub(r'[^0-9+]', '', str(value or '').strip())


def get_client_portal_user_by_identifier(identifier):
    ident_norm = normalize_login_identifier(identifier)
    phone_norm = normalize_phone(identifier)
    if not ident_norm:
        return None

    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT id, COALESCE(name, ''), COALESCE(email, ''), COALESCE(phone, ''), COALESCE(client_access_code, ''), COALESCE(client_password_hash, '')
        FROM clients
        """
    )
    rows = cur.fetchall()
    conn.close()

    for row in rows:
        cid, name, email, phone, access_code, password_hash = row
        email_norm = normalize_login_identifier(email)
        phone_row_norm = normalize_phone(phone)
        if ident_norm == email_norm or (phone_norm and phone_norm == phone_row_norm):
            return {
                'id': int(cid),
                'name': name,
                'email': email,
                'phone': phone,
                'access_code': str(access_code or ''),
                'password_hash': str(password_hash or ''),
            }
    return None


def hash_client_password(password):
    raw = str(password or '')
    if not raw:
        return ''
    salt = uuid.uuid4().hex
    digest = hashlib.sha256((salt + '|' + raw).encode('utf-8')).hexdigest()
    return f"sha256${salt}${digest}"


def verify_client_password(password, stored_hash):
    raw = str(password or '')
    saved = str(stored_hash or '').strip()
    if not raw or not saved:
        return False
    parts = saved.split('$', 2)
    if len(parts) != 3 or parts[0] != 'sha256':
        return False
    _algo, salt, expected = parts
    digest = hashlib.sha256((salt + '|' + raw).encode('utf-8')).hexdigest()
    return hmac.compare_digest(digest, expected)


def find_client_by_email(email):
    normalized = normalize_login_identifier(email)
    if not normalized:
        return None
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, COALESCE(name, ''), COALESCE(email, '') FROM clients"
    )
    rows = cur.fetchall()
    conn.close()
    for row in rows:
        if normalize_login_identifier(row[2]) == normalized:
            return row
    return None


def get_active_client_diet(client_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            h.id,
            h.diet_id,
            COALESCE(d.name, 'Dieta'),
            COALESCE(d.client_diet_name, ''),
            COALESCE(h.start_date, ''),
            COALESCE(h.end_date, ''),
            COALESCE(h.notes, '')
        FROM client_diet_history h
        LEFT JOIN diets d ON d.id = h.diet_id
        WHERE h.client_id = ? AND COALESCE(h.is_active, 0) = 1
        ORDER BY h.id DESC
        LIMIT 1
        """,
        (client_id,),
    )
    row = cur.fetchone()
    conn.close()
    return row


def get_active_client_routine(client_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            h.id,
            COALESCE(h.routine_id, 0),
            COALESCE(r.name, ''),
            COALESCE(h.start_date, ''),
            COALESCE(h.end_date, ''),
            COALESCE(h.notes, '')
        FROM client_training_history h
        LEFT JOIN routines r ON r.id = h.routine_id
        WHERE h.client_id = ? AND COALESCE(h.is_active, 0) = 1 AND COALESCE(h.routine_id, 0) > 0
        ORDER BY h.id DESC
        LIMIT 1
        """,
        (client_id,),
    )
    row = cur.fetchone()
    conn.close()
    return row


def parse_cookie_header(cookie_header):
    cookies = {}
    for part in str(cookie_header or '').split(';'):
        if '=' not in part:
            continue
        key, value = part.split('=', 1)
        cookies[key.strip()] = urllib.parse.unquote(value.strip())
    return cookies


def make_client_portal_session_token(client_id):
    issued_at = int(time.time())
    payload = f"{int(client_id)}:{issued_at}"
    signature = hmac.new(
        CLIENT_PORTAL_SECRET.encode('utf-8'),
        payload.encode('utf-8'),
        hashlib.sha256,
    ).hexdigest()
    return f"{payload}:{signature}"


def parse_client_portal_session_token(token):
    parts = str(token or '').split(':')
    if len(parts) != 3:
        return None
    client_id_raw, issued_at_raw, signature = parts
    if not client_id_raw.isdigit() or not issued_at_raw.isdigit():
        return None

    payload = f"{client_id_raw}:{issued_at_raw}"
    expected_signature = hmac.new(
        CLIENT_PORTAL_SECRET.encode('utf-8'),
        payload.encode('utf-8'),
        hashlib.sha256,
    ).hexdigest()
    if not hmac.compare_digest(signature, expected_signature):
        return None

    issued_at = int(issued_at_raw)
    if (int(time.time()) - issued_at) > CLIENT_PORTAL_SESSION_TTL_SECONDS:
        return None
    return int(client_id_raw)


def hash_admin_password(password):
    raw = str(password or '')
    if not raw:
        return ''
    salt = uuid.uuid4().hex
    digest = hashlib.sha256((salt + '|' + raw).encode('utf-8')).hexdigest()
    return f"sha256${salt}${digest}"


def verify_admin_password(password, stored_hash):
    raw = str(password or '')
    saved = str(stored_hash or '').strip()
    if not raw or not saved:
        return False
    parts = saved.split('$', 2)
    if len(parts) != 3 or parts[0] != 'sha256':
        return False
    _algo, salt, expected = parts
    digest = hashlib.sha256((salt + '|' + raw).encode('utf-8')).hexdigest()
    return hmac.compare_digest(digest, expected)


def get_admin_portal_username():
    value = str(get_app_setting('admin_portal_username', ADMIN_PORTAL_USERNAME) or '').strip()
    if value:
        return value
    fallback = str(ADMIN_PORTAL_USERNAME or '').strip()
    return fallback or 'admin'


def get_admin_portal_password_hash():
    return str(get_app_setting('admin_portal_password_hash', '') or '').strip()


def verify_admin_portal_credentials(username, password):
    entered_user = str(username or '').strip()
    entered_pass = str(password or '')
    expected_user = get_admin_portal_username()
    if not entered_user or not entered_pass or not expected_user:
        return False
    if not hmac.compare_digest(entered_user, expected_user):
        return False

    stored_hash = get_admin_portal_password_hash()
    if stored_hash:
        return verify_admin_password(entered_pass, stored_hash)

    # Backward compatibility fallback when hash setting is not yet initialized.
    expected_pass = str(ADMIN_PORTAL_PASSWORD or '')
    return bool(expected_pass) and hmac.compare_digest(entered_pass, expected_pass)


def make_admin_portal_session_token(username):
    issued_at = int(time.time())
    user = str(username or '').strip()
    payload = f"{user}:{issued_at}"
    signature = hmac.new(
        ADMIN_PORTAL_SECRET.encode('utf-8'),
        payload.encode('utf-8'),
        hashlib.sha256,
    ).hexdigest()
    return f"{payload}:{signature}"


def parse_admin_portal_session_token(token):
    parts = str(token or '').split(':')
    if len(parts) != 3:
        return None
    username, issued_at_raw, signature = parts
    if not username or not issued_at_raw.isdigit():
        return None

    payload = f"{username}:{issued_at_raw}"
    expected_signature = hmac.new(
        ADMIN_PORTAL_SECRET.encode('utf-8'),
        payload.encode('utf-8'),
        hashlib.sha256,
    ).hexdigest()
    if not hmac.compare_digest(signature, expected_signature):
        return None

    issued_at = int(issued_at_raw)
    if (int(time.time()) - issued_at) > ADMIN_PORTAL_SESSION_TTL_SECONDS:
        return None

    if not hmac.compare_digest(username, get_admin_portal_username()):
        return None
    return username


def get_client_diet_history(client_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            h.id,
            h.client_id,
            h.diet_id,
            COALESCE(d.name, 'Dieta eliminada'),
            COALESCE(d.client_diet_name, ''),
            COALESCE(h.template_diet_id, 0),
            COALESCE(td.name, ''),
            COALESCE(h.start_date, ''),
            COALESCE(h.end_date, ''),
            COALESCE(h.is_active, 0),
            COALESCE(h.notes, ''),
            COALESCE(h.created_at, '')
        FROM client_diet_history h
        LEFT JOIN diets d ON d.id = h.diet_id
        LEFT JOIN diets td ON td.id = h.template_diet_id
        WHERE h.client_id = ?
        ORDER BY COALESCE(h.start_date, h.created_at) DESC, h.id DESC
        """,
        (client_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_client_training_history(client_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT
            h.id,
            h.client_id,
            h.exercise_id,
            COALESCE(h.routine_id, 0),
            COALESCE(h.training_name, ''),
            COALESCE(e.name, ''),
            COALESCE(r.name, ''),
            COALESCE(h.template_routine_id, 0),
            COALESCE(tr.name, ''),
            COALESCE(h.start_date, ''),
            COALESCE(h.end_date, ''),
            COALESCE(h.is_active, 0),
            COALESCE(h.notes, ''),
            COALESCE(h.created_at, '')
        FROM client_training_history h
        LEFT JOIN exercises e ON e.id = h.exercise_id
        LEFT JOIN routines r ON r.id = h.routine_id
        LEFT JOIN routines tr ON tr.id = h.template_routine_id
        WHERE h.client_id = ?
        ORDER BY COALESCE(h.start_date, h.created_at) DESC, h.id DESC
        """,
        (client_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_active_client_routines_map(client_ids=None):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    if client_ids:
        placeholders = ','.join(['?'] * len(client_ids))
        cur.execute(
            f"""
            SELECT h.client_id, h.routine_id, COALESCE(r.name, '')
            FROM client_training_history h
            LEFT JOIN routines r ON r.id = h.routine_id
            WHERE h.is_active = 1 AND COALESCE(h.routine_id, 0) > 0 AND h.client_id IN ({placeholders})
            ORDER BY h.id DESC
            """,
            tuple(client_ids),
        )
    else:
        cur.execute(
            """
            SELECT h.client_id, h.routine_id, COALESCE(r.name, '')
            FROM client_training_history h
            LEFT JOIN routines r ON r.id = h.routine_id
            WHERE h.is_active = 1 AND COALESCE(h.routine_id, 0) > 0
            ORDER BY h.id DESC
            """
        )
    rows = cur.fetchall()
    conn.close()
    routine_by_client = {}
    for client_id, routine_id, routine_name in rows:
        if client_id in routine_by_client:
            continue
        routine_by_client[int(client_id)] = (int(routine_id), routine_name or 'Rutina')
    return routine_by_client


def get_active_client_diets_map(client_ids=None):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    if client_ids:
        placeholders = ','.join(['?'] * len(client_ids))
        cur.execute(
            f"""
            SELECT h.client_id, h.id, h.diet_id, COALESCE(d.client_diet_name, ''), COALESCE(d.name, ''), COALESCE(h.start_date, '')
            FROM client_diet_history h
            LEFT JOIN diets d ON d.id = h.diet_id
            WHERE h.is_active = 1 AND h.client_id IN ({placeholders})
            ORDER BY h.id DESC
            """,
            tuple(client_ids),
        )
    else:
        cur.execute(
            """
            SELECT h.client_id, h.id, h.diet_id, COALESCE(d.client_diet_name, ''), COALESCE(d.name, ''), COALESCE(h.start_date, '')
            FROM client_diet_history h
            LEFT JOIN diets d ON d.id = h.diet_id
            WHERE h.is_active = 1
            ORDER BY h.id DESC
            """
        )
    rows = cur.fetchall()
    conn.close()
    diet_by_client = {}
    for client_id, history_id, diet_id, client_diet_name, diet_name, start_date in rows:
        if client_id in diet_by_client:
            continue
        diet_by_client[int(client_id)] = {
            'history_id': int(history_id),
            'diet_id': int(diet_id or 0),
            'diet_name': (client_diet_name or '').strip() or (diet_name or '').strip() or 'Dieta',
            'start_date': start_date or '',
        }
    return diet_by_client


def clone_diet_template_for_client(template_diet_id, client_name=''):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT name, description, COALESCE(client_instructions, ''), COALESCE(client_diet_name, ''), COALESCE(client_weight_kg, 0), "
        "COALESCE(client_name, ''), COALESCE(client_height_cm, 0), COALESCE(client_age, 0) "
        "FROM diets WHERE id = ?",
        (template_diet_id,),
    )
    src = cur.fetchone()
    if not src:
        conn.close()
        return None

    template_name, description, client_instructions, client_diet_name, client_weight_kg, src_client_name, client_height_cm, client_age = src
    copy_name = f"{template_name} · {client_name}".strip() if client_name else f"{template_name} · Cliente"
    copy_client_name = src_client_name or client_name or ''

    cur.execute(
        "INSERT INTO diets(name, description, client_instructions, is_template, client_diet_name, client_weight_kg, client_name, client_height_cm, client_age, created_at) "
        "VALUES(?,?,?,?,?,?,?,?,?,datetime('now'))",
        (
            copy_name,
            description,
            client_instructions,
            0,
            client_diet_name,
            client_weight_kg,
            copy_client_name,
            client_height_cm,
            client_age,
        ),
    )
    new_diet_id = cur.lastrowid
    cur.execute("UPDATE diets SET display_number = ? WHERE id = ?", (new_diet_id, new_diet_id))

    cur.execute(
        """
        INSERT INTO diet_meals(diet_id, name, order_index)
        SELECT ?, name, order_index
        FROM diet_meals
        WHERE diet_id = ?
        ORDER BY order_index, id
        """,
        (new_diet_id, template_diet_id),
    )

    cur.execute(
        """
        INSERT INTO diet_day_config(
            diet_id, day_of_week, is_training, goal_kcal, goal_protein, goal_fat,
            goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier
        )
        SELECT ?, day_of_week, is_training, goal_kcal, goal_protein, goal_fat,
               goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier
        FROM diet_day_config
        WHERE diet_id = ?
        """,
        (new_diet_id, template_diet_id),
    )

    cur.execute(
        """
        WITH src_meals AS (
            SELECT id AS old_meal_id, ROW_NUMBER() OVER (ORDER BY order_index, id) AS rn
            FROM diet_meals
            WHERE diet_id = ?
        ),
        dst_meals AS (
            SELECT id AS new_meal_id, ROW_NUMBER() OVER (ORDER BY order_index, id) AS rn
            FROM diet_meals
            WHERE diet_id = ?
        ),
        meal_map AS (
            SELECT src_meals.old_meal_id, dst_meals.new_meal_id
            FROM src_meals
            JOIN dst_meals ON dst_meals.rn = src_meals.rn
        )
        INSERT INTO diet_items(
            diet_id, food_id, quantity, note, day_of_week, meal_time,
            meal_id, quantity_grams, quantity_units, option_group
        )
        SELECT
            ?,
            di.food_id,
            di.quantity,
            di.note,
            di.day_of_week,
            di.meal_time,
            meal_map.new_meal_id,
            COALESCE(di.quantity_grams, 100),
            COALESCE(di.quantity_units, 1),
            COALESCE(di.option_group, 1)
        FROM diet_items di
        LEFT JOIN meal_map ON meal_map.old_meal_id = di.meal_id
        WHERE di.diet_id = ?
        """,
        (template_diet_id, new_diet_id, new_diet_id, template_diet_id),
    )

    cur.execute(
        """
        INSERT INTO diet_supplements(diet_id, supplement_name, intake_time, dose, notes, order_index)
        SELECT ?, supplement_name, intake_time, dose, notes, COALESCE(order_index, 0)
        FROM diet_supplements
        WHERE diet_id = ?
        """,
        (new_diet_id, template_diet_id),
    )

    conn.commit()
    conn.close()
    return new_diet_id


def clone_routine_template_for_client(template_routine_id, client_name=''):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT name, description, COALESCE(is_template, 1) FROM routines WHERE id = ?",
        (template_routine_id,),
    )
    src = cur.fetchone()
    if not src:
        conn.close()
        return None

    template_name, description, is_template = src
    if int(is_template or 0) != 1:
        conn.close()
        return None

    copy_name = f"{template_name} · {client_name}".strip() if client_name else f"{template_name} · Cliente"
    cur.execute(
        "INSERT INTO routines(name, description, is_template, client_name, created_at) VALUES(?,?,?,?,datetime('now'))",
        (copy_name, description, 0, client_name or None),
    )
    new_routine_id = cur.lastrowid

    cur.execute(
        "SELECT day_index, day_name, day_type FROM routine_days WHERE routine_id = ? ORDER BY day_index",
        (template_routine_id,),
    )
    source_days = cur.fetchall()
    if not source_days:
        source_days = get_default_routine_days()

    for day_index, day_name, day_type in source_days:
        cur.execute(
            "INSERT INTO routine_days(routine_id, day_index, day_name, day_type) VALUES(?,?,?,?)",
            (new_routine_id, int(day_index), day_name, day_type or 'train'),
        )

    cur.execute(
        """
        SELECT day_name, exercise_id, sets_text, reps_text, notes, COALESCE(sort_order, 0), COALESCE(day_index, -1)
        FROM routine_items
        WHERE routine_id = ?
        ORDER BY COALESCE(sort_order, 0), id
        """,
        (template_routine_id,),
    )
    source_items = cur.fetchall()
    for day_name, exercise_id, sets_text, reps_text, notes, sort_order, day_index in source_items:
        cur.execute(
            """
            INSERT INTO routine_items(routine_id, day_name, exercise_id, sets_text, reps_text, notes, sort_order, day_index)
            VALUES(?,?,?,?,?,?,?,?)
            """,
            (
                new_routine_id,
                day_name,
                exercise_id,
                sets_text,
                reps_text,
                notes,
                int(sort_order or 0),
                int(day_index) if day_index is not None else None,
            ),
        )

    conn.commit()
    conn.close()
    return new_routine_id


def sync_client_payment_plan(client_id, start_date, end_date, amount, notes=''):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("DELETE FROM payment_plans WHERE client_id = ?", (client_id,))
    if start_date and end_date:
        cur.execute(
            "INSERT INTO payment_plans(client_id, start_date, end_date, amount, notes, created_at) VALUES(?,?,?,?,?,datetime('now'))",
            (client_id, start_date, end_date, amount or 0, notes or None),
        )
    conn.commit()
    conn.close()


def get_payment_plans():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT pp.id, pp.client_id, c.name, pp.start_date, pp.end_date, COALESCE(pp.amount, 0), COALESCE(pp.notes, ''), pp.created_at
        FROM payment_plans pp
        JOIN clients c ON pp.client_id = c.id
        ORDER BY pp.start_date DESC, pp.id DESC
        """
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def calculate_age(birthdate_text):
    try:
        from datetime import date, datetime
        born = datetime.strptime(str(birthdate_text), "%Y-%m-%d").date()
        today = date.today()
        age = today.year - born.year - ((today.month, today.day) < (born.month, born.day))
        return age
    except Exception:
        return None


def payment_plan_status(start_date_text, end_date_text):
    try:
        from datetime import date, datetime
        today = date.today()
        start_date = datetime.strptime(str(start_date_text), "%Y-%m-%d").date()
        end_date = datetime.strptime(str(end_date_text), "%Y-%m-%d").date()
        if today < start_date:
            return 'Próximo'
        if today > end_date:
            return 'Finalizado'
        return 'Activo'
    except Exception:
        return 'Sin fecha'


def parse_year_month(value, default_date=None):
    from datetime import date
    default_date = default_date or date.today()
    text = str(value or '').strip()
    if re.match(r'^\d{4}-\d{2}$', text):
        try:
            year, month = text.split('-')
            return int(year), int(month)
        except Exception:
            pass
    return default_date.year, default_date.month


def month_label(year, month):
    return f"{calendar.month_name[month].capitalize()} {year}"


def get_diet_items(diet_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT di.id, f.id, f.name, f.brand, f.calories, f.protein, f.carbs, f.fats, di.quantity, di.note, di.day_of_week, di.meal_time, "
        "COALESCE(di.quantity_grams, 100), COALESCE(di.quantity_units, 1), COALESCE(f.nutrition_mode, 'per100'), COALESCE(f.per100_unit, 'g') "
        "FROM diet_items di JOIN foods f ON di.food_id = f.id "
        "WHERE di.diet_id = ? ORDER BY di.day_of_week, di.meal_time, di.id",
        (diet_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_diet_items_without_meal(diet_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
        SELECT f.name, COALESCE(f.brand, ''), COALESCE(di.quantity, ''), COALESCE(di.quantity_grams, 100), COALESCE(di.quantity_units, 1), COALESCE(f.nutrition_mode, 'per100'), COALESCE(f.per100_unit, 'g')
        FROM diet_items di
        JOIN foods f ON di.food_id = f.id
        WHERE di.diet_id = ? AND di.meal_id IS NULL
        ORDER BY di.id
        """,
        (diet_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def diet_item_quantity_text(item):
    try:
        nutrition_mode = (item[14] or 'per100') if len(item) > 14 else 'per100'
        per100_unit = (item[15] or 'g') if len(item) > 15 else 'g'
        if nutrition_mode == 'unit':
            units = float(item[13] if len(item) > 13 and item[13] is not None else 1)
            return f"{int(round(units)) if abs(units - round(units)) < 0.01 else round(units, 1)} ud"
        grams = float(item[12] if len(item) > 12 and item[12] is not None else 0)
        if grams > 0:
            if abs(grams - round(grams)) < 0.01:
                grams_txt = str(int(round(grams)))
            else:
                grams_txt = f"{grams:.1f}"
            return f"{grams_txt}{per100_unit}"
    except Exception:
        pass
    legacy_quantity = ''
    if len(item) > 8 and item[8]:
        legacy_quantity = str(item[8]).strip()
    return legacy_quantity


    
    
def diet_builder_item_quantity_text(item):
    try:
        nutrition_mode = str(item.get('nutrition_mode') or 'per100').strip().lower()
        per100_unit = str(item.get('per100_unit') or 'g').strip().lower()
        if nutrition_mode == 'unit':
            units = float(item.get('units') or 1)
            if abs(units - round(units)) < 0.01:
                units_txt = str(int(round(units)))
            else:
                units_txt = f"{units:.1f}"
            return f"{units_txt} ud"
        grams = float(item.get('grams') or 0)
        if grams > 0:
            if abs(grams - round(grams)) < 0.01:
                grams_txt = str(int(round(grams)))
            else:
                grams_txt = f"{grams:.1f}"
            return f"{grams_txt}{per100_unit}"
    except Exception:
        pass
    return ''


def get_food_options():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT id, name, brand FROM foods ORDER BY name")
    rows = cur.fetchall()
    conn.close()
    return rows


def ensure_diet_builder_tables(conn_or_path=None):
    conn, should_close = _coerce_schema_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS diet_meals (
        id INTEGER PRIMARY KEY,
        diet_id INTEGER NOT NULL,
        name TEXT NOT NULL,
        order_index INTEGER DEFAULT 0
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS diet_day_config (
        id INTEGER PRIMARY KEY,
        diet_id INTEGER NOT NULL,
        day_of_week TEXT NOT NULL,
        is_training INTEGER DEFAULT 1,
        goal_kcal REAL DEFAULT 0,
        goal_steps REAL DEFAULT 0,
        goal_protein REAL DEFAULT 0,
        goal_fat REAL DEFAULT 0,
        goal_carbs REAL DEFAULT 0,
        goal_fiber REAL DEFAULT 0,
        protein_multiplier REAL DEFAULT 0,
        fat_multiplier REAL DEFAULT 0,
        carb_multiplier REAL DEFAULT 0,
        UNIQUE(diet_id, day_of_week)
    )""")
    cur.execute("""
    CREATE TABLE IF NOT EXISTS diet_supplements (
        id INTEGER PRIMARY KEY,
        diet_id INTEGER NOT NULL,
        supplement_name TEXT NOT NULL,
        intake_time TEXT,
        dose TEXT,
        notes TEXT,
        order_index INTEGER DEFAULT 0
    )""")
    cur.execute("PRAGMA table_info(diet_day_config)")
    day_cols = [r[1] for r in cur.fetchall()]
    if 'goal_steps' not in day_cols:
        cur.execute("ALTER TABLE diet_day_config ADD COLUMN goal_steps REAL DEFAULT 0")
    if 'protein_multiplier' not in day_cols:
        cur.execute("ALTER TABLE diet_day_config ADD COLUMN protein_multiplier REAL DEFAULT 0")
    if 'fat_multiplier' not in day_cols:
        cur.execute("ALTER TABLE diet_day_config ADD COLUMN fat_multiplier REAL DEFAULT 0")
    if 'carb_multiplier' not in day_cols:
        cur.execute("ALTER TABLE diet_day_config ADD COLUMN carb_multiplier REAL DEFAULT 0")
    cur.execute("PRAGMA table_info(diet_items)")
    cols = [r[1] for r in cur.fetchall()]
    if 'meal_id' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN meal_id INTEGER")
    if 'quantity_grams' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN quantity_grams REAL DEFAULT 100")
    if 'quantity_units' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN quantity_units REAL DEFAULT 1")
    if 'option_group' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN option_group INTEGER DEFAULT 1")
    cur.execute("UPDATE diet_items SET option_group = 1 WHERE option_group IS NULL OR option_group NOT IN (1,2)")
    conn.commit()
    if should_close:
        conn.close()


def get_diet_builder_data(diet_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, description, COALESCE(client_instructions, ''), COALESCE(client_diet_name, ''), COALESCE(client_weight_kg, 0), "
        "COALESCE(client_name, ''), COALESCE(client_height_cm, 0), COALESCE(client_age, 0) "
        "FROM diets WHERE id=?",
        (diet_id,),
    )
    row = cur.fetchone()
    if not row:
        conn.close()
        return None
    instructions_template = get_diet_instructions_template()
    diet = {
        'id': row[0],
        'name': row[1],
        'description': row[2] or '',
        'client_instructions': (row[3] or '').strip() or instructions_template,
        'client_diet_name': row[4] or '',
        'client_weight_kg': row[5] or 0,
        'client_name': row[6] or '',
        'client_height_cm': row[7] or 0,
        'client_age': row[8] or 0,
    }

    cur.execute("SELECT id, name, order_index FROM diet_meals WHERE diet_id=? ORDER BY order_index, id", (diet_id,))
    meals = [{'id': r[0], 'name': r[1], 'order_index': r[2]} for r in cur.fetchall()]
    if not meals:
        defaults = ['Desayuno', 'Media ma\u00f1ana', 'Almuerzo', 'Merienda', 'Cena']
        for i, name in enumerate(defaults):
            cur.execute("INSERT INTO diet_meals(diet_id, name, order_index) VALUES(?,?,?)", (diet_id, name, i))
        conn.commit()
        cur.execute("SELECT id, name, order_index FROM diet_meals WHERE diet_id=? ORDER BY order_index, id", (diet_id,))
        meals = [{'id': r[0], 'name': r[1], 'order_index': r[2]} for r in cur.fetchall()]

    cur.execute("SELECT day_of_week, is_training, goal_kcal, goal_steps, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier FROM diet_day_config WHERE diet_id=?", (diet_id,))
    day_configs = {}
    for r in cur.fetchall():
        day_configs[r[0]] = {
            'is_training': bool(r[1]),
            'goal_kcal': r[2],
            'goal_steps': r[3],
            'goal_protein': r[4],
            'goal_fat': r[5],
            'goal_carbs': r[6],
            'goal_fiber': r[7],
            'protein_multiplier': r[8],
            'fat_multiplier': r[9],
            'carb_multiplier': r[10],
        }

    cur.execute("""
         SELECT di.id, di.day_of_week, di.meal_id, di.food_id,
             f.name, COALESCE(f.brand,''), di.quantity_grams,
             COALESCE(f.calories,0), COALESCE(f.protein,0), COALESCE(f.fats,0), COALESCE(f.carbs,0),
             COALESCE(f.nutrition_mode,'per100'), COALESCE(f.per100_unit,'g'), COALESCE(di.quantity_units,1), COALESCE(di.option_group,1)
        FROM diet_items di
        JOIN foods f ON di.food_id = f.id
        WHERE di.diet_id=? AND di.meal_id IS NOT NULL
        ORDER BY di.id
    """, (diet_id,))
    items = []
    for r in cur.fetchall():
        items.append({
            'id': r[0], 'day': r[1] or '', 'meal_id': r[2], 'food_id': r[3],
            'food_name': r[4], 'food_brand': r[5],
            'grams': r[6] if r[6] is not None else 100,
            'kcal_per100': r[7], 'protein_per100': r[8], 'fat_per100': r[9], 'carbs_per100': r[10],
            'nutrition_mode': r[11] or 'per100', 'per100_unit': r[12] or 'g',
            'units': r[13] if r[13] is not None else 1,
            'option_group': r[14] if r[14] in (1, 2) else 1,
        })

    cur.execute(
        """
        SELECT id, COALESCE(supplement_name, ''), COALESCE(intake_time, ''),
               COALESCE(dose, ''), COALESCE(notes, ''), COALESCE(order_index, 0)
        FROM diet_supplements
        WHERE diet_id = ?
        ORDER BY COALESCE(order_index, 0), id
        """,
        (diet_id,),
    )
    supplements = []
    for r in cur.fetchall():
        supplements.append({
            'id': r[0],
            'supplement_name': r[1],
            'intake_time': r[2],
            'dose': r[3],
            'notes': r[4],
            'order_index': r[5],
        })
    conn.close()
    return {
        'diet': diet,
        'meals': meals,
        'day_configs': day_configs,
        'items': items,
        'supplements': supplements,
        'instructions_template': instructions_template,
    }


def search_foods_db(query, limit=25, category='', brand='', status='all', kcal_min=None, kcal_max=None):
    ensure_brand_column()
    limit = max(5, min(int(limit or 25), 5000))
    q_norm = normalize_text(query)
    terms = query_terms(query)

    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    cur = conn.cursor()

    where_parts = []
    where_vals = []

    if category:
        where_parts.append("COALESCE(c.name, '') = ?")
        where_vals.append(category)
    if brand:
        where_parts.append("COALESCE(f.brand, '') = ?")
        where_vals.append(brand)
    if status == 'active':
        where_parts.append("COALESCE(f.is_active, 1) = 1")
    elif status == 'inactive':
        where_parts.append("COALESCE(f.is_active, 1) = 0")

    try:
        if kcal_min not in (None, ''):
            where_parts.append("COALESCE(f.calories, 0) >= ?")
            where_vals.append(float(kcal_min))
        if kcal_max not in (None, ''):
            where_parts.append("COALESCE(f.calories, 0) <= ?")
            where_vals.append(float(kcal_max))
    except Exception:
        pass

    where_sql = ("WHERE " + " AND ".join(where_parts)) if where_parts else ""

    def row_payload(row, relevance):
        return {
            'id': row['id'],
            'name': row['name'] or '',
            'brand': row['brand'] or '',
            'category': row['category'] or '',
            'kcal': row['kcal'] or 0,
            'protein': row['protein'] or 0,
            'fat': row['fat'] or 0,
            'carbs': row['carbs'] or 0,
            'nutrition_mode': row['nutrition_mode'] or 'per100',
            'per100_unit': row['per100_unit'] or 'g',
            'barcode': row['barcode'] or '',
            'keywords': row['keywords'] or '',
            'is_active': int(row['is_active'] or 0),
            'relevance': round(float(relevance), 4),
        }

    def compute_relevance(row, fts_bonus=0.0):
        name_n = normalize_text(row['name'])
        brand_n = normalize_text(row['brand'])
        category_n = normalize_text(row['category'])
        barcode_n = normalize_text(row['barcode'])
        keywords_n = normalize_text(row['keywords'])
        blob = ' '.join([name_n, brand_n, category_n, barcode_n, keywords_n]).strip()

        score = 0.0
        if q_norm:
            if name_n == q_norm:
                score += 240
            elif barcode_n and barcode_n == q_norm:
                score += 260
            if name_n.startswith(q_norm):
                score += 170
            if q_norm and q_norm in name_n:
                score += 120
            if q_norm and q_norm in brand_n:
                score += 70
            if q_norm and q_norm in category_n:
                score += 60
            if q_norm and q_norm in keywords_n:
                score += 50
            if q_norm and q_norm in barcode_n:
                score += 180

            for term in terms:
                if term in name_n:
                    score += 22
                elif term in brand_n:
                    score += 14
                elif term in category_n:
                    score += 12
                elif term in keywords_n:
                    score += 10
                elif term in barcode_n:
                    score += 18

            # Lightweight typo tolerance for near matches.
            fuzzy = max(
                SequenceMatcher(None, q_norm, name_n).ratio() if name_n else 0,
                SequenceMatcher(None, q_norm, brand_n).ratio() if brand_n else 0,
                SequenceMatcher(None, q_norm, category_n).ratio() if category_n else 0,
                SequenceMatcher(None, q_norm, blob).ratio() if blob else 0,
            )
            if fuzzy >= 0.72:
                score += fuzzy * 95

            words = []
            words.extend([w for w in name_n.split(' ') if w])
            words.extend([w for w in brand_n.split(' ') if w])
            words.extend([w for w in category_n.split(' ') if w])
            words.extend([w for w in keywords_n.split(' ') if w])
            for q_word in (terms or [q_norm]):
                if not words:
                    continue
                best_word_ratio = max(SequenceMatcher(None, q_word, w).ratio() for w in words)
                if best_word_ratio >= 0.76:
                    score += best_word_ratio * 140

        score += fts_bonus
        return score

    candidates = {}

    if q_norm and supports_foods_search_fts():
        fts_q = build_fts_query(query)
        if fts_q:
            try:
                fts_where = ["fs MATCH ?"] + where_parts
                fts_where_sql = "WHERE " + " AND ".join(fts_where)
                sql = f"""
                    SELECT
                        f.id,
                        f.name,
                        COALESCE(f.brand, '') AS brand,
                        COALESCE(c.name, '') AS category,
                        COALESCE(f.calories, 0) AS kcal,
                        COALESCE(f.protein, 0) AS protein,
                        COALESCE(f.fats, 0) AS fat,
                        COALESCE(f.carbs, 0) AS carbs,
                        COALESCE(f.nutrition_mode, 'per100') AS nutrition_mode,
                        COALESCE(f.per100_unit, 'g') AS per100_unit,
                        COALESCE(f.barcode, '') AS barcode,
                        COALESCE(f.keywords, '') AS keywords,
                        COALESCE(f.is_active, 1) AS is_active,
                        bm25(fs) AS rank
                    FROM foods_search fs
                    JOIN foods f ON f.id = fs.food_id
                    LEFT JOIN categories c ON f.category_id = c.id
                    {fts_where_sql}
                    ORDER BY rank
                    LIMIT 220
                """
                vals = [fts_q] + list(where_vals)
                cur.execute(sql, vals)
                for row in cur.fetchall():
                    rel = compute_relevance(row, fts_bonus=max(0.0, 80.0 - float(row['rank'])))
                    candidates[row['id']] = row_payload(row, rel)
            except Exception:
                pass

    if len(candidates) < limit:
        likes = []
        like_vals = []
        if q_norm:
            like_vals.extend([f"%{q_norm}%", f"%{q_norm}%", f"%{q_norm}%", f"%{q_norm}%", f"%{q_norm}%"])
            likes.append(
                "(lower(COALESCE(f.name,'')) LIKE ? OR lower(COALESCE(f.brand,'')) LIKE ? OR "
                "lower(COALESCE(c.name,'')) LIKE ? OR lower(COALESCE(f.barcode,'')) LIKE ? OR lower(COALESCE(f.keywords,'')) LIKE ?)"
            )
        full_where = [w for w in where_parts]
        full_vals = list(where_vals)
        if likes:
            full_where.extend(likes)
            full_vals.extend(like_vals)
        full_where_sql = ("WHERE " + " AND ".join(full_where)) if full_where else ""
        cur.execute(
            f"""
            SELECT
                f.id,
                f.name,
                COALESCE(f.brand, '') AS brand,
                COALESCE(c.name, '') AS category,
                COALESCE(f.calories, 0) AS kcal,
                COALESCE(f.protein, 0) AS protein,
                COALESCE(f.fats, 0) AS fat,
                COALESCE(f.carbs, 0) AS carbs,
                COALESCE(f.nutrition_mode, 'per100') AS nutrition_mode,
                COALESCE(f.per100_unit, 'g') AS per100_unit,
                COALESCE(f.barcode, '') AS barcode,
                COALESCE(f.keywords, '') AS keywords,
                COALESCE(f.is_active, 1) AS is_active
            FROM foods f
            LEFT JOIN categories c ON f.category_id = c.id
            {full_where_sql}
            ORDER BY f.name
            LIMIT 260
            """,
            full_vals,
        )
        for row in cur.fetchall():
            if row['id'] in candidates:
                continue
            rel = compute_relevance(row)
            candidates[row['id']] = row_payload(row, rel)

    if q_norm and len(candidates) < limit:
        fuzzy_where_sql = ("WHERE " + " AND ".join(where_parts)) if where_parts else ""
        cur.execute(
            f"""
            SELECT
                f.id,
                f.name,
                COALESCE(f.brand, '') AS brand,
                COALESCE(c.name, '') AS category,
                COALESCE(f.calories, 0) AS kcal,
                COALESCE(f.protein, 0) AS protein,
                COALESCE(f.fats, 0) AS fat,
                COALESCE(f.carbs, 0) AS carbs,
                COALESCE(f.nutrition_mode, 'per100') AS nutrition_mode,
                COALESCE(f.per100_unit, 'g') AS per100_unit,
                COALESCE(f.barcode, '') AS barcode,
                COALESCE(f.keywords, '') AS keywords,
                COALESCE(f.is_active, 1) AS is_active
            FROM foods f
            LEFT JOIN categories c ON f.category_id = c.id
            {fuzzy_where_sql}
            ORDER BY f.id DESC
            LIMIT 420
            """,
            where_vals,
        )
        for row in cur.fetchall():
            if row['id'] in candidates:
                continue
            rel = compute_relevance(row)
            if rel >= 40:
                candidates[row['id']] = row_payload(row, rel)

    conn.close()

    ranked = sorted(candidates.values(), key=lambda x: (-x['relevance'], x['name'].lower(), x['brand'].lower()))
    return ranked[:limit]


def escape_pdf_string(value):
    if value is None:
        return ''
    normalized = unicodedata.normalize('NFKD', str(value))
    ascii_text = ''.join(ch for ch in normalized if ord(ch) < 128)
    return ascii_text.replace('\\', '\\\\').replace('(', '\\(').replace(')', '\\)').replace('\n', ' ')


def save_food_photo_data_url(photo_data_url):
    data_url = (photo_data_url or '').strip()
    if not data_url:
        return None
    m = re.match(r'^data:image/(png|jpeg|jpg|webp|gif);base64,(.+)$', data_url, flags=re.IGNORECASE | re.DOTALL)
    if not m:
        return None
    ext_map = {'jpeg': 'jpg', 'jpg': 'jpg', 'png': 'png', 'webp': 'webp', 'gif': 'gif'}
    ext = ext_map.get(m.group(1).lower(), 'jpg')
    raw_b64 = m.group(2).strip()
    try:
        content = base64.b64decode(raw_b64, validate=True)
    except Exception:
        return None
    if not content:
        return None
    upload_dir = UPLOADS_FOODS_DIR
    os.makedirs(upload_dir, exist_ok=True)
    filename = f"food_{uuid.uuid4().hex}.{ext}"
    file_path = os.path.join(upload_dir, filename)
    with open(file_path, 'wb') as f:
        f.write(content)
    return f"/static/uploads/foods/{filename}"


def format_serving_size(amount_text, unit_text, fallback_text=''):
    amount_raw = str(amount_text or '').strip().replace(',', '.')
    unit = str(unit_text or '').strip().lower()
    if unit not in ('g', 'ml'):
        unit = 'g'
    if amount_raw:
        try:
            amount = float(amount_raw)
            if amount > 0:
                if abs(amount - round(amount)) < 0.01:
                    return f"{int(round(amount))} {unit}"
                return f"{amount:.1f} {unit}"
        except Exception:
            pass
    return (fallback_text or '').strip()


def split_serving_size(serving_text):
    text = (serving_text or '').strip()
    if not text:
        return '', 'g'
    m = re.match(r'^\s*(\d+(?:[\.,]\d+)?)\s*(g|ml)\s*$', text, flags=re.IGNORECASE)
    if m:
        return m.group(1).replace(',', '.'), m.group(2).lower()
    return '', 'g'


def build_pdf(objects):
    # Binary marker line improves PDF detection in some viewers/editors.
    output = b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n'
    offsets = []
    for idx, obj in enumerate(objects, start=1):
        offsets.append(len(output))
        output += f'{idx} 0 obj\n'.encode('utf-8')
        output += obj
        output += b'\nendobj\n'
    xref_start = len(output)
    output += f'xref\n0 {len(objects) + 1}\n'.encode('utf-8')
    output += b'0000000000 65535 f \n'
    for off in offsets:
        output += f'{off:010d} 00000 n \n'.encode('utf-8')
    output += f'trailer\n<< /Size {len(objects) + 1} /Root 1 0 R >>\nstartxref\n{xref_start}\n%%EOF'.encode('utf-8')
    return output


def build_diet_pdf(diet_id):
    builder_data = get_diet_builder_data(diet_id)
    if builder_data is None:
        return None

    diet = builder_data['diet']

    days = ["Lunes", "Martes", "Miércoles", "Jueves", "Viernes", "Sábado", "Domingo"]

    def normalize_day_name(day_name):
        text = unicodedata.normalize('NFKD', str(day_name or ''))
        text = ''.join(ch for ch in text if not unicodedata.combining(ch)).strip().lower()
        aliases = {
            'lunes': 'Lunes',
            'martes': 'Martes',
            'miercoles': 'Miércoles',
            'jueves': 'Jueves',
            'viernes': 'Viernes',
            'sabado': 'Sábado',
            'domingo': 'Domingo',
        }
        return aliases.get(text)

    def to_float(value):
        try:
            return float(value)
        except Exception:
            return 0.0

    def fmt_num(value):
        return str(int(round(value)))

    internal_diet_name = (diet.get('name') or '').strip() or f'Dieta {diet_id}'
    diet_name = (diet.get('client_diet_name') or '').strip() or internal_diet_name
    client_name = (diet.get('client_name') or '').strip() or 'Sin cliente'
    client_weight = to_float(diet.get('client_weight_kg'))
    client_height = to_float(diet.get('client_height_cm'))
    try:
        client_age = int(diet.get('client_age') or 0)
    except Exception:
        client_age = 0

    client_data_parts = [
        f"Peso: {fmt_num(client_weight)} kg" if client_weight > 0 else 'Peso: -',
        f"Altura: {fmt_num(client_height)} cm" if client_height > 0 else 'Altura: -',
        f"Edad: {client_age} años" if client_age > 0 else 'Edad: -',
    ]
    client_data_text = ' · '.join(client_data_parts)
    client_instructions = (diet.get('client_instructions') or '').strip() or get_diet_instructions_template()

    def parse_quantity_text(quantity_text):
        text = (quantity_text or '').strip()
        if not text:
            return ('unit', 1.0, 'unidad')
        m = re.match(r'^\s*(\d+(?:[\.,]\d+)?)\s*([\w\-/]+)?', text, flags=re.UNICODE)
        if not m:
            return ('raw', None, text)
        amount_raw = m.group(1).replace(',', '.')
        unit_raw = (m.group(2) or 'unidad').strip().lower()
        amount = to_float(amount_raw)
        grams_aliases = {'g', 'gr', 'gramo', 'gramos'}
        if unit_raw in grams_aliases:
            return ('grams', amount, 'g')
        return ('unit', amount if amount > 0 else 1.0, unit_raw)

    def format_amount(amount):
        if abs(amount - round(amount)) < 0.01:
            return str(int(round(amount)))
        return f"{amount:.1f}"

    def fit_text(text, max_width, font_name='Helvetica', font_size=9):
        if pdf.stringWidth(text, font_name, font_size) <= max_width:
            return text
        suffix = '...'
        trimmed = text
        while trimmed and pdf.stringWidth(trimmed + suffix, font_name, font_size) > max_width:
            trimmed = trimmed[:-1]
        return (trimmed + suffix) if trimmed else suffix

    def wrap_text_lines(text, max_width, font_name='Helvetica', font_size=9):
        raw = str(text or '').strip()
        if not raw:
            return ['-']
        words = raw.split()
        if not words:
            return ['-']
        lines = []
        current = words[0]
        for word in words[1:]:
            candidate = current + ' ' + word
            if pdf.stringWidth(candidate, font_name, font_size) <= max_width:
                current = candidate
            else:
                lines.append(current)
                current = word
        lines.append(current)
        return lines

    def draw_page_number(label):
        page_w, _ = pdf._pagesize
        pdf.setFillColor(colors.HexColor('#94a3b8'))
        pdf.setFont('Helvetica', 8)
        pdf.drawRightString(page_w - 24, 18, label)

    def load_pdf_logo():
        # Optional logo for first page. If not available, PDF generation continues normally.
        env_logo_path = str(os.environ.get('DIET_PDF_LOGO_PATH') or '').strip()
        candidate_paths = []
        if env_logo_path:
            candidate_paths.append(env_logo_path if os.path.isabs(env_logo_path) else os.path.join(BASE_DIR, env_logo_path))
        candidate_paths.extend([
            os.path.join(STATIC_BASE_DIR, 'logo.png'),
            os.path.join(STATIC_BASE_DIR, 'logo.jpg'),
            os.path.join(STATIC_BASE_DIR, 'logo.jpeg'),
            os.path.join(STATIC_BASE_DIR, 'logo.webp'),
        ])
        for path in candidate_paths:
            if not os.path.exists(path):
                continue
            try:
                img = ImageReader(path)
                img_w, img_h = img.getSize()
                if img_w > 0 and img_h > 0:
                    return img, float(img_w), float(img_h)
            except Exception:
                continue
        return None

    meals_data = builder_data.get('meals') or []
    meals = meals_data if meals_data else [
        {'id': 1, 'name': 'Desayuno', 'order_index': 0},
        {'id': 2, 'name': 'Almuerzo', 'order_index': 1},
        {'id': 3, 'name': 'Merienda', 'order_index': 2},
        {'id': 4, 'name': 'Cena', 'order_index': 3},
    ]

    meal_name_by_id = {m['id']: m['name'] for m in meals}
    schedule = {m['name']: {day: [] for day in days} for m in meals}
    totals_by_day = {day: {'kcal': 0.0, 'p': 0.0, 'f': 0.0, 'c': 0.0} for day in days}
    day_configs = builder_data.get('day_configs') or {}

    def day_cfg(day):
        cfg = day_configs.get(day, {})
        return {
            'goal_kcal': to_float(cfg.get('goal_kcal')),
            'goal_steps': to_float(cfg.get('goal_steps')),
            'goal_protein': to_float(cfg.get('goal_protein')),
            'goal_fat': to_float(cfg.get('goal_fat')),
            'goal_carbs': to_float(cfg.get('goal_carbs')),
            'is_training': bool(cfg.get('is_training', True)),
        }

    shopping = {}

    for item in builder_data.get('items', []):
        food = (item.get('food_name') or 'Alimento').strip()
        brand = (item.get('food_brand') or '').strip()
        key = (food, brand)
        if key not in shopping:
            shopping[key] = {'units': {}, 'raw': []}
        nutrition_mode = (item.get('nutrition_mode') or 'per100').strip().lower()
        per100_unit = (item.get('per100_unit') or 'g').strip().lower()
        if per100_unit not in ('g', 'ml'):
            per100_unit = 'g'
        grams = to_float(item.get('grams') if item.get('grams') is not None else 100.0)
        units = to_float(item.get('units') if item.get('units') is not None else 1.0)
        if nutrition_mode == 'unit':
            shopping[key]['units']['ud'] = shopping[key]['units'].get('ud', 0.0) + max(units, 1.0)
        else:
            shopping[key]['units'][per100_unit] = shopping[key]['units'].get(per100_unit, 0.0) + grams

        day = normalize_day_name(item.get('day'))
        meal_id = item.get('meal_id')
        meal_name = meal_name_by_id.get(meal_id)
        if day in days and meal_name:
            label = food
            if brand:
                label += f' ({brand})'
            if nutrition_mode == 'unit':
                label += f' {fmt_num(max(units, 1.0))} ud'
            elif grams > 0:
                label += f' {fmt_num(grams)}{per100_unit}'
            schedule[meal_name][day].append(label)

            factor = max(units, 1.0) if nutrition_mode == 'unit' else (grams / 100.0)
            totals_by_day[day]['kcal'] += to_float(item.get('kcal_per100')) * factor
            totals_by_day[day]['p'] += to_float(item.get('protein_per100')) * factor
            totals_by_day[day]['f'] += to_float(item.get('fat_per100')) * factor
            totals_by_day[day]['c'] += to_float(item.get('carbs_per100')) * factor

    meal_name_set = {m['name'] for m in meals}
    for item in get_diet_items(diet_id):
        day = normalize_day_name(item[10])
        meal_id = item[6] if len(item) > 6 else None
        meal_time = (item[11] or '').strip()
        meal_name = meal_name_by_id.get(meal_id)
        if day not in days:
            continue
        if not meal_name and meal_time in meal_name_set:
            meal_name = meal_time
        if not meal_name:
            continue
        label = item[2]
        if item[3]:
            label += f' ({item[3]})'
        quantity_text = diet_item_quantity_text(item)
        if quantity_text:
            label += f' {quantity_text}'
        if label not in schedule[meal_name][day]:
            schedule[meal_name][day].append(label)

    for food_name, food_brand, quantity, grams, units, nutrition_mode, per100_unit in get_diet_items_without_meal(diet_id):
        food = (food_name or 'Alimento').strip()
        brand = (food_brand or '').strip()
        key = (food, brand)
        if key not in shopping:
            shopping[key] = {'units': {}, 'raw': []}
        if (nutrition_mode or 'per100') == 'unit':
            shopping[key]['units']['ud'] = shopping[key]['units'].get('ud', 0.0) + max(float(units or 1), 1.0)
        elif float(grams or 0) > 0:
            shopping[key]['units'][per100_unit or 'g'] = shopping[key]['units'].get(per100_unit or 'g', 0.0) + float(grams or 0)
        else:
            qty_kind, qty_amount, qty_unit = parse_quantity_text(quantity)
            if qty_kind == 'grams':
                shopping[key]['units']['g'] = shopping[key]['units'].get('g', 0.0) + qty_amount
            elif qty_kind == 'unit':
                shopping[key]['units'][qty_unit] = shopping[key]['units'].get(qty_unit, 0.0) + qty_amount
            else:
                if qty_unit not in shopping[key]['raw']:
                    shopping[key]['raw'].append(qty_unit)

    rows = []
    for (food, brand), data in sorted(shopping.items(), key=lambda x: (x[0][0].lower(), x[0][1].lower())):
        quantity_parts = []
        for unit_name, amount in sorted(data['units'].items()):
            quantity_parts.append(f"{format_amount(amount)} {unit_name}")
        for raw_text in data['raw']:
            quantity_parts.append(raw_text)
        quantity_text = ' + '.join(quantity_parts) if quantity_parts else '0 g'
        rows.append((food, brand or '-', quantity_text))

    buffer = io.BytesIO()
    pdf = canvas.Canvas(buffer, pagesize=landscape(A4))
    pdf.setPageCompression(0)
    width, height = landscape(A4)

    left = 24
    right = width - 24
    top = height - 24
    pdf_logo = load_pdf_logo()

    pdf.setFillColor(colors.HexColor('#f8fafc'))
    pdf.roundRect(left - 2, top - 52, (right - left) + 4, 56, 8, stroke=0, fill=1)

    if pdf_logo is not None:
        logo_img, logo_w, logo_h = pdf_logo
        max_logo_w = 210.0
        max_logo_h = 42.0
        scale = min(max_logo_w / logo_w, max_logo_h / logo_h)
        draw_w = logo_w * scale
        draw_h = logo_h * scale
        logo_x = right - draw_w - 8
        logo_y = top - draw_h - 5
        pdf.drawImage(logo_img, logo_x, logo_y, width=draw_w, height=draw_h, preserveAspectRatio=True, mask='auto')

    pdf.setFillColor(colors.HexColor('#0f172a'))
    pdf.setFont('Helvetica-Bold', 16)
    pdf.drawString(left + 4, top - 2, f"Dieta: {diet_name}")
    pdf.setFillColor(colors.HexColor('#475569'))
    pdf.setFont('Helvetica', 10)
    pdf.drawString(left + 4, top - 18, f"Cliente: {client_name}")
    pdf.drawString(left + 4, top - 31, client_data_text)
    pdf.drawString(left + 4, top - 44, f"Descripción: {diet.get('description') or '-'}")

    table_top = top - 70
    header_h = 44
    meal_col_w = 126
    day_col_w = (right - left - meal_col_w) / 7.0
    table_bottom_limit = 72
    max_table_h = table_top - table_bottom_limit - header_h

    table_font_size = 7.2
    table_line_h = 8.2
    table_row_padding = 12

    def wrap_line(text, max_width, font_size=7.2):
        words = text.split()
        if not words:
            return ['']
        lines = []
        curr = words[0]
        for word in words[1:]:
            candidate = curr + ' ' + word
            if pdf.stringWidth(candidate, 'Helvetica', font_size) <= max_width:
                curr = candidate
            else:
                lines.append(curr)
                curr = word
        lines.append(curr)
        return lines

    line_width = day_col_w - 10

    def draw_cell_lines(lines, x, y_top, w, h, font_size, line_h):
        pdf.setFont('Helvetica', font_size)
        y = y_top - 10
        for text in lines:
            if y < (y_top - h + 8):
                break
            pdf.drawString(x + 3, y, text)
            y -= line_h

    row_infos = []

    for meal in meals:
        meal_name = meal['name']
        cell_lines_by_day = []
        max_cell_lines = 1
        for day in days:
            items = schedule.get(meal_name, {}).get(day, [])
            if not items:
                cell_lines = ['Sin alimentos']
            else:
                cell_lines = []
                for it in items:
                    wrapped = wrap_line(it, max_width=line_width, font_size=table_font_size)
                    for i, segment in enumerate(wrapped):
                        cell_lines.append(('- ' if i == 0 else '  ') + segment)
            max_cell_lines = max(max_cell_lines, len(cell_lines))
            cell_lines_by_day.append(cell_lines)
        row_infos.append({
            'meal_name': meal_name,
            'cell_lines_by_day': cell_lines_by_day,
            'height': max(42.0, table_row_padding + (max_cell_lines * table_line_h)),
        })

    available_table_h = max_table_h
    total_rows_h = sum(r['height'] for r in row_infos)
    if total_rows_h > available_table_h and total_rows_h > 0:
        shrink = available_table_h / total_rows_h
        table_font_size = max(6.0, round(table_font_size * shrink, 1))
        table_line_h = max(7.0, round(table_line_h * shrink, 1))
        table_row_padding = max(8.0, round(table_row_padding * shrink, 1))
        row_infos = []
        for meal in meals:
            meal_name = meal['name']
            cell_lines_by_day = []
            max_cell_lines = 1
            for day in days:
                items = schedule.get(meal_name, {}).get(day, [])
                if not items:
                    cell_lines = ['Sin alimentos']
                else:
                    cell_lines = []
                    for it in items:
                        wrapped = wrap_line(it, max_width=line_width, font_size=table_font_size)
                        for i, segment in enumerate(wrapped):
                            cell_lines.append(('- ' if i == 0 else '  ') + segment)
                max_cell_lines = max(max_cell_lines, len(cell_lines))
                cell_lines_by_day.append(cell_lines)
            row_infos.append({
                'meal_name': meal_name,
                'cell_lines_by_day': cell_lines_by_day,
                'height': max(44.0, table_row_padding + (max_cell_lines * table_line_h)),
            })

    col_x = [left, left + meal_col_w]
    for i in range(1, 8):
        col_x.append(left + meal_col_w + (i * day_col_w))

    pdf.setFillColor(colors.HexColor('#f7efe7'))
    pdf.rect(left, table_top - header_h, right - left, header_h, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#fffaf5'))
    row_tops = [table_top - header_h]
    current_row_top = table_top - header_h
    for row_info in row_infos:
        pdf.rect(left, current_row_top - row_info['height'], meal_col_w, row_info['height'], stroke=0, fill=1)
        current_row_top -= row_info['height']
        row_tops.append(current_row_top)

    table_bottom = current_row_top

    pdf.setStrokeColor(colors.HexColor('#cbd5e1'))
    pdf.setLineWidth(0.8)
    for x in col_x:
        pdf.line(x, table_top, x, table_bottom)
    for y in [table_top, table_top - header_h] + row_tops[1:]:
        pdf.line(left, y, right, y)

    pdf.setFillColor(colors.HexColor('#334155'))
    pdf.setFont('Helvetica-Bold', 8.5)
    pdf.drawString(left + 6, table_top - 14, 'Comida / Día')

    for day_idx, day in enumerate(days):
        x = left + meal_col_w + (day_idx * day_col_w)
        cfg = day_cfg(day)
        is_training = cfg['is_training']
        goal_kcal = cfg['goal_kcal']
        goal_steps = cfg['goal_steps']
        goal_protein = cfg['goal_protein']
        goal_fat = cfg['goal_fat']
        goal_carbs = cfg['goal_carbs']

        badge_bg = colors.HexColor('#dcfce7') if is_training else colors.HexColor('#e2e8f0')
        badge_fg = colors.HexColor('#15803d') if is_training else colors.HexColor('#64748b')
        badge_text = 'Entreno' if is_training else 'Descanso'

        pdf.setFillColor(badge_bg)
        pdf.roundRect(x + 6, table_top - 17, 46, 11, 3, stroke=0, fill=1)
        pdf.setFillColor(badge_fg)
        pdf.setFont('Helvetica-Bold', 6.8)
        pdf.drawString(x + 10, table_top - 13.4, badge_text)

        pdf.setFillColor(colors.HexColor('#334155'))
        pdf.setFont('Helvetica-Bold', 8.2)
        pdf.drawString(x + 56, table_top - 8, day)

        kcal_text = f"Objetivo: {fmt_num(goal_kcal)} kcal" if goal_kcal > 0 else "Objetivo: sin definir"
        pdf.setFillColor(colors.HexColor('#0f172a'))
        pdf.setFont('Helvetica-Bold', 7.2)
        pdf.drawString(x + 6, table_top - 25, kcal_text)

        macro_goal_text = f"Obj P:{fmt_num(goal_protein)}g G:{fmt_num(goal_fat)}g C:{fmt_num(goal_carbs)}g"
        pdf.setFillColor(colors.HexColor('#64748b'))
        pdf.setFont('Helvetica', 6.4)
        pdf.drawString(x + 6, table_top - 34, macro_goal_text)

        steps_goal_text = f"Pasos: {fmt_num(goal_steps)}" if goal_steps > 0 else "Pasos: sin definir"
        pdf.setFont('Helvetica', 6.4)
        pdf.drawString(x + 6, table_top - 41, steps_goal_text)

    current_y = table_top - header_h
    for meal_idx, row_info in enumerate(row_infos):
        meal_name = row_info['meal_name']
        row_h_i = row_info['height']
        cell_top = current_y
        pdf.setFillColor(colors.HexColor('#334155'))
        pdf.setFont('Helvetica-Bold', 8.8)
        pdf.drawString(left + 6, cell_top - 14, meal_name)

        for day_idx, day in enumerate(days):
            cell_x = left + meal_col_w + (day_idx * day_col_w)
            cell_lines = row_info['cell_lines_by_day'][day_idx]
            if cell_lines == ['Sin alimentos']:
                pdf.setFillColor(colors.HexColor('#94a3b8'))
            else:
                pdf.setFillColor(colors.HexColor('#0f172a'))
            draw_cell_lines(cell_lines, cell_x, cell_top, day_col_w, row_h_i, table_font_size, table_line_h)

        current_y -= row_h_i

    draw_page_number('Página 1')
    pdf.showPage()

    # Página 2: indicaciones del cliente
    pdf.setPageSize(A4)
    width, height = A4
    left = 36
    right = width - 36
    top = height - 36
    bottom = 42

    pdf.setFillColor(colors.HexColor('#f8fafc'))
    pdf.roundRect(left - 2, top - 45, (right - left) + 4, 48, 8, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#0f172a'))
    pdf.setFont('Helvetica-Bold', 14)
    pdf.drawString(left + 2, top - 1, 'Indicaciones del cliente')
    pdf.setFillColor(colors.HexColor('#475569'))
    pdf.setFont('Helvetica', 9)
    pdf.drawString(left + 2, top - 13, f"Cliente: {client_name}")
    pdf.drawString(left + 2, top - 25, f"Dieta: {diet_name}")
    pdf.drawString(left + 2, top - 37, client_data_text)

    text_y_start = top - 64
    pdf.setFillColor(colors.HexColor('#ffffff'))
    pdf.roundRect(left - 1, bottom - 4, (right - left) + 2, text_y_start - bottom + 8, 8, stroke=0, fill=1)
    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
    pdf.setLineWidth(0.8)
    pdf.roundRect(left - 1, bottom - 4, (right - left) + 2, text_y_start - bottom + 8, 8, stroke=1, fill=0)

    max_line_width = right - left - 14
    line_height = 12
    y_cursor = text_y_start - 8
    paragraphs = [p.strip() for p in (client_instructions or '').split('\n') if p.strip()]
    if not paragraphs:
        paragraphs = ['Sin indicaciones específicas.']

    pdf.setFillColor(colors.HexColor('#0f172a'))
    pdf.setFont('Helvetica', 10)

    for paragraph in paragraphs:
        words = paragraph.split()
        if not words:
            continue
        current = words[0]
        lines = []
        for word in words[1:]:
            candidate = current + ' ' + word
            if pdf.stringWidth(candidate, 'Helvetica', 10) <= max_line_width:
                current = candidate
            else:
                lines.append(current)
                current = word
        lines.append(current)

        for idx, line in enumerate(lines):
            if y_cursor < bottom + 10:
                break
            prefix = '• ' if idx == 0 else '  '
            pdf.drawString(left + 6, y_cursor, fit_text(prefix + line, max_line_width, font_name='Helvetica', font_size=10))
            y_cursor -= line_height
        y_cursor -= 4
        if y_cursor < bottom + 10:
            break

    draw_page_number('Página 2')
    pdf.showPage()

    # Página 3: lista de compra semanal
    pdf.setPageSize(A4)
    width, height = A4
    left = 36
    right = width - 36
    top = height - 36
    bottom = 36

    title = f"Lista de compra semanal (totales): {diet_name}"

    alimento_w = (right - left) * 0.42
    marca_w = (right - left) * 0.24
    cantidad_w = (right - left) - alimento_w - marca_w

    def draw_page_header(y_top):
        pdf.setFillColor(colors.HexColor('#f8fafc'))
        pdf.roundRect(left - 2, y_top - 45, (right - left) + 4, 48, 8, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor('#0f172a'))
        pdf.setFont('Helvetica-Bold', 14)
        pdf.drawString(left + 2, y_top - 1, title)
        pdf.setFillColor(colors.HexColor('#475569'))
        pdf.setFont('Helvetica', 9)
        pdf.drawString(left + 2, y_top - 13, f"Cliente: {client_name}")
        pdf.drawString(left + 2, y_top - 25, client_data_text)
        pdf.drawString(left + 2, y_top - 37, f"Descripción: {diet.get('description') or '-'}")

        table_y = y_top - 54
        pdf.setFillColor(colors.HexColor('#f1f5f9'))
        pdf.rect(left, table_y - 16, right - left, 16, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor('#334155'))
        pdf.setFont('Helvetica-Bold', 9)
        pdf.drawString(left + 4, table_y - 11, 'Alimento')
        pdf.drawString(left + alimento_w + 4, table_y - 11, 'Marca')
        pdf.drawString(left + alimento_w + marca_w + 4, table_y - 11, 'Cantidad semanal')
        return table_y - 18

    y = draw_page_header(top)
    row_h = 16

    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
    pdf.setLineWidth(0.6)

    if not rows:
        pdf.setFillColor(colors.HexColor('#64748b'))
        pdf.setFont('Helvetica', 10)
        pdf.drawString(left, y - 4, 'No hay alimentos en la dieta para generar lista de compra.')
        draw_page_number(f"Página {pdf.getPageNumber()}")
    else:
        for idx, (food, brand, quantity) in enumerate(rows):
            if y - row_h < bottom:
                draw_page_number(f"Página {pdf.getPageNumber()}")
                pdf.showPage()
                y = draw_page_header(top)
                pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
                pdf.setLineWidth(0.6)

            if idx % 2 == 0:
                pdf.setFillColor(colors.HexColor('#f7efe7'))
                pdf.rect(left, y - row_h + 1, right - left, row_h, stroke=0, fill=1)

            pdf.setFillColor(colors.HexColor('#0f172a'))
            pdf.setFont('Helvetica', 9)
            food_txt = fit_text(food, alimento_w - 8)
            brand_txt = fit_text(brand, marca_w - 8)
            qty_txt = fit_text(quantity, cantidad_w - 8)

            pdf.drawString(left + 4, y - 11, food_txt)
            pdf.drawString(left + alimento_w + 4, y - 11, brand_txt)
            pdf.drawString(left + alimento_w + marca_w + 4, y - 11, qty_txt)

            pdf.line(left, y - row_h, right, y - row_h)
            y -= row_h
        draw_page_number(f"Página {pdf.getPageNumber()}")

    pdf.showPage()

    # Última página: suplementación
    supplements = builder_data.get('supplements') or []
    pdf.setPageSize(A4)
    width, height = A4
    left = 36
    right = width - 36
    top = height - 36
    bottom = 36

    pdf.setFillColor(colors.HexColor('#f8fafc'))
    pdf.roundRect(left - 2, top - 45, (right - left) + 4, 48, 8, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#0f172a'))
    pdf.setFont('Helvetica-Bold', 14)
    pdf.drawString(left + 2, top - 1, 'Suplementación')
    pdf.setFillColor(colors.HexColor('#475569'))
    pdf.setFont('Helvetica', 9)
    pdf.drawString(left + 2, top - 13, f"Cliente: {client_name}")
    pdf.drawString(left + 2, top - 25, f"Dieta: {diet_name}")
    pdf.drawString(left + 2, top - 37, client_data_text)

    table_top = top - 58
    name_w = (right - left) * 0.24
    when_w = (right - left) * 0.18
    dose_w = (right - left) * 0.14
    notes_w = (right - left) - name_w - when_w - dose_w

    pdf.setFillColor(colors.HexColor('#f1f5f9'))
    pdf.rect(left, table_top - 16, right - left, 16, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#334155'))
    pdf.setFont('Helvetica-Bold', 9)
    pdf.drawString(left + 4, table_top - 11, 'Suplemento')
    pdf.drawString(left + name_w + 4, table_top - 11, 'Momento de toma')
    pdf.drawString(left + name_w + when_w + 4, table_top - 11, 'Dosis')
    pdf.drawString(left + name_w + when_w + dose_w + 4, table_top - 11, 'Observaciones')

    base_row_h = 18
    line_h = 10
    y = table_top - 18
    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
    pdf.setLineWidth(0.6)

    col_1 = left + name_w
    col_2 = col_1 + when_w
    col_3 = col_2 + dose_w

    if not supplements:
        pdf.setFillColor(colors.HexColor('#64748b'))
        pdf.setFont('Helvetica', 10)
        pdf.drawString(left, y - 4, 'No hay suplementación registrada en esta dieta.')
    else:
        for idx, s in enumerate(supplements):
            if y - base_row_h < bottom:
                draw_page_number(f"Página {pdf.getPageNumber()}")
                pdf.showPage()
                pdf.setPageSize(A4)
                width, height = A4
                left = 36
                right = width - 36
                top = height - 36
                bottom = 36

                pdf.setFillColor(colors.HexColor('#f8fafc'))
                pdf.roundRect(left - 2, top - 45, (right - left) + 4, 48, 8, stroke=0, fill=1)
                pdf.setFillColor(colors.HexColor('#0f172a'))
                pdf.setFont('Helvetica-Bold', 14)
                pdf.drawString(left + 2, top - 1, 'Suplementación')
                pdf.setFillColor(colors.HexColor('#475569'))
                pdf.setFont('Helvetica', 9)
                pdf.drawString(left + 2, top - 13, f"Cliente: {client_name}")
                pdf.drawString(left + 2, top - 25, f"Dieta: {diet_name}")
                pdf.drawString(left + 2, top - 37, client_data_text)

                table_top = top - 58
                pdf.setFillColor(colors.HexColor('#f1f5f9'))
                pdf.rect(left, table_top - 16, right - left, 16, stroke=0, fill=1)
                pdf.setFillColor(colors.HexColor('#334155'))
                pdf.setFont('Helvetica-Bold', 9)
                pdf.drawString(left + 4, table_top - 11, 'Suplemento')
                pdf.drawString(left + name_w + 4, table_top - 11, 'Momento de toma')
                pdf.drawString(left + name_w + when_w + 4, table_top - 11, 'Dosis')
                pdf.drawString(left + name_w + when_w + dose_w + 4, table_top - 11, 'Observaciones')
                pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
                pdf.setLineWidth(0.6)
                y = table_top - 18

            name_lines = wrap_text_lines((s.get('supplement_name') or '-').strip() or '-', name_w - 8, font_name='Helvetica', font_size=8.8)
            when_lines = wrap_text_lines((s.get('intake_time') or '-').strip() or '-', when_w - 8, font_name='Helvetica', font_size=8.8)
            dose_lines = wrap_text_lines((s.get('dose') or '-').strip() or '-', dose_w - 8, font_name='Helvetica', font_size=8.8)
            notes_lines = wrap_text_lines((s.get('notes') or '-').strip() or '-', notes_w - 8, font_name='Helvetica', font_size=8.8)
            max_lines = max(len(name_lines), len(when_lines), len(dose_lines), len(notes_lines))
            row_h = max(base_row_h, 8 + (max_lines * line_h))

            if y - row_h < bottom:
                draw_page_number(f"Página {pdf.getPageNumber()}")
                pdf.showPage()
                pdf.setPageSize(A4)
                width, height = A4
                left = 36
                right = width - 36
                top = height - 36
                bottom = 36

                pdf.setFillColor(colors.HexColor('#f8fafc'))
                pdf.roundRect(left - 2, top - 45, (right - left) + 4, 48, 8, stroke=0, fill=1)
                pdf.setFillColor(colors.HexColor('#0f172a'))
                pdf.setFont('Helvetica-Bold', 14)
                pdf.drawString(left + 2, top - 1, 'Suplementación')
                pdf.setFillColor(colors.HexColor('#475569'))
                pdf.setFont('Helvetica', 9)
                pdf.drawString(left + 2, top - 13, f"Cliente: {client_name}")
                pdf.drawString(left + 2, top - 25, f"Dieta: {diet_name}")
                pdf.drawString(left + 2, top - 37, client_data_text)

                table_top = top - 58
                pdf.setFillColor(colors.HexColor('#f1f5f9'))
                pdf.rect(left, table_top - 16, right - left, 16, stroke=0, fill=1)
                pdf.setFillColor(colors.HexColor('#334155'))
                pdf.setFont('Helvetica-Bold', 9)
                pdf.drawString(left + 4, table_top - 11, 'Suplemento')
                pdf.drawString(left + name_w + 4, table_top - 11, 'Momento de toma')
                pdf.drawString(left + name_w + when_w + 4, table_top - 11, 'Dosis')
                pdf.drawString(left + name_w + when_w + dose_w + 4, table_top - 11, 'Observaciones')
                pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
                pdf.setLineWidth(0.6)
                y = table_top - 18

                name_lines = wrap_text_lines((s.get('supplement_name') or '-').strip() or '-', name_w - 8, font_name='Helvetica', font_size=8.8)
                when_lines = wrap_text_lines((s.get('intake_time') or '-').strip() or '-', when_w - 8, font_name='Helvetica', font_size=8.8)
                dose_lines = wrap_text_lines((s.get('dose') or '-').strip() or '-', dose_w - 8, font_name='Helvetica', font_size=8.8)
                notes_lines = wrap_text_lines((s.get('notes') or '-').strip() or '-', notes_w - 8, font_name='Helvetica', font_size=8.8)
                max_lines = max(len(name_lines), len(when_lines), len(dose_lines), len(notes_lines))
                row_h = max(base_row_h, 8 + (max_lines * line_h))

            if idx % 2 == 0:
                pdf.setFillColor(colors.HexColor('#f8fafc'))
                pdf.rect(left, y - row_h + 1, right - left, row_h, stroke=0, fill=1)

            pdf.setFillColor(colors.HexColor('#0f172a'))
            pdf.setFont('Helvetica', 8.8)
            start_y = y - 11
            for i, line in enumerate(name_lines):
                pdf.drawString(left + 4, start_y - (i * line_h), line)
            for i, line in enumerate(when_lines):
                pdf.drawString(col_1 + 4, start_y - (i * line_h), line)
            for i, line in enumerate(dose_lines):
                pdf.drawString(col_2 + 4, start_y - (i * line_h), line)
            for i, line in enumerate(notes_lines):
                pdf.drawString(col_3 + 4, start_y - (i * line_h), line)

            pdf.line(left, y - row_h, right, y - row_h)
            pdf.line(col_1, y, col_1, y - row_h)
            pdf.line(col_2, y, col_2, y - row_h)
            pdf.line(col_3, y, col_3, y - row_h)
            y -= row_h

    draw_page_number(f"Página {pdf.getPageNumber()}")

    pdf.save()
    return buffer.getvalue()


def build_routine_pdf(routine_id):
    routine = get_routine_by_id(routine_id)
    if routine is None:
        return None

    routine_title = str(routine[1] or '').strip() or f'Rutina {routine_id}'

    items = get_routine_items(routine_id)
    series_summary = get_routine_series_totals(routine_id)
    exercise_lookup = {e[0]: {'name': e[1], 'video_url': (e[7] or '').strip()} for e in get_exercises()}
    routine_days = get_routine_days(routine_id)
    if routine_days:
        ordered_days = [(int(day_index), day_name or f'Día {int(day_index) + 1}') for day_index, day_name, _day_type in routine_days]
    else:
        ordered_days = [(day_index, day_name) for day_index, day_name, _day_type in get_default_routine_days()]
    grouped_items = {day_index: [] for day_index, _day_name in ordered_days}
    for item in items:
        item_day_index = int(item[9]) if int(item[9]) >= 0 else None
        if item_day_index is None:
            for day_index, day_name in ordered_days:
                if (item[2] or '').strip() == (day_name or '').strip():
                    item_day_index = day_index
                    break
        if item_day_index is None:
            item_day_index = 0
        grouped_items.setdefault(item_day_index, []).append(item)

    def fit_text(text, max_width, font_name='Helvetica', font_size=9):
        if pdf.stringWidth(text, font_name, font_size) <= max_width:
            return text
        suffix = '...'
        trimmed = text
        while trimmed and pdf.stringWidth(trimmed + suffix, font_name, font_size) > max_width:
            trimmed = trimmed[:-1]
        return (trimmed + suffix) if trimmed else suffix

    def wrap_text(text, max_width, font_name='Helvetica', font_size=9):
        words = str(text or '').split()
        if not words:
            return ['']
        lines = []
        current = words[0]
        for word in words[1:]:
            candidate = current + ' ' + word
            if pdf.stringWidth(candidate, font_name, font_size) <= max_width:
                current = candidate
            else:
                lines.append(current)
                current = word
        lines.append(current)
        return lines

    def normalize_video_url(url):
        text = str(url or '').strip()
        if not text:
            return ''
        if re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*://', text):
            return text
        return 'https://' + text.lstrip('/')

    def draw_page_number(label):
        page_w, _ = pdf._pagesize
        pdf.setFillColor(colors.HexColor('#94a3b8'))
        pdf.setFont('Helvetica', 8)
        pdf.drawRightString(page_w - 24, 18, label)

    def draw_header(y_top):
        pdf.setFillColor(colors.HexColor('#f8fafc'))
        pdf.roundRect(24, y_top - 56, 794, 58, 8, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor('#0f172a'))
        pdf.setFont('Helvetica-Bold', 18)
        pdf.drawString(30, y_top - 6, fit_text(routine_title, 760, font_name='Helvetica-Bold', font_size=18))
        pdf.setFillColor(colors.HexColor('#475569'))
        pdf.setFont('Helvetica', 10)
        pdf.drawString(30, y_top - 24, f"Descripción: {routine[2] or '-'}")
        pdf.drawString(30, y_top - 38, f"Creada: {routine[3] or '-'}")
        pdf.drawString(30, y_top - 48, f"ID: {routine[0]}")
        return y_top - 72

    buffer = io.BytesIO()
    pdf = canvas.Canvas(buffer, pagesize=A4)
    pdf.setPageCompression(0)
    width, height = A4

    left = 24
    right = width - 24
    top = height - 24
    bottom = 42
    content_width = right - left

    y = draw_header(top)

    summary_rows = series_summary or [('Sin grupo muscular', 0)]
    summary_height = 28 + (len(summary_rows) + 1) * 14
    if y - summary_height < bottom:
        draw_page_number(f'Página {pdf.getPageNumber()}')
        pdf.showPage()
        pdf.setPageSize(A4)
        pdf.setPageCompression(0)
        pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
        pdf.setLineWidth(0.8)
        y = draw_header(top)

    pdf.setFillColor(colors.HexColor('#f8fafc'))
    pdf.roundRect(left, y - summary_height + 4, content_width, summary_height - 4, 8, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#0f172a'))
    pdf.setFont('Helvetica-Bold', 11)
    pdf.drawString(left + 8, y - 14, 'Series por grupo muscular')
    pdf.setFillColor(colors.HexColor('#64748b'))
    pdf.setFont('Helvetica-Bold', 8)
    pdf.drawString(left + 10, y - 28, 'Grupo muscular')
    pdf.drawRightString(right - 10, y - 28, 'Series')
    row_y = y - 42
    pdf.setFont('Helvetica', 9)
    pdf.setFillColor(colors.HexColor('#0f172a'))
    for group_name, series_count in summary_rows:
        pdf.drawString(left + 10, row_y, fit_text(str(group_name), content_width - 72))
        pdf.drawRightString(right - 10, row_y, str(series_count))
        row_y -= 14
    y = row_y - 10

    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
    pdf.setLineWidth(0.8)
    used_video_links = []
    used_video_ids = set()

    for day_index, day in ordered_days:
        day_items = grouped_items.get(day_index, [])
        item_lines = []
        for item in day_items:
            item_id, _routine_id, _day_name, _exercise_id, exercise_name, sets_text, reps_text, notes, _sort_order, _item_day_index = item
            if _exercise_id in exercise_lookup and _exercise_id not in used_video_ids:
                exercise_data = exercise_lookup.get(_exercise_id) or {}
                video_url = normalize_video_url(exercise_data.get('video_url') or '')
                if video_url:
                    used_video_ids.add(_exercise_id)
                    used_video_links.append((exercise_data.get('name') or exercise_name or 'Ejercicio', video_url))
            parts = [exercise_name or 'Ejercicio']
            if sets_text:
                parts.append(f'Series: {sets_text}')
            if reps_text:
                parts.append(f'Reps: {reps_text}')
            if notes:
                parts.append(f'Notas: {notes}')
            item_lines.append(' · '.join(parts))

        estimated_height = 34 + (len(item_lines) * 18 if item_lines else 18)
        if y - estimated_height < bottom:
            draw_page_number(f'Página {pdf.getPageNumber()}')
            pdf.showPage()
            pdf.setPageSize(A4)
            pdf.setPageCompression(0)
            pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
            pdf.setLineWidth(0.8)
            y = draw_header(top)

        pdf.setFillColor(colors.HexColor('#f1f5f9'))
        pdf.roundRect(left, y - 22, content_width, 20, 6, stroke=0, fill=1)
        pdf.setFillColor(colors.HexColor('#0f172a'))
        pdf.setFont('Helvetica-Bold', 11)
        pdf.drawString(left + 8, y - 16, day)

        y -= 34
        if not item_lines:
            pdf.setFillColor(colors.HexColor('#64748b'))
            pdf.setFont('Helvetica', 9)
            pdf.drawString(left + 8, y, 'Sin ejercicios asignados.')
            y -= 18
            continue

        for item_line in item_lines:
            wrapped_lines = wrap_text(item_line, content_width - 16)
            for wrapped_line in wrapped_lines:
                if y - 14 < bottom:
                    draw_page_number(f'Página {pdf.getPageNumber()}')
                    pdf.showPage()
                    pdf.setPageSize(A4)
                    pdf.setPageCompression(0)
                    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
                    pdf.setLineWidth(0.8)
                    y = draw_header(top)
                    pdf.setFillColor(colors.HexColor('#f1f5f9'))
                    pdf.roundRect(left, y - 22, content_width, 20, 6, stroke=0, fill=1)
                    pdf.setFillColor(colors.HexColor('#0f172a'))
                    pdf.setFont('Helvetica-Bold', 11)
                    pdf.drawString(left + 8, y - 16, day)
                    y -= 34
                pdf.setFillColor(colors.HexColor('#0f172a'))
                pdf.setFont('Helvetica', 9)
                pdf.drawString(left + 10, y, fit_text(wrapped_line, content_width - 16))
                y -= 12
            y -= 6

        y -= 8

    draw_page_number(f'Página {pdf.getPageNumber()}')
    pdf.showPage()
    pdf.setPageSize(A4)
    pdf.setPageCompression(0)
    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
    pdf.setLineWidth(0.8)
    y = draw_header(top)

    pdf.setFillColor(colors.HexColor('#f1f5f9'))
    pdf.roundRect(left, y - 22, content_width, 20, 6, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#0f172a'))
    pdf.setFont('Helvetica-Bold', 11)
    pdf.drawString(left + 8, y - 16, 'Link de ejercicios')
    y -= 34

    pdf.setFont('Helvetica', 9)
    if used_video_links:
        for index, (exercise_name, video_url) in enumerate(used_video_links, start=1):
            lines = wrap_text(f'{index}. {exercise_name} - {video_url}', content_width - 16, font_name='Helvetica', font_size=9)
            for line in lines:
                if y - 14 < bottom:
                    draw_page_number(f'Página {pdf.getPageNumber()}')
                    pdf.showPage()
                    pdf.setPageSize(A4)
                    pdf.setPageCompression(0)
                    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
                    pdf.setLineWidth(0.8)
                    y = draw_header(top)
                    pdf.setFillColor(colors.HexColor('#f1f5f9'))
                    pdf.roundRect(left, y - 22, content_width, 20, 6, stroke=0, fill=1)
                    pdf.setFillColor(colors.HexColor('#0f172a'))
                    pdf.setFont('Helvetica-Bold', 11)
                    pdf.drawString(left + 8, y - 16, 'Link de ejercicios')
                    y -= 34
                    pdf.setFont('Helvetica', 9)
                pdf.setFillColor(colors.HexColor('#0f172a'))
                rendered_line = fit_text(line, content_width - 16, font_name='Helvetica', font_size=9)
                pdf.drawString(left + 8, y, rendered_line)
                pdf.linkURL(
                    video_url,
                    (left + 8, y - 2, left + 8 + pdf.stringWidth(rendered_line, 'Helvetica', 9), y + 10),
                    relative=0,
                    thickness=0,
                    color=colors.transparent,
                )
                y -= 12
            y -= 6
    else:
        pdf.setFillColor(colors.HexColor('#64748b'))
        pdf.setFont('Helvetica', 10)
        pdf.drawString(left + 8, y, 'No hay links de video asociados a los ejercicios de esta rutina.')

    draw_page_number(f'Página {pdf.getPageNumber()}')
    pdf.showPage()
    pdf.save()
    return buffer.getvalue()


def category_icon(category_name):
    if not category_name:
        return ''

    name = category_name.lower().strip()
    mapping = [
        (['carne', 'vacuno', 'cerdo', 'cordero', 'pavo', 'pollo'], '🥩'),
        (['pescado', 'marisco', 'salmón', 'atun', 'atún', 'camarón', 'langosta'], '🐟'),
        (['fruta', 'manzana', 'banana', 'pera', 'uva', 'naranja', 'fresa', 'mango', 'kiwi'], '🍎'),
        (['verdura', 'vegetal', 'ensalada', 'brócoli', 'brocoli', 'espinaca', 'espinacas', 'lechuga', 'zanahoria'], '🥦'),
        (['lácteo', 'lacteo', 'queso', 'yogur', 'leche', 'nata', 'mantequilla', 'requesón'], '🧀'),
        (['pan', 'cereal', 'harina', 'pizza', 'pasta', 'tostada', 'bagel'], '🥖'),
        (['postre', 'dulce', 'helado', 'pastel', 'chocolate', 'galleta'], '🍰'),
        (['bebida', 'jugo', 'refresco', 'agua', 'té', 'café', 'vino', 'cerveza', 'coctel'], '🥤'),
        (['legumbre', 'legumbres', 'lenteja', 'garbanzo', 'frijol', 'judía', 'altramuz', 'nuez', 'semilla'], '🥜'),
        (['sopa', 'guiso', 'caldo', 'estofado'], '🍲'),
    ]

    for keywords, icon in mapping:
        for keyword in keywords:
            if re.search(rf"\b{re.escape(keyword)}\b", name, flags=re.UNICODE):
                safe_name = html.escape(category_name)
                return f'<span class="category-pill">{icon} {safe_name}</span>'

    safe_name = html.escape(category_name)
    return f'<span class="category-pill">🍽️ {safe_name}</span>'


def logo_html():
    base_dir = os.path.dirname(__file__)
    for filename in ('logo.png', 'logo.svg'):
        logo_path = os.path.join(base_dir, STATIC_DIR, filename)
        if os.path.exists(logo_path):
            return f'<img src="/static/{filename}" alt="Fitness Evolution" style="max-height:64px;margin-bottom:24px;display:block;object-fit:contain;" />'
    return ''


def home_link():
    logo = logo_html()
    return f'<div style="display:flex;align-items:center;gap:18px;flex-wrap:wrap;margin-bottom:28px;">{logo}<a href="/admin" style="display:inline-flex;align-items:center;justify-content:center;padding:14px 20px;background:#ffffff;border:1px solid #d8dde6;border-radius:14px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;font-weight:700;text-decoration:none;min-width:220px;transition:transform .18s ease,border-color .18s ease,box-shadow .18s ease;">Panel principal</a></div>'


class Handler(BaseHTTPRequestHandler):
    def is_admin_authenticated(self):
        cookies = parse_cookie_header(self.headers.get('Cookie', ''))
        token = cookies.get(ADMIN_PORTAL_COOKIE, '')
        return parse_admin_portal_session_token(token) is not None

    def redirect_admin_login(self, next_path='/admin'):
        self.send_response(303)
        self.send_header('Location', '/client_login?next=' + urllib.parse.quote(next_path or '/admin'))
        self.end_headers()

    def read_json(self):
        length = int(self.headers.get('Content-Length', 0))
        if length == 0:
            return None
        raw = self.rfile.read(length)
        try:
            return json.loads(raw.decode('utf-8'))
        except Exception:
            return None

    def send_json(self, obj, status=200):
        body = json.dumps(obj, ensure_ascii=False).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path.strip()
        q = urllib.parse.parse_qs(parsed.query)

        # Mobile browsers probe these icon paths automatically.
        # Return 204 to avoid useless auth redirects and log noise.
        if path in (
            '/favicon.ico',
            '/apple-touch-icon.png',
            '/apple-touch-icon-precomposed.png',
            '/apple-touch-icon-120x120.png',
            '/apple-touch-icon-120x120-precomposed.png',
        ):
            self.send_response(204)
            self.end_headers()
            return

        if path.startswith('/static/'):
            rel_path = urllib.parse.unquote(path[len('/static/'):]).strip()
            safe_path = os.path.normpath(rel_path)
            if safe_path.startswith('..'):
                self.send_response(403)
                self.end_headers()
                return

            path_parts = safe_path.split('/')
            if path_parts and path_parts[0] == 'uploads':
                upload_rel = '/'.join(path_parts[1:])
                uploads_root_abs = os.path.abspath(UPLOADS_DIR)
                full_path = os.path.abspath(os.path.normpath(os.path.join(uploads_root_abs, upload_rel)))
                if not full_path.startswith(uploads_root_abs + os.sep):
                    self.send_response(403)
                    self.end_headers()
                    return

                # Backward compatibility: old images may still be bundled under scripts/static/uploads.
                if not os.path.isfile(full_path):
                    legacy_uploads_abs = os.path.abspath(os.path.join(STATIC_BASE_DIR, 'uploads'))
                    legacy_path = os.path.abspath(os.path.normpath(os.path.join(legacy_uploads_abs, upload_rel)))
                    if not legacy_path.startswith(legacy_uploads_abs + os.sep):
                        self.send_response(403)
                        self.end_headers()
                        return
                    full_path = legacy_path
            else:
                full_path = os.path.join(STATIC_BASE_DIR, safe_path)

            if not os.path.isfile(full_path):
                self.send_response(404)
                self.end_headers()
                return
            ctype, _ = mimetypes.guess_type(full_path)
            if not ctype:
                ctype = 'application/octet-stream'
            with open(full_path, 'rb') as f:
                body = f.read()
            self.send_response(200)
            self.send_header('Content-Type', ctype)
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if path in ('/', '/index.html'):
            self.send_response(303)
            self.send_header('Location', '/client_login')
            self.end_headers()
            return

        if path == '/admin_logout':
            self.send_response(303)
            self.send_header('Set-Cookie', f'{ADMIN_PORTAL_COOKIE}=; Path=/; Max-Age=0; HttpOnly; SameSite=Lax')
            self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Sesión cerrada'))
            self.end_headers()
            return

        if path == '/admin_login':
            next_path = q.get('next', ['/admin'])[0] if 'next' in q else '/admin'
            self.send_response(303)
            self.send_header('Location', '/client_login?next=' + urllib.parse.quote(next_path))
            self.end_headers()
            return

        public_get_exact = {
            '/client_register', '/client_onboarding', '/client_login', '/client_app', '/client_logout',
            '/api/client_fasting_weight', '/api/client_daily_steps',
        }
        public_get_prefixes = ('/static/', '/export_diet_pdf', '/export_routine_pdf')
        is_public_get = path in public_get_exact or any(path.startswith(pref) for pref in public_get_prefixes)
        if not is_public_get and not self.is_admin_authenticated():
            next_path = path + (('?' + parsed.query) if parsed.query else '')
            self.redirect_admin_login(next_path)
            return

        if path == '/admin_security':
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            current_username = get_admin_portal_username()
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Seguridad administrador</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:700px;margin:0 auto;padding:28px;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:24px;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        h1{{margin:0 0 10px;font-size:2rem;}}
        p{{margin:0 0 18px;color:#6d7480;}}
        form{{display:grid;gap:12px;}}
        input{{padding:13px 14px;border:1px solid #d8dde6;border-radius:12px;font:inherit;}}
        button{{padding:12px 14px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;font:inherit;font-weight:700;}}
        .message{{padding:12px 14px;border-radius:12px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:14px;}}
        .helper{{margin-top:12px;font-size:.95rem;color:#6d7480;}}
        .helper a{{color:#101318;font-weight:700;text-decoration:none;}}
    </style>
</head>
<body>
    <div class="page">
        <div class="card">
            <h1>Seguridad de administrador</h1>
            <p>Modifica aquí tu usuario y contraseña para el panel maestro.</p>
            {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
            <form method="post" action="/admin_security">
                <input name="current_username" value="{html.escape(current_username)}" readonly />
                <input name="current_password" type="password" placeholder="Contraseña actual" required />
                <input name="new_username" value="{html.escape(current_username)}" placeholder="Nuevo usuario" required />
                <input name="new_password" type="password" placeholder="Nueva contraseña (mínimo 6)" />
                <input name="new_password_confirm" type="password" placeholder="Repite nueva contraseña" />
                <button type="submit">Guardar credenciales</button>
            </form>
            <div class="helper"><a href="/admin">← Volver al panel</a></div>
        </div>
    </div>
</body>
</html>
            '''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if path == '/client_logout':
            self.send_response(303)
            self.send_header('Set-Cookie', f'{CLIENT_PORTAL_COOKIE}=; Path=/; Max-Age=0; HttpOnly; SameSite=Lax')
            self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Sesión cerrada'))
            self.end_headers()
            return

        if path == '/client_register':
            diet_panel_html = f'''
            <section class="panel">
                <h2>🥗 Dietas</h2>
                <form method="post" action="/assign_client_diet" class="assign">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}&section=diet" />
                    <select name="diet_id" class="full" required>
                        <option value="">Selecciona una dieta</option>
                        {diet_options}
                    </select>
                    <input name="start_date" type="date" placeholder="Inicio" />
                    <input name="end_date" type="date" placeholder="Fin" />
                    <input name="notes" class="full" placeholder="Notas de asignación" />
                    <button type="submit" class="full">✨ Asignar dieta al cliente</button>
                </form>

                <div class="history-group">
                    <h3>Dietas activas</h3>
                    {active_diets_html}
                </div>
                <div class="history-group">
                    <h3>Dietas antiguas</h3>
                    {old_diets_html}
                </div>
            </section>
            '''

            training_panel_html = f'''
            <section class="panel">
                <h2>🏋️ Entrenamientos</h2>
                <form method="post" action="/assign_client_training" class="assign">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}&section=training" />
                    <select name="routine_id" class="full" required>
                        <option value="">Selecciona una rutina</option>
                        {routine_options}
                    </select>
                    <input name="start_date" type="date" placeholder="Inicio" />
                    <input name="end_date" type="date" placeholder="Fin" />
                    <input name="notes" class="full" placeholder="Notas de entrenamiento" />
                    <button type="submit" class="full">✨ Asignar rutina</button>
                </form>

                <div class="history-group">
                    <h3>Entrenamientos activos</h3>
                    {active_training_html}
                </div>
                <div class="history-group">
                    <h3>Entrenamientos antiguos</h3>
                    {old_training_html}
                </div>
            </section>
            '''

            weight_panel_html = f'''
            <section class="panel panel-full">
                <h2>⚖️ Peso corporal en ayunas</h2>
                {fasting_weights_html}
            </section>
            '''

            steps_panel_html = f'''
            <section class="panel panel-full">
                <h2>👟 Pasos diarios</h2>
                <form method="post" action="/set_client_steps_goal" class="steps-goal-form">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}&section=steps" />
                    <label>Objetivo diario de pasos
                        <input name="daily_steps_goal" type="number" min="0" step="1" value="{int(daily_steps_goal or 0) if int(daily_steps_goal or 0) > 0 else ''}" placeholder="Ej: 10000" />
                    </label>
                    <button type="submit">Guardar objetivo</button>
                </form>
                {daily_steps_html}
            </section>
            '''

            section_titles = {
                'diet': 'Dietas',
                'training': 'Entrenamientos',
                'weight': 'Peso corporal en ayunas',
                'steps': 'Pasos diarios',
            }
            section_descriptions = {
                'diet': 'Asigna dietas, revisa historial activo y antiguo.',
                'training': 'Asigna rutinas y consulta todo el histórico.',
                'weight': 'Registra y supervisa el peso en ayunas por día.',
                'steps': 'Define objetivo y controla pasos diarios.',
            }
            section_status = {
                'diet': 'Activa' if active_diets else 'Sin dieta activa',
                'training': 'Activa' if active_training else 'Sin entrenamiento activo',
                'weight': 'Seguimiento activo',
                'steps': f'Objetivo: {daily_steps_goal} pasos' if daily_steps_goal > 0 else 'Objetivo sin definir',
            }
            section_content = {
                'diet': diet_panel_html,
                'training': training_panel_html,
                'weight': weight_panel_html,
                'steps': steps_panel_html,
            }

            selected_section = (q.get('section', [''])[0] if 'section' in q else '').strip().lower()
            if selected_section not in section_content:
                selected_section = ''

            cards_html = ''.join([
                f'<a class="admin-home-card" href="/client_profile?id={cid_i}&section={key}">'
                f'<div class="chip">{html.escape(section_status[key])}</div>'
                f'<h3>{html.escape(section_titles[key])}</h3>'
                f'<p>{html.escape(section_descriptions[key])}</p>'
                '</a>'
                for key in ('diet', 'training', 'weight', 'steps')
            ])

            detail_html = ''
            if selected_section:
                detail_html = (
                    '<section class="detail-wrap">'
                    f'<a class="back-btn" href="/client_profile?id={cid_i}">← Volver al panel</a>'
                    '<details class="accordion" open>'
                    f'<summary>{html.escape(section_titles[selected_section])}</summary>'
                    f'<div class="accordion-body">{section_content[selected_section]}</div>'
                    '</details>'
                    '</section>'
                )

            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Registro cliente</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:560px;margin:0 auto;padding:28px;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:24px;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        h1{{margin:0 0 10px;font-size:2rem;}}
        p{{margin:0 0 18px;color:#6d7480;}}
        form{{display:grid;gap:12px;}}
        input{{padding:13px 14px;border:1px solid #d8dde6;border-radius:12px;font:inherit;}}
        button{{padding:12px 14px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;font:inherit;font-weight:700;}}
        .message{{padding:12px 14px;border-radius:12px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:14px;}}
        .helper{{margin-top:12px;font-size:.95rem;color:#6d7480;}}
        .helper a{{color:#101318;font-weight:700;text-decoration:none;}}
    </style>
</head>
<body>
    <div class="page">
        <div class="card">
            <h1>Crear cuenta cliente</h1>
            <p>Crea tu acceso con email y contraseña para entrar a tu app.</p>
            {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
            <form method="post" action="/client_register">
                <input name="email" type="email" placeholder="Tu correo" required />
                <input name="password" type="password" placeholder="Contraseña" minlength="6" required />
                <input name="password_confirm" type="password" placeholder="Repite contraseña" minlength="6" required />
                <button type="submit">Continuar</button>
            </form>
            <div class="helper">¿Ya tienes cuenta? <a href="/client_login">Iniciar sesión</a></div>
        </div>
    </div>
</body>
</html>
            '''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if path == '/client_onboarding':
            cookies = parse_cookie_header(self.headers.get('Cookie', ''))
            token = cookies.get(CLIENT_PORTAL_COOKIE, '')
            client_id = parse_client_portal_session_token(token)
            if client_id is None:
                self.send_response(303)
                self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Inicia sesión para completar tu perfil'))
                self.end_headers()
                return

            client_rows = [r for r in get_clients() if int(r[0]) == int(client_id)]
            if not client_rows:
                self.send_response(303)
                self.send_header('Location', '/client_register?msg=' + urllib.parse.quote('Primero crea tu cuenta'))
                self.end_headers()
                return

            c = client_rows[0]
            _cid, name, phone, email, birthdate, height_cm, weight_kg, objectives, _psd, _ped, _pa, _pn, _created = c
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Completar perfil</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:900px;margin:0 auto;padding:28px;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:24px;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        h1{{margin:0 0 8px;font-size:2rem;}}
        p{{margin:0 0 16px;color:#6d7480;}}
        form{{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));}}
        input,textarea{{padding:13px 14px;border:1px solid #d8dde6;border-radius:12px;font:inherit;}}
        textarea{{grid-column:1/-1;min-height:110px;resize:vertical;}}
        .full{{grid-column:1/-1;}}
        button{{padding:12px 14px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;font:inherit;font-weight:700;}}
        .message{{padding:12px 14px;border-radius:12px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:14px;}}
    </style>
</head>
<body>
    <div class="page">
        <div class="card">
            <h1>Completa tus datos</h1>
            <p>Estos datos crearán tu ficha automáticamente en el sistema del entrenador.</p>
            {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
            <form method="post" action="/client_onboarding">
                <label class="full">Nombre completo<input name="name" value="{html.escape(name or '')}" required /></label>
                <label>Teléfono<input name="phone" value="{html.escape(phone or '')}" /></label>
                <label>Email<input name="email" type="email" value="{html.escape(email or '')}" required /></label>
                <label>Fecha de nacimiento<input name="birthdate" type="date" value="{html.escape(birthdate or '')}" /></label>
                <label>Altura (cm)<input name="height_cm" type="number" min="0" step="0.1" value="{height_cm if height_cm else ''}" /></label>
                <label>Peso (kg)<input name="weight_kg" type="number" min="0" step="0.1" value="{weight_kg if weight_kg else ''}" /></label>
                <label class="full">Objetivos<textarea name="objectives">{html.escape(objectives or '')}</textarea></label>
                <div class="full"><button type="submit">Guardar y entrar</button></div>
            </form>
        </div>
    </div>
</body>
</html>
            '''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if path == '/client_login':
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            next_path = q.get('next', ['/client_app'])[0] if 'next' in q else '/client_app'
            if not next_path.startswith('/'):
                next_path = '/client_app'
            logo = logo_html()
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Acceso</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:560px;margin:0 auto;padding:28px;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:24px;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        h1{{margin:0 0 10px;font-size:2rem;}}
        p{{margin:0 0 18px;color:#6d7480;}}
        form{{display:grid;gap:12px;}}
        input{{padding:13px 14px;border:1px solid #d8dde6;border-radius:12px;font:inherit;}}
        button{{padding:12px 14px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;font:inherit;font-weight:700;}}
        .message{{padding:12px 14px;border-radius:12px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:14px;}}
        .helper{{margin-top:12px;font-size:.95rem;color:#6d7480;}}
        .helper a{{color:#101318;font-weight:700;text-decoration:none;}}
    </style>
</head>
<body>
    <div class="page">
        <div class="card">
            {logo}
            <h1>Acceso</h1>
            <p>Inicia sesión con tu cuenta de cliente o con tu cuenta de administrador.</p>
            {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
            <form method="post" action="/client_login">
                <input type="hidden" name="next" value="{html.escape(next_path)}" />
                <input name="identifier" placeholder="Usuario, email o teléfono" required />
                <input name="password" type="password" placeholder="Contraseña" />
                <input name="access_code" placeholder="Código de acceso cliente (opcional)" />
                <button type="submit">Entrar</button>
            </form>
            <div class="helper">¿Primera vez? <a href="/client_register">Crear cuenta</a></div>
        </div>
    </div>
</body>
</html>
            '''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if path == '/client_app':
            admin_preview = False
            requested_client_id = (q.get('client_id', [''])[0] if 'client_id' in q else '').strip()
            client_id = None
            if requested_client_id and self.is_admin_authenticated():
                try:
                    client_id = int(requested_client_id)
                    admin_preview = True
                except Exception:
                    client_id = None

            if client_id is None:
                cookies = parse_cookie_header(self.headers.get('Cookie', ''))
                token = cookies.get(CLIENT_PORTAL_COOKIE, '')
                client_id = parse_client_portal_session_token(token)
                if client_id is None:
                    self.send_response(303)
                    self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Inicia sesión para continuar'))
                    self.end_headers()
                    return

            client_rows = [r for r in get_clients() if int(r[0]) == int(client_id)]
            if not client_rows:
                if admin_preview:
                    self.send_response(303)
                    self.send_header('Location', '/clients?msg=' + urllib.parse.quote('Cliente no encontrado'))
                    self.end_headers()
                    return
                self.send_response(303)
                self.send_header('Set-Cookie', f'{CLIENT_PORTAL_COOKIE}=; Path=/; Max-Age=0; HttpOnly; SameSite=Lax')
                self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Cliente no encontrado'))
                self.end_headers()
                return

            c = client_rows[0]
            _cid, client_name, _phone, client_email, _birthdate, _height_cm, _weight_kg, _objectives, _psd, _ped, _pa, _pn, _created = c
            active_diet = get_active_client_diet(client_id)
            active_routine = get_active_client_routine(client_id)

            diet_html = '<p class="empty">No tienes dieta activa.</p>'
            if active_diet:
                _hid, diet_id, diet_name, client_diet_name, start_date, end_date, notes = active_diet
                diet_label = (client_diet_name or '').strip() or (diet_name or 'Dieta')
                diet_html = (
                    '<div class="info-block">'
                    f'<h3>{html.escape(diet_label)}</h3>'
                    f'<p><strong>Inicio:</strong> {html.escape(start_date or "-")}</p>'
                    f'<p><strong>Fin:</strong> {html.escape(end_date or "En curso")}</p>'
                    f'<p><strong>Notas:</strong> {html.escape(notes or "-")}</p>'
                    f'<a class="btn" href="/export_diet_pdf/dieta_{diet_id}.pdf?v={uuid.uuid4().hex}" target="_blank">Descargar PDF</a>'
                    '</div>'
                )

            routine_html = '<p class="empty">No tienes rutina activa.</p>'
            if active_routine:
                _thid, routine_id, routine_name, r_start, r_end, r_notes = active_routine
                routine_days = get_routine_days(routine_id)
                routine_items = get_routine_items(routine_id)
                day_name_by_index = {int(d[0]): d[1] for d in routine_days}
                grouped = {int(d[0]): [] for d in routine_days}
                for it in routine_items:
                    day_index = int(it[9]) if int(it[9]) >= 0 else 0
                    grouped.setdefault(day_index, []).append(it)
                day_blocks = []
                ordered_day_indexes = [int(d[0]) for d in routine_days] if routine_days else sorted(grouped.keys())
                for day_index in ordered_day_indexes:
                    day_name = day_name_by_index.get(day_index, f'Día {day_index + 1}')
                    items = grouped.get(day_index, [])
                    if not items:
                        day_blocks.append(f'<div class="day"><h4>{html.escape(day_name)}</h4><p class="empty">Sin ejercicios.</p></div>')
                        continue
                    rows = []
                    for item in items:
                        ex_name = item[4] or 'Ejercicio'
                        sets_text = item[5] or '-'
                        reps_text = item[6] or '-'
                        rows.append(
                            '<tr>'
                            f'<td>{html.escape(ex_name)}</td>'
                            f'<td>{html.escape(sets_text)}</td>'
                            f'<td>{html.escape(reps_text)}</td>'
                            '</tr>'
                        )
                    day_blocks.append(
                        f'<div class="day"><h4>{html.escape(day_name)}</h4>'
                        '<table><thead><tr><th>Ejercicio</th><th>Series</th><th>Reps</th></tr></thead>'
                        f'<tbody>{"".join(rows)}</tbody></table></div>'
                    )

                routine_html = (
                    '<div class="info-block">'
                    f'<h3>{html.escape(routine_name or "Rutina")}</h3>'
                    f'<p><strong>Inicio:</strong> {html.escape(r_start or "-")}</p>'
                    f'<p><strong>Fin:</strong> {html.escape(r_end or "En curso")}</p>'
                    f'<p><strong>Notas:</strong> {html.escape(r_notes or "-")}</p>'
                    f'<a class="btn" href="/export_routine_pdf/rutina_{routine_id}.pdf?v={uuid.uuid4().hex}" target="_blank">Descargar PDF</a>'
                    f'<div class="days">{"".join(day_blocks)}</div>'
                    '</div>'
                )

            fasting_weights_html = render_fasting_weights_panel(client_id, panel_id=f'fw-client-{client_id}', include_client_id=admin_preview)
            daily_steps_goal = get_client_daily_steps_goal(client_id)
            daily_steps_html = render_client_daily_steps_panel(
                client_id,
                panel_id=f'steps-client-{client_id}',
                include_client_id=admin_preview,
                daily_goal=daily_steps_goal,
            )
            selected_section = (q.get('section', [''])[0] if 'section' in q else '').strip().lower()
            if selected_section not in ('diet', 'routine', 'weight', 'steps'):
                selected_section = ''

            section_titles = {
                'diet': 'Mi dieta',
                'routine': 'Mi rutina',
                'weight': 'Mi peso corporal en ayunas',
                'steps': 'Mis pasos diarios',
            }
            section_descriptions = {
                'diet': 'Consulta tu plan actual y descarga tu PDF.',
                'routine': 'Revisa tus días de entrenamiento y ejercicios.',
                'weight': 'Registra tu peso diario y revisa la media semanal.',
                'steps': 'Anota tus pasos diarios y compáralos con tu objetivo.',
            }
            section_status = {
                'diet': 'Activa' if active_diet else 'Sin dieta activa',
                'routine': 'Activa' if active_routine else 'Sin rutina activa',
                'weight': 'Seguimiento activo',
                'steps': f'Objetivo: {daily_steps_goal} pasos' if daily_steps_goal > 0 else 'Objetivo sin definir',
            }

            section_content = {
                'diet': diet_html,
                'routine': routine_html,
                'weight': fasting_weights_html,
                'steps': daily_steps_html,
            }

            preview_qs = f'&client_id={client_id}' if admin_preview else ''
            cards_html = ''.join([
                f'<a class="client-home-card" href="/client_app?section={key}{preview_qs}">'
                f'<div class="chip">{html.escape(section_status[key])}</div>'
                f'<h3>{html.escape(section_titles[key])}</h3>'
                f'<p>{html.escape(section_descriptions[key])}</p>'
                '</a>'
                for key in ('diet', 'routine', 'weight', 'steps')
            ])

            detail_html = ''
            if selected_section:
                back_href = f'/client_app?client_id={client_id}' if admin_preview else '/client_app'
                detail_html = (
                    '<section class="detail-wrap">'
                    f'<a class="back-btn" href="{back_href}">← Volver al panel</a>'
                    '<details class="accordion" open>'
                    f'<summary>{html.escape(section_titles[selected_section])}</summary>'
                    f'<div class="accordion-body">{section_content[selected_section]}</div>'
                    '</details>'
                    '</section>'
                )

            top_action_html = '<a class="logout" href="/client_logout">Cerrar sesión</a>'
            if admin_preview:
                top_action_html = f'<a class="logout" href="/client_profile?id={client_id}">← Volver como admin</a>'

            welcome_subtitle = 'Selecciona un apartado para ver todo el detalle de tu progreso.'
            if admin_preview:
                welcome_subtitle = 'Vista previa como cliente desde admin. Puedes navegar y revisar cómo lo verá el cliente en móvil.'

            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Mi app</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:1040px;margin:0 auto;padding:22px;}}
        .top{{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;margin-bottom:18px;}}
        .top h1{{margin:0;font-size:2rem;}}
        .mail{{color:#6d7480;font-size:.95rem;}}
        .logout{{text-decoration:none;border:1px solid #d8dde6;border-radius:12px;padding:10px 12px;color:#101318;background:#fff;}}
        .welcome{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:20px;box-shadow:0 12px 30px rgba(16,19,24,.06);margin-bottom:14px;}}
        .welcome h2{{margin:0;font-size:1.35rem;}}
        .welcome p{{margin:8px 0 0;color:#6d7480;}}
        .cards{{display:grid;gap:12px;grid-template-columns:repeat(3,minmax(0,1fr));}}
        .client-home-card{{display:block;text-decoration:none;border:1px solid #d8dde6;background:#fff;border-radius:16px;padding:16px;box-shadow:0 10px 22px rgba(16,19,24,.06);transition:transform .14s ease, box-shadow .14s ease, border-color .14s ease;color:#101318;}}
        .client-home-card:hover{{transform:translateY(-2px);box-shadow:0 16px 30px rgba(16,19,24,.10);border-color:#c5ccd8;}}
        .client-home-card .chip{{display:inline-flex;padding:4px 10px;border-radius:999px;background:#eef2f7;color:#475569;font-size:.72rem;font-weight:800;}}
        .client-home-card h3{{margin:10px 0 6px;font-size:1.05rem;}}
        .client-home-card p{{margin:0;color:#6d7480;font-size:.92rem;line-height:1.35;}}
        .detail-wrap{{margin-top:14px;}}
        .back-btn{{display:inline-flex;align-items:center;gap:6px;text-decoration:none;border:1px solid #d8dde6;border-radius:10px;padding:8px 11px;background:#fff;color:#101318;font-weight:700;font-size:.88rem;margin-bottom:10px;}}
        .accordion{{border:1px solid #e8ebef;border-radius:16px;background:#fff;box-shadow:0 12px 30px rgba(16,19,24,.06);overflow:hidden;}}
        .accordion summary{{list-style:none;cursor:pointer;padding:14px 16px;font-weight:800;font-size:1.03rem;border-bottom:1px solid #eef2f7;}}
        .accordion summary::-webkit-details-marker{{display:none;}}
        .accordion-body{{padding:14px;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:18px;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        .card.full{{grid-column:1 / -1;}}
        .card h2{{margin:0 0 10px;}}
        .empty{{color:#6d7480;}}
        .info-block h3{{margin:0 0 8px;}}
        .info-block p{{margin:4px 0;}}
        .btn{{display:inline-flex;margin-top:8px;text-decoration:none;background:#101318;color:#fff;padding:9px 12px;border-radius:10px;}}
        .days{{display:grid;gap:10px;margin-top:12px;}}
        .day{{border:1px solid #e8ebef;border-radius:12px;padding:10px;background:#fbfcfd;}}
        .day h4{{margin:0 0 8px;}}
        table{{width:100%;border-collapse:collapse;background:#fff;border-radius:8px;overflow:hidden;}}
        th,td{{padding:8px 9px;border-bottom:1px solid #e8ebef;text-align:left;font-size:.9rem;}}
        th{{background:#f3f5f8;}}
        .fw-wrap{{border:1px solid #e8ebef;border-radius:14px;background:#fff;padding:8px;overflow:hidden;}}
        .fw-head{{font-size:.98rem;font-weight:800;color:#b91c1c;text-align:center;margin:1px 0 8px;}}
        .fw-grid{{display:grid;grid-template-columns:repeat(6,minmax(0,1fr));gap:6px;align-items:start;width:100%;min-width:0;}}
        .fw-month{{border:1px solid #d8dde6;border-radius:9px;background:#f8fafc;min-height:220px;min-width:0;overflow:hidden;}}
        .fw-month-title{{padding:5px 4px;border-bottom:1px solid #d8dde6;text-align:center;font-weight:800;color:#101318;font-size:.78rem;line-height:1.1;overflow-wrap:anywhere;}}
        .fw-month-days{{padding:5px;display:flex;flex-direction:column;gap:3px;max-height:none;overflow:visible;min-width:0;}}
        .fw-row{{display:grid;grid-template-columns:20px 58px;gap:4px;align-items:center;font-size:.74rem;color:#111827;min-width:0;justify-content:start;}}
        .fw-mean-row{{padding:2px 0 4px;}}
        .fw-mean-row span{{font-weight:800;color:#991b1b;}}
        .fw-mean-value{{color:#991b1b;font-weight:800;font-size:.74rem;line-height:1.15;}}
        .fw-mean-value em{{font-style:normal;font-weight:700;margin-left:3px;display:block;}}
        .fw-mean-value.down em{{color:#15803d;}}
        .fw-mean-value.up em{{color:#b91c1c;}}
        .fw-mean-value.neutral em{{color:#6d7480;}}
        .fw-input{{width:58px;max-width:58px;min-width:58px;padding:2px 4px;border:1px solid #d8dde6;border-radius:7px;background:#fff;font:inherit;font-size:.72rem;height:24px;}}
        .fw-steps-input{{width:58px;max-width:58px;min-width:58px;padding:2px 4px;border:1px solid #d8dde6;border-radius:7px;background:#fff;font:inherit;font-size:.72rem;height:24px;}}
        .fw-input.is-saving{{background:#fff7ed;border-color:#fdba74;}}
        .fw-steps-input.is-saving{{background:#fff7ed;border-color:#fdba74;}}
        .fw-input.is-saved{{background:#ecfdf5;border-color:#86efac;}}
        .fw-steps-input.is-saved{{background:#ecfdf5;border-color:#86efac;}}
        .fw-input.is-error{{background:#fef2f2;border-color:#fca5a5;}}
        .fw-steps-input.is-error{{background:#fef2f2;border-color:#fca5a5;}}
        .fw-steps-input.goal-met{{background:#ecfdf5;border-color:#86efac;color:#166534;font-weight:700;}}
        .fw-steps-input.goal-missed{{background:#fef2f2;border-color:#fca5a5;color:#991b1b;font-weight:700;}}
        .fw-foot{{margin-top:8px;color:#6d7480;font-size:.82rem;}}
        input, button, select, textarea{{font-size:16px;}}
        @media (max-width: 1280px){{ .fw-grid{{grid-template-columns:repeat(5,minmax(0,1fr));}} }}
        @media (max-width: 1100px){{ .fw-grid{{grid-template-columns:repeat(4,minmax(0,1fr));}} }}
        @media (max-width: 900px){{ .cards{{grid-template-columns:1fr;}} .fw-grid{{grid-template-columns:repeat(3,minmax(0,1fr));}} }}
        @media (max-width: 720px){{ .fw-grid{{grid-template-columns:repeat(2,minmax(0,1fr));}} }}
        @media (max-width: 640px){{
            .page{{padding:14px;}}
            .top{{align-items:flex-start;}}
            .top h1{{font-size:1.55rem;}}
            .welcome{{padding:16px;}}
            .welcome h2{{font-size:1.15rem;}}
            .card{{padding:14px;}}
            .accordion-body{{padding:10px;}}
            .btn{{width:100%;justify-content:center;}}
            .day table{{display:block;overflow-x:auto;white-space:nowrap;}}
            .fw-row{{grid-template-columns:24px minmax(0,1fr);}}
            .fw-input,.fw-steps-input{{width:100%;max-width:none;min-width:0;height:30px;padding:4px 6px;}}
        }}
        @media (max-width: 560px){{ .fw-grid{{grid-template-columns:1fr;}} }}
    </style>
</head>
<body>
    <div class="page">
        <div class="top">
            <div>
                <h1>Hola, {html.escape(client_name or 'Cliente')}</h1>
                <div class="mail">{html.escape(client_email or '')}</div>
            </div>
            {top_action_html}
        </div>
        <section class="welcome">
            <h2>Bienvenido/a a tu panel</h2>
            <p>{html.escape(welcome_subtitle)}</p>
        </section>
        <section class="cards">{cards_html}</section>
        {detail_html}
    </div>
</body>
</html>
            '''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # API endpoints
        m = re.match(r'^/api/foods/(\d+)$', path)
        if m:
            fid = int(m.group(1))
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "SELECT f.id, f.name, f.brand, f.category_id, c.name as category, f.calories, f.protein, f.carbs, f.fats, "
                "f.serving_size, COALESCE(f.photo_path, ''), COALESCE(f.nutrition_mode, 'per100'), COALESCE(f.per100_unit, 'g'), "
                "COALESCE(f.is_verified, 0), COALESCE(f.is_active, 1), f.has_gluten, COALESCE(f.barcode, ''), COALESCE(f.keywords, '') "
                "FROM foods f LEFT JOIN categories c ON f.category_id = c.id WHERE f.id = ?",
                (fid,),
            )
            row = cur.fetchone()
            conn.close()
            if not row:
                return self.send_json({'error': 'not found'}, status=404)
            keys = [
                'id', 'name', 'brand', 'category_id', 'category', 'calories', 'protein', 'carbs', 'fats',
                'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified', 'is_active',
                'has_gluten', 'barcode', 'keywords'
            ]
            return self.send_json(dict(zip(keys, row)))

        if path == '/api/foods':
            foods = get_foods()
            keys = ['id', 'name', 'brand', 'category', 'calories', 'protein', 'carbs', 'fats', 'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified', 'has_gluten']
            data = [dict(zip(keys, r)) for r in foods]
            return self.send_json(data)

        if path == '/api/exercises':
            exercises = get_exercises()
            keys = ['id', 'name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'category', 'video_url', 'machine_url', 'category_2']
            data = [dict(zip(keys, r)) for r in exercises]
            return self.send_json(data)

        if path == '/api/categories':
            cats = get_categories()
            data = [{'id': c[0], 'name': c[1]} for c in cats]
            return self.send_json(data)

        if path == '/api/brands':
            brands = get_brands()
            data = [{'id': b[0], 'name': b[1]} for b in brands]
            return self.send_json(data)

        if path == '/api/exercise_categories':
            cats = get_exercise_categories()
            data = [{'id': c[0], 'name': c[1]} for c in cats]
            return self.send_json(data)

        # UI: dashboard
        if path == '/admin':
            logo = logo_html()
            dash = '''
<!doctype html>
<html>
<head>
  <meta charset="utf-8"/>
  <title>Panel</title>
  <style>
        :root {--bg:#f6f7f9;--surface:#ffffff;--line:#e8ebef;--line-strong:#d8dde6;--text:#101318;--muted:#6d7480;--shadow:0 12px 30px rgba(16,19,24,.06);--shadow-hover:0 18px 38px rgba(16,19,24,.1);}
        body {font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif; margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:var(--text);}
    .page {max-width:900px;margin:0 auto;padding:28px;}
        .hero {padding:24px 30px 20px;background:var(--surface);border-radius:24px;box-shadow:var(--shadow);border:1px solid var(--line);}
    h1 {margin:0 0 8px;font-size:2.4rem;letter-spacing:-.03em;}
        p.sub {margin:0;color:var(--muted);font-size:1rem;}
    .grid {display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:18px;margin:28px 0;}
        .card {display:block;padding:22px 24px;background:var(--surface);border:1px solid var(--line);border-radius:18px;text-decoration:none;color:var(--text);transition:transform .18s ease,box-shadow .18s ease,border-color .18s ease;box-shadow:var(--shadow);}
        .card:hover {transform:translateY(-3px);box-shadow:var(--shadow-hover);border-color:var(--line-strong);}
    .card h2 {margin:0 0 10px;font-size:1.12rem;}
        .card p {margin:0;color:var(--muted);line-height:1.6;}
        .footer {margin-top:10px;color:var(--muted);font-size:.97rem;}
        .footer a {color:#101318;text-decoration:none;font-weight:700;}
  </style>
</head>
<body>
  <div class="page">
    <section class="hero">
      __LOGO_PLACEHOLDER__
    <h1>🧭 Panel</h1>
      <p class="sub">Accede rápido a tus bases de datos y a las APIs del sistema.</p>
            <p class="sub" style="margin-top:10px;"><a href="/admin_logout" style="color:#101318;font-weight:700;text-decoration:none;">Cerrar sesión</a></p>
    </section>

    <section class="grid">
      <a class="card" href="/foods">
        <h2>🍎 Base de datos de alimentos</h2>
        <p>Gestiona alimentos, marcas, categorías y datos nutricionales.</p>
      </a>
            <a class="card" href="/clients">
                <h2>👥 Panel de clientes</h2>
                <p>Consulta y organiza datos personales, objetivos y medidas de cada cliente.</p>
            </a>
            <a class="card" href="/payments">
                <h2>📆 Calendario de pagos</h2>
                <p>Registra cuándo empieza y termina cada plan, junto con su cuantía monetaria.</p>
            </a>
      <a class="card" href="/exercises">
        <h2>🏋️ Base de datos de ejercicios</h2>
                <p>Crea, edita y organiza ejercicios por grupo muscular y detalles.</p>
      </a>
      <a class="card" href="/diets">
        <h2>🥗 Creación de dietas</h2>
        <p>Define dietas y añade alimentos sincronizados desde la base de datos.</p>
      </a>
            <a class="card" href="/client_login">
                <h2>📲 App de cliente</h2>
                <p>Acceso del cliente para consultar dieta activa y rutina activa.</p>
            </a>
            <a class="card" href="/admin_security">
                <h2>🔐 Seguridad administrador</h2>
                <p>Cambia usuario y contraseña del panel maestro.</p>
            </a>
    </section>

    <div class="footer">
      <p><a href="/api/foods">API: /api/foods</a> | <a href="/api/exercises">API: /api/exercises</a></p>
    </div>
  </div>
</body>
</html>
'''
            dash = dash.replace('__LOGO_PLACEHOLDER__', logo)
            body = dash.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Diets page
        if path == '/diets':
            diets = get_diets()
            clients = get_clients()
            foods = []
            diet_id = q.get('diet_id', [''])[0]
            selected_diet = None
            diet_items = []
            if diet_id:
                try:
                    diet_id_i = int(diet_id)
                except Exception:
                    diet_id_i = None
                else:
                    selected_diet = next((d for d in diets if d[0] == diet_id_i), None)
                    if selected_diet:
                        foods = get_food_options()
                        diet_items = get_diet_items(diet_id_i)

            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            food_options = ''.join([
                f'<option value="{f[0]}">{html.escape(f[1])}' + (f' — {html.escape(f[2])}' if f[2] else '') + '</option>'
                for f in foods
            ])
            def format_date_dmy(value):
                text = str(value or '').strip()
                m = re.match(r'^(\d{4})-(\d{2})-(\d{2})', text)
                if m:
                    return f'{m.group(3)}/{m.group(2)}/{m.group(1)}'
                return text

            diet_rows_list = []
            client_options = ''.join([
                f'<option value="{c[0]}">{html.escape(c[1])}</option>'
                for c in clients
            ])
            for d in diets:
                created_dmy = format_date_dmy(d[3])
                diet_rows_list.append(
                    '<article class="diet-card">'
                    f'<div class="diet-card-head"><span class="diet-card-id">#{d[5]}</span><span class="diet-card-date">{html.escape(created_dmy)}</span></div>'
                    f'<h3 class="diet-card-name">{html.escape(d[1])}</h3>'
                    f'<p class="diet-card-desc">{html.escape(d[2] or "Sin descripción")}</p>'
                    f'<form method="post" action="/update_diet_display_number" class="diet-number-form">'
                    f'<input type="hidden" name="diet_id" value="{d[0]}" />'
                    f'<label>Número <input type="number" name="display_number" value="{d[5]}" min="1" step="1"></label>'
                    f'<button class="action-button" type="submit">Guardar</button></form>'
                    '<div class="diet-card-actions">'
                    f'<a class="action-button action-edit" href="/static/builder.html?diet_id={d[0]}">Abrir</a>'
                    f'<a class="action-button" href="/export_diet_pdf/dieta_{d[0]}.pdf?v={uuid.uuid4().hex}" target="_blank">PDF</a>'
                    f'<form method="post" action="/assign_client_diet" class="assign-inline">'
                    f'<input type="hidden" name="diet_id" value="{d[0]}" />'
                    f'<input type="hidden" name="return_to" value="/diets" />'
                    f'<select name="client_id" required><option value="">Cliente</option>{client_options}</select>'
                    f'<button class="action-button" type="submit">Asignar</button></form>'
                    f'<form method="post" action="/delete_diet" style="display:inline;margin:0">'
                    f'<input type="hidden" name="id" value="{d[0]}" />'
                    f'<button class="action-button action-delete" type="submit">Borrar</button></form>'
                    '</div>'
                    '</article>'
                )
            diet_rows = ''.join(diet_rows_list)
            selected_section = ''
            if selected_diet:
                days = ["Lunes", "Martes", "Miércoles", "Jueves", "Viernes", "Sábado", "Domingo"]
                meals = ["Desayuno", "Almuerzo", "Merienda", "Cena"]
                schedule = {meal: {day: [] for day in days} for meal in meals}
                other_items = []
                for item in diet_items:
                    label = html.escape(item[2])
                    if item[3]:
                        label += f' ({html.escape(item[3])})'
                    quantity_text = html.escape(diet_item_quantity_text(item))
                    if quantity_text:
                        label += f' — {quantity_text}'
                    if item[9]:
                        label += f' | {html.escape(item[9])}'
                    day = item[10] or ''
                    meal_time = item[11] or ''
                    if day in days and meal_time in meals:
                        schedule[meal_time][day].append(label)
                    else:
                        other_items.append((item, label))

                day_headers_html = ''.join([
                    f'<div class="diet-day-head">{day}</div>'
                    for day in days
                ])
                grid_rows = []
                for meal in meals:
                    grid_rows.append(f'<div class="diet-meal-head">{meal}</div>')
                    for day in days:
                        cell_items = schedule[meal][day]
                        if cell_items:
                            cards = ''.join([f'<div class="diet-food-card">{it}</div>' for it in cell_items])
                        else:
                            cards = '<div class="diet-empty">Sin alimentos</div>'
                        grid_rows.append(f'<div class="diet-cell">{cards}</div>')

                weekly_grid = (
                    '<div class="diet-grid-wrap">'
                    '<div class="diet-grid">'
                    '<div class="diet-corner">Comida / Día</div>'
                    f'{day_headers_html}'
                    f'{"".join(grid_rows)}'
                    '</div>'
                    '</div>'
                )
                other_section = ''
                if other_items:
                    other_rows = ''.join([
                        '<tr>' +
                        f'<td>{itm[0][0]}</td>' +
                        f'<td>{html.escape(itm[0][2])}</td>' +
                        f'<td>{html.escape(itm[0][3] or "")}</td>' +
                        f'<td>{itm[0][4]}</td>' +
                        f'<td>{itm[0][5]}</td>' +
                        f'<td>{itm[0][6]}</td>' +
                        f'<td>{itm[0][7]}</td>' +
                        f'<td>{html.escape(itm[0][8] or "")}</td>' +
                        f'<td>{html.escape(itm[0][9] or "")}</td>' +
                        f'<td>{html.escape(itm[0][10] or "")}</td>' +
                        f'<td>{html.escape(itm[0][11] or "")}</td>' +
                        f'<td><form method="post" action="/delete_diet_item" style="display:inline;margin:0">'
                        f'<input type="hidden" name="id" value="{itm[0][0]}" />'
                        f'<input type="hidden" name="diet_id" value="{selected_diet[0]}" />'
                        f'<button class="action-button action-delete" type="submit">Borrar</button></form></td>' +
                        '</tr>'
                        for itm in other_items
                    ])
                    other_section = f'''
      <h3>Elementos sin día/comida asignados</h3>
      <table>
        <thead><tr><th>ID</th><th>Alimento</th><th>Marca</th><th>Cal</th><th>Prot</th><th>Carbs</th><th>Fats</th><th>Cantidad</th><th>Nota</th><th>Día</th><th>Comida</th><th>Acciones</th></tr></thead>
        <tbody>
          {other_rows}
        </tbody>
      </table>
                    '''

                selected_section = f'''
    <section class="section-card">
      <h2>Detalles de dieta: {html.escape(selected_diet[1])}</h2>
      <p>{html.escape(selected_diet[2] or '')}</p>
            <p><strong>Peso cliente:</strong> {selected_diet[4] if selected_diet[4] else '-'} kg</p>
      <div style="margin-bottom:16px;display:flex;gap:12px;flex-wrap:wrap;">
                <a class="action-button action-edit" href="/export_diet_pdf/dieta_{selected_diet[0]}.pdf?v={uuid.uuid4().hex}" target="_blank">Exportar PDF</a>
      </div>
      <form method="post" action="/add_diet_item" style="display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));align-items:start;">
        <input type="hidden" name="diet_id" value="{selected_diet[0]}" />
        <select name="food_id" required>
          <option value="">-- Selecciona un alimento --</option>
          {food_options}
        </select>
        <select name="day_of_week" required>
          <option value="">-- Día de la semana --</option>
          {''.join([f'<option value="{d}">{d}</option>' for d in days])}
        </select>
        <select name="meal_time" required>
          <option value="">-- Tipo de comida --</option>
          {''.join([f'<option value="{m}">{m}</option>' for m in meals])}
        </select>
        <input name="quantity" placeholder="Cantidad (p.ej. 1 porción)" />
        <input name="note" placeholder="Notas adicionales" />
        <button type="submit">Añadir alimento</button>
      </form>
      <h3>Plan semanal</h3>
            {weekly_grid}
      {other_section}
    </section>
                '''
            page = f'''
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Dietas</title>
  <style>
        :root{{--bg:#f6f7f9;--surface:#ffffff;--surface-soft:#f3f5f8;--text:#101318;--muted:#6d7480;--line:#e8ebef;--line-strong:#d8dde6;--shadow:0 12px 30px rgba(16,19,24,.06);--shadow-hover:0 18px 38px rgba(16,19,24,.10);}}
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:var(--text);}}
    .page{{max-width:1100px;margin:0 auto;padding:28px;}}
    h1{{margin:0 0 12px;font-size:2.2rem;letter-spacing:-.03em;}}
        h2{{margin:28px 0 12px;font-size:1.2rem;color:var(--muted);}}
        .section-card{{background:var(--surface);border:1px solid var(--line);border-radius:18px;padding:22px;box-shadow:var(--shadow);color:var(--text);}}
                .search-shell{{position:sticky;top:12px;z-index:25;background:var(--surface);border:1px solid var(--line);border-radius:18px;padding:16px;box-shadow:var(--shadow);margin-bottom:18px;}}
        .search-main{{display:grid;grid-template-columns:1fr;gap:10px;}}
                .search-main input{{padding:15px 16px;border:1px solid var(--line-strong);border-radius:14px;background:#fff;color:var(--text);font-size:1.02rem;}}
        .search-filters{{display:grid;gap:10px;grid-template-columns:repeat(5,minmax(120px,1fr));}}
                .search-filters select,.search-filters input{{padding:11px 12px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;color:var(--text);}}
                .search-results{{margin-top:10px;border:1px solid var(--line);border-radius:14px;background:#fff;max-height:420px;overflow:auto;}}
                .search-empty{{padding:14px 16px;color:var(--muted);}}
                .search-item{{display:grid;grid-template-columns:1fr auto;gap:10px;padding:12px 14px;border-bottom:1px solid var(--line);text-decoration:none;color:var(--text);}}
        .search-item:last-child{{border-bottom:none;}}
                .search-item:hover{{background:#f5f7fa;}}
        .search-name{{font-weight:800;}}
                .search-meta{{display:flex;gap:8px;flex-wrap:wrap;margin-top:5px;font-size:.86rem;color:var(--muted);}}
                .search-chip{{display:inline-flex;align-items:center;padding:.2rem .55rem;border-radius:999px;background:#eef2f7;}}
                .search-kcal{{font-weight:800;color:#101318;}}
        .add-food-compact{{padding:12px 14px;}}
                .add-food-accordion{{border:1px solid var(--line);border-radius:14px;background:#fff;overflow:hidden;}}
                .add-food-accordion summary{{list-style:none;cursor:pointer;display:flex;align-items:center;justify-content:space-between;gap:12px;padding:12px 14px;background:var(--surface-soft);color:var(--text);font-weight:800;}}
        .add-food-accordion summary::-webkit-details-marker{{display:none;}}
                .add-food-summary-hint{{font-size:.88rem;font-weight:600;color:var(--muted);}}
                .add-food-content{{padding:14px;border-top:1px solid var(--line);}}
        @media (max-width: 900px){{
            .search-filters{{grid-template-columns:repeat(2,minmax(140px,1fr));}}
        }}
    form{{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));align-items:start;}}
    input, select, button{{font:inherit;outline:none;}}
    input, select{{padding:12px 14px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;color:var(--text);}}
    select{{appearance:none;}}
    button{{padding:13px 18px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
    button:hover{{background:#232933;transform:translateY(-1px);}}
    .message{{padding:14px 16px;border-radius:14px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:20px;}}
    .diet-cards{{display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:12px;margin-top:10px;}}
    .diet-card{{background:#fff;border:1px solid var(--line);border-radius:14px;padding:12px;box-shadow:var(--shadow);display:flex;flex-direction:column;min-height:150px;}}
    .diet-card-head{{display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:6px;}}
    .diet-card-id{{font-size:.74rem;font-weight:800;color:#101318;background:#eef2f7;border-radius:999px;padding:2px 8px;}}
    .diet-card-date{{font-size:.76rem;color:var(--muted);font-weight:700;}}
    .diet-card-name{{margin:0 0 6px;font-size:1rem;line-height:1.2;color:var(--text);}}
    .diet-card-desc{{margin:0;color:var(--muted);font-size:.83rem;line-height:1.3;min-height:2.4em;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;}}
    .diet-number-form{{display:flex;gap:6px;align-items:center;flex-wrap:wrap;margin:8px 0 10px;}}
    .diet-number-form label{{display:flex;gap:6px;align-items:center;font-size:.78rem;color:var(--muted);font-weight:700;}}
    .diet-number-form input{{padding:6px 8px;border-radius:10px;font-size:.82rem;max-width:84px;}}
    .diet-number-form .action-button{{padding:6px 10px;font-size:.8rem;border-radius:10px;}}
    .diet-card-actions{{margin-top:auto;display:flex;gap:6px;flex-wrap:wrap;}}
    .diet-card-actions .action-button{{padding:6px 10px;font-size:.82rem;border-radius:10px;}}
    .assign-inline{{display:flex;gap:6px;align-items:center;flex-wrap:wrap;margin:0;}}
    .assign-inline select{{padding:6px 8px;border-radius:10px;font-size:.8rem;max-width:140px;}}
    table{{width:100%;border-collapse:collapse;margin-top:16px;background:#fff;border-radius:16px;overflow:hidden;box-shadow:var(--shadow);color:var(--text);}}
    tbody td{{color:#23160f !important;font-weight:600;}}
    th,td{{padding:14px 16px;text-align:left;border-bottom:1px solid var(--line);}}
    th{{background:var(--surface-soft);font-weight:700;color:var(--text);border-bottom:1px solid var(--line);}}
    tr:hover{{background:#f8fafc;}}
    .action-button{{display:inline-flex;align-items:center;justify-content:center;padding:8px 12px;border-radius:12px;border:1px solid var(--line-strong);background:#fff;color:var(--text);text-decoration:none;font-weight:600;font-size:.95rem;cursor:pointer;transition:transform .18s ease,background .18s ease,border-color .18s ease;}}
    .action-button:hover{{background:#f5f7fa;transform:translateY(-1px);border-color:var(--line-strong);}}
    .action-edit{{border:none;background:#101318;color:#fff;}}
    .action-edit:hover{{background:#232933;}}
    .action-delete{{border:none;background:#8b1b20;color:#fff;}}
    .action-delete:hover{{background:#6f1116;}}
    .day-card{{display:flex;flex-direction:column;gap:12px;}}
    .day-header-row{{display:flex;align-items:center;gap:10px;justify-content:space-between;flex-wrap:wrap;}}
    .day-status-pill{{display:inline-flex;align-items:center;justify-content:center;padding:4px 10px;border-radius:999px;font-size:.78rem;font-weight:800;letter-spacing:.02em;}}
    .day-status-pill.train{{background:#e8f7ed;color:#166534;border:1px solid #b7e3c3;}}
    .day-status-pill.rest{{background:#fef3e8;color:#9a3412;border:1px solid #f8d9bf;}}
    .day-tools{{display:flex;align-items:center;gap:8px;flex-wrap:wrap;}}
    .day-tools form{{display:inline-flex !important;grid-template-columns:none !important;align-items:center;gap:8px;margin:0 !important;width:auto !important;}}
    .day-tools form button{{display:inline-flex !important;align-items:center;justify-content:center;width:auto !important;min-width:0 !important;white-space:nowrap;box-shadow:none;}}
    .day-meta-form input{{min-width:180px;max-width:260px;}}
    .rest-label{{font-size:.86rem;font-weight:700;color:#9a3412;background:#fef3e8;border:1px solid #f8d9bf;padding:8px 10px;border-radius:10px;}}
    .exercise-modal{{position:fixed;inset:0;z-index:999;display:flex;align-items:center;justify-content:center;padding:18px;}}
    .exercise-modal[hidden]{{display:none;}}
    .exercise-modal-backdrop{{position:absolute;inset:0;background:rgba(15,23,42,.42);}}
    .exercise-modal-card{{position:relative;background:#fff;border:1px solid #d8dde6;border-radius:16px;box-shadow:0 18px 40px rgba(16,19,24,.22);max-width:540px;width:100%;padding:16px;}}
    .exercise-modal-card h3{{margin:0 0 12px;font-size:1.05rem;color:#101318;}}
    .exercise-modal-form{{display:grid;gap:10px;grid-template-columns:1fr;}}
    .exercise-modal-form input,.exercise-modal-form select{{padding:12px 14px;border:1px solid #d8dde6;border-radius:12px;background:#fff;color:#101318;}}
    .modal-actions{{display:flex;justify-content:flex-end;gap:8px;margin-top:4px;}}
    .modal-actions button{{padding:11px 14px;border-radius:12px;}}
        .diet-grid-wrap{{overflow-x:auto;border:1px solid var(--line);border-radius:14px;background:#fff;box-shadow:var(--shadow);}}
        .diet-grid{{display:grid;grid-template-columns:180px repeat(7,minmax(170px,1fr));min-width:1300px;width:100%;}}
        .diet-corner{{background:#eef2f7;font-weight:800;color:#475569;font-size:.78rem;letter-spacing:.02em;padding:12px;border-right:1px solid var(--line);border-bottom:1px solid var(--line);}}
        .diet-day-head{{background:var(--surface-soft);color:var(--text);font-weight:800;font-size:.8rem;padding:12px;border-right:1px solid var(--line);border-bottom:1px solid var(--line);}}
        .diet-meal-head{{background:#f7f8fa;color:var(--text);font-weight:700;padding:12px;border-right:1px solid var(--line);border-bottom:1px solid var(--line);}}
        .diet-cell{{background:#fff;padding:10px;min-height:90px;border-right:1px solid var(--line);border-bottom:1px solid var(--line);display:flex;flex-direction:column;gap:8px;}}
        .diet-food-card{{background:#fff;border:1px solid var(--line-strong);border-radius:10px;padding:8px 10px;font-size:.85rem;line-height:1.35;color:var(--text);}}
        .diet-empty{{font-size:.8rem;color:var(--muted);font-style:italic;}}
  </style>
</head>
<body>
  <div class="page">
    {home_link()}
    <h1>🥗 Dietas</h1>
    {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
    <section class="section-card">
    <h2>✨ Crear nueva dieta</h2>
      <form method="post" action="/add_diet">
        <input name="name" placeholder="Nombre de la dieta" required />
        <input name="description" placeholder="Descripción" />
        <button type="submit">Crear dieta</button>
      </form>
    </section>
    <section class="section-card">
    <h2>📚 Dietas existentes</h2>
            <div class="diet-cards">
                    {diet_rows if diet_rows else '<p style="color:#6b4b2a;">No hay dietas creadas todavía.</p>'}
            </div>
    </section>
    {selected_section}
  </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Clients page
        if path == '/clients':
            clients = get_clients()
            clients = sorted(clients, key=lambda c: (str(c[1] or '').casefold(), c[0]))
            active_routine_by_client = get_active_client_routines_map([c[0] for c in clients]) if clients else {}
            active_diet_by_client = get_active_client_diets_map([c[0] for c in clients]) if clients else {}
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            client_cards = []
            from datetime import date, datetime
            for c in clients:
                client_id, name, phone, email, birthdate, height_cm, weight_kg, objectives, plan_start_date, plan_end_date, plan_amount, plan_notes, created_at = c
                service_status = payment_plan_status(plan_start_date, plan_end_date)
                is_active = service_status == 'Activo'

                days_remaining = '-'
                try:
                    if plan_end_date:
                        end_dt = datetime.strptime(str(plan_end_date), "%Y-%m-%d").date()
                        days_left = (end_dt - date.today()).days
                        if days_left >= 0:
                            days_remaining = f"{days_left} días"
                        else:
                            days_remaining = 'Finalizado'
                except Exception:
                    days_remaining = '-'

                if plan_amount and plan_amount > 0:
                    monthly_fee = f"{plan_amount:.2f} €"
                else:
                    monthly_fee = '-'

                plan_label = (plan_notes or '').strip() or ('Plan activo' if plan_start_date or plan_end_date else 'Sin plan')
                objective = (objectives or '').strip() or 'Sin objetivo'
                phone_value = (phone or '').strip()
                email_value = (email or '').strip()
                phone_link = re.sub(r'[^0-9+]', '', phone_value)
                contact_button = (
                    f'<a class="card-btn" href="tel:{html.escape(phone_link)}">Contactar</a>'
                    if phone_link else '<button class="card-btn is-disabled" type="button" disabled>Contactar</button>'
                )
                routine_button = ''
                active_routine = active_routine_by_client.get(int(client_id))
                if active_routine:
                    routine_id, _routine_name = active_routine
                    routine_button = f'<a class="card-btn" href="/routines?routine_id={routine_id}">Editar rutina</a>'

                active_diet = active_diet_by_client.get(int(client_id))
                active_diet_editor = '<div class="diet-start-inline muted">Sin dieta activa</div>'
                if active_diet:
                    active_diet_editor = (
                        '<form method="post" action="/update_client_diet_dates" class="diet-start-inline">'
                        f'<input type="hidden" name="history_id" value="{active_diet["history_id"]}" />'
                        f'<input type="hidden" name="client_id" value="{client_id}" />'
                        '<input type="hidden" name="return_to" value="/clients" />'
                        f'<label>Inicio dieta activa: <input type="date" name="start_date" value="{html.escape(active_diet["start_date"])}" /></label>'
                        '<button class="card-btn" type="submit">Guardar inicio</button>'
                        '</form>'
                    )

                status_class = 'status-active' if is_active else 'status-inactive'
                search_blob = ' '.join([
                    str(name or ''), str(phone_value), str(email_value), str(service_status), str(plan_label),
                    str(monthly_fee), str(objective), str(plan_start_date or ''), str(plan_end_date or '')
                ]).lower().strip()

                client_cards.append(
                    f'<article class="client-card" data-active="{"1" if is_active else "0"}" '
                    f'data-has-plan="{"1" if (plan_start_date or plan_end_date) else "0"}" '
                    f'data-search="{html.escape(search_blob)}">'
                    f'<div class="card-head"><h3>{html.escape(name)}</h3><span class="service-status {status_class}">{html.escape(service_status)}</span></div>'
                    f'<div class="card-grid">'
                    f'<div class="kv kv-email"><span>Email</span><strong>{html.escape(email_value or "-")}</strong></div>'
                    f'<div class="kv kv-phone"><span>Teléfono</span><strong>{html.escape(phone_value or "-")}</strong></div>'
                    f'<div class="kv"><span>Inicio</span><strong>{html.escape(plan_start_date or "-")}</strong></div>'
                    f'<div class="kv"><span>Fin</span><strong>{html.escape(plan_end_date or "-")}</strong></div>'
                    f'<div class="kv"><span>Días restantes</span><strong>{html.escape(days_remaining)}</strong></div>'
                    f'<div class="kv"><span>Plan</span><strong>{html.escape(plan_label)}</strong></div>'
                    f'<div class="kv"><span>Mensualidad</span><strong>{html.escape(monthly_fee)}</strong></div>'
                    f'<div class="kv"><span>Objetivo</span><strong>{html.escape(objective)}</strong></div>'
                    f'</div>'
                    f'<div class="card-actions">'
                    f'<a class="card-btn" href="/client_profile?id={client_id}">Ver perfil</a>'
                    f'{routine_button}'
                    f'{contact_button}'
                    f'<a class="card-btn" href="/edit_client?id={client_id}">Editar</a>'
                    f'<button class="card-btn" type="button" onclick="clientAction(\'Bloquear\', \'{html.escape(name)}\')">Bloquear</button>'
                    f'<button class="card-btn" type="button" onclick="clientAction(\'Desactivar\', \'{html.escape(name)}\')">Desactivar</button>'
                    f'<form method="post" action="/delete_client" onsubmit="return confirm(\'¿Seguro que quieres eliminar este cliente?\')">'
                    f'<input type="hidden" name="id" value="{client_id}" />'
                    f'<button class="card-btn danger" type="submit">Eliminar</button></form>'
                    f'</div>'
                    f'{active_diet_editor}'
                    f'</article>'
                )

            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Clientes</title>
    <style>
        :root{{
            --bg:#f6f7f9;
            --surface:#ffffff;
            --surface-soft:#f3f5f8;
            --ink:#101318;
            --muted:#6d7480;
            --line:#e8ebef;
            --line-strong:#d8dde6;
            --brand:#101318;
            --brand-2:#1f2733;
            --shadow:0 12px 30px rgba(16,19,24,.06);
            --shadow-hover:0 18px 38px rgba(16,19,24,.10);
        }}
        *{{box-sizing:border-box;}}
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, var(--bg) 60%, #f3f4f6 100%);color:var(--ink);}}
        .page{{max-width:1260px;margin:0 auto;padding:30px 28px 36px;}}
        .topbar{{display:flex;align-items:center;justify-content:space-between;gap:16px;margin:4px 0 18px;}}
        h1{{margin:0;font-size:2rem;letter-spacing:-.02em;}}
        .primary-btn{{display:inline-flex;align-items:center;justify-content:center;padding:11px 16px;border-radius:12px;border:1px solid var(--line-strong);background:linear-gradient(180deg,var(--brand-2),var(--brand));color:#fff;text-decoration:none;font-weight:700;box-shadow:0 10px 22px rgba(16,19,24,.16);}}
        .primary-btn:hover{{filter:brightness(.96);}}
        .message{{padding:12px 14px;border-radius:12px;background:#fef4ea;border:1px solid #f5dcc0;color:#4d3217;margin-bottom:14px;}}
        .tabs{{display:grid;grid-template-columns:repeat(2,minmax(220px,1fr));gap:14px;margin-bottom:14px;}}
        .tab-btn{{padding:20px 18px;border-radius:14px;border:1px solid var(--line);background:#fff;cursor:pointer;text-align:left;transition:all .18s ease;color:var(--ink);box-shadow:var(--shadow);}}
        .tab-btn strong{{display:block;font-size:1.06rem;margin-bottom:4px;}}
        .tab-btn span{{color:var(--muted);font-size:.92rem;}}
        .tab-btn.is-active{{border-color:var(--line-strong);box-shadow:var(--shadow-hover);background:var(--surface-soft);}}
        .search-wrap{{display:grid;grid-template-columns:1fr auto;gap:10px;align-items:center;margin:10px 0 18px;}}
        .search-bar{{display:flex;align-items:center;border:1px solid var(--line-strong);border-radius:12px;background:#fff;padding:0 12px;}}
        .search-bar input{{width:100%;padding:12px 4px;border:none;outline:none;font:inherit;background:transparent;color:var(--ink);}}
        .filter-btn{{padding:11px 14px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;cursor:pointer;font-weight:700;color:var(--ink);}}
        .filter-panel{{display:none;margin:-2px 0 16px;padding:12px;border:1px solid var(--line);border-radius:12px;background:#fff;}}
        .filter-panel.is-open{{display:block;}}
        .filter-grid{{display:grid;grid-template-columns:repeat(2,minmax(180px,1fr));gap:10px;}}
        .filter-grid label{{display:flex;flex-direction:column;gap:6px;font-size:.85rem;color:var(--muted);font-weight:700;}}
        .filter-grid select{{padding:10px 12px;border:1px solid var(--line-strong);border-radius:10px;background:#fff;font:inherit;color:var(--ink);}}
        .clients-grid{{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:10px;}}
        .client-card{{background:#fff;border:1px solid var(--line);border-radius:12px;padding:10px;box-shadow:var(--shadow);}}
        .card-head{{display:flex;justify-content:space-between;align-items:flex-start;gap:8px;margin-bottom:9px;}}
        .card-head h3{{margin:0;font-size:.98rem;line-height:1.2;}}
        .service-status{{padding:3px 7px;border-radius:999px;font-size:.66rem;font-weight:800;letter-spacing:.02em;}}
        .status-active{{background:#eaf8ef;color:#1f7a40;}}
        .status-inactive{{background:#eef2f7;color:#4a5568;}}
        .card-grid{{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:7px 10px;margin-bottom:9px;}}
        .kv{{min-width:0;}}
        .kv span{{display:block;font-size:.63rem;color:var(--muted);font-weight:700;text-transform:uppercase;letter-spacing:.03em;}}
        .kv strong{{display:block;margin-top:2px;font-size:.82rem;line-height:1.2;}}
        .kv-email{{grid-column:1 / -1;}}
        .kv-email strong{{overflow-wrap:anywhere;word-break:break-word;white-space:normal;}}
        .kv-phone strong{{overflow-wrap:anywhere;}}
        .card-actions{{display:flex;gap:6px;flex-wrap:wrap;border-top:1px solid var(--line);padding-top:8px;}}
        .card-actions form{{margin:0;}}
        .card-btn{{display:inline-flex;align-items:center;justify-content:center;height:28px;padding:0 8px;border-radius:8px;border:1px solid var(--line-strong);background:#fff;color:var(--ink);text-decoration:none;font-size:.72rem;font-weight:700;cursor:pointer;}}
        .card-btn:hover{{background:#f5f7fa;}}
        .card-btn.danger{{border-color:#efcfd2;color:#8b1b20;background:#fff4f4;}}
        .card-btn.danger:hover{{background:#fee2e2;}}
        .card-btn.is-disabled{{opacity:.45;cursor:not-allowed;pointer-events:none;}}
        .diet-start-inline{{margin-top:8px;padding-top:8px;border-top:1px dashed var(--line-strong);display:flex;gap:8px;align-items:center;flex-wrap:wrap;}}
        .diet-start-inline label{{font-size:.75rem;color:var(--muted);font-weight:700;display:flex;align-items:center;gap:6px;}}
        .diet-start-inline input{{font:inherit;padding:6px 8px;border:1px solid var(--line-strong);border-radius:8px;background:#fff;color:var(--ink);}}
        .diet-start-inline.muted{{font-size:.75rem;color:var(--muted);font-style:italic;}}
        .empty-state{{display:none;padding:22px;border:1px dashed var(--line-strong);border-radius:12px;background:#fff;color:var(--muted);font-weight:700;text-align:center;}}
        .empty-state.show{{display:block;}}
        .is-hidden{{display:none !important;}}
        @media (max-width: 980px){{
            .clients-grid{{grid-template-columns:repeat(3,minmax(0,1fr));}}
        }}
        @media (max-width: 760px){{
            .clients-grid{{grid-template-columns:repeat(2,minmax(0,1fr));}}
        }}
        @media (max-width: 560px){{
            .clients-grid{{grid-template-columns:1fr;}}
            .tabs{{grid-template-columns:1fr;}}
            .search-wrap{{grid-template-columns:1fr;}}
            .filter-grid{{grid-template-columns:1fr;}}
        }}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        <div class="topbar">
            <h1>👥 Clientes</h1>
            <a class="primary-btn" href="/new_client">➕ Nuevo cliente</a>
        </div>
        {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
        <div class="tabs">
            <button class="tab-btn is-active" type="button" data-tab="active">
                <strong>🟢 Clientes activos</strong>
                <span>Servicio activo actualmente</span>
            </button>
            <button class="tab-btn" type="button" data-tab="inactive">
                <strong>⚪ Clientes no activos</strong>
                <span>Finalizados, próximos o sin plan</span>
            </button>
        </div>

        <div class="search-wrap">
            <div class="search-bar">
                <input id="clients-search" type="text" placeholder="Buscar por nombre, teléfono, plan u objetivo" />
            </div>
            <button id="toggle-filters" class="filter-btn" type="button">🎛️ Filtros</button>
        </div>

        <div id="filter-panel" class="filter-panel">
            <div class="filter-grid">
                <label>Estado del plan
                    <select id="filter-plan">
                        <option value="all">Todos</option>
                        <option value="with">Con plan</option>
                        <option value="without">Sin plan</option>
                    </select>
                </label>
                <label>Mensualidad
                    <select id="filter-fee">
                        <option value="all">Todas</option>
                        <option value="paid">Con mensualidad</option>
                        <option value="free">Sin mensualidad</option>
                    </select>
                </label>
            </div>
        </div>

        <div id="clients-grid" class="clients-grid">
            {''.join(client_cards) if client_cards else '<div class="empty-state show">No hay clientes registrados todavía.</div>'}
        </div>
        <div id="empty-state" class="empty-state">No hay clientes para los filtros seleccionados.</div>
    </div>
    <script>
        (() => {{
            const tabs = Array.from(document.querySelectorAll('[data-tab]'));
            const cards = Array.from(document.querySelectorAll('.client-card'));
            const searchInput = document.getElementById('clients-search');
            const toggleFilters = document.getElementById('toggle-filters');
            const filterPanel = document.getElementById('filter-panel');
            const filterPlan = document.getElementById('filter-plan');
            const filterFee = document.getElementById('filter-fee');
            const emptyState = document.getElementById('empty-state');

            let currentTab = 'active';

            const clientAction = (action, clientName) => {{
                alert(action + ' para ' + clientName + ' estará disponible en la siguiente versión.');
            }};
            window.clientAction = clientAction;

            const hasFee = (text) => {{
                return /\d/.test(text || '');
            }};

            const applyFilters = () => {{
                const query = (searchInput.value || '').toLowerCase().trim();
                const planMode = filterPlan.value;
                const feeMode = filterFee.value;
                let visible = 0;

                cards.forEach((card) => {{
                    const cardTab = card.dataset.active === '1' ? 'active' : 'inactive';
                    const searchBlob = card.dataset.search || '';
                    const planFlag = card.dataset.hasPlan || '0';
                    const feeText = card.querySelector('.kv:nth-child(7) strong')?.textContent || '';

                    const matchesTab = cardTab === currentTab;
                    const matchesQuery = !query || searchBlob.includes(query);
                    const matchesPlan = (
                        planMode === 'all' ||
                        (planMode === 'with' && planFlag === '1') ||
                        (planMode === 'without' && planFlag === '0')
                    );
                    const matchesFee = (
                        feeMode === 'all' ||
                        (feeMode === 'paid' && hasFee(feeText)) ||
                        (feeMode === 'free' && !hasFee(feeText))
                    );

                    const show = matchesTab && matchesQuery && matchesPlan && matchesFee;
                    card.classList.toggle('is-hidden', !show);
                    if (show) visible += 1;
                }});

                emptyState.classList.toggle('show', visible === 0 && cards.length > 0);
            }};

            tabs.forEach((tab) => {{
                tab.addEventListener('click', () => {{
                    currentTab = tab.dataset.tab;
                    tabs.forEach((other) => other.classList.toggle('is-active', other === tab));
                    applyFilters();
                }});
            }});

            searchInput.addEventListener('input', applyFilters);
            filterPlan.addEventListener('change', applyFilters);
            filterFee.addEventListener('change', applyFilters);
            toggleFilters.addEventListener('click', () => {{
                filterPanel.classList.toggle('is-open');
            }});

            applyFilters();
        }})();
    </script>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # New client page
        if path == '/new_client':
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Nuevo cliente</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:900px;margin:0 auto;padding:28px;}}
        h1{{margin:0 0 16px;font-size:2.1rem;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:26px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
        form{{display:grid;gap:16px;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));}}
        label{{display:flex;flex-direction:column;font-weight:600;color:#6d7480;gap:8px;}}
        input, textarea, button{{font:inherit;outline:none;}}
        input, textarea{{padding:14px 16px;border:1px solid #d8dde6;border-radius:14px;background:#fff;color:#101318;}}
        textarea{{min-height:130px;resize:vertical;grid-column:1 / -1;}}
        .full{{grid-column:1 / -1;}}
        button{{padding:13px 18px;border:none;border-radius:14px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
        button:hover{{background:#232933;transform:translateY(-1px);}}
        .actions{{display:flex;gap:14px;align-items:center;flex-wrap:wrap;}}
        .secondary-link{{color:#101318;text-decoration:none;font-weight:700;}}
        .message{{padding:14px 16px;border-radius:14px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:20px;}}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
        <div class="card">
            <h1>Nuevo cliente</h1>
            <form method="post" action="/add_client">
                <label>Nombre<input name="name" placeholder="Nombre del cliente" required /></label>
                <label>Teléfono<input name="phone" placeholder="Número de teléfono" /></label>
                <label>Email<input name="email" type="email" placeholder="cliente@email.com" /></label>
                <label>Código acceso app<input name="client_access_code" placeholder="Ej: 1234" /></label>
                <label>Fecha de nacimiento<input name="birthdate" type="date" /></label>
                <label>Altura (cm)<input name="height_cm" type="number" min="0" step="0.1" placeholder="184" /></label>
                <label>Peso (kg)<input name="weight_kg" type="number" min="0" step="0.1" placeholder="80" /></label>
                <label>Inicio del plan<input name="plan_start_date" type="date" /></label>
                <label>Fin del plan<input name="plan_end_date" type="date" /></label>
                <label>Importe del plan<input name="plan_amount" type="number" min="0" step="0.01" placeholder="100" /></label>
                <label class="full">Notas del plan<input name="plan_notes" placeholder="Observaciones del plan" /></label>
                <label class="full">Objetivos<textarea name="objectives" placeholder="Objetivos del cliente"></textarea></label>
                <div class="actions full">
                    <button type="submit">Crear cliente</button>
                    <a class="secondary-link" href="/clients">Volver</a>
                </div>
            </form>
        </div>
    </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Client edit page
        if path == '/edit_client':
            cid = q.get('id', [''])[0]
            try:
                cid_i = int(cid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            rows = [r for r in get_clients() if r[0] == cid_i]
            if not rows:
                self.send_response(404)
                self.end_headers()
                return
            c = rows[0]
            _, name, phone, email, birthdate, height_cm, weight_kg, objectives, plan_start_date, plan_end_date, plan_amount, plan_notes, _created_at = c
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT COALESCE(client_access_code, '') FROM clients WHERE id = ?", (cid_i,))
            access_row = cur.fetchone()
            conn.close()
            client_access_code = access_row[0] if access_row else ''
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Editar cliente</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:900px;margin:0 auto;padding:28px;}}
        h1{{margin:0 0 16px;font-size:2.1rem;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:26px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
        form{{display:grid;gap:16px;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));}}
        label{{display:flex;flex-direction:column;font-weight:600;color:#6d7480;gap:8px;}}
        input, textarea, button{{font:inherit;outline:none;}}
        input, textarea{{padding:14px 16px;border:1px solid #d8dde6;border-radius:14px;background:#fff;color:#101318;}}
        textarea{{min-height:130px;resize:vertical;grid-column:1 / -1;}}
        .full{{grid-column:1 / -1;}}
        button{{padding:13px 18px;border:none;border-radius:14px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
        button:hover{{background:#232933;transform:translateY(-1px);}}
        .actions{{display:flex;gap:14px;align-items:center;flex-wrap:wrap;}}
        .secondary-link{{color:#101318;text-decoration:none;font-weight:700;}}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        <div class="card">
            <h1>Editar cliente</h1>
            <form method="post" action="/edit_client">
                <input type="hidden" name="id" value="{cid_i}" />
                <label>Nombre<input name="name" value="{html.escape(name)}" required /></label>
                <label>Teléfono<input name="phone" value="{html.escape(phone or '')}" /></label>
                <label>Email<input name="email" type="email" value="{html.escape(email or '')}" /></label>
                <label>Código acceso app<input name="client_access_code" value="{html.escape(client_access_code or '')}" /></label>
                <label>Fecha de nacimiento<input name="birthdate" type="date" value="{html.escape(birthdate or '')}" /></label>
                <label>Altura (cm)<input name="height_cm" type="number" min="0" step="0.1" value="{height_cm if height_cm else ''}" /></label>
                <label>Peso (kg)<input name="weight_kg" type="number" min="0" step="0.1" value="{weight_kg if weight_kg else ''}" /></label>
                <label>Inicio del plan<input name="plan_start_date" type="date" value="{html.escape(plan_start_date or '')}" /></label>
                <label>Fin del plan<input name="plan_end_date" type="date" value="{html.escape(plan_end_date or '')}" /></label>
                <label>Importe del plan<input name="plan_amount" type="number" min="0" step="0.01" value="{plan_amount if plan_amount else ''}" /></label>
                <label class="full">Notas del plan<input name="plan_notes" value="{html.escape(plan_notes or '')}" /></label>
                <label class="full">Objetivos<textarea name="objectives">{html.escape(objectives or '')}</textarea></label>
                <div class="actions full">
                    <button type="submit">Guardar cambios</button>
                    <a class="secondary-link" href="/clients">Volver</a>
                </div>
            </form>
        </div>
    </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Payments page
        if path == '/client_profile':
            cid = q.get('id', [''])[0]
            assign_diet_id = q.get('assign_diet_id', [''])[0]
            selected_section = (q.get('section', [''])[0] if 'section' in q else '').strip().lower()
            try:
                cid_i = int(cid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            c = get_client_by_id(cid_i)
            if not c:
                self.send_response(404)
                self.end_headers()
                return

            _, name, phone, email, birthdate, _height_cm, _weight_kg, objectives, _plan_start_date, _plan_end_date, _plan_amount, _plan_notes, _created_at = c
            age = calculate_age(birthdate)
            active_diet = get_active_client_diet(cid_i)
            active_routine = get_active_client_routine(cid_i)
            daily_steps_goal = get_client_daily_steps_goal(cid_i)
            diets = []
            routines_all = []
            diet_history = []
            training_history = []

            selected_diet_id = ''
            try:
                selected_diet_id = str(int(assign_diet_id)) if assign_diet_id else ''
            except Exception:
                selected_diet_id = ''

            if selected_section == 'diet':
                diets = get_diets()
                diet_history = get_client_diet_history(cid_i)
            elif selected_section == 'training':
                routines_all = get_routines()
                training_history = get_client_training_history(cid_i)

            diet_options = ''.join([
                f'<option value="{d[0]}" {"selected" if selected_diet_id == str(d[0]) else ""}>{html.escape(d[1])}</option>'
                for d in diets
            ])
            routine_options = ''.join([
                f'<option value="{r[0]}">{html.escape(r[1] or "Rutina")}</option>'
                for r in routines_all
            ])

            active_diets = [h for h in diet_history if int(h[9] or 0) == 1]
            old_diets = [h for h in diet_history if int(h[9] or 0) == 0]
            active_training = [h for h in training_history if int(h[11] or 0) == 1]
            old_training = [h for h in training_history if int(h[11] or 0) == 0]

            def diet_item_html(item):
                history_id, _client_id, diet_id, diet_name, client_diet_name, template_diet_id, template_diet_name, start_date, end_date, is_active, notes, _created = item
                display_name = (client_diet_name or '').strip() or (diet_name or '').strip() or 'Dieta'
                badge = 'Activa' if int(is_active or 0) == 1 else 'No activa'
                end_label = end_date or ('En curso' if int(is_active or 0) == 1 else '-')
                template_label = template_diet_name or ('Plantilla #' + str(template_diet_id) if template_diet_id else '-')
                badge_html = f'<span class="badge badge-old">{badge}</span>'
                if int(is_active or 0) == 1:
                    badge_html = (
                        f'<form method="post" action="/deactivate_client_diet" style="display:inline;margin:0">'
                        f'<input type="hidden" name="history_id" value="{history_id}" />'
                        f'<input type="hidden" name="client_id" value="{cid_i}" />'
                        f'<button type="submit" class="badge badge-active badge-btn" title="Pulsar para pasar a no activa">Activa</button>'
                        f'</form>'
                    )
                else:
                    badge_html = (
                        f'<form method="post" action="/activate_client_diet" style="display:inline;margin:0">'
                        f'<input type="hidden" name="history_id" value="{history_id}" />'
                        f'<input type="hidden" name="client_id" value="{cid_i}" />'
                        f'<input type="hidden" name="return_to" value="/client_profile?id={cid_i}" />'
                        f'<button type="submit" class="badge badge-inactive badge-btn" title="Pulsar para activar esta dieta">No activa</button>'
                        f'</form>'
                    )
                date_form_fields = (
                    '<label>Inicio'
                    f'<input type="date" name="start_date" value="{html.escape(start_date or "")}" />'
                    '</label>'
                )
                save_label = 'Guardar inicio'
                if int(is_active or 0) == 0:
                    date_form_fields += (
                        '<label>Fin'
                        f'<input type="date" name="end_date" value="{html.escape(end_date or "")}" />'
                        '</label>'
                    )
                    save_label = 'Guardar fechas'
                edit_dates_form = (
                    f'<form method="post" action="/update_client_diet_dates" class="inline-dates-form">'
                    f'<input type="hidden" name="history_id" value="{history_id}" />'
                    f'<input type="hidden" name="client_id" value="{cid_i}" />'
                    f'<input type="hidden" name="return_to" value="/client_profile?id={cid_i}" />'
                    f'{date_form_fields}'
                    f'<button type="submit" class="mini-btn">{save_label}</button>'
                    f'</form>'
                )
                return (
                    '<div class="history-item">'
                    f'<div class="history-head"><strong>{html.escape(display_name)}</strong>{badge_html}</div>'
                    f'<div class="history-meta">Inicio: {html.escape(start_date or "-")} · Fin: {html.escape(end_label)} · Plantilla: {html.escape(template_label)}</div>'
                    f'<div class="history-note">{html.escape(notes or "Sin notas")}</div>'
                    f'<div class="history-edit-box">{edit_dates_form}</div>'
                    f'<div style="margin-top:8px;display:flex;gap:8px;flex-wrap:wrap;"><a class="mini-btn" href="/static/builder.html?diet_id={diet_id}">Editar dieta</a></div>'
                    '</div>'
                )

            def training_item_html(item):
                history_id, _client_id, _exercise_id, routine_id, training_name, exercise_name, routine_name, template_routine_id, template_routine_name, start_date, end_date, is_active, notes, _created = item
                routine_id_i = int(routine_id or 0)
                display_name = (training_name or '').strip() or (routine_name or '').strip() or (exercise_name or '').strip() or 'Entrenamiento'
                badge = 'Activa' if int(is_active or 0) == 1 else 'No activa'
                end_label = end_date or ('En curso' if int(is_active or 0) == 1 else '-')
                template_label = template_routine_name or ('Plantilla #' + str(template_routine_id) if template_routine_id else '-')
                badge_html = f'<span class="badge badge-old">{badge}</span>'
                if int(is_active or 0) == 1:
                    badge_html = (
                        f'<form method="post" action="/deactivate_client_training" style="display:inline;margin:0">'
                        f'<input type="hidden" name="history_id" value="{history_id}" />'
                        f'<input type="hidden" name="client_id" value="{cid_i}" />'
                        f'<input type="hidden" name="return_to" value="/client_profile?id={cid_i}" />'
                        f'<button type="submit" class="badge badge-active badge-btn" title="Pulsar para pasar a no activa">Activa</button>'
                        f'</form>'
                    )
                else:
                    badge_html = (
                        f'<form method="post" action="/activate_client_training" style="display:inline;margin:0">'
                        f'<input type="hidden" name="history_id" value="{history_id}" />'
                        f'<input type="hidden" name="client_id" value="{cid_i}" />'
                        f'<input type="hidden" name="return_to" value="/client_profile?id={cid_i}" />'
                        f'<button type="submit" class="badge badge-inactive badge-btn" title="Pulsar para activar esta rutina">No activa</button>'
                        f'</form>'
                    )
                edit_button = ''
                if routine_id_i > 0:
                    edit_button = f'<div style="margin-top:8px;"><a class="mini-btn" href="/routines?routine_id={routine_id_i}">Editar rutina</a></div>'
                return (
                    '<div class="history-item">'
                    f'<div class="history-head"><strong>{html.escape(display_name)}</strong>{badge_html}</div>'
                    f'<div class="history-meta">Inicio: {html.escape(start_date or "-")} · Fin: {html.escape(end_label)} · Plantilla: {html.escape(template_label)}</div>'
                    f'<div class="history-note">{html.escape(notes or "Sin notas")}</div>'
                    f'{edit_button}'
                    '</div>'
                )

            active_diets_html = ''.join([diet_item_html(h) for h in active_diets]) or '<p class="empty">Sin dietas activas.</p>'
            old_diets_html = ''.join([diet_item_html(h) for h in old_diets]) or '<p class="empty">Sin dietas antiguas.</p>'
            active_training_html = ''.join([training_item_html(h) for h in active_training]) or '<p class="empty">Sin entrenamientos activos.</p>'
            old_training_html = ''.join([training_item_html(h) for h in old_training]) or '<p class="empty">Sin entrenamientos antiguos.</p>'
            fasting_weights_html = ''
            daily_steps_html = ''
            if selected_section == 'weight':
                fasting_weights_html = render_fasting_weights_panel(cid_i, panel_id=f'fw-admin-{cid_i}', include_client_id=True)
            if selected_section == 'steps':
                daily_steps_html = render_client_daily_steps_panel(
                    cid_i,
                    panel_id=f'steps-admin-{cid_i}',
                    include_client_id=True,
                    daily_goal=daily_steps_goal,
                )

            diet_panel_html = f'''
            <section class="panel">
                <h2>🥗 Dietas</h2>
                <form method="post" action="/assign_client_diet" class="assign">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}&section=diet" />
                    <select name="diet_id" class="full" required>
                        <option value="">Selecciona una dieta</option>
                        {diet_options}
                    </select>
                    <input name="start_date" type="date" placeholder="Inicio" />
                    <input name="end_date" type="date" placeholder="Fin" />
                    <input name="notes" class="full" placeholder="Notas de asignación" />
                    <button type="submit" class="full">✨ Asignar dieta al cliente</button>
                </form>
                <div class="history-group">
                    <h3>Dietas activas</h3>
                    {active_diets_html}
                </div>
                <div class="history-group">
                    <h3>Dietas antiguas</h3>
                    {old_diets_html}
                </div>
            </section>
            '''

            training_panel_html = f'''
            <section class="panel">
                <h2>🏋️ Entrenamientos</h2>
                <form method="post" action="/assign_client_training" class="assign">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}&section=training" />
                    <select name="routine_id" class="full" required>
                        <option value="">Selecciona una rutina</option>
                        {routine_options}
                    </select>
                    <input name="start_date" type="date" placeholder="Inicio" />
                    <input name="end_date" type="date" placeholder="Fin" />
                    <input name="notes" class="full" placeholder="Notas de entrenamiento" />
                    <button type="submit" class="full">✨ Asignar rutina</button>
                </form>
                <div class="history-group">
                    <h3>Entrenamientos activos</h3>
                    {active_training_html}
                </div>
                <div class="history-group">
                    <h3>Entrenamientos antiguos</h3>
                    {old_training_html}
                </div>
            </section>
            '''

            weight_panel_html = f'''
            <section class="panel panel-full">
                <h2>⚖️ Peso corporal en ayunas</h2>
                {fasting_weights_html}
            </section>
            '''

            steps_panel_html = f'''
            <section class="panel panel-full">
                <h2>👟 Pasos diarios</h2>
                <form method="post" action="/set_client_steps_goal" class="steps-goal-form">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}&section=steps" />
                    <label>Objetivo diario de pasos
                        <input name="daily_steps_goal" type="number" min="0" step="1" value="{int(daily_steps_goal or 0) if int(daily_steps_goal or 0) > 0 else ''}" placeholder="Ej: 10000" />
                    </label>
                    <button type="submit">Guardar objetivo</button>
                </form>
                {daily_steps_html}
            </section>
            '''

            section_titles = {
                'diet': 'Dietas',
                'training': 'Entrenamientos',
                'weight': 'Peso corporal en ayunas',
                'steps': 'Pasos diarios',
            }
            section_descriptions = {
                'diet': 'Asigna dietas y revisa el historial del cliente.',
                'training': 'Asigna rutinas y consulta histórico de entrenamientos.',
                'weight': 'Control diario del peso corporal en ayunas.',
                'steps': 'Objetivo y seguimiento de pasos diarios.',
            }
            section_status = {
                'diet': 'Activa' if active_diet else 'Sin dieta activa',
                'training': 'Activa' if active_routine else 'Sin entrenamiento activo',
                'weight': 'Seguimiento activo',
                'steps': f'Objetivo: {daily_steps_goal} pasos' if daily_steps_goal > 0 else 'Objetivo sin definir',
            }
            section_content = {
                'diet': diet_panel_html,
                'training': training_panel_html,
                'weight': weight_panel_html,
                'steps': steps_panel_html,
            }

            if selected_section not in section_content:
                selected_section = ''

            cards_html = ''.join([
                f'<a class="admin-home-card" href="/client_profile?id={cid_i}&section={key}">'
                f'<div class="chip">{html.escape(section_status[key])}</div>'
                f'<h3>{html.escape(section_titles[key])}</h3>'
                f'<p>{html.escape(section_descriptions[key])}</p>'
                '</a>'
                for key in ('diet', 'training', 'weight', 'steps')
            ])

            detail_html = ''
            if selected_section:
                detail_html = (
                    '<section class="detail-wrap">'
                    f'<a class="back-btn" href="/client_profile?id={cid_i}">← Volver al panel</a>'
                    '<details class="accordion" open>'
                    f'<summary>{html.escape(section_titles[selected_section])}</summary>'
                    f'<div class="accordion-body">{section_content[selected_section]}</div>'
                    '</details>'
                    '</section>'
                )

            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Perfil de cliente</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:1200px;margin:0 auto;padding:28px;}}
        .top{{display:flex;justify-content:space-between;align-items:flex-start;gap:16px;flex-wrap:wrap;margin-bottom:16px;}}
        h1{{margin:0;font-size:2rem;}}
        .sub{{color:#6d7480;margin-top:4px;}}
        .back{{text-decoration:none;color:#101318;font-weight:700;}}
        .msg{{padding:10px 12px;border-radius:10px;background:#fef4ea;border:1px solid #f5dcc0;color:#4d3217;margin:10px 0 16px;}}
        .cards{{display:grid;gap:12px;grid-template-columns:repeat(4,minmax(0,1fr));}}
        .admin-home-card{{display:block;text-decoration:none;border:1px solid #d8dde6;background:#fff;border-radius:16px;padding:16px;box-shadow:0 10px 22px rgba(16,19,24,.06);transition:transform .14s ease, box-shadow .14s ease, border-color .14s ease;color:#101318;}}
        .admin-home-card:hover{{transform:translateY(-2px);box-shadow:0 16px 30px rgba(16,19,24,.10);border-color:#c5ccd8;}}
        .admin-home-card .chip{{display:inline-flex;padding:4px 10px;border-radius:999px;background:#eef2f7;color:#475569;font-size:.72rem;font-weight:800;}}
        .admin-home-card h3{{margin:10px 0 6px;font-size:1.05rem;}}
        .admin-home-card p{{margin:0;color:#6d7480;font-size:.92rem;line-height:1.35;}}
        .detail-wrap{{margin-top:14px;}}
        .back-btn{{display:inline-flex;align-items:center;gap:6px;text-decoration:none;border:1px solid #d8dde6;border-radius:10px;padding:8px 11px;background:#fff;color:#101318;font-weight:700;font-size:.88rem;margin-bottom:10px;}}
        .accordion{{border:1px solid #e8ebef;border-radius:16px;background:#fff;box-shadow:0 12px 30px rgba(16,19,24,.06);overflow:hidden;}}
        .accordion summary{{list-style:none;cursor:pointer;padding:14px 16px;font-weight:800;font-size:1.03rem;border-bottom:1px solid #eef2f7;}}
        .accordion summary::-webkit-details-marker{{display:none;}}
        .accordion-body{{padding:14px;}}
        .panel{{background:#fff;border:1px solid #e8ebef;border-radius:16px;padding:16px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
        .panel h2{{margin:0 0 12px;font-size:1.2rem;}}
        .profile-meta{{display:flex;gap:10px;flex-wrap:wrap;margin:6px 0 12px;}}
        .chip{{padding:6px 10px;border-radius:999px;background:#eef2f7;font-size:.82rem;color:#4a5568;font-weight:700;}}
        .assign{{display:grid;grid-template-columns:repeat(2,minmax(120px,1fr));gap:8px;margin-bottom:12px;}}
        .assign .full{{grid-column:1 / -1;}}
        .assign input,.assign select,.assign button{{font:inherit;padding:10px 11px;border-radius:10px;border:1px solid #d8dde6;background:#fff;color:#101318;}}
        .assign button{{background:#101318;color:#fff;border-color:#101318;cursor:pointer;font-weight:700;}}
        .history-group{{margin-top:10px;}}
        .history-group h3{{margin:0 0 8px;font-size:1rem;color:#6d7480;}}
        .history-item{{border:1px solid #e8ebef;border-radius:12px;padding:10px;margin-bottom:8px;background:#fff;}}
        .history-head{{display:flex;justify-content:space-between;gap:8px;align-items:center;}}
        .badge{{padding:4px 8px;border-radius:999px;background:#eef2f7;font-size:.74rem;font-weight:800;color:#4a5568;}}
        .badge-old{{background:#eef2f7;color:#4a5568;}}
        .badge-active{{background:#dcfce7;color:#166534;}}
        .badge-inactive{{background:#fee2e2;color:#991b1b;}}
        .badge-btn{{border:1px solid #bbf7d0;cursor:pointer;}}
        .badge-btn:hover{{filter:brightness(.97);}}
        .history-meta{{margin-top:6px;color:#6d7480;font-size:.86rem;}}
        .history-note{{margin-top:6px;color:#101318;font-size:.9rem;}}
        .mini-btn{{display:inline-flex;margin-top:8px;padding:7px 10px;border:1px solid #d8dde6;border-radius:8px;background:#fff;color:#101318;font-weight:700;cursor:pointer;text-decoration:none;}}
        .history-edit-box{{margin-top:10px;padding:10px;border:1px dashed #d8dde6;border-radius:10px;background:#f9fbfd;}}
        .inline-dates-form{{display:flex;gap:8px;flex-wrap:wrap;align-items:flex-end;}}
        .inline-dates-form label{{display:flex;flex-direction:column;gap:4px;font-size:.75rem;color:#6d7480;font-weight:700;}}
        .inline-dates-form input{{font:inherit;padding:7px 10px;border-radius:8px;border:1px solid #d8dde6;background:#fff;color:#101318;min-width:170px;}}
        .inline-dates-form .mini-btn{{margin-top:0;}}
        .panel-full{{grid-column:1 / -1;}}
        .fw-wrap{{border:1px solid #e8ebef;border-radius:14px;background:#fff;padding:8px;overflow:hidden;}}
        .fw-head{{font-size:.98rem;font-weight:800;color:#b91c1c;text-align:center;margin:1px 0 8px;}}
        .fw-grid{{display:grid;grid-template-columns:repeat(6,minmax(0,1fr));gap:6px;align-items:start;width:100%;min-width:0;}}
        .fw-month{{border:1px solid #d8dde6;border-radius:9px;background:#f8fafc;min-height:220px;min-width:0;overflow:hidden;}}
        .fw-month-title{{padding:5px 4px;border-bottom:1px solid #d8dde6;text-align:center;font-weight:800;color:#101318;font-size:.78rem;line-height:1.1;overflow-wrap:anywhere;}}
        .fw-month-days{{padding:5px;display:flex;flex-direction:column;gap:3px;max-height:none;overflow:visible;min-width:0;}}
        .fw-row{{display:grid;grid-template-columns:20px 58px;gap:4px;align-items:center;font-size:.74rem;color:#111827;min-width:0;justify-content:start;}}
        .fw-mean-row{{padding:2px 0 4px;}}
        .fw-mean-row span{{font-weight:800;color:#991b1b;}}
        .fw-mean-value{{color:#991b1b;font-weight:800;font-size:.74rem;line-height:1.15;}}
        .fw-mean-value em{{font-style:normal;font-weight:700;margin-left:3px;display:block;}}
        .fw-mean-value.down em{{color:#15803d;}}
        .fw-mean-value.up em{{color:#b91c1c;}}
        .fw-mean-value.neutral em{{color:#6d7480;}}
        .fw-input{{width:58px;max-width:58px;min-width:58px;padding:2px 4px;border:1px solid #d8dde6;border-radius:7px;background:#fff;font:inherit;font-size:.72rem;height:24px;}}
        .fw-steps-input{{width:58px;max-width:58px;min-width:58px;padding:2px 4px;border:1px solid #d8dde6;border-radius:7px;background:#fff;font:inherit;font-size:.72rem;height:24px;}}
        .fw-input.is-saving{{background:#fff7ed;border-color:#fdba74;}}
        .fw-steps-input.is-saving{{background:#fff7ed;border-color:#fdba74;}}
        .fw-input.is-saved{{background:#ecfdf5;border-color:#86efac;}}
        .fw-steps-input.is-saved{{background:#ecfdf5;border-color:#86efac;}}
        .fw-input.is-error{{background:#fef2f2;border-color:#fca5a5;}}
        .fw-steps-input.is-error{{background:#fef2f2;border-color:#fca5a5;}}
        .fw-steps-input.goal-met{{background:#ecfdf5;border-color:#86efac;color:#166534;font-weight:700;}}
        .fw-steps-input.goal-missed{{background:#fef2f2;border-color:#fca5a5;color:#991b1b;font-weight:700;}}
        .fw-foot{{margin-top:8px;color:#6d7480;font-size:.82rem;}}
        .steps-goal-form{{display:flex;gap:8px;align-items:flex-end;flex-wrap:wrap;margin-bottom:10px;}}
        .steps-goal-form label{{display:flex;flex-direction:column;gap:5px;font-size:.78rem;color:#6d7480;font-weight:700;}}
        .steps-goal-form input{{font:inherit;padding:8px 10px;border-radius:9px;border:1px solid #d8dde6;background:#fff;color:#101318;min-width:200px;}}
        .steps-goal-form button{{padding:8px 12px;border:1px solid #d8dde6;border-radius:9px;background:#fff;color:#101318;font-weight:700;cursor:pointer;}}
        .empty{{color:#6d7480;font-style:italic;}}
        @media (max-width: 1280px){{ .fw-grid{{grid-template-columns:repeat(5,minmax(0,1fr));}} }}
        @media (max-width: 1200px){{ .fw-grid{{grid-template-columns:repeat(4,minmax(0,1fr));}} }}
        @media (max-width: 960px){{
            .cards{{grid-template-columns:repeat(2,minmax(0,1fr));}}
            .fw-grid{{grid-template-columns:repeat(3,minmax(0,1fr));}}
        }}
        @media (max-width: 820px){{ .cards{{grid-template-columns:1fr;}} }}
        @media (max-width: 720px){{ .fw-grid{{grid-template-columns:repeat(2,minmax(0,1fr));}} }}
        @media (max-width: 560px){{ .fw-grid{{grid-template-columns:1fr;}} }}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        <div class="top">
            <div>
                <h1>👤 Perfil de {html.escape(name)}</h1>
                <div class="sub">Dos apartados principales: Dietas y Entrenamientos</div>
                <div class="profile-meta">
                    <span class="chip">Teléfono: {html.escape(phone or '-')}</span>
                    <span class="chip">Email: {html.escape(email or '-')}</span>
                    <span class="chip">Edad: {age if age is not None else '-'}</span>
                    <span class="chip">Objetivo: {html.escape((objectives or '').strip() or 'Sin objetivo')}</span>
                </div>
            </div>
            <div style="display:flex;gap:10px;align-items:center;flex-wrap:wrap;">
                <a class="back" href="/client_app?client_id={cid_i}">📱 Ver vista cliente</a>
                <a class="back" href="/edit_client?id={cid_i}">✏️ Editar cliente</a>
                <a class="back" href="/clients">← Volver a clientes</a>
            </div>
        </div>
        {f'<div class="msg">{html.escape(msg)}</div>' if msg else ''}
        <section class="cards">{cards_html}</section>
        {detail_html}
    </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Payments page
        if path == '/payments':
            clients = get_clients()
            plans = get_payment_plans()
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            year, month = parse_year_month(q.get('month', [''])[0])
            from datetime import date, timedelta
            first_day = date(year, month, 1)
            if month == 12:
                next_month = date(year + 1, 1, 1)
            else:
                next_month = date(year, month + 1, 1)
            prev_month_date = date(year - 1, 12, 1) if month == 1 else date(year, month - 1, 1)
            prev_link = f'/payments?month={prev_month_date.year:04d}-{prev_month_date.month:02d}'
            next_link = f'/payments?month={next_month.year:04d}-{next_month.month:02d}'
            client_options = ''.join([f'<option value="{c[0]}">{html.escape(c[1])}</option>' for c in clients])
            from datetime import datetime
            day_events = {}
            for plan in plans:
                plan_id, client_id, client_name, start_date, end_date, amount, notes, created_at = plan
                try:
                    start_dt = datetime.strptime(start_date, '%Y-%m-%d').date()
                    end_dt = datetime.strptime(end_date, '%Y-%m-%d').date()
                except Exception:
                    continue
                day_events.setdefault(start_dt, []).append({'kind': 'start', 'name': client_name, 'amount': amount, 'id': plan_id, 'end': end_dt})
                day_events.setdefault(end_dt, []).append({'kind': 'end', 'name': client_name, 'amount': amount, 'id': plan_id, 'start': start_dt})

            weeks = calendar.monthcalendar(year, month)
            weekday_labels = ['Lun', 'Mar', 'Mié', 'Jue', 'Vie', 'Sáb', 'Dom']
            week_rows = []
            for week in weeks:
                day_cells = []
                for idx, day_num in enumerate(week):
                    if day_num == 0:
                        day_cells.append('<div class="cal-day empty"></div>')
                        continue
                    current_date = date(year, month, day_num)
                    events = day_events.get(current_date, [])
                    event_html = []
                    for event in events:
                        pill_class = 'pill-start' if event['kind'] == 'start' else 'pill-end'
                        suffix = 'inicio' if event['kind'] == 'start' else 'fin'
                        event_html.append(
                            f'<div class="plan-pill {pill_class}"><span>{html.escape(event["name"])} · {suffix}</span><strong>{event["amount"]:.2f} €</strong></div>'
                        )
                    day_cells.append(
                        f'<div class="cal-day"><div class="cal-num">{day_num}</div><div class="cal-events">{"".join(event_html) if event_html else ""}</div></div>'
                    )
                week_rows.append(f'<div class="cal-week">{"".join(day_cells)}</div>')

            plan_rows = []
            for plan in plans:
                plan_id, client_id, client_name, start_date, end_date, amount, notes, created_at = plan
                status = payment_plan_status(start_date, end_date)
                status_class = 'status-ok' if status == 'Activo' else 'status-warn' if status == 'Próximo' else 'status-bad' if status == 'Finalizado' else 'status-gray'
                plan_rows.append(
                    '<tr>'
                    f'<td>{plan_id}</td>'
                    f'<td>{html.escape(client_name)}</td>'
                    f'<td>{html.escape(start_date)}</td>'
                    f'<td>{html.escape(end_date)}</td>'
                    f'<td>{amount:.2f}</td>'
                    f'<td><span class="status-pill {status_class}">{status}</span></td>'
                    f'<td>{html.escape(notes or "")}</td>'
                    f'<td>{html.escape(created_at or "")}</td>'
                    f'<td><a class="action-button action-edit" href="/edit_payment?id={plan_id}">Editar</a> '
                    f'<form method="post" action="/delete_payment" style="display:inline;margin:0 0 0 8px">'
                    f'<input type="hidden" name="id" value="{plan_id}" />'
                    f'<button class="action-button action-delete" type="submit">Borrar</button></form></td>'
                    '</tr>'
                )

            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Calendario de pagos</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:1200px;margin:0 auto;padding:28px;}}
        h1{{margin:0 0 12px;font-size:2.2rem;letter-spacing:-.03em;}}
        h2{{margin:28px 0 12px;font-size:1.2rem;color:#6d7480;}}
        .section-card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:22px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
        form{{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));align-items:start;}}
        input, textarea, select, button{{font:inherit;outline:none;}}
        input, textarea, select{{padding:12px 14px;border:1px solid #d8dde6;border-radius:12px;background:#fff;color:#101318;}}
        textarea{{min-height:96px;resize:vertical;grid-column:1 / -1;}}
        select{{appearance:none;}}
        button{{padding:13px 18px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
        button:hover{{background:#232933;transform:translateY(-1px);}}
        .message{{padding:14px 16px;border-radius:14px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:20px;}}
        table{{width:100%;border-collapse:collapse;margin-top:16px;background:#fff;border-radius:16px;overflow:hidden;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
        tbody td{{color:#23160f !important;font-weight:600;}}
        th,td{{padding:14px 16px;text-align:left;border-bottom:1px solid #e8ebef;vertical-align:top;}}
        th{{background:#f3f5f8;font-weight:700;color:#101318;border-bottom:1px solid #e8ebef;}}
        tr:hover{{background:#f8fafc;}}
        .action-button{{display:inline-flex;align-items:center;justify-content:center;padding:8px 12px;border-radius:12px;border:1px solid #d8dde6;background:#fff;color:#101318;text-decoration:none;font-weight:600;font-size:.95rem;cursor:pointer;transition:transform .18s ease,background .18s ease,border-color .18s ease;}}
        .action-button:hover{{background:#f5f7fa;transform:translateY(-1px);border-color:#d8dde6;}}
        .action-edit{{border:none;background:#101318;color:#fff;}}
        .action-edit:hover{{background:#232933;}}
        .action-delete{{border:none;background:#8b1b20;color:#fff;}}
        .action-delete:hover{{background:#6f1116;}}
        .status-pill{{display:inline-flex;align-items:center;padding:4px 10px;border-radius:999px;font-size:.78rem;font-weight:700;}}
        .status-ok{{background:#dcfce7;color:#166534;}}
        .status-warn{{background:#fef3c7;color:#92400e;}}
        .status-bad{{background:#fee2e2;color:#991b1b;}}
        .status-gray{{background:#e2e8f0;color:#475569;}}
        .calendar-shell{{margin-top:16px;border:1px solid #e8ebef;border-radius:22px;overflow:hidden;background:#fff;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        .calendar-head{{display:flex;align-items:center;justify-content:space-between;padding:18px 20px;border-bottom:1px solid #e8ebef;background:#fff;backdrop-filter:blur(10px);position:sticky;top:0;z-index:2;}}
        .calendar-title{{font-size:1.35rem;font-weight:800;letter-spacing:-.03em;color:#0f172a;}}
        .calendar-nav{{display:flex;gap:8px;align-items:center;}}
        .nav-btn{{display:inline-flex;align-items:center;justify-content:center;width:36px;height:36px;border-radius:999px;border:1px solid #d8dde6;background:#fff;color:#0f172a;text-decoration:none;font-weight:800;}}
        .legend{{display:flex;gap:10px;flex-wrap:wrap;padding:0 20px 18px;align-items:center;color:#475569;font-size:.9rem;}}
        .legend-item{{display:inline-flex;align-items:center;gap:8px;}}
        .legend-dot{{width:12px;height:12px;border-radius:999px;display:inline-block;}}
        .lg-start{{background:#22c55e;}}
        .lg-end{{background:#ef4444;}}
        .weekday-row,.cal-week{{display:grid;grid-template-columns:repeat(7,minmax(0,1fr));}}
        .weekday-row{{border-top:1px solid #e8ebef;border-bottom:1px solid #e8ebef;background:#fff;}}
        .weekday{{padding:12px 10px;text-align:center;font-size:.8rem;font-weight:800;color:#64748b;text-transform:uppercase;letter-spacing:.08em;}}
        .cal-week{{min-height:140px;border-bottom:1px solid #e2e8f0;}}
        .cal-day{{position:relative;padding:10px 10px 12px;border-right:1px solid #eef2f7;min-height:140px;background:#fff;}}
        .cal-day:last-child{{border-right:none;}}
        .cal-day.empty{{background:transparent;}}
        .cal-num{{font-weight:800;color:#0f172a;font-size:.98rem;margin-bottom:8px;}}
        .cal-events{{display:flex;flex-direction:column;gap:6px;}}
        .plan-pill{{display:flex;flex-direction:column;gap:2px;padding:8px 10px;border-radius:14px;font-size:.78rem;line-height:1.25;border:1px solid transparent;box-shadow:0 8px 18px rgba(15,23,42,.05);}}
        .pill-start{{background:#dcfce7;border-color:#bbf7d0;color:#166534;}}
        .pill-end{{background:#fee2e2;border-color:#fecaca;color:#991b1b;}}
        .plan-pill strong{{font-size:.83rem;}}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        <h1>📆 Calendario de pagos</h1>
        {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
        <section class="section-card">
            <h2>➕ Añadir plan de pago</h2>
            <form method="post" action="/add_payment">
                <select name="client_id" required>
                    <option value="">-- Selecciona un cliente --</option>
                    {client_options}
                </select>
                <input name="start_date" type="date" required />
                <input name="end_date" type="date" required />
                <input name="amount" type="number" min="0" step="0.01" placeholder="Cuantía monetaria" required />
                <textarea name="notes" placeholder="Notas o detalles del plan"></textarea>
                <button type="submit">Crear plan</button>
            </form>
        </section>
        <section class="section-card">
            <div class="calendar-shell">
                <div class="calendar-head">
                    <div class="calendar-title">{month_label(year, month)}</div>
                    <div class="calendar-nav">
                        <a class="nav-btn" href="{prev_link}" aria-label="Mes anterior">‹</a>
                        <a class="nav-btn" href="/payments" aria-label="Mes actual">•</a>
                        <a class="nav-btn" href="{next_link}" aria-label="Mes siguiente">›</a>
                    </div>
                </div>
                <div class="legend">
                    <span class="legend-item"><span class="legend-dot lg-start"></span> Inicio de plan</span>
                    <span class="legend-item"><span class="legend-dot lg-end"></span> Fin de plan</span>
                    <span class="legend-item">Selecciona mes con los botones para ver el paso del calendario</span>
                </div>
                <div class="weekday-row">
                    {''.join([f'<div class="weekday">{wd}</div>' for wd in weekday_labels])}
                </div>
                {''.join(week_rows)}
            </div>
        </section>
        <section class="section-card">
            <h2>Planes registrados</h2>
            <table>
                <thead><tr><th>ID</th><th>Cliente</th><th>Inicio</th><th>Fin</th><th>Importe</th><th>Estado</th><th>Notas</th><th>Creado</th><th>Acciones</th></tr></thead>
                <tbody>
                    {''.join(plan_rows)}
                </tbody>
            </table>
        </section>
    </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        if path == '/edit_payment':
            pid = q.get('id', [''])[0]
            try:
                pid_i = int(pid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            rows = []
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "SELECT pp.id, pp.client_id, c.name, pp.start_date, pp.end_date, COALESCE(pp.amount, 0), COALESCE(pp.notes, ''), pp.created_at FROM payment_plans pp JOIN clients c ON pp.client_id = c.id WHERE pp.id = ?",
                (pid_i,),
            )
            row = cur.fetchone()
            conn.close()
            if not row:
                self.send_response(404)
                self.end_headers()
                return
            plan_id, client_id, client_name, start_date, end_date, amount, notes, created_at = row
            clients = get_clients()
            client_options = ''.join([
                f'<option value="{c[0]}" {"selected" if c[0] == client_id else ""}>{html.escape(c[1])}</option>'
                for c in clients
            ])
            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <title>Editar plan de pago</title>
    <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:900px;margin:0 auto;padding:28px;}}
        h1{{margin:0 0 16px;font-size:2.1rem;}}
        .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:26px;box-shadow:0 12px 30px rgba(16,19,24,.06);}}
        form{{display:grid;gap:16px;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));}}
        label{{display:flex;flex-direction:column;font-weight:600;color:#6d7480;gap:8px;}}
        input, textarea, select, button{{font:inherit;outline:none;}}
        input, textarea, select{{padding:14px 16px;border:1px solid #d8dde6;border-radius:14px;background:#fff;color:#101318;}}
        textarea{{min-height:130px;resize:vertical;grid-column:1 / -1;}}
        .full{{grid-column:1 / -1;}}
        button{{padding:13px 18px;border:none;border-radius:14px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
        button:hover{{background:#232933;transform:translateY(-1px);}}
        .actions{{display:flex;gap:14px;align-items:center;flex-wrap:wrap;}}
        .secondary-link{{color:#101318;text-decoration:none;font-weight:700;}}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        <div class="card">
            <h1>Editar plan de pago</h1>
            <form method="post" action="/edit_payment">
                <input type="hidden" name="id" value="{plan_id}" />
                <label>Cliente<select name="client_id" required>{client_options}</select></label>
                <label>Inicio<input name="start_date" type="date" value="{html.escape(start_date)}" required /></label>
                <label>Fin<input name="end_date" type="date" value="{html.escape(end_date)}" required /></label>
                <label>Cuantía<input name="amount" type="number" min="0" step="0.01" value="{amount:.2f}" required /></label>
                <label class="full">Notas<textarea name="notes">{html.escape(notes or '')}</textarea></label>
                <div class="actions full">
                    <button type="submit">Guardar cambios</button>
                    <a class="secondary-link" href="/payments">Volver</a>
                </div>
            </form>
        </div>
    </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # API: diet builder full data
        m = re.match(r'^/api/diet_builder/(\d+)$', path)
        if m:
            try:
                did = int(m.group(1))
            except Exception:
                return self.send_json({'error': 'bad id'}, status=400)
            data = get_diet_builder_data(did)
            if data is None:
                return self.send_json({'error': 'not found'}, status=404)
            return self.send_json(data)

        if path == '/api/settings/diet_instructions_template':
            return self.send_json({'value': get_diet_instructions_template()})

        # API: instant food search
        if path == '/api/foods/search':
            query = q.get('q', [''])[0].strip()
            category = q.get('category', [''])[0].strip()
            brand = q.get('brand', [''])[0].strip()
            status = q.get('status', ['all'])[0].strip().lower()
            kcal_min = q.get('kcal_min', [''])[0].strip()
            kcal_max = q.get('kcal_max', [''])[0].strip()
            limit_raw = q.get('limit', ['25'])[0].strip()
            try:
                limit = int(limit_raw or 25)
            except Exception:
                limit = 25
            data = search_foods_db(
                query,
                limit=limit,
                category=category,
                brand=brand,
                status=status,
                kcal_min=kcal_min,
                kcal_max=kcal_max,
            )
            return self.send_json(data)

        pdf_path_match = re.match(r'^/export_diet_pdf/dieta_(\d+)\.pdf$', path)
        if path == '/export_diet_pdf' or pdf_path_match:
            if pdf_path_match:
                diet_id = pdf_path_match.group(1)
            else:
                diet_id = q.get('diet_id', [''])[0]
            try:
                diet_id_i = int(diet_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            pdf = build_diet_pdf(diet_id_i)
            if pdf is None:
                self.send_response(404)
                self.end_headers()
                return
            self.send_response(200)
            self.send_header('Content-Type', 'application/pdf')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Disposition', f'inline; filename="dieta_{diet_id}.pdf"; filename*=UTF-8\'\'dieta_{diet_id}.pdf')
            self.send_header('Content-Length', str(len(pdf)))
            self.end_headers()
            self.wfile.write(pdf)
            return

        routine_pdf_path_match = re.match(r'^/export_routine_pdf/rutina_(\d+)\.pdf$', path)
        if path == '/export_routine_pdf' or routine_pdf_path_match:
            if routine_pdf_path_match:
                routine_id = routine_pdf_path_match.group(1)
            else:
                routine_id = q.get('routine_id', [''])[0]
            try:
                routine_id_i = int(routine_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            pdf = build_routine_pdf(routine_id_i)
            if pdf is None:
                self.send_response(404)
                self.end_headers()
                return
            self.send_response(200)
            self.send_header('Content-Type', 'application/pdf')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Disposition', f'inline; filename="rutina_{routine_id}.pdf"; filename*=UTF-8\'\'rutina_{routine_id}.pdf')
            self.send_header('Content-Length', str(len(pdf)))
            self.end_headers()
            self.wfile.write(pdf)
            return

        # Foods page
        if path == '/foods':
            foods = get_foods()
            categories = get_categories()
            brands = get_brands()
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            category_options = ''.join([f'<option value="{c[0]}">{html.escape(c[1])}</option>' for c in categories])
            brand_options = ''.join([f'<option value="{html.escape(b[1])}">{html.escape(b[1])}</option>' for b in brands])

            category_names = [c[1] for c in categories]
            category_id_by_norm_name = {normalize_text(c[1]): c[0] for c in categories}
            category_grid_names = list(category_names)

            def category_emoji(name):
                low = normalize_text(name)
                mapping = [
                    (['carne', 'embutido'], '🥩'),
                    (['pescado', 'marisco'], '🐟'),
                    (['huevo'], '🥚'),
                    (['lacteo', 'queso', 'leche', 'yogur'], '🧀'),
                    (['arroz'], '🍚'),
                    (['pasta'], '🍝'),
                    (['patata', 'batata'], '🥔'),
                    (['fruta'], '🍎'),
                    (['verdura', 'vegetal'], '🥦'),
                    (['legumbre'], '🫘'),
                    (['frutos secos', 'nuez'], '🥜'),
                    (['aceite', 'grasa'], '🫒'),
                    (['salsa'], '🥫'),
                    (['bebida', 'liquido'], '🥤'),
                    (['dulce', 'postre'], '🍫'),
                    (['suplemento', 'proteina'], '💊'),
                ]
                for words, icon in mapping:
                    if any(word in low for word in words):
                        return icon
                return '🍽️'

            category_cards_html = ''.join([
                f'''<div class="category-tile">
                        <button class="category-tile-button" type="button" data-category="{html.escape(name)}">
                            <span class="category-tile-icon">{category_emoji(name)}</span>
                            <span class="category-tile-name">{html.escape(name)}</span>
                        </button>
                        {f"<form method='post' action='/delete_category' class='category-delete-form' onsubmit='return confirm(`¿Seguro que quieres eliminar esta categoría?`)'><input type='hidden' name='id' value='{category_id_by_norm_name.get(normalize_text(name), '')}' /><button type='submit' class='category-delete-btn' title='Eliminar categoría'>×</button></form>" if category_id_by_norm_name.get(normalize_text(name)) else ''}
                    </div>'''
                for name in category_grid_names
            ])

            foods_sorted = sorted(foods, key=lambda r: normalize_text(r[1]))

            def fmt_macro(value):
                try:
                    return f"{float(value):g}"
                except Exception:
                    return '0'

            food_cards_html = []
            for r in foods_sorted:
                fid, name, brand, category, cal, prot, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, is_verified, has_gluten = r
                brand_name = brand or 'Sin marca'
                category_name = category or 'Sin categoría'
                photo_html = (
                    f'<img src="{html.escape(photo_path)}" alt="{html.escape(name)}" loading="lazy" />'
                    if photo_path else
                    '<div class="food-photo-placeholder">Sin foto</div>'
                )
                verified_badge = '<span class="verified-pill" title="Alimento verificado">✓ Verificado</span>' if int(is_verified or 0) == 1 else ''
                gluten_value = parse_gluten_input(has_gluten)
                if gluten_value == 1:
                    gluten_badge = '<span class="gluten-pill has-gluten" title="Con gluten">🌾 Con gluten</span>'
                elif gluten_value == 0:
                    gluten_badge = '<span class="gluten-pill gluten-free" title="Sin gluten">✅ Sin gluten</span>'
                else:
                    gluten_badge = '<span class="gluten-pill gluten-unknown" title="Gluten no indicado">❔ Gluten n/i</span>'
                food_cards_html.append(f'''
                    <article class="food-result-card" data-name="{html.escape(normalize_text(name))}" data-brand="{html.escape(normalize_text(brand_name))}" data-category="{html.escape(normalize_text(category_name))}" data-open-url="/edit?id={fid}">
                        <div class="food-result-photo">{photo_html}</div>
                        <div class="food-result-main">
                            <h3>{html.escape(name)} {verified_badge}</h3>
                            <p class="food-result-sub">{html.escape(brand_name)} · {html.escape(category_name)}</p>
                            <div class="food-tags-row">{gluten_badge}</div>
                            <div class="food-macros-grid">
                                <span><strong>{fmt_macro(cal)}</strong> kcal</span>
                                <span><strong>{fmt_macro(prot)} g</strong> proteínas</span>
                                <span><strong>{fmt_macro(carbs)} g</strong> hidratos</span>
                                <span><strong>{fmt_macro(fats)} g</strong> grasas</span>
                            </div>
                        </div>
                        <div class="card-actions">
                            <a href="/edit?id={fid}" class="ghost-btn">Editar</a>
                            <form method="post" action="/duplicate_food">
                                <input type="hidden" name="id" value="{fid}" />
                                <button type="submit" class="ghost-btn">Duplicar</button>
                            </form>
                            <form method="post" action="/delete_food">
                                <input type="hidden" name="id" value="{fid}" />
                                <button type="submit" class="ghost-btn danger-btn" onclick="return confirm('¿Seguro que quieres eliminar este alimento?')">Eliminar</button>
                            </form>
                        </div>
                    </article>
                ''')

            page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Biblioteca de Alimentos</title>
    <style>
        :root{{
            --bg:#f6f7f9;
            --surface:#ffffff;
            --surface-soft:#f3f5f8;
            --text:#101318;
            --muted:#6d7480;
            --line:#e8ebef;
            --line-strong:#d8dde6;
            --shadow:0 12px 30px rgba(16, 19, 24, 0.06);
            --shadow-hover:0 18px 38px rgba(16, 19, 24, 0.10);
            --radius-xl:22px;
            --radius-lg:18px;
            --radius-md:14px;
            --trans:200ms cubic-bezier(.2,.8,.2,1);
        }}
        *{{box-sizing:border-box;}}
        body{{
            margin:0;
            font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;
            background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);
            color:var(--text);
        }}
        .page{{max-width:1320px;margin:0 auto;padding:38px 32px 60px;}}
        .message{{padding:14px 16px;border-radius:14px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin:0 0 24px;}}
        .library-title{{margin:14px 0 28px;font-size:clamp(2.15rem,5vw,3.6rem);letter-spacing:-.04em;line-height:1.02;font-weight:800;}}

        .create-trigger{{
            width:100%;height:86px;border:none;border-radius:20px;background:var(--surface);
            border:1px solid var(--line);box-shadow:var(--shadow);padding:0 26px;
            display:flex;align-items:center;justify-content:space-between;cursor:pointer;text-align:left;
            transition:transform var(--trans),box-shadow var(--trans),border-color var(--trans);
        }}
        .create-trigger:hover{{transform:translateY(-2px);box-shadow:var(--shadow-hover);border-color:var(--line-strong);}}
        .create-left{{display:flex;align-items:center;gap:16px;min-width:0;}}
        .create-plus{{width:44px;height:44px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;background:#eef2f7;color:#101318;font-size:1.4rem;font-weight:700;}}
        .create-copy{{display:flex;flex-direction:column;gap:2px;min-width:0;}}
        .create-copy strong{{font-size:1.2rem;letter-spacing:-.02em;}}
        .create-copy span{{font-size:.95rem;color:var(--muted);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;}}
        .create-arrow{{font-size:1.25rem;color:#7d8592;}}

        .create-panel{{
            margin-top:14px;background:var(--surface);border:1px solid var(--line);border-radius:var(--radius-xl);
            box-shadow:var(--shadow);padding:20px;display:none;
        }}
        .create-panel.open{{display:block;animation:fadeIn var(--trans);}}
        .create-form{{display:grid;grid-template-columns:repeat(4,minmax(170px,1fr));gap:14px;align-items:start;}}
        .create-form input,.create-form select,.create-form button{{font:inherit;}}
        .create-form input,.create-form select{{height:46px;padding:0 14px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;}}
        .create-form button{{height:46px;border:none;border-radius:12px;background:#101318;color:#fff;font-weight:700;cursor:pointer;}}
        .create-form .full{{grid-column:1 / -1;}}
        .photo-preview{{display:flex;align-items:center;gap:10px;}}
        .photo-preview img{{width:58px;height:58px;border-radius:12px;object-fit:cover;border:1px solid var(--line);display:none;}}
        .nutrition-hint{{font-size:.8rem;color:var(--muted);}}

        .search-wrap{{margin-top:28px;}}
        .search-bar{{
            height:62px;background:var(--surface);border:1px solid var(--line);border-radius:18px;box-shadow:var(--shadow);
            display:flex;align-items:center;gap:12px;padding:0 12px 0 18px;
        }}
        .search-icon{{font-size:1.05rem;color:#7a828f;}}
        .search-input{{border:none;outline:none;background:transparent;flex:1;height:100%;font:inherit;font-size:1rem;color:var(--text);}}
        .search-btn{{height:46px;padding:0 18px;border:none;border-radius:13px;background:#101318;color:#fff;font-weight:700;cursor:pointer;}}

        .spacer-large{{height:42px;}}
        .section-head{{display:flex;align-items:center;justify-content:space-between;gap:12px;margin-bottom:18px;}}
        .section-kicker{{margin:0;font-size:.8rem;letter-spacing:.2em;color:#6a7280;font-weight:800;}}
        .inline-form{{display:flex;align-items:center;gap:8px;}}
        .inline-form input{{height:38px;padding:0 12px;border:1px solid var(--line-strong);border-radius:10px;background:#fff;min-width:200px;}}
        .inline-form button,.head-btn{{height:38px;padding:0 14px;border:1px solid var(--line-strong);border-radius:10px;background:#fff;color:var(--text);font-weight:700;cursor:pointer;}}
        .category-grid{{display:flex;flex-wrap:wrap;gap:12px;justify-content:center;}}
        .category-tile{{
            height:112px;border:1px solid var(--line);border-radius:14px;background:var(--surface);box-shadow:0 8px 20px rgba(16, 19, 24, 0.06);
            transition:transform var(--trans),box-shadow var(--trans),border-color var(--trans);
            position:relative;
            overflow:hidden;
            flex:0 1 150px;
        }}
        .category-tile:hover{{transform:translateY(-3px);box-shadow:var(--shadow-hover);border-color:var(--line-strong);}}
        .category-tile-button{{
            width:100%;height:100%;border:none;background:transparent;cursor:pointer;
            padding:12px;display:flex;flex-direction:column;justify-content:space-between;align-items:flex-start;
            text-align:left;
        }}
        .category-tile-icon{{font-size:1.25rem;line-height:1;}}
        .category-tile-name{{font-size:.98rem;font-weight:700;letter-spacing:0;color:#161b23;text-align:left;line-height:1.2;max-width:126px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;}}
        .category-delete-form{{position:absolute;top:8px;right:8px;margin:0;z-index:2;}}
        .category-delete-btn{{width:22px;height:22px;border:none;border-radius:999px;background:#f7dfe1;color:#8b1b20;font-weight:800;cursor:pointer;line-height:1;display:inline-flex;align-items:center;justify-content:center;padding:0;font-size:.96rem;}}
        .category-delete-btn:hover{{background:#efc7cb;}}

        .separator{{height:1px;background:var(--line);margin:54px 0;}}

        .results-head{{display:flex;align-items:flex-end;justify-content:space-between;gap:14px;}}
        .results-title{{margin:0;font-size:.82rem;letter-spacing:.2em;color:#6a7280;font-weight:800;}}
        .results-total{{font-size:.95rem;color:#67707e;font-weight:700;}}
        .results-controls{{margin:14px 0 20px;display:flex;align-items:center;gap:8px;}}
        .results-controls label{{font-size:.9rem;color:#6e7683;font-weight:700;}}
        .results-controls select{{height:36px;border:1px solid var(--line-strong);border-radius:10px;padding:0 10px;background:#fff;font:inherit;}}

        .results-list{{display:grid;grid-template-columns:repeat(auto-fill,210px);gap:12px;align-items:start;justify-content:start;}}
        .food-result-card{{
            border:1px solid var(--line);border-radius:20px;background:var(--surface);box-shadow:var(--shadow);
            padding:12px;display:grid;grid-template-columns:1fr;gap:10px;align-items:start;
            transition:transform var(--trans),box-shadow var(--trans),border-color var(--trans);cursor:pointer;
        }}
        .food-result-card:hover{{transform:translateY(-2px);box-shadow:var(--shadow-hover);border-color:var(--line-strong);}}
        .food-result-photo{{height:110px;border-radius:14px;border:1px solid var(--line);background:#ffffff;display:flex;align-items:center;justify-content:center;overflow:hidden;padding:6px;}}
        .food-result-photo img{{max-width:100%;max-height:100%;width:auto;height:auto;border-radius:10px;object-fit:contain !important;object-position:center;display:block;background:#ffffff;}}
        .food-photo-placeholder{{width:100%;height:110px;border-radius:14px;border:1px dashed var(--line-strong);display:flex;align-items:center;justify-content:center;font-size:.86rem;color:var(--muted);background:#f8f9fb;text-align:center;}}
        .food-result-main h3{{margin:0;font-size:1.08rem;letter-spacing:-.02em;}}
        .verified-pill{{display:inline-flex;align-items:center;gap:6px;margin-left:8px;padding:3px 10px;border-radius:999px;font-size:.74rem;font-weight:800;letter-spacing:.02em;background:#eaf8ef;color:#1f7a40;border:1px solid #bde7cc;vertical-align:middle;}}
        .food-result-sub{{margin:4px 0 8px;color:var(--muted);font-size:.92rem;}}
        .food-tags-row{{display:flex;align-items:center;gap:6px;margin:0 0 8px;min-height:22px;}}
        .gluten-pill{{display:inline-flex;align-items:center;justify-content:center;height:22px;padding:0 8px;border-radius:999px;font-size:.72rem;font-weight:800;letter-spacing:.01em;border:1px solid transparent;}}
        .gluten-pill.has-gluten{{background:#fff2e8;color:#9a3412;border-color:#fed7aa;}}
        .gluten-pill.gluten-free{{background:#eaf8ef;color:#1f7a40;border-color:#bde7cc;}}
        .gluten-pill.gluten-unknown{{background:#f3f5f8;color:#5b6574;border-color:#dce2ea;}}
        .food-macros-grid{{display:grid;grid-template-columns:1fr;gap:6px;font-size:.88rem;color:#333d4b;margin-top:6px;}}
        .food-macros-grid strong{{font-weight:800;color:#11151a;}}
        .card-actions{{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-start;padding-top:6px;}}
        .card-actions form{{margin:0;}}
        .ghost-btn{{height:36px;padding:0 12px;border:1px solid var(--line-strong);border-radius:10px;background:#fff;color:#15202b;font-weight:700;cursor:pointer;text-decoration:none;display:inline-flex;align-items:center;}}
        .ghost-btn:hover{{background:#f5f7fa;}}
        .danger-btn{{color:#8b1b20;border-color:#efcfd2;}}
        .empty-note{{padding:20px;border-radius:14px;border:1px dashed var(--line-strong);color:var(--muted);background:#fbfcfd;}}

        @keyframes fadeIn{{from{{opacity:0;transform:translateY(-4px);}}to{{opacity:1;transform:translateY(0);}}}}

        @media (max-width:1024px){{
            .create-form{{grid-template-columns:repeat(2,minmax(170px,1fr));}}
            .results-list{{grid-template-columns:repeat(auto-fill,190px);}}
        }}
        @media (max-width:860px){{
            .results-list{{grid-template-columns:repeat(auto-fill,170px);}}
        }}
        @media (max-width:640px){{
            .page{{padding:26px 16px 48px;}}
            .library-title{{font-size:2.05rem;}}
            .create-trigger{{height:auto;padding:14px 16px;}}
            .create-copy span{{white-space:normal;}}
            .create-form{{grid-template-columns:1fr;}}
            .search-bar{{height:auto;padding:10px;gap:10px;flex-wrap:wrap;}}
            .search-input{{min-height:42px;}}
            .search-btn{{width:100%;}}
            .inline-form{{width:100%;flex-wrap:wrap;justify-content:flex-end;}}
            .inline-form input{{flex:1;min-width:0;}}
            .category-grid{{gap:10px;justify-content:center;}}
            .category-tile{{height:98px;}}
            .category-tile{{flex-basis:130px;}}
            .category-tile-button{{padding:10px;}}
            .category-tile-icon{{font-size:1.08rem;}}
            .category-tile-name{{font-size:.86rem;max-width:108px;}}
            .category-delete-form{{top:6px;right:6px;}}
            .category-delete-btn{{width:18px;height:18px;font-size:.78rem;}}
            .results-list{{grid-template-columns:1fr;}}
            .food-result-photo{{height:160px;}}
            .food-photo-placeholder{{height:160px;}}
        }}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
        <h1 class="library-title">BIBLIOTECA DE ALIMENTOS</h1>

        <button type="button" id="create_food_trigger" class="create-trigger" aria-expanded="false" aria-controls="create_food_panel">
            <span class="create-left">
                <span class="create-plus">+</span>
                <span class="create-copy">
                    <strong>Crear nuevo alimento</strong>
                    <span>Añade un alimento a tu biblioteca.</span>
                </span>
            </span>
            <span class="create-arrow">→</span>
        </button>

        <section id="create_food_panel" class="create-panel" aria-hidden="true">
            <form method="post" action="/add" class="create-form">
                <input name="name" placeholder="Nombre" required />
                <select name="brand">
                    <option value="">Marca (opcional)</option>
                    {brand_options}
                </select>
                <select name="category">
                    <option value="">Categoría (opcional)</option>
                    {category_options}
                </select>
                <select name="has_gluten">
                    <option value="">Gluten (no indicado)</option>
                    <option value="1">Con gluten</option>
                    <option value="0">Sin gluten</option>
                </select>
                <input name="calories" placeholder="Kcal" />
                <input name="protein" placeholder="Proteínas (g)" />
                <input name="carbs" placeholder="Hidratos (g)" />
                <input name="fats" placeholder="Grasas (g)" />
                <select name="nutrition_mode" id="nutrition_mode">
                    <option value="per100">Valores por 100 g/ml</option>
                    <option value="unit">Valores por unidad</option>
                </select>
                <select name="per100_unit" id="per100_unit">
                    <option value="g">Base 100 g</option>
                    <option value="ml">Base 100 ml</option>
                </select>
                <label class="full" style="display:flex;align-items:center;gap:10px;color:#1f7a40;font-weight:700;">
                    <input type="checkbox" name="is_verified" value="1" style="width:18px;height:18px;" />
                    Marcar como verificado (información nutricional revisada)
                </label>
                <div class="nutrition-hint full" id="nutrition_hint">Introduce calorías y macros por 100 g o 100 ml según base elegida.</div>
                <input class="full" type="file" accept="image/*" id="food_photo_file" />
                <input type="hidden" name="photo_data_url" id="food_photo_data_url" />
                <div class="photo-preview full"><img id="food_photo_preview" alt="Vista previa" /><span id="food_photo_text">Sin foto seleccionada</span></div>
                <button class="full" type="submit">Guardar alimento</button>
            </form>
        </section>

        <section class="search-wrap">
            <div class="search-bar">
                <span class="search-icon">🔍</span>
                <input id="library_search_input" class="search-input" type="search" placeholder="Buscar alimento..." autocomplete="off" />
                <button id="library_search_btn" class="search-btn" type="button">Buscar</button>
            </div>
        </section>

        <div class="spacer-large"></div>

        <section>
            <div class="section-head">
                <h2 class="section-kicker">CATEGORÍAS</h2>
                <form method="post" action="/add_category" class="inline-form">
                    <input name="name" placeholder="Nueva categoría" required />
                    <button type="submit" class="head-btn">Nueva categoría</button>
                </form>
            </div>
            <div class="category-grid">
                {category_cards_html}
            </div>
        </section>

        <div class="separator"></div>

        <section>
            <div class="results-head">
                <h2 class="results-title">RESULTADOS</h2>
                <div class="results-total"><span id="results_count">{len(foods_sorted)}</span> alimentos</div>
            </div>
            <div class="results-controls">
                <label for="results_order">Orden</label>
                <select id="results_order">
                    <option value="az" selected>A → Z</option>
                </select>
            </div>
            <div id="results_list" class="results-list">
                {''.join(food_cards_html) if food_cards_html else '<div class="empty-note">Todavía no hay alimentos en tu biblioteca.</div>'}
            </div>
        </section>
    </div>
    <script>
        (function() {{
            const createTrigger = document.getElementById('create_food_trigger');
            const createPanel = document.getElementById('create_food_panel');
            const fileInput = document.getElementById('food_photo_file');
            const hidden = document.getElementById('food_photo_data_url');
            const preview = document.getElementById('food_photo_preview');
            const text = document.getElementById('food_photo_text');
            const modeSel = document.getElementById('nutrition_mode');
            const unitSel = document.getElementById('per100_unit');
            const hint = document.getElementById('nutrition_hint');
            const searchInput = document.getElementById('library_search_input');
            const searchBtn = document.getElementById('library_search_btn');
            const resultCards = Array.from(document.querySelectorAll('.food-result-card'));
            const resultCount = document.getElementById('results_count');
            const categoryTiles = Array.from(document.querySelectorAll('.category-tile-button'));
            const categoryDeleteButtons = Array.from(document.querySelectorAll('.category-delete-btn'));
            const categoryDeleteForms = Array.from(document.querySelectorAll('.category-delete-form'));

            function setPanelOpen(open) {{
                if (!createPanel || !createTrigger) return;
                createPanel.classList.toggle('open', open);
                createPanel.setAttribute('aria-hidden', open ? 'false' : 'true');
                createTrigger.setAttribute('aria-expanded', open ? 'true' : 'false');
            }}

            if (createTrigger && createPanel) {{
                createTrigger.addEventListener('click', () => setPanelOpen(!createPanel.classList.contains('open')));
            }}

            function toggleMode() {{
                const isUnit = modeSel && modeSel.value === 'unit';
                if (unitSel) unitSel.disabled = isUnit;
                if (hint) {{
                    hint.textContent = isUnit
                        ? 'Introduce calorías y macros por 1 unidad del alimento.'
                        : 'Introduce calorías y macros por 100 g o 100 ml según base elegida.';
                }}
            }}
            toggleMode();
            if (modeSel) modeSel.addEventListener('change', toggleMode);

            if (fileInput && hidden && preview && text) {{
                fileInput.addEventListener('change', () => {{
                    const file = fileInput.files && fileInput.files[0];
                    if (!file) {{
                        hidden.value = '';
                        preview.style.display = 'none';
                        preview.removeAttribute('src');
                        text.textContent = 'Sin foto seleccionada';
                        return;
                    }}
                    const reader = new FileReader();
                    reader.onload = () => {{
                        hidden.value = String(reader.result || '');
                        preview.src = hidden.value;
                        preview.style.display = 'inline-block';
                        text.textContent = file.name;
                    }};
                    reader.readAsDataURL(file);
                }});
            }}

            function normalize(v) {{
                return String(v || '')
                    .toLowerCase()
                    .normalize('NFD')
                    .replace(/[\u0300-\u036f]/g, '')
                    .trim();
            }}

            function applySearch() {{
                const q = normalize(searchInput ? searchInput.value : '');
                let visible = 0;
                resultCards.forEach((card) => {{
                    const blob = [card.dataset.name || '', card.dataset.brand || '', card.dataset.category || ''].join(' ');
                    const ok = !q || blob.includes(q);
                    card.style.display = ok ? '' : 'none';
                    if (ok) visible += 1;
                }});
                if (resultCount) resultCount.textContent = String(visible);
            }}

            if (searchInput) searchInput.addEventListener('input', applySearch);
            if (searchBtn) searchBtn.addEventListener('click', applySearch);
            if (searchInput) searchInput.addEventListener('keydown', (ev) => {{
                if (ev.key === 'Enter') {{
                    ev.preventDefault();
                    applySearch();
                }}
            }});

            categoryTiles.forEach((tile) => {{
                tile.addEventListener('click', () => {{
                    const cat = tile.getAttribute('data-category') || '';
                    if (searchInput) {{
                        searchInput.value = cat;
                        applySearch();
                        searchInput.focus();
                    }}
                }});
            }});

            categoryDeleteButtons.forEach((btn) => {{
                btn.addEventListener('click', (ev) => {{
                    ev.stopPropagation();
                }});
            }});

            categoryDeleteForms.forEach((form) => {{
                form.addEventListener('submit', (ev) => {{
                    const ok = window.confirm('¿Seguro que quieres eliminar esta categoría?');
                    if (!ok) ev.preventDefault();
                }});
            }});

            resultCards.forEach((card) => {{
                card.addEventListener('click', (ev) => {{
                    if (ev.target.closest('a, button, form')) return;
                    const url = card.getAttribute('data-open-url');
                    if (url) window.location.href = url;
                }});
            }});

            applySearch();
        }})();
    </script>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Exercises page
        if path == '/exercises':
            exercises = get_exercises()
            categories = get_exercise_categories()
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            rows_html = []
            grouped_exercises = {}
            for e in exercises:
                video_url = (e[7] or '').strip()
                if video_url:
                    safe_url = html.escape(video_url, quote=True)
                    video_cell = f'<a class="action-link" href="{safe_url}" target="_blank" rel="noopener noreferrer">Ver video</a>'
                else:
                    video_cell = '-'
                machine_url = (e[8] or '').strip()
                if machine_url:
                    safe_machine_url = html.escape(machine_url, quote=True)
                    machine_cell = f'<a class="action-link" href="{safe_machine_url}" target="_blank" rel="noopener noreferrer">Ver máquina</a>'
                else:
                    machine_cell = '-'

                group_names = []
                primary_group = (e[6] or '').strip()
                secondary_group = (e[9] or '').strip()
                if primary_group:
                    group_names.append(primary_group)
                if secondary_group and secondary_group not in group_names:
                    group_names.append(secondary_group)
                if not group_names:
                    group_names = ['Sin grupo muscular']
                for group_name in group_names:
                    grouped_exercises.setdefault(group_name, []).append(e)

                group_cell = ' + '.join([html.escape(g) for g in group_names])

                rows_html.append(
                    '<tr>' +
                    f'<td>{html.escape(e[1])}</td>' +
                    f'<td>{group_cell}</td>' +
                    f'<td>{video_cell}</td>' +
                    f'<td>{machine_cell}</td>' +
                    '<td>' +
                    f'<a class="action-link" href="/edit_exercise?id={e[0]}">Editar</a>' +
                    f'<form method="post" action="/delete_exercise" style="display:inline" onsubmit="return confirm(\'¿Seguro que quieres borrar este ejercicio?\')">'
                    f'<input type="hidden" name="id" value="{e[0]}" />'
                    '<button class="action-link" type="submit" style="background:none;border:none;padding:0;cursor:pointer">Borrar</button>' +
                    '</form>' +
                    '</td>' +
                    '</tr>'
                )

            grouped_blocks = []
            ordered_group_names = sorted(grouped_exercises.keys(), key=lambda n: (n == 'Sin grupo muscular', n.casefold()))
            for group_name in ordered_group_names:
                group_items = grouped_exercises[group_name]
                group_items_sorted = sorted(group_items, key=lambda ex: (str(ex[1] or '').casefold(), ex[0]))
                item_links = ''.join([
                    '<li>'
                    f'<a class="group-ex-link" href="/edit_exercise?id={ex[0]}">{html.escape(ex[1] or "Ejercicio")}</a>'
                    '</li>'
                    for ex in group_items_sorted
                ])
                grouped_blocks.append(
                    '<details class="group-chip">'
                    f'<summary>{html.escape(group_name)} <span class="group-count">{len(group_items)}</span></summary>'
                    f'<ul class="group-ex-list">{item_links}</ul>'
                    '</details>'
                )

            category_options = ''.join([f'<option value="{c[0]}">{html.escape(c[1])}</option>' for c in categories])
            secondary_category_options = '<option value="">-- Segundo grupo muscular (opcional) --</option>' + category_options
            category_list = ''.join([
                f'<li><span class="muscle-name">{html.escape(c[1])}</span><form method="post" action="/delete_exercise_category" class="muscle-delete-form" style="display:inline-flex;width:auto;grid-template-columns:none;"><input type="hidden" name="id" value="{c[0]}" /><button class="muscle-delete-btn" type="submit" style="width:86px;min-width:86px;max-width:86px;padding:6px 10px;">Borrar</button></form></li>'
                for c in categories
            ])

            page = f'''
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Ejercicios</title>
  <style>
        body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
    .page{{max-width:1100px;margin:0 auto;padding:28px;}}
    h1{{margin:0 0 12px;font-size:2.2rem;letter-spacing:-.03em;}}
        h2{{margin:28px 0 12px;font-size:1.2rem;color:#6d7480;}}
        .section-card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:22px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
    form{{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));align-items:start;}}
    input, select, button{{font:inherit;outline:none;}}
        input, select{{padding:12px 14px;border:1px solid #d8dde6;border-radius:12px;background:#fff;color:#101318;}}
    select{{appearance:none;}}
        button{{padding:13px 18px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
        button:hover{{background:#232933;transform:translateY(-1px);}}
        .message{{padding:14px 16px;border-radius:14px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:20px;}}
    .grid-list{{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;list-style:none;padding:0;margin:0;}}
        .grid-list li{{padding:12px;border:1px solid #e8ebef;border-radius:12px;background:#fff;display:flex;flex-direction:column;justify-content:space-between;align-items:flex-start;min-height:140px;color:#101318;box-shadow:0 8px 18px rgba(16,19,24,.04);}}
        .muscle-name{{font-size:1rem;font-weight:800;line-height:1.2;word-break:break-word;}}
        .muscle-delete-form{{display:flex !important;width:auto !important;margin-top:10px;align-self:flex-start;}}
        .muscle-delete-btn{{
            display:inline-flex !important;
            align-items:center;
            justify-content:center;
            width:86px !important;
            min-width:86px !important;
            max-width:86px !important;
            padding:6px 10px !important;
            border-radius:8px !important;
            border:1px solid #efcfd2 !important;
            background:#fff4f4 !important;
            color:#8b1b20 !important;
            font-size:.8rem !important;
            font-weight:700;
            line-height:1;
            cursor:pointer;
            box-shadow:none !important;
        }}
        .muscle-delete-btn:hover{{background:#fee2e2 !important;transform:none !important;}}
        .action-button{{display:inline-flex;align-items:center;justify-content:center;padding:8px 12px;border-radius:12px;border:1px solid #d8dde6;background:#fff;color:#101318;text-decoration:none;font-weight:600;font-size:.95rem;cursor:pointer;transition:transform .18s ease,background .18s ease,border-color .18s ease;}}
        .action-button:hover{{background:#f5f7fa;transform:translateY(-1px);border-color:#d8dde6;}}
        .action-edit{{border:none;background:#101318;color:#fff;}}
        .action-edit:hover{{background:#232933;}}
        .action-delete{{border:none;background:#8b1b20;color:#fff;}}
        .action-delete:hover{{background:#6f1116;}}
        table{{width:100%;border-collapse:collapse;margin-top:16px;background:#fff;border-radius:16px;overflow:hidden;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
    tbody td{{color:#23160f !important;font-weight:600;}}
        th,td{{padding:14px 16px;text-align:left;border-bottom:1px solid #e8ebef;}}
        th{{background:#f3f5f8;font-weight:700;color:#101318;border-bottom:1px solid #e8ebef;}}
        tr:hover{{background:#f8fafc;}}
    .actions form{{display:inline;}}
        .action-link{{color:#101318;text-decoration:none;font-weight:700;margin-right:10px;}}
                .group-grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:8px;}}
                .group-chip{{border:1px solid #d7deea;border-radius:12px;background:#fff;overflow:hidden;}}
                .group-chip summary{{list-style:none;cursor:pointer;padding:8px 10px;background:#f8fafc;font-weight:800;font-size:.82rem;line-height:1.2;display:flex;justify-content:space-between;align-items:center;}}
                .group-chip summary::-webkit-details-marker{{display:none;}}
                .group-chip[open] summary{{background:#eef3fb;border-bottom:1px solid #dbe5f4;}}
                .group-count{{display:inline-flex;align-items:center;justify-content:center;min-width:18px;height:18px;padding:0 4px;border-radius:999px;background:#101318;color:#fff;font-size:.62rem;font-weight:800;}}
                .group-ex-list{{margin:0;padding:8px 10px 10px 22px;background:#fff;}}
                .group-ex-list li{{margin:4px 0;line-height:1.15;}}
                .group-ex-link{{color:#101318;text-decoration:none;font-weight:600;font-size:.8rem;}}
                .group-ex-link:hover{{text-decoration:underline;}}
  </style>
</head>
<body>
  <div class="page">
    {home_link()}
    <h1>🏋️ Base de datos de ejercicios</h1>
    {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
        <section class="section-card" style="margin-bottom:16px;display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;">
            <div>
                <h2 style="margin:0 0 4px;">📋 Creación de rutinas</h2>
                <div style="color:#6d7480;">Crea rutinas y organiza ejercicios por día.</div>
            </div>
            <a class="action-button action-edit" href="/routines">Abrir creador</a>
        </section>
    <section class="section-card">
    <h2>➕ Añadir ejercicio</h2>
      <form method="post" action="/add_exercise">
        <input name="name" placeholder="Nombre" required />
                <select name="category_id" required>
                                        <option value="">-- Selecciona grupo muscular --</option>
          {category_options}
        </select>
                                <select name="category_id_2">
                    {secondary_category_options}
                </select>
                <input name="video_url" placeholder="Link de video (YouTube o propio)" />
                                <input name="machine_url" placeholder="Link de la máquina" />
        <button type="submit">Añadir ejercicio</button>
      </form>
    </section>

    <section class="section-card">
        <h2>🏷️ Grupos musculares</h2>
      <form method="post" action="/add_exercise_category" style="display:grid;grid-template-columns:1fr auto;gap:12px;align-items:center;margin-bottom:16px;">
                <input name="name" placeholder="Nuevo grupo muscular" required />
                <button type="submit">Crear grupo muscular</button>
      </form>
      <ul class="grid-list">
        {category_list}
      </ul>
    </section>

        <section class="section-card">
            <h2>🧩 Ejercicios por grupo muscular</h2>
            {'<div class="group-grid">' + ''.join(grouped_blocks) + '</div>' if grouped_blocks else '<p>No hay ejercicios registrados todavía.</p>'}
        </section>

        <section class="section-card" style="clear:both;">
            <table>
                                                                <thead><tr><th>Nombre</th><th>Grupo muscular</th><th>Video</th><th>Máquina</th><th>Acciones</th></tr></thead>
        <tbody>
          {''.join(rows_html)}
        </tbody>
      </table>
    </section>
  </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Routines page
        if path == '/routines':
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            routines = get_routines()
            exercises = get_exercises()
            clients = sorted(get_clients(), key=lambda c: (str(c[1] or '').casefold(), c[0]))
            routine_id = q.get('routine_id', [''])[0]
            selected_routine = None
            selected_is_template = True
            items = []
            if routine_id:
                try:
                    routine_id_i = int(routine_id)
                except Exception:
                    routine_id_i = None
                else:
                    selected_routine = get_routine_by_id(routine_id_i)
                    if selected_routine:
                        selected_is_template = int(selected_routine[4] or 0) == 1
                        items = get_routine_items(routine_id_i)

            routine_editor_html = ''
            if selected_routine:
                routine_name = selected_routine[1]
                routine_desc = selected_routine[2] or ''
                client_assign_options = ''.join([
                    f'<option value="{c[0]}">{html.escape(c[1] or "Cliente")}</option>'
                    for c in clients
                ])
                routine_day_rows = get_routine_days(routine_id_i)
                if not routine_day_rows:
                    routine_day_rows = get_default_routine_days()

                grouped_by_day_index = {int(day_index): [] for day_index, _day_name, _day_type in routine_day_rows}
                fallback_day_index_by_name = {(day_name or '').strip(): int(day_index) for day_index, day_name, _day_type in routine_day_rows}
                for item in items:
                    try:
                        item_day_index = int(item[9]) if int(item[9]) >= 0 else None
                    except Exception:
                        item_day_index = None
                    if item_day_index is None:
                        item_day_index = fallback_day_index_by_name.get((item[2] or '').strip(), 0)
                    grouped_by_day_index.setdefault(item_day_index, []).append(item)

                for ex in sorted(exercises, key=lambda row: normalize_text(row[1] or '')):
                    category_main = (ex[6] or '').strip()
                    category_secondary = (ex[9] or '').strip()
                    category_parts = [c for c in [category_main, category_secondary] if c]
                    category_text = ' + '.join(category_parts) if category_parts else 'Sin grupo muscular'
                exercise_search_options = [
                    {
                        'value': int(ex[0]),
                        'label': f'{(ex[1] or "Ejercicio")} ({(" + ".join([c for c in [(ex[6] or "").strip(), (ex[9] or "").strip()] if c]) or "Sin grupo muscular")})'
                    }
                    for ex in sorted(exercises, key=lambda row: normalize_text(row[1] or ''))
                ]
                exercise_search_options_json = json.dumps(exercise_search_options, ensure_ascii=False).replace('</', '<\\/')

                day_cards = []
                for day_index, day_name, day_type in routine_day_rows:
                    day_index_i = int(day_index)
                    normalized_day_type = 'rest' if str(day_type or '').strip().lower() == 'rest' else 'train'
                    status_label = 'Entreno' if normalized_day_type == 'train' else 'Descanso'

                    cards_html = []
                    sorted_day_items = sorted(grouped_by_day_index.get(day_index_i, []), key=lambda row: (row[8], row[0]))
                    for exercise_index, item in enumerate(sorted_day_items, start=1):
                        item_id, _routine_id, _day_name, _exercise_id, exercise_name, sets_text, reps_text, notes, _sort_order, _item_day_index = item
                        safe_sets = html.escape(sets_text or '')
                        safe_reps = html.escape(reps_text or '')
                        cards_html.append(
                            f'<div class="routine-item-row" draggable="true" data-item-id="{item_id}">'
                            '<button type="button" class="routine-drag-handle" title="Arrastra para mover" aria-label="Arrastra para mover">⋮⋮</button>'
                            '<div class="routine-item-main">'
                            f'<p class="routine-item-name"><span class="routine-item-order">{exercise_index}.</span> {html.escape(exercise_name or "Ejercicio")}</p>'
                            '<div class="routine-item-editline">'
                            '<label class="routine-item-label">Series '
                            f'<input class="routine-item-edit" data-field="sets_text" value="{safe_sets}" placeholder="-" />'
                            '</label>'
                            '<label class="routine-item-label">Reps '
                            f'<input class="routine-item-edit" data-field="reps_text" value="{safe_reps}" placeholder="-" />'
                            '</label>'
                            '</div>'
                            '</div>'
                            f'<form method="post" action="/delete_routine_item" class="routine-item-delete-form"><input type="hidden" name="id" value="{item_id}" /><input type="hidden" name="routine_id" value="{routine_id}" /><button type="submit" class="routine-item-delete">Eliminar</button></form>'
                            '</div>'
                        )

                    cards_html_rendered = ''.join(cards_html) or '<p style="color:#6d7480;">Sin ejercicios para este día.</p>'
                    day_cards.append(
                        f'<section id="routine-day-{day_index_i}" class="section-card day-card">'
                        '<div class="day-header-row">'
                        f'<h2 class="day-title" style="margin:0;">🏷️ Día {day_index_i + 1} · <span class="day-name-inline" contenteditable="false" data-routine-id="{routine_id}" data-day-index="{day_index_i}">{html.escape(day_name or f"Dia {day_index_i + 1}")}</span></h2>'
                        '<div class="day-header-actions">'
                        '<div class="day-type-segment">'
                        f'<form method="post" action="/update_routine_day" class="segment-form">'
                        f'<input type="hidden" name="routine_id" value="{routine_id}" />'
                        f'<input type="hidden" name="day_index" value="{day_index_i}" />'
                        f'<input type="hidden" name="day_name" value="{html.escape(day_name or "")}" />'
                        '<input type="hidden" name="day_type" value="train" />'
                        f'<button type="submit" class="segment-btn train {"active" if normalized_day_type == "train" else ""}">Entreno</button>'
                        '</form>'
                        f'<form method="post" action="/update_routine_day" class="segment-form">'
                        f'<input type="hidden" name="routine_id" value="{routine_id}" />'
                        f'<input type="hidden" name="day_index" value="{day_index_i}" />'
                        f'<input type="hidden" name="day_name" value="{html.escape(day_name or "")}" />'
                        '<input type="hidden" name="day_type" value="rest" />'
                        f'<button type="submit" class="segment-btn rest {"active" if normalized_day_type == "rest" else ""}">Descanso</button>'
                        '</form>'
                        '</div>'
                        f'<button type="button" class="action-button action-edit open-add-exercise" data-day-index="{day_index_i}" data-day-name="{html.escape(day_name or "")}">+ Añadir ejercicio</button>'
                        '</div>'
                        f'<div class="routine-items" data-routine-id="{routine_id}" data-day-index="{day_index_i}">{cards_html_rendered}</div>'
                        '</section>'
                    )

                assign_form_html = ''
                if selected_is_template:
                    assign_form_html = f'''
            <form method="post" action="/assign_client_training" class="routine-assign-form">
                <input type="hidden" name="routine_id" value="{routine_id}" />
                <input type="hidden" name="return_to" value="/routines?routine_id={routine_id}" />
                <select name="client_id" required>
                    <option value="">Asignar esta rutina a cliente...</option>
                    {client_assign_options}
                </select>
                <input name="start_date" type="date" placeholder="Inicio" />
                <input name="end_date" type="date" placeholder="Fin" />
                <input name="notes" placeholder="Notas (opcional)" />
                <button type="submit">Asignar a cliente</button>
            </form>
'''

                routine_editor_html = f'''
    <section class="section-card">
      <h2>Editar rutina: {html.escape(routine_name)}</h2>
      <p style="color:#6d7480;margin-top:-4px;">{html.escape(routine_desc or 'Sin descripción')}</p>
            <form method="post" action="/update_routine_name" class="routine-name-form">
                <input type="hidden" name="routine_id" value="{routine_id}" />
                <input type="hidden" name="return_to" value="/routines?routine_id={routine_id}" />
                <label class="routine-name-label">Nombre visible para el cliente
                    <input name="name" value="{html.escape(routine_name)}" placeholder="Nombre de la rutina" required />
                </label>
                <button type="submit">Guardar nombre</button>
            </form>
            <div style="margin:8px 0 14px;">
                <a class="action-button action-edit" href="/export_routine_pdf/rutina_{routine_id}.pdf" target="_blank">Exportar PDF</a>
            </div>
            {assign_form_html}
    </section>
    {''.join(day_cards)}
    <div id="exercise-modal" class="exercise-modal" hidden>
      <div class="exercise-modal-backdrop"></div>
      <div class="exercise-modal-card">
        <h3 id="exercise-modal-title">Añadir ejercicio</h3>
        <form method="post" action="/add_routine_item" class="exercise-modal-form">
          <input type="hidden" name="routine_id" value="{routine_id}" />
          <input type="hidden" name="day_index" id="modal_day_index" />
          <input type="hidden" name="day_name" id="modal_day_name" />
                    <input type="hidden" name="exercise_id" id="exercise_id_hidden" />
                    <div class="exercise-search-wrap">
                        <input id="exercise_search" type="text" placeholder="Buscar ejercicio por nombre o grupo" autocomplete="off" />
                        <div id="exercise_search_results" class="exercise-search-results" hidden></div>
                    </div>
          <input name="sets_text" placeholder="Número de series" required />
          <input name="reps_text" placeholder="Número de repeticiones" required />
          <input name="notes" placeholder="Notas (opcional)" />
          <div class="modal-actions">
            <button type="button" id="exercise-modal-cancel">Cancelar</button>
            <button type="submit">Guardar</button>
          </div>
        </form>
      </div>
    </div>
        <script>
            (function() {{
                const modal = document.getElementById('exercise-modal');
                const modalTitle = document.getElementById('exercise-modal-title');
                const modalDayIndex = document.getElementById('modal_day_index');
                const modalDayName = document.getElementById('modal_day_name');
                const modalCancel = document.getElementById('exercise-modal-cancel');
                const modalBackdrop = modal ? modal.querySelector('.exercise-modal-backdrop') : null;
                const exerciseSearch = document.getElementById('exercise_search');
                const exerciseSearchResults = document.getElementById('exercise_search_results');
                const exerciseHiddenInput = document.getElementById('exercise_id_hidden');
                const exerciseModalForm = modal ? modal.querySelector('.exercise-modal-form') : null;
                const baseExerciseOptions = {exercise_search_options_json};
                let lastFilteredOptions = [];

                function hideExerciseResults() {{
                    if (!exerciseSearchResults) return;
                    exerciseSearchResults.innerHTML = '';
                    exerciseSearchResults.setAttribute('hidden', 'hidden');
                }}

                function renderExerciseResults(filterText) {{
                    if (!exerciseSearchResults) return;
                    const needle = String(filterText || '').toLowerCase().trim();
                    if (!needle) {{
                        lastFilteredOptions = [];
                        if (exerciseHiddenInput) exerciseHiddenInput.value = '';
                        hideExerciseResults();
                        return;
                    }}

                    const filtered = baseExerciseOptions
                        .filter((item) => item.label.toLowerCase().includes(needle))
                        .slice(0, 20);
                    lastFilteredOptions = filtered;

                    exerciseSearchResults.innerHTML = '';
                    if (!filtered.length) {{
                        if (exerciseHiddenInput) exerciseHiddenInput.value = '';
                        hideExerciseResults();
                        return;
                    }}

                    filtered.forEach((item, idx) => {{
                        const row = document.createElement('button');
                        row.type = 'button';
                        row.className = 'exercise-search-item' + (idx === 0 ? ' active' : '');
                        row.textContent = item.label;
                        row.addEventListener('click', () => {{
                            if (exerciseSearch) exerciseSearch.value = item.label;
                            if (exerciseHiddenInput) exerciseHiddenInput.value = item.value;
                            hideExerciseResults();
                        }});
                        exerciseSearchResults.appendChild(row);
                    }});
                    if (exerciseHiddenInput) exerciseHiddenInput.value = '';
                    exerciseSearchResults.removeAttribute('hidden');
                }}

                function closeModal() {{
                    if (!modal) return;
                    hideExerciseResults();
                    modal.setAttribute('hidden', 'hidden');
                }}

                function openModal(dayIndex, dayName) {{
                    if (!modal) return;
                    modalDayIndex.value = dayIndex || '0';
                    modalDayName.value = dayName || '';
                    modalTitle.textContent = 'Añadir ejercicio - ' + (dayName || 'Día');
                    if (exerciseSearch) exerciseSearch.value = '';
                    if (exerciseHiddenInput) exerciseHiddenInput.value = '';
                    hideExerciseResults();
                    modal.removeAttribute('hidden');
                    if (exerciseSearch) exerciseSearch.focus();
                }}

                function bindAddExerciseButton(btn) {{
                    if (!btn) return;
                    btn.addEventListener('click', () => openModal(btn.dataset.dayIndex, btn.dataset.dayName));
                }}

                function applyDayTypeUI(dayCard, dayType, dayName, dayIndex) {{
                    if (!dayCard) return;
                    const normalizedType = dayType === 'rest' ? 'rest' : 'train';

                    dayCard.querySelectorAll('.segment-btn').forEach((button) => {{
                        const isTrainBtn = button.classList.contains('train');
                        const shouldBeActive = (normalizedType === 'train' && isTrainBtn) || (normalizedType === 'rest' && !isTrainBtn);
                        button.classList.toggle('active', shouldBeActive);
                    }});

                    const dayNameInput = dayCard.querySelector('.day-name-inline');
                    if (dayNameInput) {{
                        dayNameInput.dataset.dayType = normalizedType;
                        if (dayName) {{
                            dayNameInput.textContent = dayName;
                            dayNameInput.dataset.lastValue = dayName;
                        }}
                    }}

                    dayCard.querySelectorAll('.segment-form input[name="day_name"]').forEach((input) => {{
                        input.value = dayName || input.value;
                    }});

                    const existingAddBtn = dayCard.querySelector('.open-add-exercise');
                    if (existingAddBtn) {{
                        existingAddBtn.dataset.dayName = dayName || existingAddBtn.dataset.dayName;
                        existingAddBtn.dataset.dayIndex = String(dayIndex || existingAddBtn.dataset.dayIndex || '0');
                    }}
                }}

                function getActiveDayType(dayCard) {{
                    if (!dayCard) return 'train';
                    const activeBtn = dayCard.querySelector('.segment-btn.active');
                    if (!activeBtn) return 'train';
                    return activeBtn.classList.contains('rest') ? 'rest' : 'train';
                }}

                async function saveInlineDayName(inputEl) {{
                    if (!inputEl) return;
                    const dayCard = inputEl.closest('.day-card');
                    const routineId = inputEl.dataset.routineId || '';
                    const dayIndex = inputEl.dataset.dayIndex || '0';
                    const rawName = (inputEl.textContent || '').trim();
                    const parsedDayIndex = parseInt(dayIndex, 10);
                    const fallbackName = Number.isFinite(parsedDayIndex) ? ('Dia ' + String(parsedDayIndex + 1)) : 'Dia';
                    const newName = rawName || fallbackName;
                    const lastValue = inputEl.dataset.lastValue || '';
                    if (newName === lastValue) return;

                    const dayType = getActiveDayType(dayCard);
                    const payload = new URLSearchParams();
                    payload.set('routine_id', routineId);
                    payload.set('day_index', dayIndex);
                    payload.set('day_name', newName);
                    payload.set('day_type', dayType);

                    inputEl.contentEditable = 'false';
                    try {{
                        const response = await fetch('/update_routine_day', {{
                            method: 'POST',
                            headers: {{
                                'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8',
                                'X-Requested-With': 'fetch'
                            }},
                            body: payload.toString()
                        }});
                        if (!response.ok) throw new Error('request_failed');
                        inputEl.textContent = newName;
                        inputEl.dataset.lastValue = newName;
                        applyDayTypeUI(dayCard, dayType, newName, dayIndex);
                    }} catch (_err) {{
                        inputEl.textContent = lastValue || inputEl.textContent;
                    }}
                }}

                function renumberRoutineRows(dayCard) {{
                    if (!dayCard) return;
                    dayCard.querySelectorAll('.routine-item-row').forEach((row, idx) => {{
                        const orderEl = row.querySelector('.routine-item-order');
                        if (orderEl) orderEl.textContent = String(idx + 1) + '.';
                    }});
                }}

                async function persistRoutineOrder(dayCard) {{
                    if (!dayCard) return;
                    const list = dayCard.querySelector('.routine-items');
                    if (!list) return;
                    const routineId = list.dataset.routineId || '';
                    const dayIndex = list.dataset.dayIndex || '0';
                    const itemIds = Array.from(list.querySelectorAll('.routine-item-row'))
                        .map((row) => row.dataset.itemId)
                        .filter(Boolean)
                        .join(',');
                    const payload = new URLSearchParams();
                    payload.set('routine_id', routineId);
                    payload.set('day_index', dayIndex);
                    payload.set('item_ids', itemIds);
                    const response = await fetch('/reorder_routine_items', {{
                        method: 'POST',
                        headers: {{
                            'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8',
                            'X-Requested-With': 'fetch'
                        }},
                        body: payload.toString()
                    }});
                    if (!response.ok) throw new Error('reorder_failed');
                }}

                async function saveRoutineItemRow(row) {{
                    if (!row) return;
                    const itemId = row.dataset.itemId || '';
                    const setsInput = row.querySelector('.routine-item-edit[data-field="sets_text"]');
                    const repsInput = row.querySelector('.routine-item-edit[data-field="reps_text"]');
                    if (!itemId || !setsInput || !repsInput) return;
                    const payload = new URLSearchParams();
                    payload.set('id', itemId);
                    payload.set('sets_text', (setsInput.value || '').trim());
                    payload.set('reps_text', (repsInput.value || '').trim());

                    setsInput.disabled = true;
                    repsInput.disabled = true;
                    try {{
                        const response = await fetch('/update_routine_item', {{
                            method: 'POST',
                            headers: {{
                                'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8',
                                'X-Requested-With': 'fetch'
                            }},
                            body: payload.toString()
                        }});
                        if (!response.ok) throw new Error('save_failed');
                        const meta = row.querySelector('.routine-item-meta');
                        if (meta) {{
                            const s = (setsInput.value || '').trim() || '-';
                            const r = (repsInput.value || '').trim() || '-';
                            meta.textContent = 'Series: ' + s + ' · Reps: ' + r;
                        }}
                    }} catch (_err) {{
                        // keep current text; user can retry by blurring again
                    }} finally {{
                        setsInput.disabled = false;
                        repsInput.disabled = false;
                    }}
                }}

                function bindRoutineItemInteractions() {{
                    let draggingRow = null;

                    document.querySelectorAll('.routine-item-row').forEach((row) => {{
                        row.addEventListener('dragstart', (ev) => {{
                            draggingRow = row;
                            row.classList.add('dragging');
                            if (ev.dataTransfer) ev.dataTransfer.effectAllowed = 'move';
                        }});

                        row.addEventListener('dragend', () => {{
                            row.classList.remove('dragging');
                            draggingRow = null;
                        }});

                        row.addEventListener('dragover', (ev) => {{
                            if (!draggingRow || draggingRow === row) return;
                            if (draggingRow.parentElement !== row.parentElement) return;
                            ev.preventDefault();
                            const rect = row.getBoundingClientRect();
                            const before = ev.clientY < rect.top + rect.height / 2;
                            const parent = row.parentElement;
                            if (before) parent.insertBefore(draggingRow, row);
                            else parent.insertBefore(draggingRow, row.nextSibling);
                        }});

                        row.addEventListener('drop', async (ev) => {{
                            if (!draggingRow) return;
                            ev.preventDefault();
                            const dayCard = row.closest('.day-card');
                            renumberRoutineRows(dayCard);
                            try {{
                                await persistRoutineOrder(dayCard);
                            }} catch (_err) {{
                                window.location.reload();
                            }}
                        }});

                        row.querySelectorAll('.routine-item-edit').forEach((inputEl) => {{
                            inputEl.addEventListener('keydown', (ev) => {{
                                if (ev.key === 'Enter') {{
                                    ev.preventDefault();
                                    inputEl.blur();
                                }}
                            }});
                            inputEl.addEventListener('blur', () => saveRoutineItemRow(row));
                        }});
                    }});
                }}

                async function handleSegmentSubmit(event) {{
                    event.preventDefault();
                    const form = event.currentTarget;
                    if (!form) return;
                    const dayCard = form.closest('.day-card');
                    const dayIndexInput = form.querySelector('input[name="day_index"]');
                    const dayTypeInput = form.querySelector('input[name="day_type"]');
                    const formDayNameInput = form.querySelector('input[name="day_name"]');
                    const dayNameEditor = dayCard ? dayCard.querySelector('.day-name-inline') : null;

                    if (formDayNameInput && dayNameEditor && dayNameEditor.textContent.trim()) {{
                        formDayNameInput.value = dayNameEditor.textContent.trim();
                    }}

                    const payload = new URLSearchParams(new FormData(form));
                    const buttons = dayCard ? Array.from(dayCard.querySelectorAll('.segment-btn')) : [];
                    buttons.forEach((btn) => {{ btn.disabled = true; }});

                    try {{
                        const response = await fetch(form.action, {{
                            method: 'POST',
                            headers: {{
                                'Content-Type': 'application/x-www-form-urlencoded;charset=UTF-8',
                                'X-Requested-With': 'fetch'
                            }},
                            body: payload.toString()
                        }});

                        if (!response.ok) throw new Error('request_failed');

                        applyDayTypeUI(
                            dayCard,
                            (dayTypeInput ? dayTypeInput.value : 'train'),
                            (formDayNameInput ? formDayNameInput.value : ''),
                            (dayIndexInput ? dayIndexInput.value : '0')
                        );
                    }} catch (_err) {{
                        form.submit();
                    }} finally {{
                        buttons.forEach((btn) => {{ btn.disabled = false; }});
                    }}
                }}

                document.querySelectorAll('.open-add-exercise').forEach((btn) => bindAddExerciseButton(btn));
                document.querySelectorAll('.segment-form').forEach((form) => {{
                    form.addEventListener('submit', handleSegmentSubmit);
                }});
                bindRoutineItemInteractions();
                if (exerciseSearch) {{
                    exerciseSearch.addEventListener('input', () => {{
                        const text = exerciseSearch.value;
                        renderExerciseResults(text);

                        // If user typed an exact suggestion label, bind it immediately.
                        const exact = baseExerciseOptions.find((item) => item.label.toLowerCase() === text.toLowerCase().trim());
                        if (exerciseHiddenInput && exact) exerciseHiddenInput.value = exact.value;
                    }});
                    exerciseSearch.addEventListener('keydown', (ev) => {{
                        if (ev.key === 'Enter') {{
                            ev.preventDefault();
                            if (!exerciseSearch.value.trim()) return;
                            const chosenId = exerciseHiddenInput ? String(exerciseHiddenInput.value || '').trim() : '';
                            if (chosenId) {{
                                const selected = baseExerciseOptions.find((item) => String(item.value) === chosenId);
                                if (selected && exerciseSearch) exerciseSearch.value = selected.label;
                                hideExerciseResults();
                                return;
                            }}
                            if (lastFilteredOptions.length) {{
                                exerciseSearch.value = lastFilteredOptions[0].label;
                                if (exerciseHiddenInput) exerciseHiddenInput.value = lastFilteredOptions[0].value;
                                hideExerciseResults();
                            }}
                        }}
                    }});
                }}
                if (exerciseModalForm) {{
                    exerciseModalForm.addEventListener('submit', (ev) => {{
                        const chosenId = exerciseHiddenInput ? String(exerciseHiddenInput.value || '').trim() : '';
                        if (!chosenId) {{
                            ev.preventDefault();
                            if (exerciseSearch) exerciseSearch.focus();
                            alert('Selecciona un ejercicio del buscador antes de guardar.');
                        }}
                    }});
                }}
                document.addEventListener('click', (ev) => {{
                    if (!modal || modal.hasAttribute('hidden')) return;
                    if (!exerciseSearchResults || exerciseSearchResults.hasAttribute('hidden')) return;
                    const target = ev.target;
                    if (exerciseSearch && exerciseSearch.contains(target)) return;
                    if (exerciseSearchResults.contains(target)) return;
                    hideExerciseResults();
                }});
                document.querySelectorAll('.day-name-inline').forEach((inputEl) => {{
                    inputEl.dataset.lastValue = (inputEl.textContent || '').trim();
                    const dayCard = inputEl.closest('.day-card');
                    inputEl.dataset.dayType = getActiveDayType(dayCard);
                    inputEl.addEventListener('click', () => {{
                        inputEl.contentEditable = 'true';
                        inputEl.focus();
                        const selection = window.getSelection();
                        if (selection) {{
                            const range = document.createRange();
                            range.selectNodeContents(inputEl);
                            range.collapse(false);
                            selection.removeAllRanges();
                            selection.addRange(range);
                        }}
                    }});
                    inputEl.addEventListener('blur', () => saveInlineDayName(inputEl));
                    inputEl.addEventListener('keydown', (ev) => {{
                        if (ev.key === 'Enter') {{
                            ev.preventDefault();
                            inputEl.blur();
                        }}
                        if (ev.key === 'Escape') {{
                            ev.preventDefault();
                            inputEl.textContent = inputEl.dataset.lastValue || inputEl.textContent;
                            inputEl.contentEditable = 'false';
                            inputEl.blur();
                        }}
                    }});
                }});
                if (modalCancel) modalCancel.addEventListener('click', closeModal);
                if (modalBackdrop) modalBackdrop.addEventListener('click', closeModal);
            }})();
        </script>
'''

            show_only_selected_editor = bool(selected_routine) and not selected_is_template
            manager_sections_html = ''
            if not show_only_selected_editor:
                manager_sections_html = f'''
    <section class="section-card">
            <h2>➕ Nueva rutina</h2>
            <form method="post" action="/add_routine">
                <input name="name" placeholder="Nombre de la rutina" required />
                <input name="description" placeholder="Descripción" />
                <button type="submit">Crear rutina</button>
            </form>
    </section>
    <section class="section-card">
            <h2>Rutinas existentes</h2>
            <div class="diet-cards">
                                {''.join([f'<div class="diet-card"><div class="diet-card-head"><span class="diet-card-id">#{r[0]}</span><span class="diet-card-date">{html.escape(r[3].split(" ")[0] if r[3] else "")}</span></div><h3 class="diet-card-name">{html.escape(r[1])}</h3><p class="diet-card-desc">{html.escape(r[2] or "Sin descripción")}</p><div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:auto;"><a class="action-button action-edit" href="/routines?routine_id={r[0]}">Abrir creador</a><a class="action-button action-edit" href="/export_routine_pdf/rutina_{r[0]}.pdf" target="_blank">PDF</a><form method="post" action="/delete_routine" style="margin:0;"><input type="hidden" name="id" value="{r[0]}" /><button type="submit" class="action-button action-delete">Borrar</button></form></div></div>' for r in routines]) if routines else '<p style="color:#6d7480;">No hay rutinas creadas todavía.</p>'}
            </div>
    </section>
'''

            routine_summary_html = render_routine_series_summary_html(routine_id_i) if selected_routine else ''

            page = f'''
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Creación de rutinas</title>
  <style>
    body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
    .page{{max-width:1200px;margin:0 auto;padding:28px;}}
    h1{{margin:0 0 12px;font-size:2.2rem;letter-spacing:-.03em;}}
    h2{{margin:0 0 12px;font-size:1.2rem;color:#6d7480;}}
    .section-card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:22px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;margin-bottom:16px;}}
    form{{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));align-items:start;}}
    input, select, button{{font:inherit;outline:none;}}
    input, select{{padding:12px 14px;border:1px solid #d8dde6;border-radius:12px;background:#fff;color:#101318;}}
    select{{appearance:none;}}
    button{{padding:13px 18px;border:none;border-radius:12px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
    button:hover{{background:#232933;transform:translateY(-1px);}}
    .message{{padding:14px 16px;border-radius:14px;background:#fef4ea;color:#4d3217;border:1px solid #f5dcc0;margin-bottom:20px;}}
    .diet-cards{{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:12px;margin-top:10px;}}
    .diet-card{{background:#fff;border:1px solid #e8ebef;border-radius:14px;padding:12px;box-shadow:0 10px 24px rgba(16,19,24,.08);display:flex;flex-direction:column;gap:8px;}}
    .diet-card-head{{display:flex;justify-content:space-between;align-items:center;gap:8px;}}
    .diet-card-id{{font-size:.74rem;font-weight:800;color:#101318;background:#eef2f7;border-radius:999px;padding:2px 8px;}}
    .diet-card-date{{font-size:.76rem;color:#6d7480;font-weight:700;}}
    .diet-card-name{{margin:0;font-size:1rem;line-height:1.2;color:#101318;}}
    .diet-card-desc{{margin:0;color:#6d7480;font-size:.83rem;line-height:1.3;}}
    .action-button{{display:inline-flex;align-items:center;justify-content:center;padding:8px 12px;border-radius:12px;border:1px solid #d8dde6;background:#fff;color:#101318;text-decoration:none;font-weight:600;font-size:.95rem;cursor:pointer;transition:transform .18s ease,background .18s ease,border-color .18s ease;}}
    .action-button:hover{{background:#f5f7fa;transform:translateY(-1px);border-color:#d8dde6;}}
    .action-edit{{border:none;background:#101318;color:#fff;}}
    .action-edit:hover{{background:#232933;}}
    .action-delete{{border:none;background:#8b1b20;color:#fff;}}
    .action-delete:hover{{background:#6f1116;}}
        .day-card{{display:flex;flex-direction:column;gap:12px;}}
        .day-header-row{{display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap;}}
        .day-header-actions{{display:flex;align-items:center;gap:8px;flex-wrap:wrap;}}
        .day-title{{display:flex;align-items:center;gap:6px;flex-wrap:wrap;}}
        .routine-items{{display:flex;flex-direction:column;gap:0;margin-top:4px;border-top:1px solid #eef1f5;width:100%;align-self:stretch;}}
        .routine-item-row{{display:grid;grid-template-columns:18px minmax(0,1fr) auto;column-gap:6px;align-items:center;padding:4px 0;border-bottom:1px solid #eef1f5;width:100%;}}
        .routine-item-row.dragging{{opacity:.45;}}
        .routine-drag-handle{{grid-column:1;border:none;background:transparent;box-shadow:none;color:#9aa2ad;cursor:grab;padding:0 1px;font-size:.9rem;line-height:1;align-self:center;justify-self:start;}}
        .routine-drag-handle:hover{{background:transparent;transform:none;color:#6d7480;}}
        .routine-item-main{{grid-column:2;display:flex;flex-direction:row;gap:10px;min-width:0;align-items:center;justify-self:start;flex-wrap:wrap;}}
        .routine-item-name{{margin:0;font-size:.9rem;font-weight:700;color:#101318;line-height:1.15;}}
        .routine-item-order{{display:inline-block;min-width:1.2em;color:#6d7480;font-weight:800;}}
        .routine-item-editline{{display:flex;align-items:center;gap:6px;flex-wrap:wrap;margin:0;}}
        .routine-item-label{{display:inline-flex;align-items:center;gap:4px;font-size:.74rem;color:#6d7480;font-weight:700;}}
        .routine-item-edit{{width:54px;height:24px;min-height:24px;padding:0 5px;border:1px solid #d8dde6;border-radius:7px;background:#fff;color:#101318;font-size:.76rem;line-height:1;}}
        .routine-item-meta{{display:none;}}
        .routine-item-delete-form{{grid-column:3;margin:0;display:inline-flex;align-self:center;justify-self:end;}}
        .routine-item-delete{{background:transparent;border:none;box-shadow:none;color:#8b1b20;font-size:.78rem;font-weight:700;padding:0;cursor:pointer;}}
        .routine-item-delete:hover{{background:transparent;transform:none;color:#6f1116;}}
        .routine-summary-card{{margin-top:12px;}}
        .routine-summary-card h3{{margin:0 0 10px;font-size:1rem;color:#101318;}}
        .routine-summary-table{{width:100%;border-collapse:collapse;}}
        .routine-summary-table thead th{{text-align:left;padding:8px 10px;background:#f8fafc;border-bottom:1px solid #e8ebef;font-size:.8rem;color:#6d7480;text-transform:uppercase;letter-spacing:.03em;}}
        .routine-summary-table tbody td{{padding:8px 10px;border-bottom:1px solid #eef1f5;font-size:.92rem;}}
        .routine-summary-table tbody td:last-child{{text-align:right;font-weight:800;color:#101318;}}
        .routine-name-form{{display:grid;grid-template-columns:minmax(280px,1fr) auto;gap:8px;align-items:end;margin:8px 0 2px;}}
        .routine-name-label{{display:flex;flex-direction:column;gap:6px;font-size:.78rem;color:#6d7480;font-weight:700;}}
        .routine-name-label input{{padding:10px 12px;border:1px solid #d8dde6;border-radius:10px;background:#fff;color:#101318;}}
        .day-status-pill{{display:inline-flex;align-items:center;justify-content:center;padding:4px 10px;border-radius:999px;font-size:.78rem;font-weight:800;}}
        .day-status-pill.train{{background:#e8f7ed;color:#166534;border:1px solid #b7e3c3;}}
        .day-status-pill.rest{{background:#fef3e8;color:#9a3412;border:1px solid #f8d9bf;}}
        .day-type-segment{{display:inline-flex;align-items:center;border:1px solid #d8dde6;border-radius:12px;overflow:hidden;background:#fff;}}
        .segment-form{{display:block !important;margin:0 !important;}}
        .segment-form input{{display:none;}}
        .segment-btn{{border:none !important;box-shadow:none !important;border-radius:0 !important;padding:8px 12px !important;min-width:96px;font-weight:800;font-size:.82rem;opacity:.5;filter:saturate(.25) contrast(.92);transform:none !important;transition:opacity .16s ease,filter .16s ease,background .16s ease,color .16s ease;}}
        .segment-btn.train{{background:#e7f8ec;color:#166534;}}
        .segment-btn.rest{{background:#ffe9e9;color:#991b1b;}}
        .segment-btn.active{{opacity:1;filter:none;}}
        .segment-btn:not(.active){{background:#edf1f5;color:#6b7280;}}
        .segment-btn:hover{{opacity:.85;}}
        .day-name-inline{{display:inline-block;min-width:110px;padding:2px 8px;border-radius:8px;border:1px dashed transparent;cursor:text;color:#101318;background:transparent;}}
        .day-name-inline:hover{{background:#f5f7fa;border-color:#d8dde6;}}
        .day-name-inline[contenteditable="true"]{{background:#fff;border-color:#101318;outline:none;}}
        .open-add-exercise{{display:inline-flex !important;align-items:center;justify-content:center;width:auto !important;min-width:0 !important;white-space:nowrap;box-shadow:none;padding:10px 12px;}}
        .routine-assign-form{{display:grid;grid-template-columns:minmax(200px,1.2fr) repeat(2,minmax(130px,.8fr)) minmax(180px,1fr) auto;gap:8px;align-items:center;margin-top:6px;}}
        .routine-assign-form input,.routine-assign-form select{{padding:10px 11px;border:1px solid #d8dde6;border-radius:10px;background:#fff;color:#101318;}}
        .routine-assign-form button{{padding:10px 12px;border-radius:10px;box-shadow:none;white-space:nowrap;}}
        .rest-label{{font-size:.86rem;font-weight:700;color:#9a3412;background:#fef3e8;border:1px solid #f8d9bf;padding:8px 10px;border-radius:10px;}}
        .exercise-modal{{position:fixed;inset:0;z-index:999;display:flex;align-items:center;justify-content:center;padding:18px;overflow:auto;}}
        .exercise-modal[hidden]{{display:none;}}
        .exercise-modal-backdrop{{position:absolute;inset:0;background:rgba(15,23,42,.42);}}
        .exercise-modal-card{{position:relative;background:#fff;border:1px solid #d8dde6;border-radius:16px;box-shadow:0 18px 40px rgba(16,19,24,.22);max-width:560px;width:min(560px,calc(100vw - 28px));max-height:calc(100vh - 28px);overflow:auto;padding:16px;box-sizing:border-box;}}
        .exercise-modal-card h3{{margin:0 0 12px;font-size:1.05rem;color:#101318;}}
        .exercise-modal-form{{display:flex;flex-direction:column;gap:10px;width:100%;min-width:0;}}
        .exercise-modal-form > *{{min-width:0;}}
        .exercise-modal-form input,.exercise-modal-form select{{padding:12px 14px;border:1px solid #d8dde6;border-radius:12px;background:#fff;color:#101318;width:100%;max-width:100%;box-sizing:border-box;}}
        .exercise-search-wrap{{display:flex;flex-direction:column;gap:6px;width:100%;}}
        .exercise-modal-form #exercise_search{{display:block;width:100% !important;max-width:100% !important;min-height:46px;box-sizing:border-box;}}
        .exercise-search-results{{display:flex;flex-direction:column;gap:4px;max-height:220px;overflow:auto;padding:0;border:none;background:transparent;box-shadow:none;}}
        .exercise-search-results[hidden]{{display:none !important;}}
        .exercise-search-item{{display:block;width:100%;text-align:left;padding:10px 12px;border:1px solid #d8dde6;background:#f3f5f8;color:#101318;border-radius:12px;cursor:pointer;font-size:.92rem;font-weight:600;box-shadow:none;transform:none !important;}}
        .exercise-search-item.active{{background:#e8edf5;}}
        .exercise-search-item:hover{{background:#e3e9f2;}}
        .exercise-search-empty{{padding:9px 10px;color:#6d7480;font-size:.9rem;font-weight:600;}}
        .modal-actions{{display:flex;justify-content:flex-end;gap:8px;flex-wrap:wrap;}}
        .modal-actions button{{padding:10px 14px;width:auto !important;min-width:110px;box-shadow:none;}}
        @media (max-width:640px){{
            .exercise-modal{{padding:10px;align-items:flex-start;}}
            .exercise-modal-card{{width:calc(100vw - 20px);max-height:calc(100vh - 20px);margin-top:8px;padding:14px;}}
            .modal-actions button{{flex:1 1 auto;min-width:0;}}
            .routine-assign-form{{grid-template-columns:1fr;}}
            .routine-name-form{{grid-template-columns:1fr;}}
            .routine-item-row{{grid-template-columns:16px minmax(0,1fr);row-gap:3px;column-gap:5px;align-items:flex-start;}}
            .routine-item-main{{grid-column:2;gap:6px;align-items:flex-start;}}
            .routine-item-delete-form{{grid-column:2;justify-self:start;}}
            .routine-item-edit{{width:50px;height:23px;min-height:23px;}}
        }}
  </style>
</head>
<body>
  <div class="page">
    {home_link()}
        <h1>{'📋 Edición de rutina de cliente' if show_only_selected_editor else '📋 Creación de rutinas'}</h1>
    {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
        {manager_sections_html}
    {routine_editor_html}
        {routine_summary_html}
  </div>
</body>
</html>
'''
            body = page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Edit food
        if path == '/edit':
            q = urllib.parse.parse_qs(parsed.query)
            fid = q.get('id', [''])[0]
            try:
                fid_i = int(fid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            rows = [r for r in get_foods() if r[0] == fid_i]
            if not rows:
                self.send_response(404)
                self.end_headers()
                return
            r = rows[0]
            fid, name, brand, category, cal, prot, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, is_verified_row, _has_gluten_row = r
            serving_amount, serving_unit = split_serving_size(serving)
            cats = get_categories()
            brands = get_brands()
            conn_meta = sqlite3.connect(DB_PATH)
            cur_meta = conn_meta.cursor()
            cur_meta.execute("SELECT COALESCE(barcode,''), COALESCE(keywords,''), COALESCE(is_active,1), COALESCE(is_verified,0), has_gluten FROM foods WHERE id = ?", (fid,))
            meta = cur_meta.fetchone() or ('', '', 1, 0, None)
            conn_meta.close()
            barcode = meta[0]
            keywords = meta[1]
            is_active = 1 if int(meta[2] or 0) else 0
            is_verified = 1 if int(meta[3] or 0) else 0
            has_gluten = parse_gluten_input(meta[4])
            category_options = ''.join([f'<option value="{c[0]}" {"selected" if c[1]==category else ""}>{html.escape(c[1])}</option>' for c in cats])
            brand_options = ''.join([f'<option value="{html.escape(b[1])}" {"selected" if b[1]==brand else ""}>{html.escape(b[1])}</option>' for b in brands])
            edit_page = f'''
<!doctype html>
<html>
<head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Editar alimento</title>
    <style>
        :root{{
            --bg:#f4f6fa;--surface:#ffffff;--line:#e8ebf1;--line-strong:#d2d9e4;--text:#111827;--muted:#6b7280;
            --shadow:0 16px 40px rgba(16,19,24,.06);--radius:18px;
        }}
        *{{box-sizing:border-box;}}
        body{{margin:0;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:var(--bg);color:var(--text);}}
        .page{{max-width:1320px;margin:0 auto;padding:38px 32px 60px;}}
        .library-title{{margin:0 0 22px;font-size:2.35rem;letter-spacing:.02em;}}
        .create-panel{{display:block;background:var(--surface);border:1px solid var(--line);border-radius:var(--radius);box-shadow:var(--shadow);padding:18px;}}
        .create-form{{display:grid;grid-template-columns:repeat(4,minmax(170px,1fr));gap:14px;align-items:start;}}
        .create-form input,.create-form select,.create-form button{{height:46px;padding:0 14px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;font:inherit;color:var(--text);outline:none;}}
        .create-form .full{{grid-column:1 / -1;}}
        .create-form .check-line{{display:flex;align-items:center;gap:10px;height:46px;padding:0 12px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;color:#1f7a40;font-weight:700;}}
        .create-form .check-line input{{width:18px;height:18px;margin:0;padding:0;}}
        .create-form button{{cursor:pointer;font-weight:700;background:#111827;color:#fff;border-color:#111827;}}
        .create-form button:hover{{filter:brightness(.95);}}
        .nutrition-hint{{display:flex;align-items:center;min-height:42px;padding:10px 12px;border:1px dashed var(--line-strong);border-radius:12px;color:#5f6673;background:#fbfcfe;font-size:.92rem;}}
        .photo-preview{{display:flex;align-items:center;gap:12px;padding:10px 12px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;min-height:58px;color:#4b5563;}}
        .photo-preview img{{width:58px;height:58px;border-radius:12px;object-fit:contain;border:1px solid var(--line);display:none;background:#fff;}}
        .back-link{{display:inline-flex;align-items:center;justify-content:center;height:46px;padding:0 16px;border:1px solid var(--line-strong);border-radius:12px;background:#fff;color:var(--text);text-decoration:none;font-weight:700;}}
        .back-link:hover{{background:#f5f7fa;}}
        @media (max-width:1024px){{
            .create-form{{grid-template-columns:repeat(2,minmax(170px,1fr));}}
        }}
        @media (max-width:640px){{
            .page{{padding:26px 16px 48px;}}
            .library-title{{font-size:2.05rem;}}
            .create-form{{grid-template-columns:1fr;}}
        }}
    </style>
</head>
<body>
    <div class="page">
        {home_link()}
        <h1 class="library-title">EDITAR ALIMENTO</h1>
        <section class="create-panel">
            <form method="post" action="/edit" class="create-form">
                <input type="hidden" name="id" value="{fid}" />
                <input type="hidden" name="existing_serving_size" value="{html.escape(serving or '')}" />
                <input type="hidden" name="existing_photo_path" value="{html.escape(photo_path or '')}" />
                <input type="hidden" name="barcode" value="{html.escape(barcode)}" />
                <input type="hidden" name="keywords" value="{html.escape(keywords)}" />
                <input type="hidden" name="is_active" value="{is_active}" />

                <input name="name" placeholder="Nombre" value="{html.escape(name)}" required />
                <select name="brand">
                    <option value="">Marca (opcional)</option>
                    {brand_options}
                </select>
                <select name="category">
                    <option value="">Categoría (opcional)</option>
                    {category_options}
                </select>
                <select name="has_gluten">
                    <option value="" {"selected" if has_gluten is None else ""}>Gluten (no indicado)</option>
                    <option value="1" {"selected" if has_gluten == 1 else ""}>Con gluten</option>
                    <option value="0" {"selected" if has_gluten == 0 else ""}>Sin gluten</option>
                </select>
                <input name="calories" placeholder="Kcal" value="{cal if cal is not None else ''}" />
                <input name="protein" placeholder="Proteínas (g)" value="{prot if prot is not None else ''}" />
                <input name="carbs" placeholder="Hidratos (g)" value="{carbs if carbs is not None else ''}" />
                <input name="fats" placeholder="Grasas (g)" value="{fats if fats is not None else ''}" />
                <select name="nutrition_mode" id="edit_nutrition_mode">
                    <option value="per100" {"selected" if nutrition_mode != "unit" else ""}>Valores por 100 g/ml</option>
                    <option value="unit" {"selected" if nutrition_mode == "unit" else ""}>Valores por unidad</option>
                </select>
                <select name="per100_unit" id="edit_per100_unit">
                    <option value="g" {"selected" if per100_unit != "ml" else ""}>Base por 100 g</option>
                    <option value="ml" {"selected" if per100_unit == "ml" else ""}>Base por 100 ml</option>
                </select>
                <label class="check-line full"><input type="checkbox" name="is_verified" value="1" {"checked" if is_verified == 1 else ""} /> Verificado (nutrición correcta)</label>

                <div class="nutrition-hint full" id="edit_nutrition_hint">Introduce calorías y macros por 100 g o 100 ml según base elegida.</div>
                <input class="full" type="file" accept="image/*" id="edit_food_photo_file" />
                <input type="hidden" name="photo_data_url" id="edit_food_photo_data_url" />
                <div class="photo-preview full"><img id="edit_food_photo_preview" src="{html.escape(photo_path or '')}" style="{'display:block;' if photo_path else 'display:none;'}" alt="Vista previa" /><span id="edit_food_photo_text">{html.escape('Foto actual' if photo_path else 'Sin foto seleccionada')}</span></div>

                <button class="full" type="submit">Guardar alimento</button>
            </form>
            <div style="margin-top:12px;">
                <a class="back-link" href="/foods">Volver</a>
            </div>
        </section>
    </div>
    <script>
        (function() {{
            const fileInput = document.getElementById('edit_food_photo_file');
            const hidden = document.getElementById('edit_food_photo_data_url');
            const preview = document.getElementById('edit_food_photo_preview');
            const text = document.getElementById('edit_food_photo_text');
            const modeSel = document.getElementById('edit_nutrition_mode');
            const unitSel = document.getElementById('edit_per100_unit');
            const hint = document.getElementById('edit_nutrition_hint');

            function toggleMode() {{
                const isUnit = modeSel && modeSel.value === 'unit';
                if (unitSel) unitSel.disabled = isUnit;
                if (hint) {{
                    hint.textContent = isUnit
                        ? 'Introduce calorías y macros por 1 unidad del alimento.'
                        : 'Introduce calorías y macros por 100 g o 100 ml según base elegida.';
                }}
            }}
            toggleMode();
            if (modeSel) modeSel.addEventListener('change', toggleMode);

            if (!fileInput || !hidden || !preview || !text) return;
            fileInput.addEventListener('change', () => {{
                const file = fileInput.files && fileInput.files[0];
                if (!file) {{
                    hidden.value = '';
                    text.textContent = preview.style.display === 'block' ? 'Foto actual' : 'Sin foto seleccionada';
                    return;
                }}
                const reader = new FileReader();
                reader.onload = () => {{
                    hidden.value = String(reader.result || '');
                    preview.src = hidden.value;
                    preview.style.display = 'inline-block';
                    text.textContent = file.name;
                }};
                reader.readAsDataURL(file);
            }});
        }})();
    </script>
</body>
</html>
'''
            body = edit_page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Edit exercise
        if path == '/edit_exercise':
            q = urllib.parse.parse_qs(parsed.query)
            eid = q.get('id', [''])[0]
            try:
                eid_i = int(eid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            rows = [e for e in get_exercises() if e[0] == eid_i]
            if not rows:
                self.send_response(404)
                self.end_headers()
                return
            e = rows[0]
            eid, name, muscle_group, equipment, difficulty, notes, category, video_url, machine_url, category_2 = e
            categories = get_exercise_categories()
            category_options = ''.join([
                f'<option value="{c[0]}" {"selected" if c[1] == category else ""}>{html.escape(c[1])}</option>'
                for c in categories
            ])
            secondary_category_options = ''.join([
                f'<option value="{c[0]}" {"selected" if c[1] == category_2 else ""}>{html.escape(c[1])}</option>'
                for c in categories
            ])
            edit_page = f'''
<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Editar ejercicio</title>
    <style>
                body{{font-family:'Manrope','Avenir Next','SF Pro Display','Segoe UI',sans-serif;margin:0;background:radial-gradient(1100px 600px at 0% -5%, #ffffff 0%, #f6f7f9 60%, #f3f4f6 100%);color:#101318;}}
        .page{{max-width:900px;margin:0 auto;padding:28px;}}
        h1{{margin:0 0 16px;font-size:2.1rem;}}
                .card{{background:#fff;border:1px solid #e8ebef;border-radius:18px;padding:26px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;}}
        form{{display:grid;gap:16px;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));}}
                label{{display:flex;flex-direction:column;font-weight:600;color:#6d7480;gap:8px;}}
        input, textarea, select, button{{font:inherit;outline:none;}}
                input, select, textarea{{padding:14px 16px;border:1px solid #d8dde6;border-radius:14px;background:#fff;color:#101318;}}
        textarea{{min-height:130px;resize:vertical;}}
        select{{appearance:none;}}
        .full{{grid-column:1 / -1;}}
                button{{padding:13px 18px;border:none;border-radius:14px;background:#101318;color:#fff;cursor:pointer;transition:transform .18s ease,background .18s ease,box-shadow .18s ease;box-shadow:0 8px 18px rgba(16,19,24,.12);}}
                button:hover{{background:#232933;transform:translateY(-1px);}}
        .actions{{display:flex;gap:14px;align-items:center;flex-wrap:wrap;}}
                .secondary-link{{color:#101318;text-decoration:none;font-weight:700;}}
    </style>
</head>
<body>
  <div class="page">
    {home_link()}
    <div class="card">
      <h1>Editar ejercicio</h1>
      <form method="post" action="/edit_exercise">
        <input type="hidden" name="id" value="{eid}" />
        <label>Nombre<input name="name" value="{html.escape(name)}" required /></label>
                <label>Grupo muscular<select name="category_id">
                    <option value="">-- Sin grupo muscular --</option>
          {category_options}
        </select></label>
                <label>Segundo grupo muscular<select name="category_id_2">
                    <option value="">-- Sin segundo grupo muscular --</option>
              {secondary_category_options}
            </select></label>
                <label class="full">Link de video<input name="video_url" value="{html.escape(video_url or '')}" placeholder="https://..." /></label>
                <label class="full">Link de máquina<input name="machine_url" value="{html.escape(machine_url or '')}" placeholder="https://..." /></label>
        <label class="full">Notas<textarea name="notes">{html.escape(notes or '')}</textarea></label>
        <div class="actions full">
          <button type="submit">Guardar cambios</button>
          <a class="secondary-link" href="/exercises">Volver</a>
        </div>
      </form>
    </div>
  </div>
</body>
</html>
'''
            body = edit_page.encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

    def do_PUT(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        ctype = self.headers.get('Content-Type', '')
        if 'application/json' not in ctype:
            return self.send_json({'error': 'Content-Type must be application/json'}, status=415)

        public_put_paths = {'/api/client_fasting_weight', '/api/client_daily_steps'}
        if path not in public_put_paths and not self.is_admin_authenticated():
            return self.send_json({'error': 'unauthorized'}, status=401)

        payload = self.read_json() or {}

        if path == '/api/client_fasting_weight':
            date_text = str(payload.get('date') or '').strip()
            if not re.match(r'^\d{4}-\d{2}-\d{2}$', date_text):
                return self.send_json({'error': 'invalid date'}, status=400)

            try:
                from datetime import datetime
                datetime.strptime(date_text, '%Y-%m-%d')
            except Exception:
                return self.send_json({'error': 'invalid date'}, status=400)

            cookies = parse_cookie_header(self.headers.get('Cookie', ''))
            token = cookies.get(CLIENT_PORTAL_COOKIE, '')
            session_client_id = parse_client_portal_session_token(token)

            client_id_raw = payload.get('client_id')
            if session_client_id is not None:
                if client_id_raw is not None:
                    try:
                        requested_client_id = int(client_id_raw)
                    except Exception:
                        return self.send_json({'error': 'invalid client_id'}, status=400)
                    if int(requested_client_id) != int(session_client_id):
                        return self.send_json({'error': 'forbidden'}, status=403)
                client_id_i = int(session_client_id)
            else:
                try:
                    client_id_i = int(client_id_raw)
                except Exception:
                    return self.send_json({'error': 'client_id required'}, status=400)

            weight_raw = payload.get('weight_kg')
            weight_text = str(weight_raw or '').strip()
            if not weight_text:
                upsert_client_fasting_weight(client_id_i, date_text, None)
                return self.send_json({'ok': True, 'cleared': True})

            weight = parse_numeric_input(weight_text, default=0)
            if weight <= 0 or weight > 400:
                return self.send_json({'error': 'invalid weight'}, status=400)

            upsert_client_fasting_weight(client_id_i, date_text, weight)
            return self.send_json({'ok': True, 'weight_kg': round(weight, 2)})

        if path == '/api/client_daily_steps':
            date_text = str(payload.get('date') or '').strip()
            if not re.match(r'^\d{4}-\d{2}-\d{2}$', date_text):
                return self.send_json({'error': 'invalid date'}, status=400)

            try:
                from datetime import datetime
                datetime.strptime(date_text, '%Y-%m-%d')
            except Exception:
                return self.send_json({'error': 'invalid date'}, status=400)

            cookies = parse_cookie_header(self.headers.get('Cookie', ''))
            token = cookies.get(CLIENT_PORTAL_COOKIE, '')
            session_client_id = parse_client_portal_session_token(token)

            client_id_raw = payload.get('client_id')
            if session_client_id is not None:
                if client_id_raw is not None:
                    try:
                        requested_client_id = int(client_id_raw)
                    except Exception:
                        return self.send_json({'error': 'invalid client_id'}, status=400)
                    if int(requested_client_id) != int(session_client_id):
                        return self.send_json({'error': 'forbidden'}, status=403)
                client_id_i = int(session_client_id)
            else:
                try:
                    client_id_i = int(client_id_raw)
                except Exception:
                    return self.send_json({'error': 'client_id required'}, status=400)

            steps_raw = payload.get('steps')
            steps_text = str(steps_raw or '').strip()
            if not steps_text:
                upsert_client_daily_steps(client_id_i, date_text, None)
                return self.send_json({'ok': True, 'cleared': True})

            digits = re.sub(r'[^0-9]', '', steps_text)
            if not digits:
                return self.send_json({'error': 'invalid steps'}, status=400)

            try:
                steps_i = int(digits)
            except Exception:
                return self.send_json({'error': 'invalid steps'}, status=400)

            if steps_i < 0 or steps_i > 100000:
                return self.send_json({'error': 'invalid steps'}, status=400)

            upsert_client_daily_steps(client_id_i, date_text, steps_i)
            return self.send_json({'ok': True, 'steps': steps_i})

        # Update food: /api/foods/<id>
        if path.startswith('/api/foods/'):
            try:
                fid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)

            allowed = [
                'name', 'brand', 'category_id', 'calories', 'protein', 'carbs', 'fats', 'serving_size',
                'photo_path', 'nutrition_mode', 'per100_unit', 'barcode', 'keywords', 'is_active', 'is_verified', 'has_gluten'
            ]
            sets = []
            vals = []
            for k in allowed:
                if k in payload:
                    sets.append(f"{k} = ?")
                    if k == 'has_gluten':
                        vals.append(parse_gluten_input(payload.get(k)))
                    else:
                        vals.append(payload.get(k))
            if not sets:
                return self.send_json({'error': 'no fields to update'}, status=400)

            vals.append(fid)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(f"UPDATE foods SET {', '.join(sets)} WHERE id = ?", tuple(vals))
            refresh_food_search_row(cur, fid)
            conn.commit()
            conn.close()
            rows = [r for r in get_foods() if r[0] == fid]
            if not rows:
                return self.send_json({'error': 'not found'}, status=404)
            keys = ['id', 'name', 'brand', 'category', 'calories', 'protein', 'carbs', 'fats', 'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified', 'has_gluten']
            return self.send_json(dict(zip(keys, rows[0])))

        # Update exercise
        if path.startswith('/api/exercises/'):
            try:
                eid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)
            allowed = ['name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'exercise_category_id', 'exercise_category_id_2', 'video_url', 'machine_url']
            sets = []
            vals = []
            for k in allowed:
                if k in payload:
                    sets.append(f"{k} = ?")
                    vals.append(payload.get(k))
            if not sets:
                return self.send_json({'error': 'no fields to update'}, status=400)
            vals.append(eid)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(f"UPDATE exercises SET {', '.join(sets)} WHERE id = ?", tuple(vals))
            conn.commit()
            conn.close()
            rows = [r for r in get_exercises() if r[0] == eid]
            if not rows:
                return self.send_json({'error': 'not found'}, status=404)
            keys = ['id', 'name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'category', 'video_url', 'machine_url', 'category_2']
            return self.send_json(dict(zip(keys, rows[0])))

        # Update category
        if path.startswith('/api/categories/'):
            try:
                cid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)
            name = payload.get('name')
            if not name:
                return self.send_json({'error': 'name required'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE categories SET name = ? WHERE id = ?", (name, cid))
            rebuild_foods_search_index(cur)
            conn.commit()
            conn.close()
            return self.send_json({'status': 'updated'})

        # Update diet meal name
        m = re.match(r'^/api/diet_meal/(\d+)$', path)
        if m:
            mid = int(m.group(1))
            name = (payload.get('name') or '').strip()
            if name:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute("UPDATE diet_meals SET name=? WHERE id=?", (name, mid))
                conn.commit()
                conn.close()
            return self.send_json({'ok': True})

        # Update diet weight/details
        m = re.match(r'^/api/diets/(\d+)$', path)
        if m:
            did = int(m.group(1))
            allowed = ['name', 'description', 'client_instructions', 'client_diet_name', 'client_weight_kg', 'client_name', 'client_height_cm', 'client_age']
            sets = []
            vals = []
            for k in allowed:
                if k in payload:
                    sets.append(f"{k} = ?")
                    vals.append(payload.get(k))
            if not sets:
                return self.send_json({'error': 'no fields to update'}, status=400)
            vals.append(did)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(f"UPDATE diets SET {', '.join(sets)} WHERE id = ?", tuple(vals))
            conn.commit()
            conn.close()
            return self.send_json({'ok': True})

        if path == '/api/settings/diet_instructions_template':
            value = str(payload.get('value') or '').strip()
            set_app_setting('diet_instructions_template', value or DEFAULT_DIET_INSTRUCTIONS_TEMPLATE)
            return self.send_json({'ok': True})

        # Update diet item grams
        m = re.match(r'^/api/diet_item_b/(\d+)$', path)
        if m:
            iid = int(m.group(1))
            grams = float(payload.get('grams', 100) or 100)
            units = float(payload.get('units', 1) or 1)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE diet_items SET quantity_grams=?, quantity_units=? WHERE id=?", (grams, units, iid))
            conn.commit()
            conn.close()
            return self.send_json({'ok': True})

        m = re.match(r'^/api/diet_supplement_b/(\d+)$', path)
        if m:
            sid = int(m.group(1))
            supplement_name = str(payload.get('supplement_name', '')).strip()
            intake_time = str(payload.get('intake_time', '')).strip()
            dose = str(payload.get('dose', '')).strip()
            notes = str(payload.get('notes', '')).strip()
            if not supplement_name:
                return self.send_json({'error': 'supplement_name required'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE diet_supplements SET supplement_name=?, intake_time=?, dose=?, notes=? WHERE id=?",
                (supplement_name, intake_time, dose, notes, sid),
            )
            conn.commit()
            conn.close()
            return self.send_json({'ok': True})

        return self.send_json({'error': 'not found'}, status=404)

    def do_DELETE(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

        if not self.is_admin_authenticated():
            return self.send_json({'error': 'unauthorized'}, status=401)

        if path.startswith('/api/foods/'):
            try:
                fid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM foods_search WHERE food_id = ?", (fid,))
            cur.execute("DELETE FROM foods WHERE id = ?", (fid,))
            conn.commit()
            conn.close()
            return self.send_json({'status': 'deleted'})

        if path.startswith('/api/exercises/'):
            try:
                eid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE client_training_history SET exercise_id = NULL WHERE exercise_id = ?", (eid,))
            cur.execute("DELETE FROM exercises WHERE id = ?", (eid,))
            conn.commit()
            conn.close()
            return self.send_json({'status': 'deleted'})

        if path.startswith('/api/categories/'):
            try:
                cid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE foods SET category_id = NULL WHERE category_id = ?", (cid,))
            cur.execute("DELETE FROM categories WHERE id = ?", (cid,))
            rebuild_foods_search_index(cur)
            conn.commit()
            conn.close()
            return self.send_json({'status': 'deleted'})

        # Delete diet meal and its items
        m = re.match(r'^/api/diet_meal/(\d+)$', path)
        if m:
            mid = int(m.group(1))
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM diet_items WHERE meal_id=?", (mid,))
            cur.execute("DELETE FROM diet_meals WHERE id=?", (mid,))
            conn.commit()
            conn.close()
            return self.send_json({'ok': True})

        # Delete diet item (builder)
        m = re.match(r'^/api/diet_item_b/(\d+)$', path)
        if m:
            iid = int(m.group(1))
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM diet_items WHERE id=?", (iid,))
            conn.commit()
            conn.close()
            return self.send_json({'ok': True})

        m = re.match(r'^/api/diet_supplement_b/(\d+)$', path)
        if m:
            sid = int(m.group(1))
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM diet_supplements WHERE id=?", (sid,))
            conn.commit()
            conn.close()
            return self.send_json({'ok': True})

        return self.send_json({'error': 'not found'}, status=404)

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        ctype = self.headers.get('Content-Type', '')

        public_post_paths = {'/client_login', '/client_register', '/client_onboarding', '/admin_login'}
        if path not in public_post_paths and not self.is_admin_authenticated():
            self.redirect_admin_login(path)
            return

        # Diet builder JSON API
        bm = re.match(r'^/api/diet_builder/(\d+)/(meals|items|day_config|copy_day|supplements)$', path)
        dup_m = re.match(r'^/api/diet_item_b/(\d+)/duplicate$', path)
        if dup_m:
            item_id = int(dup_m.group(1))
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, note, COALESCE(option_group,1) FROM diet_items WHERE id=?", (item_id,))
            r = cur.fetchone()
            if not r:
                conn.close()
                return self.send_json({'error': 'not found'}, status=404)
            cur.execute("INSERT INTO diet_items(diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, note, option_group) VALUES(?,?,?,?,?,?,?,?)", r)
            new_id = cur.lastrowid
            conn.commit()
            cur.execute("""SELECT di.id, di.day_of_week, di.meal_id, di.food_id, f.name, COALESCE(f.brand,''), di.quantity_grams,
                                  COALESCE(f.calories,0), COALESCE(f.protein,0), COALESCE(f.fats,0), COALESCE(f.carbs,0),
                                  COALESCE(f.nutrition_mode,'per100'), COALESCE(f.per100_unit,'g'), COALESCE(di.quantity_units,1), COALESCE(di.option_group,1)
                           FROM diet_items di JOIN foods f ON di.food_id=f.id WHERE di.id=?""", (new_id,))
            r2 = cur.fetchone()
            conn.close()
            if not r2:
                return self.send_json({'error': 'error'}, status=500)
            return self.send_json({'id': r2[0], 'day': r2[1], 'meal_id': r2[2], 'food_id': r2[3],
                                   'food_name': r2[4], 'food_brand': r2[5], 'grams': r2[6] or 100,
                                   'kcal_per100': r2[7], 'protein_per100': r2[8], 'fat_per100': r2[9], 'carbs_per100': r2[10],
                                   'nutrition_mode': r2[11], 'per100_unit': r2[12], 'units': r2[13] or 1,
                                   'option_group': r2[14] if r2[14] in (1, 2) else 1})

        if bm and 'application/json' in ctype:
            payload = self.read_json() or {}
            if bm:
                diet_id_i = int(bm.group(1))
                action = bm.group(2)
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                if action == 'meals':
                    name = str(payload.get('name', 'Nueva comida')).strip() or 'Nueva comida'
                    cur.execute("SELECT COALESCE(MAX(order_index),0)+1 FROM diet_meals WHERE diet_id=?", (diet_id_i,))
                    oi = cur.fetchone()[0]
                    cur.execute("INSERT INTO diet_meals(diet_id, name, order_index) VALUES(?,?,?)", (diet_id_i, name, oi))
                    mid = cur.lastrowid
                    conn.commit()
                    conn.close()
                    return self.send_json({'id': mid, 'name': name, 'order_index': oi})
                elif action == 'items':
                    food_id = int(payload.get('food_id', 0) or 0)
                    meal_id = int(payload.get('meal_id', 0) or 0)
                    day = str(payload.get('day_of_week', '')).strip()
                    grams = float(payload.get('grams', 100) or 100)
                    units = float(payload.get('units', 1) or 1)
                    try:
                        option_group = int(payload.get('option_group', 1) or 1)
                    except Exception:
                        option_group = 1
                    if option_group not in (1, 2):
                        option_group = 1
                    if not food_id or not meal_id:
                        conn.close()
                        return self.send_json({'error': 'food_id and meal_id required'}, status=400)
                    cur.execute("INSERT INTO diet_items(diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, option_group) VALUES(?,?,?,?,?,?,?)",
                                (diet_id_i, food_id, meal_id, day, grams, units, option_group))
                    item_id = cur.lastrowid
                    cur.execute(
                        "SELECT COALESCE(nutrition_mode,'per100'), COALESCE(per100_unit,'g') FROM foods WHERE id=?",
                        (food_id,),
                    )
                    fm = cur.fetchone() or ('per100', 'g')
                    conn.commit()
                    conn.close()
                    return self.send_json({
                        'id': item_id, 'food_id': food_id, 'meal_id': meal_id, 'day': day,
                        'grams': grams, 'units': units, 'nutrition_mode': fm[0], 'per100_unit': fm[1],
                        'option_group': option_group,
                    })
                elif action == 'day_config':
                    day = str(payload.get('day', '')).strip()
                    is_training = 1 if payload.get('is_training', True) else 0
                    goal_kcal = float(payload.get('goal_kcal', 0) or 0)
                    goal_steps = float(payload.get('goal_steps', 0) or 0)
                    goal_protein = float(payload.get('goal_protein', 0) or 0)
                    goal_fat = float(payload.get('goal_fat', 0) or 0)
                    goal_carbs = float(payload.get('goal_carbs', 0) or 0)
                    goal_fiber = float(payload.get('goal_fiber', 0) or 0)
                    protein_multiplier = float(payload.get('protein_multiplier', 0) or 0)
                    fat_multiplier = float(payload.get('fat_multiplier', 0) or 0)
                    carb_multiplier = float(payload.get('carb_multiplier', 0) or 0)
                    cur.execute("SELECT id FROM diet_day_config WHERE diet_id=? AND day_of_week=?", (diet_id_i, day))
                    if cur.fetchone():
                        cur.execute("UPDATE diet_day_config SET is_training=?,goal_kcal=?,goal_steps=?,goal_protein=?,goal_fat=?,goal_carbs=?,goal_fiber=?,protein_multiplier=?,fat_multiplier=?,carb_multiplier=? WHERE diet_id=? AND day_of_week=?",
                                    (is_training, goal_kcal, goal_steps, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier, diet_id_i, day))
                    else:
                        cur.execute("INSERT INTO diet_day_config(diet_id,day_of_week,is_training,goal_kcal,goal_steps,goal_protein,goal_fat,goal_carbs,goal_fiber,protein_multiplier,fat_multiplier,carb_multiplier) VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",
                                    (diet_id_i, day, is_training, goal_kcal, goal_steps, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier))
                    conn.commit()
                    conn.close()
                    return self.send_json({'ok': True})
                elif action == 'copy_day':
                    from_day = str(payload.get('from_day', '')).strip()
                    to_day = str(payload.get('to_day', '')).strip()
                    cur.execute("DELETE FROM diet_items WHERE diet_id=? AND day_of_week=? AND meal_id IS NOT NULL", (diet_id_i, to_day))
                    cur.execute("SELECT food_id, meal_id, quantity_grams, quantity_units, note, COALESCE(option_group,1) FROM diet_items WHERE diet_id=? AND day_of_week=? AND meal_id IS NOT NULL", (diet_id_i, from_day))
                    src = cur.fetchall()
                    new_ids = []
                    for s in src:
                        cur.execute("INSERT INTO diet_items(diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, note, option_group) VALUES(?,?,?,?,?,?,?,?)",
                                    (diet_id_i, s[0], s[1], to_day, s[2], s[3], s[4], s[5]))
                        new_ids.append(cur.lastrowid)
                    conn.commit()
                    new_items = []
                    for nid in new_ids:
                        cur.execute("""SELECT di.id, di.day_of_week, di.meal_id, di.food_id, f.name, COALESCE(f.brand,''), di.quantity_grams,
                                              COALESCE(f.calories,0), COALESCE(f.protein,0), COALESCE(f.fats,0), COALESCE(f.carbs,0),
                                              COALESCE(f.nutrition_mode,'per100'), COALESCE(f.per100_unit,'g'), COALESCE(di.quantity_units,1), COALESCE(di.option_group,1)
                                       FROM diet_items di JOIN foods f ON di.food_id=f.id WHERE di.id=?""", (nid,))
                        r = cur.fetchone()
                        if r:
                            new_items.append({'id': r[0], 'day': r[1], 'meal_id': r[2], 'food_id': r[3],
                                              'food_name': r[4], 'food_brand': r[5], 'grams': r[6] or 100,
                                              'kcal_per100': r[7], 'protein_per100': r[8], 'fat_per100': r[9], 'carbs_per100': r[10],
                                              'nutrition_mode': r[11], 'per100_unit': r[12], 'units': r[13] or 1,
                                              'option_group': r[14] if r[14] in (1, 2) else 1})
                    conn.close()
                    return self.send_json({'items': new_items})
                elif action == 'supplements':
                    supplement_name = str(payload.get('supplement_name', '')).strip()
                    intake_time = str(payload.get('intake_time', '')).strip()
                    dose = str(payload.get('dose', '')).strip()
                    notes = str(payload.get('notes', '')).strip()
                    if not supplement_name:
                        conn.close()
                        return self.send_json({'error': 'supplement_name required'}, status=400)
                    cur.execute("SELECT COALESCE(MAX(order_index),0)+1 FROM diet_supplements WHERE diet_id=?", (diet_id_i,))
                    oi = cur.fetchone()[0]
                    cur.execute(
                        "INSERT INTO diet_supplements(diet_id, supplement_name, intake_time, dose, notes, order_index) VALUES(?,?,?,?,?,?)",
                        (diet_id_i, supplement_name, intake_time, dose, notes, oi),
                    )
                    sid = cur.lastrowid
                    conn.commit()
                    conn.close()
                    return self.send_json({
                        'id': sid,
                        'supplement_name': supplement_name,
                        'intake_time': intake_time,
                        'dose': dose,
                        'notes': notes,
                        'order_index': oi,
                    })
                conn.close()
            return self.send_json({'error': 'bad request'}, status=400)

        # JSON API
        if path == '/api/foods' and 'application/json' in ctype:
            payload = self.read_json() or {}
            name = payload.get('name')
            if not name:
                return self.send_json({'error': 'name is required'}, status=400)
            brand = payload.get('brand')
            cat = payload.get('category_id')
            barcode = str(payload.get('barcode') or '').strip()
            keywords = str(payload.get('keywords') or '').strip()
            is_active = payload.get('is_active', 1)
            try:
                is_active = 1 if int(is_active) else 0
            except Exception:
                is_active = 1
            is_verified = payload.get('is_verified', 0)
            try:
                is_verified = 1 if int(is_verified) else 0
            except Exception:
                is_verified = 0
            has_gluten = parse_gluten_input(payload.get('has_gluten'))
            calories = parse_numeric_input(payload.get('calories'))
            protein = parse_numeric_input(payload.get('protein'))
            carbs = parse_numeric_input(payload.get('carbs'))
            fats = parse_numeric_input(payload.get('fats'))
            serving = payload.get('serving_size')
            photo_path = payload.get('photo_path')
            nutrition_mode = payload.get('nutrition_mode') or 'per100'
            if nutrition_mode not in ('per100', 'unit'):
                nutrition_mode = 'per100'
            per100_unit = payload.get('per100_unit') or 'g'
            if per100_unit not in ('g', 'ml'):
                per100_unit = 'g'
            if nutrition_mode == 'unit' and not serving:
                serving = '1 unidad'
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "INSERT INTO foods(name, brand, category_id, calories, protein, carbs, fats, serving_size, photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified, has_gluten) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (name, brand, cat, calories, protein, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, barcode or None, keywords or None, is_active, is_verified, has_gluten),
            )
            new_food_id = cur.lastrowid
            refresh_food_search_row(cur, new_food_id)
            cur.execute(
                "SELECT f.id, f.name, f.brand, c.name as category, f.calories, f.protein, f.carbs, f.fats, f.serving_size, "
                "COALESCE(f.photo_path, ''), COALESCE(f.nutrition_mode, 'per100'), COALESCE(f.per100_unit, 'g'), COALESCE(f.is_verified, 0), f.has_gluten "
                "FROM foods f LEFT JOIN categories c ON f.category_id = c.id WHERE f.id = ?",
                (new_food_id,),
            )
            row = cur.fetchone()
            conn.commit()
            conn.close()
            keys = ['id', 'name', 'brand', 'category', 'calories', 'protein', 'carbs', 'fats', 'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified', 'has_gluten']
            return self.send_json(dict(zip(keys, row)), status=201)

        if path == '/api/exercises' and 'application/json' in ctype:
            payload = self.read_json() or {}
            name = payload.get('name')
            if not name:
                return self.send_json({'error': 'name is required'}, status=400)
            muscle_group = payload.get('muscle_group')
            equipment = payload.get('equipment')
            difficulty = payload.get('difficulty')
            notes = payload.get('notes')
            exercise_category_id = payload.get('exercise_category_id')
            exercise_category_id_2 = payload.get('exercise_category_id_2')
            video_url = payload.get('video_url')
            machine_url = payload.get('machine_url')
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "INSERT INTO exercises(name, muscle_group, equipment, difficulty, notes, exercise_category_id, exercise_category_id_2, video_url, machine_url) VALUES(?,?,?,?,?,?,?,?,?)",
                (name, muscle_group, equipment, difficulty, notes, exercise_category_id, exercise_category_id_2, video_url, machine_url),
            )
            conn.commit()
            conn.close()
            ex = get_exercises()[-1]
            keys = ['id', 'name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'category', 'video_url', 'machine_url', 'category_2']
            return self.send_json(dict(zip(keys, ex)), status=201)

        if path == '/api/categories' and 'application/json' in ctype:
            payload = self.read_json() or {}
            name = payload.get('name')
            if not name:
                return self.send_json({'error': 'name is required'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (name,))
            conn.commit()
            conn.close()
            return self.send_json({'status': 'created'}, status=201)

        if path == '/api/exercise_categories' and 'application/json' in ctype:
            payload = self.read_json() or {}
            name = payload.get('name')
            if not name:
                return self.send_json({'error': 'name is required'}, status=400)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("INSERT OR IGNORE INTO exercise_categories(name) VALUES(?)", (name,))
            conn.commit()
            conn.close()
            return self.send_json({'status': 'created'}, status=201)

        # form handlers
        length = int(self.headers.get('Content-Length', 0))
        data = self.rfile.read(length).decode('utf-8')
        params = urllib.parse.parse_qs(data)

        def get(field, default=''):
            return params.get(field, [default])[0]

        if path == '/admin_login':
            username = get('username').strip()
            password = get('password').strip()
            next_path = get('next').strip() or '/admin'
            if not next_path.startswith('/'):
                next_path = '/admin'

            if not verify_admin_portal_credentials(username, password):
                self.send_response(303)
                self.send_header(
                    'Location',
                    '/admin_login?msg=' + urllib.parse.quote('Credenciales inválidas') + '&next=' + urllib.parse.quote(next_path),
                )
                self.end_headers()
                return

            token = make_admin_portal_session_token(username)
            self.send_response(303)
            self.send_header(
                'Set-Cookie',
                f'{ADMIN_PORTAL_COOKIE}={urllib.parse.quote(token)}; Path=/; Max-Age={ADMIN_PORTAL_SESSION_TTL_SECONDS}; HttpOnly; SameSite=Lax',
            )
            self.send_header('Location', next_path)
            self.end_headers()
            return

        if path == '/admin_security':
            current_password = get('current_password').strip()
            new_username = get('new_username').strip()
            new_password = get('new_password').strip()
            new_password_confirm = get('new_password_confirm').strip()
            current_username = get_admin_portal_username()

            if not verify_admin_portal_credentials(current_username, current_password):
                self.send_response(303)
                self.send_header('Location', '/admin_security?msg=' + urllib.parse.quote('Contraseña actual incorrecta'))
                self.end_headers()
                return

            if not new_username:
                self.send_response(303)
                self.send_header('Location', '/admin_security?msg=' + urllib.parse.quote('El usuario no puede estar vacío'))
                self.end_headers()
                return

            if new_password and len(new_password) < 6:
                self.send_response(303)
                self.send_header('Location', '/admin_security?msg=' + urllib.parse.quote('La nueva contraseña debe tener al menos 6 caracteres'))
                self.end_headers()
                return

            if new_password != new_password_confirm:
                self.send_response(303)
                self.send_header('Location', '/admin_security?msg=' + urllib.parse.quote('Las nuevas contraseñas no coinciden'))
                self.end_headers()
                return

            set_app_setting('admin_portal_username', new_username)
            if new_password:
                set_app_setting('admin_portal_password_hash', hash_admin_password(new_password))

            refreshed_token = make_admin_portal_session_token(new_username)
            self.send_response(303)
            self.send_header(
                'Set-Cookie',
                f'{ADMIN_PORTAL_COOKIE}={urllib.parse.quote(refreshed_token)}; Path=/; Max-Age={ADMIN_PORTAL_SESSION_TTL_SECONDS}; HttpOnly; SameSite=Lax',
            )
            self.send_header('Location', '/admin_security?msg=' + urllib.parse.quote('Credenciales actualizadas'))
            self.end_headers()
            return

        if path == '/client_login':
            identifier = get('identifier').strip()
            password = get('password').strip()
            access_code = get('access_code').strip()
            next_path = get('next').strip() or '/client_app'
            if not next_path.startswith('/'):
                next_path = '/client_app'

            # Unified access: admin can log in from the same entry form.
            if verify_admin_portal_credentials(identifier, password):
                admin_token = make_admin_portal_session_token(identifier)
                self.send_response(303)
                self.send_header(
                    'Set-Cookie',
                    f'{ADMIN_PORTAL_COOKIE}={urllib.parse.quote(admin_token)}; Path=/; Max-Age={ADMIN_PORTAL_SESSION_TTL_SECONDS}; HttpOnly; SameSite=Lax',
                )
                self.send_header('Location', '/admin')
                self.end_headers()
                return

            user = get_client_portal_user_by_identifier(identifier)
            if not user:
                self.send_response(303)
                self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Usuario no encontrado'))
                self.end_headers()
                return

            ok = False
            stored_hash = str(user.get('password_hash') or '').strip()
            if password and stored_hash:
                ok = verify_client_password(password, stored_hash)
            elif access_code:
                expected_code = str(user.get('access_code') or '').strip()
                ok = bool(expected_code and access_code == expected_code)

            if not ok:
                self.send_response(303)
                self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Credenciales incorrectas'))
                self.end_headers()
                return

            token = make_client_portal_session_token(int(user['id']))
            self.send_response(303)
            self.send_header(
                'Set-Cookie',
                f'{CLIENT_PORTAL_COOKIE}={urllib.parse.quote(token)}; Path=/; Max-Age={CLIENT_PORTAL_SESSION_TTL_SECONDS}; HttpOnly; SameSite=Lax',
            )
            self.send_header('Location', next_path)
            self.end_headers()
            return

        if path == '/client_register':
            email = get('email').strip()
            password = get('password').strip()
            password_confirm = get('password_confirm').strip()

            if not email or '@' not in email:
                self.send_response(303)
                self.send_header('Location', '/client_register?msg=' + urllib.parse.quote('Introduce un email válido'))
                self.end_headers()
                return
            if len(password) < 6:
                self.send_response(303)
                self.send_header('Location', '/client_register?msg=' + urllib.parse.quote('La contraseña debe tener al menos 6 caracteres'))
                self.end_headers()
                return
            if password != password_confirm:
                self.send_response(303)
                self.send_header('Location', '/client_register?msg=' + urllib.parse.quote('Las contraseñas no coinciden'))
                self.end_headers()
                return
            if find_client_by_email(email):
                self.send_response(303)
                self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Ese email ya existe. Inicia sesión'))
                self.end_headers()
                return

            password_hash = hash_client_password(password)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            default_name = email.split('@', 1)[0].strip() or 'Cliente'
            cur.execute(
                "INSERT INTO clients(name, email, client_password_hash, created_at) VALUES(?,?,?,datetime('now'))",
                (default_name, email, password_hash),
            )
            client_id = cur.lastrowid
            cur.execute("UPDATE clients SET client_access_code = ? WHERE id = ?", (f'C{client_id}', client_id))
            conn.commit()
            conn.close()

            token = make_client_portal_session_token(client_id)
            self.send_response(303)
            self.send_header(
                'Set-Cookie',
                f'{CLIENT_PORTAL_COOKIE}={urllib.parse.quote(token)}; Path=/; Max-Age={CLIENT_PORTAL_SESSION_TTL_SECONDS}; HttpOnly; SameSite=Lax',
            )
            self.send_header('Location', '/client_onboarding')
            self.end_headers()
            return

        if path == '/client_onboarding':
            cookies = parse_cookie_header(self.headers.get('Cookie', ''))
            token = cookies.get(CLIENT_PORTAL_COOKIE, '')
            client_id = parse_client_portal_session_token(token)
            if client_id is None:
                self.send_response(303)
                self.send_header('Location', '/client_login?msg=' + urllib.parse.quote('Inicia sesión para continuar'))
                self.end_headers()
                return

            name = get('name').strip()
            phone = get('phone').strip()
            email = get('email').strip()
            birthdate = get('birthdate').strip()
            objectives = get('objectives').strip()
            try:
                height_cm = float(get('height_cm') or 0)
            except Exception:
                height_cm = 0
            try:
                weight_kg = float(get('weight_kg') or 0)
            except Exception:
                weight_kg = 0

            if not name:
                self.send_response(303)
                self.send_header('Location', '/client_onboarding?msg=' + urllib.parse.quote('El nombre es obligatorio'))
                self.end_headers()
                return
            if not email or '@' not in email:
                self.send_response(303)
                self.send_header('Location', '/client_onboarding?msg=' + urllib.parse.quote('El email es obligatorio'))
                self.end_headers()
                return

            existing = find_client_by_email(email)
            if existing and int(existing[0]) != int(client_id):
                self.send_response(303)
                self.send_header('Location', '/client_onboarding?msg=' + urllib.parse.quote('Ese email ya está en uso'))
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE clients SET name=?, phone=?, email=?, birthdate=?, height_cm=?, weight_kg=?, objectives=? WHERE id=?",
                (name, phone or None, email, birthdate or None, height_cm, weight_kg, objectives or None, int(client_id)),
            )
            conn.commit()
            conn.close()

            self.send_response(303)
            self.send_header('Location', '/client_app')
            self.end_headers()
            return

        if path == '/add':
            name = get('name').strip()
            brand = get('brand').strip()
            cat_param = get('category').strip()
            has_gluten = parse_gluten_input(get('has_gluten'))
            barcode = get('barcode').strip()
            keywords = get('keywords').strip()
            is_active = 0 if get('is_active').strip() == '0' else 1
            is_verified = 1 if get('is_verified').strip() == '1' else 0
            calories = parse_numeric_input(get('calories'))
            protein = parse_numeric_input(get('protein'))
            carbs = parse_numeric_input(get('carbs'))
            fats = parse_numeric_input(get('fats'))
            serving = format_serving_size(get('serving_amount'), get('serving_unit'))
            photo_data_url = get('photo_data_url')
            photo_path = save_food_photo_data_url(photo_data_url)
            nutrition_mode = get('nutrition_mode').strip() or 'per100'
            if nutrition_mode not in ('per100', 'unit'):
                nutrition_mode = 'per100'
            per100_unit = get('per100_unit').strip().lower() or 'g'
            if per100_unit not in ('g', 'ml'):
                per100_unit = 'g'
            if nutrition_mode == 'unit' and not serving:
                serving = '1 unidad'

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cat_id = None
            if cat_param:
                try:
                    cat_id = int(cat_param)
                except Exception:
                    cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (cat_param,))
                    cur.execute("SELECT id FROM categories WHERE name= ?", (cat_param,))
                    row = cur.fetchone()
                    cat_id = row[0] if row else None

            cur.execute(
                "INSERT INTO foods(name, brand, category_id, calories, protein, carbs, fats, serving_size, photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified, has_gluten) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (name, brand or None, cat_id, calories, protein, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, barcode or None, keywords or None, is_active, is_verified, has_gluten),
            )
            refresh_food_search_row(cur, cur.lastrowid)
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Alimento añadido'))
            self.end_headers()
            return

        if path == '/add_exercise':
            name = get('name').strip()
            category_id = get('category_id').strip()
            category_id_2 = get('category_id_2').strip()
            video_url = get('video_url').strip()
            machine_url = get('machine_url').strip()
            cat_id = None
            if category_id:
                try:
                    cat_id = int(category_id)
                except Exception:
                    cat_id = None
            cat_id_2 = None
            if category_id_2:
                try:
                    cat_id_2 = int(category_id_2)
                except Exception:
                    cat_id_2 = None
            if cat_id_2 is not None and cat_id_2 == cat_id:
                cat_id_2 = None
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "INSERT INTO exercises(name, muscle_group, equipment, difficulty, notes, exercise_category_id, exercise_category_id_2, video_url, machine_url) VALUES(?,?,?,?,?,?,?,?,?)",
                (name, None, None, None, None, cat_id, cat_id_2, video_url or None, machine_url or None),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Ejercicio añadido'))
            self.end_headers()
            return

        if path == '/add_diet':
            name = get('name').strip()
            description = get('description').strip()
            try:
                client_weight_kg = float(get('client_weight_kg') or 0)
            except ValueError:
                client_weight_kg = 0
            new_diet_id = None
            if name:
                default_instructions = get_diet_instructions_template()
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute(
                    "INSERT INTO diets(name, description, client_instructions, client_weight_kg, created_at) VALUES(?,?,?,?,datetime('now'))",
                    (name, description or None, default_instructions, client_weight_kg),
                )
                new_diet_id = cur.lastrowid
                cur.execute("UPDATE diets SET display_number = ? WHERE id = ?", (new_diet_id, new_diet_id))
                conn.commit()
                conn.close()
            self.send_response(303)
            if new_diet_id:
                self.send_header('Location', f'/static/builder.html?diet_id={new_diet_id}')
            else:
                self.send_header('Location', '/diets?msg=' + urllib.parse.quote('Dieta creada'))
            self.end_headers()
            return

        if path == '/add_client':
            name = get('name').strip()
            phone = get('phone').strip()
            email = get('email').strip()
            client_access_code = get('client_access_code').strip()
            birthdate = get('birthdate').strip()
            try:
                height_cm = float(get('height_cm') or 0)
            except ValueError:
                height_cm = 0
            try:
                weight_kg = float(get('weight_kg') or 0)
            except ValueError:
                weight_kg = 0
            objectives = get('objectives').strip()
            plan_start_date = get('plan_start_date').strip()
            plan_end_date = get('plan_end_date').strip()
            try:
                plan_amount = float(get('plan_amount') or 0)
            except ValueError:
                plan_amount = 0
            plan_notes = get('plan_notes').strip()
            if name:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute(
                    "INSERT INTO clients(name, phone, email, client_access_code, birthdate, height_cm, weight_kg, objectives, plan_start_date, plan_end_date, plan_amount, plan_notes, created_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,datetime('now'))",
                    (name, phone or None, email or None, client_access_code or None, birthdate or None, height_cm, weight_kg, objectives or None, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes or None),
                )
                client_id = cur.lastrowid
                if not client_access_code:
                    cur.execute("UPDATE clients SET client_access_code = ? WHERE id = ?", (f'C{client_id}', client_id))
                conn.commit()
                conn.close()
                sync_client_payment_plan(client_id, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes)
            self.send_response(303)
            self.send_header('Location', '/clients?msg=' + urllib.parse.quote('Cliente creado'))
            self.end_headers()
            return

        if path == '/assign_client_diet':
            assign_perf_enabled = str(os.environ.get('ASSIGN_DIET_PERF_LOG', '')).strip().lower() in ('1', 'true', 'yes', 'on')

            def assign_mark(stage_name, stage_started_at):
                if not assign_perf_enabled:
                    return
                elapsed_ms = (time.perf_counter() - stage_started_at) * 1000.0
                print(
                    f"[assign-diet] stage={stage_name} ms={elapsed_ms:.3f} client_id={client_id} template_diet_id={template_diet_id}",
                    flush=True,
                )

            client_id = get('client_id').strip()
            template_diet_id = get('diet_id').strip()
            start_date = get('start_date').strip()
            end_date = get('end_date').strip()
            notes = get('notes').strip()
            return_to = get('return_to').strip() or '/clients'
            assign_t0 = time.perf_counter()
            try:
                client_id_i = int(client_id)
                template_diet_id_i = int(template_diet_id)
            except Exception:
                self.send_response(303)
                self.send_header('Location', '/clients?msg=' + urllib.parse.quote('No se pudo asignar la dieta'))
                self.end_headers()
                return
            assign_mark('parse_ids', assign_t0)

            lookup_t0 = time.perf_counter()
            client_row = get_client_by_id(client_id_i)
            client_name = client_row[1] if client_row else ''
            assign_mark('client_lookup', lookup_t0)

            clone_t0 = time.perf_counter()
            assigned_diet_id = clone_diet_template_for_client(template_diet_id_i, client_name)
            assign_mark('clone_template', clone_t0)
            if not assigned_diet_id:
                self.send_response(303)
                self.send_header('Location', '/clients?msg=' + urllib.parse.quote('No se pudo clonar la plantilla'))
                self.end_headers()
                return

            tx_t0 = time.perf_counter()
            conn = sqlite3.connect(DB_PATH)
            try:
                cur = conn.cursor()
                deactivate_t0 = time.perf_counter()
                cur.execute(
                    "UPDATE client_diet_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), CAST(date('now') AS TEXT)) WHERE client_id = ? AND is_active = 1",
                    (client_id_i,),
                )
                assign_mark('deactivate_active_history', deactivate_t0)
                history_insert_t0 = time.perf_counter()
                cur.execute(
                    "INSERT INTO client_diet_history(client_id, diet_id, template_diet_id, start_date, end_date, is_active, notes, created_at) VALUES(?,?,?,?,?,?,?,datetime('now'))",
                    (client_id_i, assigned_diet_id, template_diet_id_i, start_date or None, end_date or None, 1, notes or None),
                )
                assign_mark('insert_history', history_insert_t0)
                commit_t0 = time.perf_counter()
                conn.commit()
                assign_mark('commit_history_tx', commit_t0)
            except Exception:
                try:
                    conn.rollback()
                except Exception:
                    pass
                try:
                    cleanup_conn = sqlite3.connect(DB_PATH)
                    cleanup_cur = cleanup_conn.cursor()
                    cleanup_cur.execute("DELETE FROM diet_supplements WHERE diet_id = ?", (assigned_diet_id,))
                    cleanup_cur.execute("DELETE FROM diet_items WHERE diet_id = ?", (assigned_diet_id,))
                    cleanup_cur.execute("DELETE FROM diet_day_config WHERE diet_id = ?", (assigned_diet_id,))
                    cleanup_cur.execute("DELETE FROM diet_meals WHERE diet_id = ?", (assigned_diet_id,))
                    cleanup_cur.execute("DELETE FROM diets WHERE id = ?", (assigned_diet_id,))
                    cleanup_conn.commit()
                    cleanup_conn.close()
                except Exception:
                    pass
                raise
            finally:
                conn.close()
            assign_mark('history_transaction_total', tx_t0)
            assign_mark('request_total', assign_t0)
            location = return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Dieta asignada')
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/update_diet_display_number':
            did = get('diet_id').strip()
            display_number_raw = get('display_number').strip()
            try:
                did_i = int(did)
                display_number_i = int(display_number_raw)
            except Exception:
                self.send_response(303)
                self.send_header('Location', '/diets?msg=' + urllib.parse.quote('Número inválido'))
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE diets SET display_number = ? WHERE id = ?", (display_number_i, did_i))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/diets?msg=' + urllib.parse.quote('Número de dieta actualizado'))
            self.end_headers()
            return

        if path == '/deactivate_client_diet':
            history_id = get('history_id').strip()
            client_id = get('client_id').strip()
            try:
                history_id_i = int(history_id)
                client_id_i = int(client_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE client_diet_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), CAST(date('now') AS TEXT)) WHERE id = ?",
                (history_id_i,),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', f'/client_profile?id={client_id_i}&msg=' + urllib.parse.quote('Dieta cerrada'))
            self.end_headers()
            return

        if path == '/activate_client_diet':
            history_id = get('history_id').strip()
            client_id = get('client_id').strip()
            return_to = get('return_to').strip()
            try:
                history_id_i = int(history_id)
                client_id_i = int(client_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "SELECT id FROM client_diet_history WHERE id = ? AND client_id = ?",
                (history_id_i, client_id_i),
            )
            row = cur.fetchone()
            if row is None:
                conn.close()
                self.send_response(404)
                self.end_headers()
                return

            cur.execute(
                "UPDATE client_diet_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), CAST(date('now') AS TEXT)) WHERE client_id = ? AND is_active = 1 AND id <> ?",
                (client_id_i, history_id_i),
            )
            cur.execute(
                "UPDATE client_diet_history SET is_active = 1, end_date = NULL WHERE id = ? AND client_id = ?",
                (history_id_i, client_id_i),
            )
            conn.commit()
            conn.close()

            location_base = return_to or f'/client_profile?id={client_id_i}'
            location = location_base + ('&' if '?' in location_base else '?') + 'msg=' + urllib.parse.quote('Dieta activada')
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/update_client_diet_dates':
            history_id = get('history_id').strip()
            client_id = get('client_id').strip()
            start_date = get('start_date').strip()
            end_date = get('end_date').strip()
            return_to = get('return_to').strip()
            try:
                history_id_i = int(history_id)
                client_id_i = int(client_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "SELECT COALESCE(is_active, 0) FROM client_diet_history WHERE id = ? AND client_id = ?",
                (history_id_i, client_id_i),
            )
            row = cur.fetchone()
            if row is None:
                conn.close()
                self.send_response(404)
                self.end_headers()
                return

            is_active = int(row[0] or 0)
            if is_active == 1:
                cur.execute(
                    "UPDATE client_diet_history SET start_date = ? WHERE id = ? AND client_id = ?",
                    (start_date or None, history_id_i, client_id_i),
                )
                msg = 'Fecha de inicio actualizada'
            else:
                cur.execute(
                    "UPDATE client_diet_history SET start_date = ?, end_date = ? WHERE id = ? AND client_id = ?",
                    (start_date or None, end_date or None, history_id_i, client_id_i),
                )
                msg = 'Fechas actualizadas'

            conn.commit()
            conn.close()
            location_base = return_to or f'/client_profile?id={client_id_i}'
            location = location_base + ('&' if '?' in location_base else '?') + 'msg=' + urllib.parse.quote(msg)
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/assign_client_training':
            client_id = get('client_id').strip()
            exercise_id = get('exercise_id').strip()
            routine_id = get('routine_id').strip()
            training_name = get('training_name').strip()
            start_date = get('start_date').strip()
            end_date = get('end_date').strip()
            notes = get('notes').strip()
            return_to = get('return_to').strip() or '/clients'
            try:
                client_id_i = int(client_id)
            except Exception:
                self.send_response(303)
                self.send_header('Location', '/clients?msg=' + urllib.parse.quote('No se pudo asignar el entrenamiento'))
                self.end_headers()
                return
            exercise_id_i = None
            if exercise_id:
                try:
                    exercise_id_i = int(exercise_id)
                except Exception:
                    exercise_id_i = None

            routine_id_i = None
            if routine_id:
                try:
                    routine_id_i = int(routine_id)
                except Exception:
                    routine_id_i = None

            template_routine_id_i = None
            assigned_routine_id_i = None
            if routine_id_i:
                client_rows = [r for r in get_clients() if r[0] == client_id_i]
                client_name = client_rows[0][1] if client_rows else ''
                assigned_routine_id_i = clone_routine_template_for_client(routine_id_i, client_name)
                if not assigned_routine_id_i:
                    self.send_response(303)
                    self.send_header('Location', '/clients?msg=' + urllib.parse.quote('No se pudo asignar la rutina'))
                    self.end_headers()
                    return
                template_routine_id_i = routine_id_i

            conn = sqlite3.connect(DB_PATH)
            try:
                cur = conn.cursor()
                cur.execute(
                    "UPDATE client_training_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), CAST(date('now') AS TEXT)) WHERE client_id = ? AND is_active = 1",
                    (client_id_i,),
                )
                cur.execute(
                    """
                    INSERT INTO client_training_history(
                        client_id, exercise_id, routine_id, template_routine_id, training_name,
                        start_date, end_date, is_active, notes, created_at
                    )
                    VALUES(?,?,?,?,?,?,?,?,?,datetime('now'))
                    """,
                    (
                        client_id_i,
                        exercise_id_i,
                        assigned_routine_id_i,
                        template_routine_id_i,
                        training_name or None,
                        start_date or None,
                        end_date or None,
                        1,
                        notes or None,
                    ),
                )
                conn.commit()
            except Exception:
                try:
                    conn.rollback()
                except Exception:
                    pass
                if assigned_routine_id_i:
                    try:
                        cleanup_conn = sqlite3.connect(DB_PATH)
                        cleanup_cur = cleanup_conn.cursor()
                        cleanup_cur.execute("DELETE FROM routine_items WHERE routine_id = ?", (assigned_routine_id_i,))
                        cleanup_cur.execute("DELETE FROM routine_days WHERE routine_id = ?", (assigned_routine_id_i,))
                        cleanup_cur.execute("DELETE FROM routines WHERE id = ?", (assigned_routine_id_i,))
                        cleanup_conn.commit()
                        cleanup_conn.close()
                    except Exception:
                        pass
                raise
            finally:
                conn.close()
            assigned_label = 'Rutina asignada' if assigned_routine_id_i else 'Entrenamiento asignado'
            location = return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote(assigned_label)
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/deactivate_client_training':
            history_id = get('history_id').strip()
            client_id = get('client_id').strip()
            return_to = get('return_to').strip()
            try:
                history_id_i = int(history_id)
                client_id_i = int(client_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE client_training_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), CAST(date('now') AS TEXT)) WHERE id = ?",
                (history_id_i,),
            )
            conn.commit()
            conn.close()
            location_base = return_to or f'/client_profile?id={client_id_i}'
            location = location_base + ('&' if '?' in location_base else '?') + 'msg=' + urllib.parse.quote('Entrenamiento cerrado')
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/activate_client_training':
            history_id = get('history_id').strip()
            client_id = get('client_id').strip()
            return_to = get('return_to').strip()
            try:
                history_id_i = int(history_id)
                client_id_i = int(client_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "SELECT id FROM client_training_history WHERE id = ? AND client_id = ?",
                (history_id_i, client_id_i),
            )
            row = cur.fetchone()
            if row is None:
                conn.close()
                self.send_response(404)
                self.end_headers()
                return

            cur.execute(
                "UPDATE client_training_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), CAST(date('now') AS TEXT)) WHERE client_id = ? AND is_active = 1 AND id <> ?",
                (client_id_i, history_id_i),
            )
            cur.execute(
                "UPDATE client_training_history SET is_active = 1, end_date = NULL WHERE id = ? AND client_id = ?",
                (history_id_i, client_id_i),
            )
            conn.commit()
            conn.close()

            location_base = return_to or f'/client_profile?id={client_id_i}'
            location = location_base + ('&' if '?' in location_base else '?') + 'msg=' + urllib.parse.quote('Rutina activada')
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/add_payment':
            client_id = get('client_id').strip()
            start_date = get('start_date').strip()
            end_date = get('end_date').strip()
            notes = get('notes').strip()
            try:
                amount = float(get('amount') or 0)
            except ValueError:
                amount = 0
            try:
                client_id_i = int(client_id)
            except Exception:
                client_id_i = None
            if client_id_i and start_date and end_date:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute(
                    "INSERT INTO payment_plans(client_id, start_date, end_date, amount, notes, created_at) VALUES(?,?,?,?,?,datetime('now'))",
                    (client_id_i, start_date, end_date, amount, notes or None),
                )
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', '/payments?msg=' + urllib.parse.quote('Plan de pago creado'))
            self.end_headers()
            return

        if path == '/add_diet_item':
            diet_id = get('diet_id').strip()
            food_id = get('food_id').strip()
            day_of_week = get('day_of_week').strip()
            meal_time = get('meal_time').strip()
            quantity = get('quantity').strip()
            note = get('note').strip()
            try:
                diet_id_i = int(diet_id)
                food_id_i = int(food_id)
            except Exception:
                diet_id_i = None
                food_id_i = None
            if diet_id_i and food_id_i:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute(
                    "INSERT INTO diet_items(diet_id, food_id, day_of_week, meal_time, quantity, note) VALUES(?,?,?,?,?,?)",
                    (diet_id_i, food_id_i, day_of_week or None, meal_time or None, quantity or None, note or None),
                )
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', f'/diets?diet_id={diet_id}&msg=' + urllib.parse.quote('Alimento añadido a la dieta'))
            self.end_headers()
            return

        if path == '/add_routine':
            name = get('name').strip()
            description = get('description').strip()
            new_routine_id = None
            if name:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute(
                    "INSERT INTO routines(name, description, created_at) VALUES(?,?,datetime('now'))",
                    (name, description or None),
                )
                new_routine_id = cur.lastrowid
                conn.commit()
                conn.close()
                ensure_routine_days_for_routine(new_routine_id)
            self.send_response(303)
            if new_routine_id:
                self.send_header('Location', f'/routines?routine_id={new_routine_id}&msg=' + urllib.parse.quote('Rutina creada'))
            else:
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('Rutina creada'))
            self.end_headers()
            return

        if path == '/update_routine_name':
            routine_id = get('routine_id').strip()
            name = get('name').strip()
            return_to = get('return_to').strip() or '/routines'
            try:
                routine_id_i = int(routine_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            if not name:
                self.send_response(303)
                self.send_header('Location', return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('El nombre no puede estar vacío'))
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE routines SET name = ? WHERE id = ?", (name, routine_id_i))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Rutina renombrada'))
            self.end_headers()
            return

        if path == '/update_routine_day':
            routine_id = get('routine_id').strip()
            day_index = get('day_index').strip()
            day_name = get('day_name').strip()
            day_type = get('day_type').strip().lower()
            try:
                routine_id_i = int(routine_id)
                day_index_i = int(day_index)
            except Exception:
                self.send_response(303)
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('No se pudo actualizar el día'))
                self.end_headers()
                return

            if not day_name:
                day_name = f'Día {day_index_i + 1}'
            if day_type not in ('train', 'rest'):
                day_type = 'train'

            ensure_routine_days_for_routine(routine_id_i)
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE routine_days SET day_name = ?, day_type = ? WHERE routine_id = ? AND day_index = ?",
                (day_name, day_type, routine_id_i, day_index_i),
            )
            cur.execute(
                "UPDATE routine_items SET day_name = ?, day_index = ? WHERE routine_id = ? AND day_index = ?",
                (day_name, day_index_i, routine_id_i, day_index_i),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header(
                'Location',
                f'/routines?routine_id={routine_id_i}&msg=' + urllib.parse.quote('Día actualizado') + f'#routine-day-{day_index_i}'
            )
            self.end_headers()
            return

        if path == '/delete_routine':
            routine_id = get('id').strip()
            try:
                routine_id_i = int(routine_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE client_training_history SET template_routine_id = NULL WHERE template_routine_id = ?", (routine_id_i,))
            cur.execute("DELETE FROM client_training_history WHERE routine_id = ?", (routine_id_i,))
            cur.execute("DELETE FROM routine_items WHERE routine_id = ?", (routine_id_i,))
            cur.execute("DELETE FROM routine_days WHERE routine_id = ?", (routine_id_i,))
            cur.execute("DELETE FROM routines WHERE id = ?", (routine_id_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/routines?msg=' + urllib.parse.quote('Rutina borrada'))
            self.end_headers()
            return

        if path == '/add_routine_item':
            routine_id = get('routine_id').strip()
            day_name = get('day_name').strip()
            day_index = get('day_index').strip()
            exercise_id = get('exercise_id').strip()
            sets_text = get('sets_text').strip()
            reps_text = get('reps_text').strip()
            notes = get('notes').strip()
            try:
                routine_id_i = int(routine_id)
            except Exception:
                self.send_response(303)
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('No se pudo añadir el ejercicio'))
                self.end_headers()
                return
            exercise_id_i = None
            if exercise_id:
                try:
                    exercise_id_i = int(exercise_id)
                except Exception:
                    exercise_id_i = None

            day_index_i = None
            if day_index:
                try:
                    day_index_i = int(day_index)
                except Exception:
                    day_index_i = None

            ensure_routine_days_for_routine(routine_id_i)
            if day_index_i is None:
                routine_days_lookup = {str(day_name_row[1] or '').strip(): int(day_name_row[0]) for day_name_row in get_routine_days(routine_id_i)}
                day_index_i = routine_days_lookup.get(day_name, 0)
            routine_days_by_idx = {int(row[0]): row for row in get_routine_days(routine_id_i)}
            selected_day = routine_days_by_idx.get(day_index_i)
            selected_day_name = str(selected_day[1]).strip() if selected_day else (day_name or 'Lunes')

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT COALESCE(MAX(sort_order), 0) + 1 FROM routine_items WHERE routine_id = ?", (routine_id_i,))
            next_sort_order = cur.fetchone()[0] or 1
            cur.execute(
                "INSERT INTO routine_items(routine_id, day_name, day_index, exercise_id, sets_text, reps_text, notes, sort_order) VALUES(?,?,?,?,?,?,?,?)",
                (routine_id_i, selected_day_name, day_index_i, exercise_id_i, sets_text or None, reps_text or None, notes or None, next_sort_order),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', f'/routines?routine_id={routine_id_i}&msg=' + urllib.parse.quote('Ejercicio añadido a la rutina'))
            self.end_headers()
            return

        if path == '/delete_routine_item':
            item_id = get('id').strip()
            routine_id = get('routine_id').strip()
            try:
                item_id_i = int(item_id)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            try:
                routine_id_i = int(routine_id)
            except Exception:
                routine_id_i = None
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM routine_items WHERE id = ?", (item_id_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            if routine_id_i:
                self.send_header('Location', f'/routines?routine_id={routine_id_i}&msg=' + urllib.parse.quote('Ejercicio eliminado'))
            else:
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('Ejercicio eliminado'))
            self.end_headers()
            return

        if path == '/update_routine_item':
            item_id = get('id').strip()
            sets_text = get('sets_text').strip()
            reps_text = get('reps_text').strip()
            routine_id = get('routine_id').strip()
            try:
                item_id_i = int(item_id)
            except Exception:
                if self.headers.get('X-Requested-With', '').lower() == 'fetch':
                    return self.send_json({'error': 'invalid id'}, status=400)
                self.send_response(303)
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('No se pudo actualizar el ejercicio'))
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE routine_items SET sets_text = ?, reps_text = ? WHERE id = ?",
                (sets_text or None, reps_text or None, item_id_i),
            )
            conn.commit()
            conn.close()

            if self.headers.get('X-Requested-With', '').lower() == 'fetch':
                return self.send_json({'ok': True})

            if routine_id:
                self.send_response(303)
                self.send_header('Location', f'/routines?routine_id={routine_id}&msg=' + urllib.parse.quote('Ejercicio actualizado'))
                self.end_headers()
                return
            self.send_response(303)
            self.send_header('Location', '/routines?msg=' + urllib.parse.quote('Ejercicio actualizado'))
            self.end_headers()
            return

        if path == '/reorder_routine_items':
            routine_id = get('routine_id').strip()
            day_index = get('day_index').strip()
            item_ids_raw = get('item_ids').strip()
            try:
                routine_id_i = int(routine_id)
                day_index_i = int(day_index)
            except Exception:
                if self.headers.get('X-Requested-With', '').lower() == 'fetch':
                    return self.send_json({'error': 'invalid parameters'}, status=400)
                self.send_response(303)
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('No se pudo reordenar'))
                self.end_headers()
                return

            parsed_ids = []
            for token in item_ids_raw.split(','):
                token = token.strip()
                if not token:
                    continue
                try:
                    parsed_ids.append(int(token))
                except Exception:
                    continue

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "SELECT id FROM routine_items WHERE routine_id = ? AND day_index = ? ORDER BY sort_order, id",
                (routine_id_i, day_index_i),
            )
            existing_ids = [int(r[0]) for r in cur.fetchall()]
            valid_set = set(existing_ids)
            ordered_ids = [iid for iid in parsed_ids if iid in valid_set]
            for iid in existing_ids:
                if iid not in ordered_ids:
                    ordered_ids.append(iid)

            base_sort = (day_index_i + 1) * 100000
            for idx, iid in enumerate(ordered_ids, start=1):
                cur.execute(
                    "UPDATE routine_items SET sort_order = ? WHERE id = ?",
                    (base_sort + idx, iid),
                )
            conn.commit()
            conn.close()

            if self.headers.get('X-Requested-With', '').lower() == 'fetch':
                return self.send_json({'ok': True})
            self.send_response(303)
            self.send_header('Location', f'/routines?routine_id={routine_id_i}&msg=' + urllib.parse.quote('Orden actualizado'))
            self.end_headers()
            return

        if path == '/edit_client':
            def getp(k):
                return params.get(k, [''])[0]

            try:
                cid = int(getp('id'))
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            name = getp('name').strip()
            phone = getp('phone').strip()
            email = getp('email').strip()
            client_access_code = getp('client_access_code').strip()
            birthdate = getp('birthdate').strip()
            try:
                height_cm = float(getp('height_cm') or 0)
            except Exception:
                height_cm = 0
            try:
                weight_kg = float(getp('weight_kg') or 0)
            except Exception:
                weight_kg = 0
            objectives = getp('objectives').strip()
            plan_start_date = getp('plan_start_date').strip()
            plan_end_date = getp('plan_end_date').strip()
            try:
                plan_amount = float(getp('plan_amount') or 0)
            except Exception:
                plan_amount = 0
            plan_notes = getp('plan_notes').strip()
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            if not client_access_code:
                cur.execute("SELECT COALESCE(client_access_code, '') FROM clients WHERE id = ?", (cid,))
                row = cur.fetchone()
                client_access_code = (row[0] or '').strip() if row else ''
            if not client_access_code:
                client_access_code = f'C{cid}'
            cur.execute(
                "UPDATE clients SET name=?, phone=?, email=?, client_access_code=?, birthdate=?, height_cm=?, weight_kg=?, objectives=?, plan_start_date=?, plan_end_date=?, plan_amount=?, plan_notes=? WHERE id=?",
                (name, phone or None, email or None, client_access_code, birthdate or None, height_cm, weight_kg, objectives or None, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes or None, cid),
            )
            conn.commit()
            conn.close()
            sync_client_payment_plan(cid, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes)
            self.send_response(303)
            self.send_header('Location', '/clients?msg=' + urllib.parse.quote('Cliente actualizado'))
            self.end_headers()
            return

        if path == '/set_client_steps_goal':
            client_id = get('client_id').strip()
            return_to = get('return_to').strip() or '/clients'
            try:
                client_id_i = int(client_id)
            except Exception:
                self.send_response(303)
                self.send_header('Location', return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Cliente inválido'))
                self.end_headers()
                return

            goal_raw = get('daily_steps_goal').strip()
            if not goal_raw:
                goal_i = 0
            else:
                digits = re.sub(r'[^0-9]', '', goal_raw)
                if not digits:
                    self.send_response(303)
                    self.send_header('Location', return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Objetivo inválido'))
                    self.end_headers()
                    return
                goal_i = int(digits)

            if goal_i < 0 or goal_i > 100000:
                self.send_response(303)
                self.send_header('Location', return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Objetivo fuera de rango'))
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE clients SET daily_steps_goal = ? WHERE id = ?", (goal_i, client_id_i))
            conn.commit()
            conn.close()

            self.send_response(303)
            self.send_header('Location', return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Objetivo de pasos actualizado'))
            self.end_headers()
            return

        if path == '/edit_payment':
            def getp(k):
                return params.get(k, [''])[0]

            try:
                pid = int(getp('id'))
                client_id_i = int(getp('client_id'))
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            start_date = getp('start_date').strip()
            end_date = getp('end_date').strip()
            notes = getp('notes').strip()
            try:
                amount = float(getp('amount') or 0)
            except Exception:
                amount = 0
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE payment_plans SET client_id=?, start_date=?, end_date=?, amount=?, notes=? WHERE id=?",
                (client_id_i, start_date, end_date, amount, notes or None, pid),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/payments?msg=' + urllib.parse.quote('Plan de pago actualizado'))
            self.end_headers()
            return

        if path == '/delete_diet':
            did = params.get('id', [''])[0]
            try:
                did_i = int(did)
            except Exception:
                did_i = None
            if did_i:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute("UPDATE client_diet_history SET template_diet_id = NULL WHERE template_diet_id = ?", (did_i,))
                cur.execute("DELETE FROM client_diet_history WHERE diet_id = ?", (did_i,))
                cur.execute("DELETE FROM diet_items WHERE diet_id = ?", (did_i,))
                cur.execute("DELETE FROM diet_meals WHERE diet_id = ?", (did_i,))
                cur.execute("DELETE FROM diet_day_config WHERE diet_id = ?", (did_i,))
                cur.execute("DELETE FROM diet_supplements WHERE diet_id = ?", (did_i,))
                cur.execute("DELETE FROM diets WHERE id = ?", (did_i,))
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', '/diets?msg=' + urllib.parse.quote('Dieta borrada'))
            self.end_headers()
            return

        if path == '/delete_client':
            cid = params.get('id', [''])[0]
            try:
                cid_i = int(cid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT diet_id FROM client_diet_history WHERE client_id = ?", (cid_i,))
            client_diet_ids = [int(r[0]) for r in cur.fetchall() if r[0]]
            cur.execute(
                "SELECT routine_id FROM client_training_history WHERE client_id = ? AND COALESCE(template_routine_id, 0) > 0",
                (cid_i,),
            )
            client_routine_ids = [int(r[0]) for r in cur.fetchall() if r and r[0]]
            cur.execute("DELETE FROM client_diet_history WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM client_training_history WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM client_fasting_weights WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM client_daily_steps WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM payment_plans WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM clients WHERE id = ?", (cid_i,))
            for did in client_diet_ids:
                cur.execute("DELETE FROM diet_items WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diet_meals WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diet_day_config WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diet_supplements WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diets WHERE id = ? AND COALESCE(is_template, 1) = 0", (did,))
            for rid in client_routine_ids:
                cur.execute("DELETE FROM routine_items WHERE routine_id = ?", (rid,))
                cur.execute("DELETE FROM routine_days WHERE routine_id = ?", (rid,))
                cur.execute("DELETE FROM routines WHERE id = ?", (rid,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/clients?msg=' + urllib.parse.quote('Cliente borrado'))
            self.end_headers()
            return

        if path == '/delete_payment':
            pid = params.get('id', [''])[0]
            try:
                pid_i = int(pid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM payment_plans WHERE id = ?", (pid_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/payments?msg=' + urllib.parse.quote('Plan de pago borrado'))
            self.end_headers()
            return

        if path == '/delete_diet_item':
            item_id = params.get('id', [''])[0]
            diet_id = params.get('diet_id', [''])[0]
            try:
                item_id_i = int(item_id)
            except Exception:
                item_id_i = None
            if item_id_i:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute("DELETE FROM diet_items WHERE id = ?", (item_id_i,))
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', f'/diets?diet_id={diet_id}&msg=' + urllib.parse.quote('Alimento borrado de la dieta'))
            self.end_headers()
            return

        if path == '/edit':
            def getp(k):
                return params.get(k, [''])[0]

            try:
                fid = int(getp('id'))
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            name = getp('name').strip()
            brand = getp('brand').strip()
            cat = getp('category').strip()
            has_gluten = parse_gluten_input(getp('has_gluten'))
            barcode = getp('barcode').strip()
            keywords = getp('keywords').strip()
            is_active = 0 if getp('is_active').strip() == '0' else 1
            is_verified = 1 if getp('is_verified').strip() == '1' else 0
            calories = parse_numeric_input(getp('calories'))
            protein = parse_numeric_input(getp('protein'))
            carbs = parse_numeric_input(getp('carbs'))
            fats = parse_numeric_input(getp('fats'))
            serving = format_serving_size(getp('serving_amount'), getp('serving_unit'), getp('existing_serving_size'))
            existing_photo_path = getp('existing_photo_path').strip()
            photo_data_url = getp('photo_data_url').strip()
            photo_path = save_food_photo_data_url(photo_data_url) if photo_data_url else (existing_photo_path or None)
            nutrition_mode = getp('nutrition_mode').strip() or 'per100'
            if nutrition_mode not in ('per100', 'unit'):
                nutrition_mode = 'per100'
            per100_unit = getp('per100_unit').strip().lower() or 'g'
            if per100_unit not in ('g', 'ml'):
                per100_unit = 'g'
            if nutrition_mode == 'unit' and not serving:
                serving = '1 unidad'

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cat_id = None
            if cat:
                try:
                    cat_id = int(cat)
                except Exception:
                    cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (cat,))
                    cur.execute("SELECT id FROM categories WHERE name= ?", (cat,))
                    row = cur.fetchone()
                    cat_id = row[0] if row else None

            cur.execute(
                "UPDATE foods SET name=?, brand=?, category_id=?, calories=?, protein=?, carbs=?, fats=?, serving_size=?, photo_path=?, nutrition_mode=?, per100_unit=?, barcode=?, keywords=?, is_active=?, is_verified=?, has_gluten=? WHERE id=?",
                (name, brand or None, cat_id, calories, protein, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, barcode or None, keywords or None, is_active, is_verified, has_gluten, fid),
            )
            refresh_food_search_row(cur, fid)
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Alimento actualizado'))
            self.end_headers()
            return

        if path == '/edit_exercise':
            def getp(k):
                return params.get(k, [''])[0]

            try:
                eid = int(getp('id'))
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            name = getp('name').strip()
            category_id = getp('category_id').strip()
            category_id_2 = getp('category_id_2').strip()
            video_url = getp('video_url').strip()
            machine_url = getp('machine_url').strip()
            notes = getp('notes').strip()
            cat_id = None
            if category_id:
                try:
                    cat_id = int(category_id)
                except Exception:
                    cat_id = None
            cat_id_2 = None
            if category_id_2:
                try:
                    cat_id_2 = int(category_id_2)
                except Exception:
                    cat_id_2 = None
            if cat_id_2 is not None and cat_id_2 == cat_id:
                cat_id_2 = None
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE exercises SET name=?, exercise_category_id=?, exercise_category_id_2=?, video_url=?, machine_url=?, notes=? WHERE id=?",
                (name, cat_id, cat_id_2, video_url or None, machine_url or None, notes or None, eid),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Ejercicio actualizado'))
            self.end_headers()
            return

        if path == '/delete_food':
            fid = params.get('id', [''])[0]
            try:
                fid_i = int(fid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("DELETE FROM foods_search WHERE food_id = ?", (fid_i,))
            cur.execute("DELETE FROM foods WHERE id = ?", (fid_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Alimento borrado'))
            self.end_headers()
            return

        if path == '/duplicate_food':
            fid = params.get('id', [''])[0]
            try:
                fid_i = int(fid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                """
                SELECT name, brand, category_id, calories, protein, carbs, fats, serving_size,
                      photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified, has_gluten
                FROM foods
                WHERE id = ?
                """,
                (fid_i,),
            )
            row = cur.fetchone()
            if not row:
                conn.close()
                self.send_response(303)
                self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Alimento no encontrado'))
                self.end_headers()
                return

            original_name = row[0] or 'Alimento'
            duplicate_name = f"{original_name} (copia)"
            cur.execute(
                """
                INSERT INTO foods(name, brand, category_id, calories, protein, carbs, fats, serving_size,
                                  photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified, has_gluten)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    duplicate_name,
                    row[1],
                    row[2],
                    row[3],
                    row[4],
                    row[5],
                    row[6],
                    row[7],
                    row[8],
                    row[9],
                    row[10],
                    row[11],
                    row[12],
                    row[13],
                    row[14],
                    row[15],
                ),
            )
            refresh_food_search_row(cur, cur.lastrowid)
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Alimento duplicado'))
            self.end_headers()
            return

        if path == '/delete_exercise':
            eid = params.get('id', [''])[0]
            try:
                eid_i = int(eid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE client_training_history SET exercise_id = NULL WHERE exercise_id = ?", (eid_i,))
            cur.execute("DELETE FROM exercises WHERE id = ?", (eid_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Ejercicio borrado'))
            self.end_headers()
            return

        if path == '/add_category':
            name = params.get('name', [''])[0].strip()
            if name:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (name,))
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Categoría creada'))
            self.end_headers()
            return

        if path == '/add_brand':
            name = params.get('name', [''])[0].strip()
            if name:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute("INSERT OR IGNORE INTO brands(name) VALUES(?)", (name,))
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Marca creada'))
            self.end_headers()
            return

        if path == '/add_exercise_category':
            name = params.get('name', [''])[0].strip()
            if name:
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute("INSERT OR IGNORE INTO exercise_categories(name) VALUES(?)", (name,))
                conn.commit()
                conn.close()
            self.send_response(303)
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Grupo muscular creado'))
            self.end_headers()
            return

        if path == '/delete_exercise_category':
            cid = params.get('id', [''])[0]
            try:
                cid_i = int(cid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE exercises SET exercise_category_id = NULL WHERE exercise_category_id = ?", (cid_i,))
            cur.execute("UPDATE exercises SET exercise_category_id_2 = NULL WHERE exercise_category_id_2 = ?", (cid_i,))
            cur.execute("DELETE FROM exercise_categories WHERE id = ?", (cid_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Grupo muscular borrado'))
            self.end_headers()
            return

        if path == '/delete_category':
            cid = params.get('id', [''])[0]
            try:
                cid_i = int(cid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("UPDATE foods SET category_id = NULL WHERE category_id = ?", (cid_i,))
            cur.execute("DELETE FROM categories WHERE id = ?", (cid_i,))
            rebuild_foods_search_index(cur)
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Categoría borrada'))
            self.end_headers()
            return

        if path == '/delete_brand':
            bid = params.get('id', [''])[0]
            try:
                bid_i = int(bid)
            except Exception:
                self.send_response(400)
                self.end_headers()
                return
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT name FROM brands WHERE id = ?", (bid_i,))
            row = cur.fetchone()
            if row:
                brand_name = row[0]
                cur.execute("UPDATE foods SET brand = NULL WHERE brand = ?", (brand_name,))
                cur.execute("DELETE FROM brands WHERE id = ?", (bid_i,))
                rebuild_foods_search_index(cur)
                conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/foods?msg=' + urllib.parse.quote('Marca borrada'))
            self.end_headers()
            return

        # unknown
        self.send_response(404)
        self.end_headers()

    # keep server robust
    def handle_one_request(self):
        sqlite3.begin_request()
        try:
            super().handle_one_request()
        except ConnectionResetError:
            # Client disconnected before completing the request.
            return
        except Exception as e:
            import traceback
            traceback.print_exc()
            try:
                self.send_error(500, f'Internal server error: {e}')
            except Exception:
                pass
        finally:
            try:
                sqlite3.end_request()
            except Exception:
                pass


def run():
    print("Using PostgreSQL" if os.environ.get('DATABASE_URL', '').strip() else "Using SQLite", flush=True)
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(STATIC_BASE_DIR, exist_ok=True)
    os.makedirs(UPLOADS_FOODS_DIR, exist_ok=True)
    sqlite3.begin_request()
    try:
        ensure_catalog_schema(DB_PATH)
        ensure_default_food_categories(DB_PATH)
        ensure_brand_column()
        ensure_exercises_table()
        ensure_routines_table()
        ensure_diets_table()
        ensure_clients_table()
        ensure_payment_plans_table()
        ensure_client_history_tables()
        ensure_fasting_weights_table()
        ensure_client_daily_steps_table()
        ensure_diet_builder_tables()
        ensure_app_settings_table()
    finally:
        sqlite3.end_request()
    port = PORT
    server = HTTPServer((HOST, port), Handler)
    print(f"Servidor iniciado en http://{HOST}:{port} — Ctrl-C para detener")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("Detenido")
        server.server_close()


if __name__ == '__main__':
    run()
