#!/usr/bin/env python3
"""Servidor HTTP simple para gestionar alimentos y ejercicios (UI + JSON API).
"""
from http.server import HTTPServer, BaseHTTPRequestHandler
import sqlite3
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
from difflib import SequenceMatcher

from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib import colors

BASE_DIR = os.path.dirname(os.path.dirname(__file__))
STATIC_DIR = "static"
DATA_DIR = os.environ.get("DATA_DIR", os.path.join(BASE_DIR, "data"))
DB_PATH = os.path.join(DATA_DIR, "foods.db")
STATIC_BASE_DIR = os.path.join(os.path.dirname(__file__), STATIC_DIR)
UPLOADS_DIR = os.environ.get("UPLOADS_DIR", os.path.join(DATA_DIR, "uploads"))
UPLOADS_FOODS_DIR = os.path.join(UPLOADS_DIR, "foods")
HOST = "0.0.0.0"
PORT = int(os.environ.get("PORT", "8005"))

# migrations
_schema_checked = False

DEFAULT_FOOD_CATEGORIES = [
    'Carnes', 'Pescados', 'Huevos', 'Lácteos', 'Arroz', 'Pasta', 'Patata/Batata',
    'Frutas', 'Verduras', 'Legumbres', 'Frutos secos', 'Aceites', 'Grasas saludables',
    'Salsas', 'Embutidos', 'Bebidas', 'Dulces', 'Suplementos'
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


def query_terms(query):
    return [t for t in re.findall(r'[a-z0-9]+', normalize_text(query)) if t]


def build_fts_query(query):
    terms = query_terms(query)
    if not terms:
        return ''
    return ' '.join([f'"{t}"*' for t in terms])


def rebuild_foods_search_index(cur):
    try:
        cur.execute("DELETE FROM foods_search")
        cur.execute(
            """
            INSERT INTO foods_search (food_id, name, brand, category, barcode, keywords, searchable)
            SELECT
                f.id,
                COALESCE(f.name, ''),
                COALESCE(f.brand, ''),
                COALESCE(c.name, ''),
                COALESCE(f.barcode, ''),
                COALESCE(f.keywords, ''),
                TRIM(
                    COALESCE(f.name, '') || ' ' ||
                    COALESCE(f.brand, '') || ' ' ||
                    COALESCE(c.name, '') || ' ' ||
                    COALESCE(f.barcode, '') || ' ' ||
                    COALESCE(f.keywords, '')
                )
            FROM foods f
            LEFT JOIN categories c ON f.category_id = c.id
            """
        )
    except Exception:
        # FTS extension may be unavailable on some SQLite builds.
        pass


def refresh_food_search_row(cur, food_id):
    try:
        cur.execute("DELETE FROM foods_search WHERE food_id = ?", (food_id,))
        cur.execute(
            """
            INSERT INTO foods_search (food_id, name, brand, category, barcode, keywords, searchable)
            SELECT
                f.id,
                COALESCE(f.name, ''),
                COALESCE(f.brand, ''),
                COALESCE(c.name, ''),
                COALESCE(f.barcode, ''),
                COALESCE(f.keywords, ''),
                TRIM(
                    COALESCE(f.name, '') || ' ' ||
                    COALESCE(f.brand, '') || ' ' ||
                    COALESCE(c.name, '') || ' ' ||
                    COALESCE(f.barcode, '') || ' ' ||
                    COALESCE(f.keywords, '')
                )
            FROM foods f
            LEFT JOIN categories c ON f.category_id = c.id
            WHERE f.id = ?
            """,
            (food_id,),
        )
    except Exception:
        pass


def ensure_brand_column():
    global _schema_checked
    if _schema_checked:
        return
    conn = sqlite3.connect(DB_PATH)
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

    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS brands (
        id INTEGER PRIMARY KEY,
        name TEXT UNIQUE NOT NULL
    )
    """
    )

    try:
        cur.execute("SELECT DISTINCT TRIM(brand) FROM foods WHERE brand IS NOT NULL AND TRIM(brand) != ''")
        for (brand_name,) in cur.fetchall():
            cur.execute("INSERT OR IGNORE INTO brands(name) VALUES(?)", (brand_name,))
        conn.commit()
    except Exception:
        pass

    cur.execute("CREATE INDEX IF NOT EXISTS idx_foods_name ON foods(name)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_foods_brand ON foods(brand)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_foods_category_id ON foods(category_id)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_foods_barcode ON foods(barcode)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_foods_is_active ON foods(is_active)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_foods_calories ON foods(calories)")

    try:
        cur.execute(
            """
            CREATE VIRTUAL TABLE IF NOT EXISTS foods_search USING fts5(
                food_id UNINDEXED,
                name,
                brand,
                category,
                barcode,
                keywords,
                searchable,
                tokenize = 'unicode61 remove_diacritics 2'
            )
            """
        )
        rebuild_foods_search_index(cur)
        conn.commit()
    except Exception:
        pass

    conn.close()
    _schema_checked = True


def ensure_exercises_table():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS exercises (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        muscle_group TEXT,
        equipment TEXT,
        difficulty TEXT,
        notes TEXT,
        exercise_category_id INTEGER
    )
    """
    )
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS exercise_categories (
        id INTEGER PRIMARY KEY,
        name TEXT UNIQUE NOT NULL
    )
    """
    )
    conn.commit()
    cur.execute("PRAGMA table_info(exercises)")
    cols = [r[1] for r in cur.fetchall()]
    if 'exercise_category_id' not in cols:
        cur.execute("ALTER TABLE exercises ADD COLUMN exercise_category_id INTEGER")
        conn.commit()
    if 'video_url' not in cols:
        cur.execute("ALTER TABLE exercises ADD COLUMN video_url TEXT")
        conn.commit()
    conn.close()


def ensure_routines_table():
    conn = sqlite3.connect(DB_PATH)
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
    conn.commit()
    conn.close()


def ensure_diets_table():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS diets (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        description TEXT,
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
    cur.execute("PRAGMA table_info(diet_items)")
    cols = [r[1] for r in cur.fetchall()]
    if 'day_of_week' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN day_of_week TEXT")
    if 'meal_time' not in cols:
        cur.execute("ALTER TABLE diet_items ADD COLUMN meal_time TEXT")
    conn.commit()
    conn.close()


def ensure_clients_table():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        """
    CREATE TABLE IF NOT EXISTS clients (
        id INTEGER PRIMARY KEY,
        name TEXT NOT NULL,
        phone TEXT,
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
    conn.commit()
    conn.close()


def ensure_payment_plans_table():
    conn = sqlite3.connect(DB_PATH)
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
    conn.close()


def ensure_client_history_tables():
    conn = sqlite3.connect(DB_PATH)
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
    conn.commit()
    conn.close()


# helpers
def get_foods():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT f.id, f.name, f.brand, c.name as category, f.calories, f.protein, f.carbs, f.fats, f.serving_size, "
        "COALESCE(f.photo_path, ''), COALESCE(f.nutrition_mode, 'per100'), COALESCE(f.per100_unit, 'g'), COALESCE(f.is_verified, 0) "
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


def ensure_default_food_categories():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT COUNT(*) FROM categories")
    count = int(cur.fetchone()[0] or 0)
    if count == 0:
        for name in DEFAULT_FOOD_CATEGORIES:
            cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (name,))
        conn.commit()
    conn.close()


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
        "SELECT e.id, e.name, e.muscle_group, e.equipment, e.difficulty, e.notes, ec.name, COALESCE(e.video_url, '') "
        "FROM exercises e LEFT JOIN exercise_categories ec ON e.exercise_category_id = ec.id "
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


def get_routines():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT id, name, description, created_at FROM routines ORDER BY id DESC")
    rows = cur.fetchall()
    conn.close()
    return rows


def get_routine_items(routine_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT ri.id, ri.routine_id, ri.day_name, ri.exercise_id, e.name, COALESCE(ri.sets_text, ''), COALESCE(ri.reps_text, ''), COALESCE(ri.notes, ''), COALESCE(ri.sort_order, 0) "
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
        "SELECT id, name, description, created_at, COALESCE(client_weight_kg, 0) "
        "FROM diets WHERE COALESCE(is_template, 1) = 1 ORDER BY id"
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def get_clients():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, phone, birthdate, COALESCE(height_cm, 0), COALESCE(weight_kg, 0), COALESCE(objectives, ''), COALESCE(plan_start_date, ''), COALESCE(plan_end_date, ''), COALESCE(plan_amount, 0), COALESCE(plan_notes, ''), created_at FROM clients ORDER BY id"
    )
    rows = cur.fetchall()
    conn.close()
    return rows


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
            COALESCE(h.training_name, ''),
            COALESCE(e.name, ''),
            COALESCE(h.start_date, ''),
            COALESCE(h.end_date, ''),
            COALESCE(h.is_active, 0),
            COALESCE(h.notes, ''),
            COALESCE(h.created_at, '')
        FROM client_training_history h
        LEFT JOIN exercises e ON e.id = h.exercise_id
        WHERE h.client_id = ?
        ORDER BY COALESCE(h.start_date, h.created_at) DESC, h.id DESC
        """,
        (client_id,),
    )
    rows = cur.fetchall()
    conn.close()
    return rows


def clone_diet_template_for_client(template_diet_id, client_name=''):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT name, description, COALESCE(client_diet_name, ''), COALESCE(client_weight_kg, 0), "
        "COALESCE(client_name, ''), COALESCE(client_height_cm, 0), COALESCE(client_age, 0) "
        "FROM diets WHERE id = ?",
        (template_diet_id,),
    )
    src = cur.fetchone()
    if not src:
        conn.close()
        return None

    template_name, description, client_diet_name, client_weight_kg, src_client_name, client_height_cm, client_age = src
    copy_name = f"{template_name} · {client_name}".strip() if client_name else f"{template_name} · Cliente"
    copy_client_name = src_client_name or client_name or ''

    cur.execute(
        "INSERT INTO diets(name, description, is_template, client_diet_name, client_weight_kg, client_name, client_height_cm, client_age, created_at) "
        "VALUES(?,?,?,?,?,?,?,?,datetime('now'))",
        (
            copy_name,
            description,
            0,
            client_diet_name,
            client_weight_kg,
            copy_client_name,
            client_height_cm,
            client_age,
        ),
    )
    new_diet_id = cur.lastrowid

    cur.execute(
        "SELECT id, name, order_index FROM diet_meals WHERE diet_id = ? ORDER BY order_index, id",
        (template_diet_id,),
    )
    source_meals = cur.fetchall()
    meal_map = {}
    for old_meal_id, meal_name, order_index in source_meals:
        cur.execute(
            "INSERT INTO diet_meals(diet_id, name, order_index) VALUES(?,?,?)",
            (new_diet_id, meal_name, order_index),
        )
        meal_map[old_meal_id] = cur.lastrowid

    cur.execute(
        "SELECT day_of_week, is_training, goal_kcal, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier "
        "FROM diet_day_config WHERE diet_id = ?",
        (template_diet_id,),
    )
    day_rows = cur.fetchall()
    for r in day_rows:
        cur.execute(
            "INSERT INTO diet_day_config(diet_id, day_of_week, is_training, goal_kcal, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?)",
            (new_diet_id, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9]),
        )

    cur.execute(
        "SELECT food_id, quantity, note, day_of_week, meal_time, COALESCE(meal_id, 0), COALESCE(quantity_grams, 100), COALESCE(quantity_units, 1) "
        "FROM diet_items WHERE diet_id = ?",
        (template_diet_id,),
    )
    source_items = cur.fetchall()
    for item in source_items:
        mapped_meal = meal_map.get(item[5]) if item[5] else None
        cur.execute(
            "INSERT INTO diet_items(diet_id, food_id, quantity, note, day_of_week, meal_time, meal_id, quantity_grams, quantity_units) "
            "VALUES(?,?,?,?,?,?,?,?,?)",
            (new_diet_id, item[0], item[1], item[2], item[3], item[4], mapped_meal, item[6], item[7]),
        )

    conn.commit()
    conn.close()
    return new_diet_id


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
        "SELECT di.id, f.id, f.name, f.brand, f.calories, f.protein, f.carbs, f.fats, di.quantity, di.note, di.day_of_week, di.meal_time "
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
        SELECT f.name, COALESCE(f.brand, ''), COALESCE(di.quantity, '')
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


def get_food_options():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("SELECT id, name, brand FROM foods ORDER BY name")
    rows = cur.fetchall()
    conn.close()
    return rows


def ensure_diet_builder_tables():
    conn = sqlite3.connect(DB_PATH)
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
        goal_protein REAL DEFAULT 0,
        goal_fat REAL DEFAULT 0,
        goal_carbs REAL DEFAULT 0,
        goal_fiber REAL DEFAULT 0,
        protein_multiplier REAL DEFAULT 0,
        fat_multiplier REAL DEFAULT 0,
        carb_multiplier REAL DEFAULT 0,
        UNIQUE(diet_id, day_of_week)
    )""")
    cur.execute("PRAGMA table_info(diet_day_config)")
    day_cols = [r[1] for r in cur.fetchall()]
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
    conn.commit()
    conn.close()


def get_diet_builder_data(diet_id):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT id, name, description, COALESCE(client_diet_name, ''), COALESCE(client_weight_kg, 0), "
        "COALESCE(client_name, ''), COALESCE(client_height_cm, 0), COALESCE(client_age, 0) "
        "FROM diets WHERE id=?",
        (diet_id,),
    )
    row = cur.fetchone()
    if not row:
        conn.close()
        return None
    diet = {
        'id': row[0],
        'name': row[1],
        'description': row[2] or '',
        'client_diet_name': row[3] or '',
        'client_weight_kg': row[4] or 0,
        'client_name': row[5] or '',
        'client_height_cm': row[6] or 0,
        'client_age': row[7] or 0,
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

    cur.execute("SELECT day_of_week, is_training, goal_kcal, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier FROM diet_day_config WHERE diet_id=?", (diet_id,))
    day_configs = {}
    for r in cur.fetchall():
        day_configs[r[0]] = {'is_training': bool(r[1]), 'goal_kcal': r[2], 'goal_protein': r[3], 'goal_fat': r[4], 'goal_carbs': r[5], 'goal_fiber': r[6], 'protein_multiplier': r[7], 'fat_multiplier': r[8], 'carb_multiplier': r[9]}

    cur.execute("""
         SELECT di.id, di.day_of_week, di.meal_id, di.food_id,
             f.name, COALESCE(f.brand,''), di.quantity_grams,
             COALESCE(f.calories,0), COALESCE(f.protein,0), COALESCE(f.fats,0), COALESCE(f.carbs,0),
             COALESCE(f.nutrition_mode,'per100'), COALESCE(f.per100_unit,'g'), COALESCE(di.quantity_units,1)
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
        })
    conn.close()
    return {'diet': diet, 'meals': meals, 'day_configs': day_configs, 'items': items}


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

    if q_norm:
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

    def draw_page_number(label):
        page_w, _ = pdf._pagesize
        pdf.setFillColor(colors.HexColor('#94a3b8'))
        pdf.setFont('Helvetica', 8)
        pdf.drawRightString(page_w - 24, 18, label)

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
        meal_time = (item[11] or '').strip()
        if day not in days or meal_time not in meal_name_set:
            continue
        label = item[2]
        if item[3]:
            label += f' ({item[3]})'
        if item[8]:
            label += f' {item[8]}'
        if label not in schedule[meal_time][day]:
            schedule[meal_time][day].append(label)

    for food_name, food_brand, quantity in get_diet_items_without_meal(diet_id):
        food = (food_name or 'Alimento').strip()
        brand = (food_brand or '').strip()
        key = (food, brand)
        if key not in shopping:
            shopping[key] = {'units': {}, 'raw': []}
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

    pdf.setFillColor(colors.HexColor('#f8fafc'))
    pdf.roundRect(left - 2, top - 52, (right - left) + 4, 56, 8, stroke=0, fill=1)
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
    row_count = max(1, len(meals))
    table_bottom_limit = 72
    max_table_h = table_top - table_bottom_limit - header_h
    row_h = max(56.0, min(82.0, max_table_h / row_count))
    if table_top - header_h - (row_h * row_count) < table_bottom_limit:
        row_h = (table_top - header_h - table_bottom_limit) / row_count
    table_bottom = table_top - header_h - (row_h * row_count)

    col_x = [left, left + meal_col_w]
    for i in range(1, 8):
        col_x.append(left + meal_col_w + (i * day_col_w))

    row_y = [table_top, table_top - header_h]
    for i in range(1, row_count + 1):
        row_y.append(table_top - header_h - (i * row_h))

    pdf.setFillColor(colors.HexColor('#f7efe7'))
    pdf.rect(left, table_top - header_h, right - left, header_h, stroke=0, fill=1)
    pdf.setFillColor(colors.HexColor('#fffaf5'))
    for idx in range(row_count):
        y = table_top - header_h - ((idx + 1) * row_h)
        pdf.rect(left, y, meal_col_w, row_h, stroke=0, fill=1)

    pdf.setStrokeColor(colors.HexColor('#cbd5e1'))
    pdf.setLineWidth(0.8)
    for x in col_x:
        pdf.line(x, table_top, x, table_bottom)
    for y in row_y:
        pdf.line(left, y, right, y)

    pdf.setFillColor(colors.HexColor('#334155'))
    pdf.setFont('Helvetica-Bold', 8.5)
    pdf.drawString(left + 6, table_top - 14, 'Comida / Día')

    for day_idx, day in enumerate(days):
        x = left + meal_col_w + (day_idx * day_col_w)
        cfg = day_cfg(day)
        is_training = cfg['is_training']
        goal_kcal = cfg['goal_kcal']
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

    def draw_cell_lines(lines, x, y_top, w, h):
        pdf.setFont('Helvetica', 7.2)
        line_h = 8.2
        max_lines = max(2, int((h - 10) // line_h))
        y = y_top - 10
        for text in lines[:max_lines]:
            pdf.drawString(x + 3, y, text)
            y -= line_h

    def wrap_line(text, max_width):
        words = text.split()
        if not words:
            return ['']
        lines = []
        curr = words[0]
        for word in words[1:]:
            candidate = curr + ' ' + word
            if pdf.stringWidth(candidate, 'Helvetica', 7.2) <= max_width:
                curr = candidate
            else:
                lines.append(curr)
                curr = word
        lines.append(curr)
        return lines

    line_width = day_col_w - 10

    for meal_idx, meal in enumerate(meals):
        meal_name = meal['name']
        cell_top = table_top - header_h - (meal_idx * row_h)
        pdf.setFillColor(colors.HexColor('#334155'))
        pdf.setFont('Helvetica-Bold', 8.8)
        pdf.drawString(left + 6, cell_top - 14, meal_name)

        for day_idx, day in enumerate(days):
            items = schedule.get(meal_name, {}).get(day, [])
            cell_x = left + meal_col_w + (day_idx * day_col_w)
            if not items:
                pdf.setFillColor(colors.HexColor('#94a3b8'))
                draw_cell_lines(['Sin alimentos'], cell_x, cell_top, day_col_w, row_h)
                continue

            lines = []
            for it in items:
                wrapped = wrap_line(it, max_width=line_width)
                for i, segment in enumerate(wrapped):
                    lines.append(('- ' if i == 0 else '  ') + segment)
            pdf.setFillColor(colors.HexColor('#0f172a'))
            draw_cell_lines(lines, cell_x, cell_top, day_col_w, row_h)

    draw_page_number('Página 1')
    pdf.showPage()

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
    pdf.save()
    return buffer.getvalue()


def build_routine_pdf(routine_id):
    routines = get_routines()
    routine = next((r for r in routines if r[0] == routine_id), None)
    if routine is None:
        return None

    items = get_routine_items(routine_id)
    exercise_lookup = {e[0]: {'name': e[1], 'video_url': (e[7] or '').strip()} for e in get_exercises()}
    days = ['Lunes', 'Martes', 'Miércoles', 'Jueves', 'Viernes', 'Sábado', 'Domingo']
    grouped_items = {day: [] for day in days}
    for item in items:
        grouped_items.setdefault(item[2], []).append(item)

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
        pdf.setFont('Helvetica-Bold', 16)
        pdf.drawString(30, y_top - 4, f"Rutina: {routine[1]}")
        pdf.setFillColor(colors.HexColor('#475569'))
        pdf.setFont('Helvetica', 10)
        pdf.drawString(30, y_top - 20, f"Descripción: {routine[2] or '-'}")
        pdf.drawString(30, y_top - 34, f"Creada: {routine[3] or '-'}")
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

    pdf.setStrokeColor(colors.HexColor('#e2e8f0'))
    pdf.setLineWidth(0.8)
    used_video_links = []
    used_video_ids = set()

    for day in days:
        day_items = grouped_items.get(day, [])
        item_lines = []
        for item in day_items:
            item_id, _routine_id, _day_name, _exercise_id, exercise_name, sets_text, reps_text, notes, _sort_order = item
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
    return f'<div style="display:flex;align-items:center;gap:18px;flex-wrap:wrap;margin-bottom:28px;">{logo}<a href="/" style="display:inline-flex;align-items:center;justify-content:center;padding:14px 20px;background:#ffffff;border:1px solid #d8dde6;border-radius:14px;box-shadow:0 12px 30px rgba(16,19,24,.06);color:#101318;font-weight:700;text-decoration:none;min-width:220px;transition:transform .18s ease,border-color .18s ease,box-shadow .18s ease;">Panel principal</a></div>'


class Handler(BaseHTTPRequestHandler):
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

        # API endpoints
        if path == '/api/foods':
            foods = get_foods()
            keys = ['id', 'name', 'brand', 'category', 'calories', 'protein', 'carbs', 'fats', 'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified']
            data = [dict(zip(keys, r)) for r in foods]
            return self.send_json(data)

        if path == '/api/exercises':
            exercises = get_exercises()
            keys = ['id', 'name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'category', 'video_url']
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
        if path in ('/', '/index.html'):
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
        <p>Crea, edita y organiza ejercicios con categorías y detalles.</p>
      </a>
      <a class="card" href="/diets">
        <h2>🥗 Creación de dietas</h2>
        <p>Define dietas y añade alimentos sincronizados desde la base de datos.</p>
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
            foods = get_food_options()
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
                    f'<div class="diet-card-head"><span class="diet-card-id">#{d[0]}</span><span class="diet-card-date">{html.escape(created_dmy)}</span></div>'
                    f'<h3 class="diet-card-name">{html.escape(d[1])}</h3>'
                    f'<p class="diet-card-desc">{html.escape(d[2] or "Sin descripción")}</p>'
                    '<div class="diet-card-actions">'
                    f'<a class="action-button action-edit" href="/static/builder.html?diet_id={d[0]}">Abrir</a>'
                    f'<a class="action-button" href="/export_diet_pdf/dieta_{d[0]}.pdf" target="_blank">PDF</a>'
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
                    if item[8]:
                        label += f' — {html.escape(item[8])}'
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
                <a class="action-button action-edit" href="/export_diet_pdf/dieta_{selected_diet[0]}.pdf" target="_blank">Exportar PDF</a>
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
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # Clients page
        if path == '/clients':
            clients = get_clients()
            msg = q.get('msg', [''])[0] if 'msg' in q else ''
            client_cards = []
            from datetime import date, datetime
            for c in clients:
                client_id, name, phone, birthdate, height_cm, weight_kg, objectives, plan_start_date, plan_end_date, plan_amount, plan_notes, created_at = c
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
                phone_link = re.sub(r'[^0-9+]', '', phone_value)
                contact_button = (
                    f'<a class="card-btn" href="tel:{html.escape(phone_link)}">Contactar</a>'
                    if phone_link else '<button class="card-btn is-disabled" type="button" disabled>Contactar</button>'
                )

                status_class = 'status-active' if is_active else 'status-inactive'
                search_blob = ' '.join([
                    str(name or ''), str(phone_value), str(service_status), str(plan_label),
                    str(monthly_fee), str(objective), str(plan_start_date or ''), str(plan_end_date or '')
                ]).lower().strip()

                client_cards.append(
                    f'<article class="client-card" data-active="{"1" if is_active else "0"}" '
                    f'data-has-plan="{"1" if (plan_start_date or plan_end_date) else "0"}" '
                    f'data-search="{html.escape(search_blob)}">'
                    f'<div class="card-head"><h3>{html.escape(name)}</h3><span class="service-status {status_class}">{html.escape(service_status)}</span></div>'
                    f'<div class="card-grid">'
                    f'<div class="kv"><span>Email</span><strong>-</strong></div>'
                    f'<div class="kv"><span>Teléfono</span><strong>{html.escape(phone_value or "-")}</strong></div>'
                    f'<div class="kv"><span>Inicio</span><strong>{html.escape(plan_start_date or "-")}</strong></div>'
                    f'<div class="kv"><span>Fin</span><strong>{html.escape(plan_end_date or "-")}</strong></div>'
                    f'<div class="kv"><span>Días restantes</span><strong>{html.escape(days_remaining)}</strong></div>'
                    f'<div class="kv"><span>Plan</span><strong>{html.escape(plan_label)}</strong></div>'
                    f'<div class="kv"><span>Mensualidad</span><strong>{html.escape(monthly_fee)}</strong></div>'
                    f'<div class="kv"><span>Objetivo</span><strong>{html.escape(objective)}</strong></div>'
                    f'</div>'
                    f'<div class="card-actions">'
                    f'<a class="card-btn" href="/client_profile?id={client_id}">Ver perfil</a>'
                    f'{contact_button}'
                    f'<a class="card-btn" href="/edit_client?id={client_id}">Extender</a>'
                    f'<button class="card-btn" type="button" onclick="clientAction(\'Bloquear\', \'{html.escape(name)}\')">Bloquear</button>'
                    f'<button class="card-btn" type="button" onclick="clientAction(\'Desactivar\', \'{html.escape(name)}\')">Desactivar</button>'
                    f'<form method="post" action="/delete_client" onsubmit="return confirm(\'¿Seguro que quieres eliminar este cliente?\')">'
                    f'<input type="hidden" name="id" value="{client_id}" />'
                    f'<button class="card-btn danger" type="submit">Eliminar</button></form>'
                    f'</div>'
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
        .clients-grid{{display:grid;grid-template-columns:repeat(2,minmax(320px,1fr));gap:14px;}}
        .client-card{{background:#fff;border:1px solid var(--line);border-radius:16px;padding:16px;box-shadow:var(--shadow);}}
        .card-head{{display:flex;justify-content:space-between;align-items:flex-start;gap:12px;margin-bottom:14px;}}
        .card-head h3{{margin:0;font-size:1.15rem;}}
        .service-status{{padding:5px 9px;border-radius:999px;font-size:.75rem;font-weight:800;letter-spacing:.02em;}}
        .status-active{{background:#eaf8ef;color:#1f7a40;}}
        .status-inactive{{background:#eef2f7;color:#4a5568;}}
        .card-grid{{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px 14px;margin-bottom:14px;}}
        .kv span{{display:block;font-size:.74rem;color:var(--muted);font-weight:700;text-transform:uppercase;letter-spacing:.03em;}}
        .kv strong{{display:block;margin-top:3px;font-size:.95rem;line-height:1.25;}}
        .card-actions{{display:flex;gap:8px;flex-wrap:wrap;border-top:1px solid var(--line);padding-top:12px;}}
        .card-actions form{{margin:0;}}
        .card-btn{{display:inline-flex;align-items:center;justify-content:center;height:34px;padding:0 10px;border-radius:9px;border:1px solid var(--line-strong);background:#fff;color:var(--ink);text-decoration:none;font-size:.82rem;font-weight:700;cursor:pointer;}}
        .card-btn:hover{{background:#f5f7fa;}}
        .card-btn.danger{{border-color:#efcfd2;color:#8b1b20;background:#fff4f4;}}
        .card-btn.danger:hover{{background:#fee2e2;}}
        .card-btn.is-disabled{{opacity:.45;cursor:not-allowed;pointer-events:none;}}
        .empty-state{{display:none;padding:22px;border:1px dashed var(--line-strong);border-radius:12px;background:#fff;color:var(--muted);font-weight:700;text-align:center;}}
        .empty-state.show{{display:block;}}
        .is-hidden{{display:none !important;}}
        @media (max-width: 1000px){{
            .clients-grid{{grid-template-columns:1fr;}}
        }}
        @media (max-width: 760px){{
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
            _, name, phone, birthdate, height_cm, weight_kg, objectives, plan_start_date, plan_end_date, plan_amount, plan_notes, _created_at = c
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
            _, name, phone, birthdate, _height_cm, _weight_kg, objectives, _plan_start_date, _plan_end_date, _plan_amount, _plan_notes, _created_at = c
            age = calculate_age(birthdate)
            diets = get_diets()
            exercises = get_exercises()
            diet_history = get_client_diet_history(cid_i)
            training_history = get_client_training_history(cid_i)

            selected_diet_id = ''
            try:
                selected_diet_id = str(int(assign_diet_id)) if assign_diet_id else ''
            except Exception:
                selected_diet_id = ''

            diet_options = ''.join([
                f'<option value="{d[0]}" {"selected" if selected_diet_id == str(d[0]) else ""}>{html.escape(d[1])}</option>'
                for d in diets
            ])
            exercise_options = ''.join([
                f'<option value="{e[0]}">{html.escape(e[1])}</option>'
                for e in exercises
            ])

            active_diets = [h for h in diet_history if int(h[9] or 0) == 1]
            old_diets = [h for h in diet_history if int(h[9] or 0) == 0]
            active_training = [h for h in training_history if int(h[7] or 0) == 1]
            old_training = [h for h in training_history if int(h[7] or 0) == 0]

            def diet_item_html(item):
                history_id, _client_id, diet_id, diet_name, client_diet_name, template_diet_id, template_diet_name, start_date, end_date, is_active, notes, _created = item
                display_name = (client_diet_name or '').strip() or (diet_name or '').strip() or 'Dieta'
                badge = 'Activa' if int(is_active or 0) == 1 else 'Antigua'
                end_label = end_date or ('En curso' if int(is_active or 0) == 1 else '-')
                template_label = template_diet_name or ('Plantilla #' + str(template_diet_id) if template_diet_id else '-')
                close_button = ''
                if int(is_active or 0) == 1:
                    close_button = (
                        f'<form method="post" action="/deactivate_client_diet" style="display:inline;margin:0">'
                        f'<input type="hidden" name="history_id" value="{history_id}" />'
                        f'<input type="hidden" name="client_id" value="{cid_i}" />'
                        f'<button type="submit" class="mini-btn">Cerrar</button>'
                        f'</form>'
                    )
                return (
                    '<div class="history-item">'
                    f'<div class="history-head"><strong>{html.escape(display_name)}</strong><span class="badge">{badge}</span></div>'
                    f'<div class="history-meta">Inicio: {html.escape(start_date or "-")} · Fin: {html.escape(end_label)} · Plantilla: {html.escape(template_label)}</div>'
                    f'<div class="history-note">{html.escape(notes or "Sin notas")}</div>'
                    f'<div style="margin-top:8px;"><a class="mini-btn" href="/static/builder.html?diet_id={diet_id}">Editar dieta</a></div>'
                    f'{close_button}'
                    '</div>'
                )

            def training_item_html(item):
                history_id, _client_id, _exercise_id, training_name, exercise_name, start_date, end_date, is_active, notes, _created = item
                display_name = (training_name or '').strip() or (exercise_name or '').strip() or 'Entrenamiento'
                badge = 'Activo' if int(is_active or 0) == 1 else 'Antiguo'
                end_label = end_date or ('En curso' if int(is_active or 0) == 1 else '-')
                close_button = ''
                if int(is_active or 0) == 1:
                    close_button = (
                        f'<form method="post" action="/deactivate_client_training" style="display:inline;margin:0">'
                        f'<input type="hidden" name="history_id" value="{history_id}" />'
                        f'<input type="hidden" name="client_id" value="{cid_i}" />'
                        f'<button type="submit" class="mini-btn">Cerrar</button>'
                        f'</form>'
                    )
                return (
                    '<div class="history-item">'
                    f'<div class="history-head"><strong>{html.escape(display_name)}</strong><span class="badge">{badge}</span></div>'
                    f'<div class="history-meta">Inicio: {html.escape(start_date or "-")} · Fin: {html.escape(end_label)}</div>'
                    f'<div class="history-note">{html.escape(notes or "Sin notas")}</div>'
                    f'{close_button}'
                    '</div>'
                )

            active_diets_html = ''.join([diet_item_html(h) for h in active_diets]) or '<p class="empty">Sin dietas activas.</p>'
            old_diets_html = ''.join([diet_item_html(h) for h in old_diets]) or '<p class="empty">Sin dietas antiguas.</p>'
            active_training_html = ''.join([training_item_html(h) for h in active_training]) or '<p class="empty">Sin entrenamientos activos.</p>'
            old_training_html = ''.join([training_item_html(h) for h in old_training]) or '<p class="empty">Sin entrenamientos antiguos.</p>'

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
        .grid{{display:grid;grid-template-columns:repeat(2,minmax(320px,1fr));gap:16px;}}
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
        .history-meta{{margin-top:6px;color:#6d7480;font-size:.86rem;}}
        .history-note{{margin-top:6px;color:#101318;font-size:.9rem;}}
        .mini-btn{{display:inline-flex;margin-top:8px;padding:7px 10px;border:1px solid #d8dde6;border-radius:8px;background:#fff;color:#101318;font-weight:700;cursor:pointer;text-decoration:none;}}
        .empty{{color:#6d7480;font-style:italic;}}
        @media (max-width: 960px){{
            .grid{{grid-template-columns:1fr;}}
        }}
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
                    <span class="chip">Edad: {age if age is not None else '-'}</span>
                    <span class="chip">Objetivo: {html.escape((objectives or '').strip() or 'Sin objetivo')}</span>
                </div>
            </div>
            <a class="back" href="/clients">← Volver a clientes</a>
        </div>
        {f'<div class="msg">{html.escape(msg)}</div>' if msg else ''}
        <div class="grid">
            <section class="panel">
                <h2>🥗 Dietas</h2>
                <form method="post" action="/assign_client_diet" class="assign">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}" />
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

            <section class="panel">
                <h2>🏋️ Entrenamientos</h2>
                <form method="post" action="/assign_client_training" class="assign">
                    <input type="hidden" name="client_id" value="{cid_i}" />
                    <input type="hidden" name="return_to" value="/client_profile?id={cid_i}" />
                    <select name="exercise_id" class="full">
                        <option value="">Selecciona ejercicio base (opcional)</option>
                        {exercise_options}
                    </select>
                    <input name="training_name" class="full" placeholder="Nombre del entrenamiento" />
                    <input name="start_date" type="date" placeholder="Inicio" />
                    <input name="end_date" type="date" placeholder="Fin" />
                    <input name="notes" class="full" placeholder="Notas de entrenamiento" />
                    <button type="submit" class="full">✨ Asignar entrenamiento</button>
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
            self.send_header('Content-Disposition', f'inline; filename="rutina_{routine_id}.pdf"; filename*=UTF-8\'\'rutina_{routine_id}.pdf')
            self.send_header('Content-Length', str(len(pdf)))
            self.end_headers()
            self.wfile.write(pdf)
            return

        # Foods page
        if path == '/foods':
            ensure_default_food_categories()
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
                fid, name, brand, category, cal, prot, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, is_verified = r
                brand_name = brand or 'Sin marca'
                category_name = category or 'Sin categoría'
                photo_html = (
                    f'<img src="{html.escape(photo_path)}" alt="{html.escape(name)}" loading="lazy" />'
                    if photo_path else
                    '<div class="food-photo-placeholder">Sin foto</div>'
                )
                verified_badge = '<span class="verified-pill" title="Alimento verificado">✓ Verificado</span>' if int(is_verified or 0) == 1 else ''
                food_cards_html.append(f'''
                    <article class="food-result-card" data-name="{html.escape(normalize_text(name))}" data-brand="{html.escape(normalize_text(brand_name))}" data-category="{html.escape(normalize_text(category_name))}" data-open-url="/edit?id={fid}">
                        <div class="food-result-photo">{photo_html}</div>
                        <div class="food-result-main">
                            <h3>{html.escape(name)} {verified_badge}</h3>
                            <p class="food-result-sub">{html.escape(brand_name)} · {html.escape(category_name)}</p>
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
            for e in exercises:
                video_url = (e[7] or '').strip()
                if video_url:
                    safe_url = html.escape(video_url, quote=True)
                    video_cell = f'<a class="action-link" href="{safe_url}" target="_blank" rel="noopener noreferrer">Ver video</a>'
                else:
                    video_cell = '-'
                rows_html.append(
                    '<tr>' +
                    f'<td>{html.escape(e[1])}</td>' +
                    f'<td>{html.escape(e[6] or "")}</td>' +
                    f'<td>{video_cell}</td>' +
                    '</tr>'
                )

            category_options = ''.join([f'<option value="{c[0]}">{html.escape(c[1])}</option>' for c in categories])
            category_list = ''.join([
                f'<li>{html.escape(c[1])} <form method="post" action="/delete_exercise_category" style="display:inline;margin-left:8px"><input type="hidden" name="id" value="{c[0]}" /><button type="submit">Borrar</button></form></li>'
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
    .grid-list{{display:grid;grid-template-columns:1fr;gap:12px;list-style:none;padding:0;margin:0;}}
        .grid-list li{{padding:12px 16px;border:1px solid #e8ebef;border-radius:12px;background:#fff;display:flex;justify-content:space-between;align-items:center;color:#101318;}}
    .grid-list button{{margin:0;padding:8px 12px;font-size:.95rem;}}
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
                    <option value="">-- Selecciona categoría --</option>
          {category_options}
        </select>
                <input name="video_url" placeholder="Link de video (YouTube o propio)" />
        <button type="submit">Añadir ejercicio</button>
      </form>
    </section>

    <section class="section-card">
    <h2>🏷️ Categorías de ejercicios</h2>
      <form method="post" action="/add_exercise_category" style="display:grid;grid-template-columns:1fr auto;gap:12px;align-items:center;margin-bottom:16px;">
        <input name="name" placeholder="Nueva categoría de ejercicio" required />
        <button type="submit">Crear categoría</button>
      </form>
      <ul class="grid-list">
        {category_list}
      </ul>
    </section>

    <section class="section-card">
            <table>
                                <thead><tr><th>Nombre</th><th>Categoría</th><th>Video</th></tr></thead>
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
            routine_id = q.get('routine_id', [''])[0]
            selected_routine = None
            items = []
            if routine_id:
                try:
                    routine_id_i = int(routine_id)
                except Exception:
                    routine_id_i = None
                else:
                    selected_routine = next((r for r in routines if r[0] == routine_id_i), None)
                    if selected_routine:
                        items = get_routine_items(routine_id_i)

            day_names = ['Lunes', 'Martes', 'Miércoles', 'Jueves', 'Viernes', 'Sábado', 'Domingo']
            exercise_options = ''.join([f'<option value="{e[0]}">{html.escape(e[1])}</option>' for e in exercises])

            routine_editor_html = ''
            if selected_routine:
                routine_name = selected_routine[1]
                routine_desc = selected_routine[2] or ''
                grouped = {d: [] for d in day_names}
                for item in items:
                    grouped.setdefault(item[2], []).append(item)

                day_cards = []
                for day_name in day_names:
                    cards_html = []
                    for item in grouped.get(day_name, []):
                        item_id, _routine_id, _day_name, _exercise_id, exercise_name, sets_text, reps_text, notes, _sort_order = item
                        cards_html.append(
                            '<div class="diet-card" style="min-height:auto;">'
                            f'<div class="diet-card-head"><span class="diet-card-id">#{item_id}</span><span class="diet-card-date">{html.escape(day_name)}</span></div>'
                            f'<h3 class="diet-card-name">{html.escape(exercise_name or "Ejercicio")}</h3>'
                            f'<p class="diet-card-desc">Series: {html.escape(sets_text or "-")} · Reps: {html.escape(reps_text or "-")}</p>'
                            f'<p class="diet-card-desc">{html.escape(notes or "Sin notas")}</p>'
                            f'<form method="post" action="/delete_routine_item" style="margin-top:8px;"><input type="hidden" name="id" value="{item_id}" /><input type="hidden" name="routine_id" value="{routine_id}" /><button type="submit">Eliminar</button></form>'
                            '</div>'
                        )
                    cards_html = ''.join(cards_html) or '<p style="color:#6d7480;">Sin ejercicios para este día.</p>'
                    day_cards.append(f'<section class="section-card"><h2>🏷️ {html.escape(day_name)}</h2><div class="diet-cards">{cards_html}</div></section>')

                routine_editor_html = f'''
    <section class="section-card">
      <h2>Editar rutina: {html.escape(routine_name)}</h2>
      <p style="color:#6d7480;margin-top:-4px;">{html.escape(routine_desc or 'Sin descripción')}</p>
            <div style="margin:8px 0 14px;">
                <a class="action-button action-edit" href="/export_routine_pdf/rutina_{routine_id}.pdf" target="_blank">Exportar PDF</a>
            </div>
      <form method="post" action="/add_routine_item">
        <input type="hidden" name="routine_id" value="{routine_id}" />
        <select name="day_name" required>
          <option value="">Selecciona día</option>
          {''.join([f'<option value="{day}">{day}</option>' for day in day_names])}
        </select>
        <select name="exercise_id" required>
          <option value="">Selecciona ejercicio</option>
          {exercise_options}
        </select>
        <input name="sets_text" placeholder="Series" />
        <input name="reps_text" placeholder="Reps" />
        <input class="full" name="notes" placeholder="Notas" />
        <button class="full" type="submit">Añadir ejercicio a la rutina</button>
      </form>
    </section>
    {''.join(day_cards)}
'''

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
  </style>
</head>
<body>
  <div class="page">
    {home_link()}
    <h1>📋 Creación de rutinas</h1>
    {f'<div class="message">{html.escape(msg)}</div>' if msg else ''}
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
    {routine_editor_html}
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
            fid, name, brand, category, cal, prot, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, is_verified_row = r
            serving_amount, serving_unit = split_serving_size(serving)
            cats = get_categories()
            brands = get_brands()
            conn_meta = sqlite3.connect(DB_PATH)
            cur_meta = conn_meta.cursor()
            cur_meta.execute("SELECT COALESCE(barcode,''), COALESCE(keywords,''), COALESCE(is_active,1), COALESCE(is_verified,0) FROM foods WHERE id = ?", (fid,))
            meta = cur_meta.fetchone() or ('', '', 1, 0)
            conn_meta.close()
            barcode = meta[0]
            keywords = meta[1]
            is_active = 1 if int(meta[2] or 0) else 0
            is_verified = 1 if int(meta[3] or 0) else 0
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
            eid, name, muscle_group, equipment, difficulty, notes, category, video_url = e
            categories = get_exercise_categories()
            category_options = ''.join([
                f'<option value="{c[0]}" {"selected" if c[1] == category else ""}>{html.escape(c[1])}</option>'
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
        <label>Categoría de ejercicio<select name="category_id">
          <option value="">-- Sin categoría --</option>
          {category_options}
        </select></label>
                <label class="full">Link de video<input name="video_url" value="{html.escape(video_url or '')}" placeholder="https://..." /></label>
        <label>Grupo muscular<input name="muscle_group" value="{html.escape(muscle_group or '')}" /></label>
        <label>Equipo<input name="equipment" value="{html.escape(equipment or '')}" /></label>
        <label>Dificultad<input name="difficulty" value="{html.escape(difficulty or '')}" /></label>
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

        payload = self.read_json() or {}

        # Update food: /api/foods/<id>
        if path.startswith('/api/foods/'):
            try:
                fid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)

            allowed = [
                'name', 'brand', 'category_id', 'calories', 'protein', 'carbs', 'fats', 'serving_size',
                'photo_path', 'nutrition_mode', 'per100_unit', 'barcode', 'keywords', 'is_active', 'is_verified'
            ]
            sets = []
            vals = []
            for k in allowed:
                if k in payload:
                    sets.append(f"{k} = ?")
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
            keys = ['id', 'name', 'brand', 'category', 'calories', 'protein', 'carbs', 'fats', 'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified']
            return self.send_json(dict(zip(keys, rows[0])))

        # Update exercise
        if path.startswith('/api/exercises/'):
            try:
                eid = int(path.split('/')[-1])
            except Exception:
                return self.send_json({'error': 'invalid id'}, status=400)
            allowed = ['name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'exercise_category_id', 'video_url']
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
            keys = ['id', 'name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'category', 'video_url']
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
            allowed = ['name', 'description', 'client_diet_name', 'client_weight_kg', 'client_name', 'client_height_cm', 'client_age']
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

        return self.send_json({'error': 'not found'}, status=404)

    def do_DELETE(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

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

        return self.send_json({'error': 'not found'}, status=404)

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        ctype = self.headers.get('Content-Type', '')

        # Diet builder JSON API
        bm = re.match(r'^/api/diet_builder/(\d+)/(meals|items|day_config|copy_day)$', path)
        dup_m = re.match(r'^/api/diet_item_b/(\d+)/duplicate$', path)
        if dup_m:
            item_id = int(dup_m.group(1))
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, note FROM diet_items WHERE id=?", (item_id,))
            r = cur.fetchone()
            if not r:
                conn.close()
                return self.send_json({'error': 'not found'}, status=404)
            cur.execute("INSERT INTO diet_items(diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, note) VALUES(?,?,?,?,?,?,?)", r)
            new_id = cur.lastrowid
            conn.commit()
            cur.execute("""SELECT di.id, di.day_of_week, di.meal_id, di.food_id, f.name, COALESCE(f.brand,''), di.quantity_grams,
                                  COALESCE(f.calories,0), COALESCE(f.protein,0), COALESCE(f.fats,0), COALESCE(f.carbs,0),
                                  COALESCE(f.nutrition_mode,'per100'), COALESCE(f.per100_unit,'g'), COALESCE(di.quantity_units,1)
                           FROM diet_items di JOIN foods f ON di.food_id=f.id WHERE di.id=?""", (new_id,))
            r2 = cur.fetchone()
            conn.close()
            if not r2:
                return self.send_json({'error': 'error'}, status=500)
            return self.send_json({'id': r2[0], 'day': r2[1], 'meal_id': r2[2], 'food_id': r2[3],
                                   'food_name': r2[4], 'food_brand': r2[5], 'grams': r2[6] or 100,
                                   'kcal_per100': r2[7], 'protein_per100': r2[8], 'fat_per100': r2[9], 'carbs_per100': r2[10],
                                   'nutrition_mode': r2[11], 'per100_unit': r2[12], 'units': r2[13] or 1})

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
                    if not food_id or not meal_id:
                        conn.close()
                        return self.send_json({'error': 'food_id and meal_id required'}, status=400)
                    cur.execute("INSERT INTO diet_items(diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units) VALUES(?,?,?,?,?,?)",
                                (diet_id_i, food_id, meal_id, day, grams, units))
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
                    })
                elif action == 'day_config':
                    day = str(payload.get('day', '')).strip()
                    is_training = 1 if payload.get('is_training', True) else 0
                    goal_kcal = float(payload.get('goal_kcal', 0) or 0)
                    goal_protein = float(payload.get('goal_protein', 0) or 0)
                    goal_fat = float(payload.get('goal_fat', 0) or 0)
                    goal_carbs = float(payload.get('goal_carbs', 0) or 0)
                    goal_fiber = float(payload.get('goal_fiber', 0) or 0)
                    protein_multiplier = float(payload.get('protein_multiplier', 0) or 0)
                    fat_multiplier = float(payload.get('fat_multiplier', 0) or 0)
                    carb_multiplier = float(payload.get('carb_multiplier', 0) or 0)
                    cur.execute("SELECT id FROM diet_day_config WHERE diet_id=? AND day_of_week=?", (diet_id_i, day))
                    if cur.fetchone():
                        cur.execute("UPDATE diet_day_config SET is_training=?,goal_kcal=?,goal_protein=?,goal_fat=?,goal_carbs=?,goal_fiber=?,protein_multiplier=?,fat_multiplier=?,carb_multiplier=? WHERE diet_id=? AND day_of_week=?",
                                    (is_training, goal_kcal, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier, diet_id_i, day))
                    else:
                        cur.execute("INSERT INTO diet_day_config(diet_id,day_of_week,is_training,goal_kcal,goal_protein,goal_fat,goal_carbs,goal_fiber,protein_multiplier,fat_multiplier,carb_multiplier) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                                    (diet_id_i, day, is_training, goal_kcal, goal_protein, goal_fat, goal_carbs, goal_fiber, protein_multiplier, fat_multiplier, carb_multiplier))
                    conn.commit()
                    conn.close()
                    return self.send_json({'ok': True})
                elif action == 'copy_day':
                    from_day = str(payload.get('from_day', '')).strip()
                    to_day = str(payload.get('to_day', '')).strip()
                    cur.execute("DELETE FROM diet_items WHERE diet_id=? AND day_of_week=? AND meal_id IS NOT NULL", (diet_id_i, to_day))
                    cur.execute("SELECT food_id, meal_id, quantity_grams, quantity_units, note FROM diet_items WHERE diet_id=? AND day_of_week=? AND meal_id IS NOT NULL", (diet_id_i, from_day))
                    src = cur.fetchall()
                    new_ids = []
                    for s in src:
                        cur.execute("INSERT INTO diet_items(diet_id, food_id, meal_id, day_of_week, quantity_grams, quantity_units, note) VALUES(?,?,?,?,?,?,?)",
                                    (diet_id_i, s[0], s[1], to_day, s[2], s[3], s[4]))
                        new_ids.append(cur.lastrowid)
                    conn.commit()
                    new_items = []
                    for nid in new_ids:
                        cur.execute("""SELECT di.id, di.day_of_week, di.meal_id, di.food_id, f.name, COALESCE(f.brand,''), di.quantity_grams,
                                              COALESCE(f.calories,0), COALESCE(f.protein,0), COALESCE(f.fats,0), COALESCE(f.carbs,0),
                                              COALESCE(f.nutrition_mode,'per100'), COALESCE(f.per100_unit,'g'), COALESCE(di.quantity_units,1)
                                       FROM diet_items di JOIN foods f ON di.food_id=f.id WHERE di.id=?""", (nid,))
                        r = cur.fetchone()
                        if r:
                            new_items.append({'id': r[0], 'day': r[1], 'meal_id': r[2], 'food_id': r[3],
                                              'food_name': r[4], 'food_brand': r[5], 'grams': r[6] or 100,
                                              'kcal_per100': r[7], 'protein_per100': r[8], 'fat_per100': r[9], 'carbs_per100': r[10],
                                              'nutrition_mode': r[11], 'per100_unit': r[12], 'units': r[13] or 1})
                    conn.close()
                    return self.send_json({'items': new_items})
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
                "INSERT INTO foods(name, brand, category_id, calories, protein, carbs, fats, serving_size, photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (name, brand, cat, calories, protein, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, barcode or None, keywords or None, is_active, is_verified),
            )
            new_food_id = cur.lastrowid
            refresh_food_search_row(cur, new_food_id)
            conn.commit()
            conn.close()
            row = get_foods()[-1]
            keys = ['id', 'name', 'brand', 'category', 'calories', 'protein', 'carbs', 'fats', 'serving_size', 'photo_path', 'nutrition_mode', 'per100_unit', 'is_verified']
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
            video_url = payload.get('video_url')
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "INSERT INTO exercises(name, muscle_group, equipment, difficulty, notes, video_url) VALUES(?,?,?,?,?,?)",
                (name, muscle_group, equipment, difficulty, notes, video_url),
            )
            conn.commit()
            conn.close()
            ex = get_exercises()[-1]
            keys = ['id', 'name', 'muscle_group', 'equipment', 'difficulty', 'notes', 'category', 'video_url']
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

        if path == '/add':
            name = get('name').strip()
            brand = get('brand').strip()
            cat_param = get('category').strip()
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
                "INSERT INTO foods(name, brand, category_id, calories, protein, carbs, fats, serving_size, photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (name, brand or None, cat_id, calories, protein, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, barcode or None, keywords or None, is_active, is_verified),
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
            video_url = get('video_url').strip()
            cat_id = None
            if category_id:
                try:
                    cat_id = int(category_id)
                except Exception:
                    cat_id = None
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "INSERT INTO exercises(name, muscle_group, equipment, difficulty, notes, exercise_category_id, video_url) VALUES(?,?,?,?,?,?,?)",
                (name, None, None, None, None, cat_id, video_url or None),
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
                conn = sqlite3.connect(DB_PATH)
                cur = conn.cursor()
                cur.execute(
                    "INSERT INTO diets(name, description, client_weight_kg, created_at) VALUES(?,?,?,datetime('now'))",
                    (name, description or None, client_weight_kg),
                )
                new_diet_id = cur.lastrowid
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
                    "INSERT INTO clients(name, phone, birthdate, height_cm, weight_kg, objectives, plan_start_date, plan_end_date, plan_amount, plan_notes, created_at) VALUES(?,?,?,?,?,?,?,?,?,?,datetime('now'))",
                    (name, phone or None, birthdate or None, height_cm, weight_kg, objectives or None, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes or None),
                )
                client_id = cur.lastrowid
                conn.commit()
                conn.close()
                sync_client_payment_plan(client_id, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes)
            self.send_response(303)
            self.send_header('Location', '/clients?msg=' + urllib.parse.quote('Cliente creado'))
            self.end_headers()
            return

        if path == '/assign_client_diet':
            client_id = get('client_id').strip()
            template_diet_id = get('diet_id').strip()
            start_date = get('start_date').strip()
            end_date = get('end_date').strip()
            notes = get('notes').strip()
            return_to = get('return_to').strip() or '/clients'
            try:
                client_id_i = int(client_id)
                template_diet_id_i = int(template_diet_id)
            except Exception:
                self.send_response(303)
                self.send_header('Location', '/clients?msg=' + urllib.parse.quote('No se pudo asignar la dieta'))
                self.end_headers()
                return

            client_rows = [r for r in get_clients() if r[0] == client_id_i]
            client_name = client_rows[0][1] if client_rows else ''
            assigned_diet_id = clone_diet_template_for_client(template_diet_id_i, client_name)
            if not assigned_diet_id:
                self.send_response(303)
                self.send_header('Location', '/clients?msg=' + urllib.parse.quote('No se pudo clonar la plantilla'))
                self.end_headers()
                return

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE client_diet_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), date('now')) WHERE client_id = ? AND is_active = 1",
                (client_id_i,),
            )
            cur.execute(
                "INSERT INTO client_diet_history(client_id, diet_id, template_diet_id, start_date, end_date, is_active, notes, created_at) VALUES(?,?,?,?,?,?,?,datetime('now'))",
                (client_id_i, assigned_diet_id, template_diet_id_i, start_date or None, end_date or None, 1, notes or None),
            )
            conn.commit()
            conn.close()
            location = return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Dieta asignada')
            self.send_response(303)
            self.send_header('Location', location)
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
                "UPDATE client_diet_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), date('now')) WHERE id = ?",
                (history_id_i,),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', f'/client_profile?id={client_id_i}&msg=' + urllib.parse.quote('Dieta cerrada'))
            self.end_headers()
            return

        if path == '/assign_client_training':
            client_id = get('client_id').strip()
            exercise_id = get('exercise_id').strip()
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

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE client_training_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), date('now')) WHERE client_id = ? AND is_active = 1",
                (client_id_i,),
            )
            cur.execute(
                "INSERT INTO client_training_history(client_id, exercise_id, training_name, start_date, end_date, is_active, notes, created_at) VALUES(?,?,?,?,?,?,?,datetime('now'))",
                (client_id_i, exercise_id_i, training_name or None, start_date or None, end_date or None, 1, notes or None),
            )
            conn.commit()
            conn.close()
            location = return_to + ('&' if '?' in return_to else '?') + 'msg=' + urllib.parse.quote('Entrenamiento asignado')
            self.send_response(303)
            self.send_header('Location', location)
            self.end_headers()
            return

        if path == '/deactivate_client_training':
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
                "UPDATE client_training_history SET is_active = 0, end_date = COALESCE(NULLIF(end_date, ''), date('now')) WHERE id = ?",
                (history_id_i,),
            )
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', f'/client_profile?id={client_id_i}&msg=' + urllib.parse.quote('Entrenamiento cerrado'))
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
            self.send_response(303)
            if new_routine_id:
                self.send_header('Location', f'/routines?routine_id={new_routine_id}&msg=' + urllib.parse.quote('Rutina creada'))
            else:
                self.send_header('Location', '/routines?msg=' + urllib.parse.quote('Rutina creada'))
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
            cur.execute("DELETE FROM routine_items WHERE routine_id = ?", (routine_id_i,))
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
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("SELECT COALESCE(MAX(sort_order), 0) + 1 FROM routine_items WHERE routine_id = ?", (routine_id_i,))
            next_sort_order = cur.fetchone()[0] or 1
            cur.execute(
                "INSERT INTO routine_items(routine_id, day_name, exercise_id, sets_text, reps_text, notes, sort_order) VALUES(?,?,?,?,?,?,?)",
                (routine_id_i, day_name or 'Lunes', exercise_id_i, sets_text or None, reps_text or None, notes or None, next_sort_order),
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
            cur.execute(
                "UPDATE clients SET name=?, phone=?, birthdate=?, height_cm=?, weight_kg=?, objectives=?, plan_start_date=?, plan_end_date=?, plan_amount=?, plan_notes=? WHERE id=?",
                (name, phone or None, birthdate or None, height_cm, weight_kg, objectives or None, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes or None, cid),
            )
            conn.commit()
            conn.close()
            sync_client_payment_plan(cid, plan_start_date or None, plan_end_date or None, plan_amount, plan_notes)
            self.send_response(303)
            self.send_header('Location', '/clients?msg=' + urllib.parse.quote('Cliente actualizado'))
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
            cur.execute("DELETE FROM client_diet_history WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM client_training_history WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM payment_plans WHERE client_id = ?", (cid_i,))
            cur.execute("DELETE FROM clients WHERE id = ?", (cid_i,))
            for did in client_diet_ids:
                cur.execute("DELETE FROM diet_items WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diet_meals WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diet_day_config WHERE diet_id = ?", (did,))
                cur.execute("DELETE FROM diets WHERE id = ? AND COALESCE(is_template, 1) = 0", (did,))
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
                "UPDATE foods SET name=?, brand=?, category_id=?, calories=?, protein=?, carbs=?, fats=?, serving_size=?, photo_path=?, nutrition_mode=?, per100_unit=?, barcode=?, keywords=?, is_active=?, is_verified=? WHERE id=?",
                (name, brand or None, cat_id, calories, protein, carbs, fats, serving, photo_path, nutrition_mode, per100_unit, barcode or None, keywords or None, is_active, is_verified, fid),
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
            video_url = getp('video_url').strip()
            muscle_group = getp('muscle_group').strip()
            equipment = getp('equipment').strip()
            difficulty = getp('difficulty').strip()
            notes = getp('notes').strip()
            cat_id = None
            if category_id:
                try:
                    cat_id = int(category_id)
                except Exception:
                    cat_id = None
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute(
                "UPDATE exercises SET name=?, exercise_category_id=?, video_url=?, muscle_group=?, equipment=?, difficulty=?, notes=? WHERE id=?",
                (name, cat_id, video_url or None, muscle_group or None, equipment or None, difficulty or None, notes or None, eid),
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
                       photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified
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
                                  photo_path, nutrition_mode, per100_unit, barcode, keywords, is_active, is_verified)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
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
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Categoría de ejercicio creada'))
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
            cur.execute("DELETE FROM exercise_categories WHERE id = ?", (cid_i,))
            conn.commit()
            conn.close()
            self.send_response(303)
            self.send_header('Location', '/exercises?msg=' + urllib.parse.quote('Categoría de ejercicio borrada'))
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
        try:
            super().handle_one_request()
        except Exception as e:
            import traceback
            traceback.print_exc()
            try:
                self.send_error(500, f'Internal server error: {e}')
            except Exception:
                pass


def run():
    ensure_brand_column()
    ensure_exercises_table()
    ensure_routines_table()
    ensure_diets_table()
    ensure_clients_table()
    ensure_payment_plans_table()
    ensure_client_history_tables()
    ensure_diet_builder_tables()
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(STATIC_BASE_DIR, exist_ok=True)
    os.makedirs(UPLOADS_FOODS_DIR, exist_ok=True)
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
