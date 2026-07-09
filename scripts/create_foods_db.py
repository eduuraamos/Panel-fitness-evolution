#!/usr/bin/env python3
"""Crear y poblar una base de datos SQLite de ejemplo para alimentos."""
from pathlib import Path
import sqlite3


BASE = Path(__file__).resolve().parents[1]
DATA_DIR = BASE / "data"
DB_PATH = DATA_DIR / "foods.db"


FOODS = [
    # (name, category, calories, protein, carbs, fats, serving, brand)
    ("Apple", "Fruits", 52, 0.3, 14, 0.2, "1 medium (182g)", "Generic"),
    ("Banana", "Fruits", 96, 1.3, 27, 0.3, "1 medium (118g)", "Generic"),
    ("Chicken Breast", "Meat", 165, 31, 0, 3.6, "100 g cooked", "FarmCo"),
    ("White Rice", "Grains", 130, 2.4, 28, 0.3, "100 g cooked", "RiceBrand"),
    ("Almonds", "Nuts", 579, 21.2, 21.6, 49.9, "100 g", "NutCo"),
]

EXERCISE_CATEGORIES = [
    "Strength",
    "Cardio",
    "Flexibility",
]

EXERCISES = [
    # (name, muscle_group, equipment, difficulty, notes, category_name)
    ("Bench Press", "Chest", "Barbell", "Intermediate", "3 sets", "Strength"),
    ("Squat", "Legs", "Barbell", "Intermediate", "3 sets", "Strength"),
    ("Deadlift", "Back", "Barbell", "Advanced", "Warm up first", "Strength"),
]


def ensure_db():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()

    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS categories (
            id INTEGER PRIMARY KEY,
            name TEXT UNIQUE NOT NULL
        )
        """
    )

    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS brands (
            id INTEGER PRIMARY KEY,
            name TEXT UNIQUE NOT NULL
        )
        """
    )

    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS foods (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            brand TEXT,
            category_id INTEGER,
            barcode TEXT,
            keywords TEXT,
            is_active INTEGER DEFAULT 1,
            is_verified INTEGER DEFAULT 0,
            calories REAL,
            protein REAL,
            carbs REAL,
            fats REAL,
            serving_size TEXT,
            FOREIGN KEY(category_id) REFERENCES categories(id)
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

    cur.execute(
        """
        CREATE TABLE IF NOT EXISTS exercises (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            muscle_group TEXT,
            equipment TEXT,
            difficulty TEXT,
            notes TEXT,
            exercise_category_id INTEGER,
            FOREIGN KEY(exercise_category_id) REFERENCES exercise_categories(id)
        )
        """
    )

    conn.commit()
    return conn


def seed(conn):
    cur = conn.cursor()
    seen_brands = set()
    for name, category, calories, protein, carbs, fats, serving, brand in FOODS:
        cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (category,))
        cur.execute("SELECT id FROM categories WHERE name=?", (category,))
        cat_id = cur.fetchone()[0]

        if brand and brand not in seen_brands:
            cur.execute("INSERT OR IGNORE INTO brands(name) VALUES(?)", (brand,))
            seen_brands.add(brand)

        cur.execute(
            "INSERT INTO foods(name, brand, category_id, calories, protein, carbs, fats, serving_size)"
            " VALUES(?,?,?,?,?,?,?,?)",
            (name, brand, cat_id, calories, protein, carbs, fats, serving),
        )

    for category in EXERCISE_CATEGORIES:
        cur.execute("INSERT OR IGNORE INTO exercise_categories(name) VALUES(?)", (category,))

    for name, muscle_group, equipment, difficulty, notes, category in EXERCISES:
        cat_id = None
        if category:
            cur.execute("INSERT OR IGNORE INTO exercise_categories(name) VALUES(?)", (category,))
            cur.execute("SELECT id FROM exercise_categories WHERE name=?", (category,))
            result = cur.fetchone()
            cat_id = result[0] if result else None
        cur.execute(
            "INSERT INTO exercises(name, muscle_group, equipment, difficulty, notes, exercise_category_id) VALUES(?,?,?,?,?,?)",
            (name, muscle_group, equipment, difficulty, notes, cat_id),
        )

    conn.commit()


def main():
    conn = ensure_db()
    seed(conn)
    cur = conn.cursor()
    cur.execute("SELECT COUNT(*) FROM categories")
    categories = cur.fetchone()[0]
    cur.execute("SELECT COUNT(*) FROM foods")
    foods = cur.fetchone()[0]
    conn.close()
    print(f"Base de datos creada en: {DB_PATH}")
    print(f"Categorías: {categories}, Alimentos: {foods}")


if __name__ == "__main__":
    main()
