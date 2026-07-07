#!/usr/bin/env python3
"""Crear y poblar una base de datos SQLite de ejemplo para alimentos."""
from pathlib import Path
import sqlite3


BASE = Path(__file__).resolve().parents[1]
DATA_DIR = BASE / "data"
DB_PATH = DATA_DIR / "foods.db"


FOODS = [
    ("Apple", "Fruits", 52, 0.3, 14, 0.2, "1 medium (182g)"),
    ("Banana", "Fruits", 96, 1.3, 27, 0.3, "1 medium (118g)"),
    ("Chicken Breast", "Meat", 165, 31, 0, 3.6, "100 g cooked"),
    ("White Rice", "Grains", 130, 2.4, 28, 0.3, "100 g cooked"),
    ("Almonds", "Nuts", 579, 21.2, 21.6, 49.9, "100 g"),
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
        CREATE TABLE IF NOT EXISTS foods (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            category_id INTEGER,
            calories REAL,
            protein REAL,
            carbs REAL,
            fats REAL,
            serving_size TEXT,
            FOREIGN KEY(category_id) REFERENCES categories(id)
        )
        """
    )

    conn.commit()
    return conn


def seed(conn):
    cur = conn.cursor()
    for name, category, calories, protein, carbs, fats, serving in FOODS:
        cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (category,))
        cur.execute("SELECT id FROM categories WHERE name=?", (category,))
        cat_id = cur.fetchone()[0]

        cur.execute(
            "INSERT INTO foods(name, category_id, calories, protein, carbs, fats, serving_size)"
            " VALUES(?,?,?,?,?,?,?)",
            (name, cat_id, calories, protein, carbs, fats, serving),
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
