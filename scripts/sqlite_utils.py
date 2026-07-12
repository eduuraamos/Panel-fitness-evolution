import sqlite3


def _asegurar_columna_status(cur):
    cur.execute("PRAGMA table_info(foods)")
    columnas = {row[1] for row in cur.fetchall()}
    if "status" not in columnas:
        cur.execute("ALTER TABLE foods ADD COLUMN status TEXT DEFAULT 'pending'")


def insertar_producto(nombre, marca, category_id):
    conn = sqlite3.connect('data/foods.db')
    try:
        cur = conn.cursor()
        _asegurar_columna_status(cur)
        cur.execute(
            "SELECT 1 FROM foods WHERE LOWER(name) = LOWER(?) LIMIT 1",
            (nombre,),
        )
        if cur.fetchone() is not None:
            return False

        cur.execute(
            "INSERT INTO foods(name, brand, category_id, status) VALUES(?, ?, ?, ?)",
            (nombre, marca, category_id, "pending"),
        )
        conn.commit()
        return True
    finally:
        conn.close()
