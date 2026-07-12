from db_adapter import is_postgres_enabled, sqlite3_compat as sqlite3


DEFAULT_FOOD_CATEGORIES = [
    'Carnes', 'Pescados', 'Huevos', 'Lacteos', 'Arroz', 'Pasta', 'Patata/Batata',
    'Frutas', 'Verduras', 'Legumbres', 'Frutos secos', 'Aceites', 'Grasas saludables',
    'Salsas', 'Embutidos', 'Bebidas', 'Dulces', 'Suplementos'
]


_FOOD_SEARCH_FTS_ENABLED = not is_postgres_enabled()


def _coerce_connection(conn_or_path):
    if hasattr(conn_or_path, 'cursor'):
        return conn_or_path, False
    return sqlite3.connect(conn_or_path), True


def supports_foods_search_fts():
    return _FOOD_SEARCH_FTS_ENABLED


def ensure_catalog_schema(conn_or_path):
    conn, should_close = _coerce_connection(conn_or_path)
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
            photo_path TEXT,
            nutrition_mode TEXT DEFAULT 'per100',
            per100_unit TEXT DEFAULT 'g',
            has_gluten INTEGER,
            FOREIGN KEY(category_id) REFERENCES categories(id)
        )
        """
    )

    global _FOOD_SEARCH_FTS_ENABLED
    try:
        if is_postgres_enabled():
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS foods_search (
                    food_id INTEGER PRIMARY KEY,
                    name TEXT,
                    brand TEXT,
                    category TEXT,
                    barcode TEXT,
                    keywords TEXT,
                    searchable TEXT
                )
                """
            )
            _FOOD_SEARCH_FTS_ENABLED = False
        else:
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
            _FOOD_SEARCH_FTS_ENABLED = True
    except Exception:
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS foods_search (
                food_id INTEGER PRIMARY KEY,
                name TEXT,
                brand TEXT,
                category TEXT,
                barcode TEXT,
                keywords TEXT,
                searchable TEXT
            )
            """
        )
        _FOOD_SEARCH_FTS_ENABLED = False

    conn.commit()
    if should_close:
        conn.close()


def ensure_exercise_schema(conn_or_path):
    conn, should_close = _coerce_connection(conn_or_path)
    cur = conn.cursor()
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
            exercise_category_id_2 INTEGER,
            video_url TEXT,
            machine_url TEXT,
            FOREIGN KEY(exercise_category_id) REFERENCES exercise_categories(id),
            FOREIGN KEY(exercise_category_id_2) REFERENCES exercise_categories(id)
        )
        """
    )
    conn.commit()

    cur.execute("PRAGMA table_info(exercises)")
    cols = [r[1] for r in cur.fetchall()]
    if 'exercise_category_id' not in cols:
        cur.execute("ALTER TABLE exercises ADD COLUMN exercise_category_id INTEGER")
        conn.commit()
    if 'exercise_category_id_2' not in cols:
        cur.execute("ALTER TABLE exercises ADD COLUMN exercise_category_id_2 INTEGER")
        conn.commit()
    if 'video_url' not in cols:
        cur.execute("ALTER TABLE exercises ADD COLUMN video_url TEXT")
        conn.commit()
    if 'machine_url' not in cols:
        cur.execute("ALTER TABLE exercises ADD COLUMN machine_url TEXT")
        conn.commit()

    if should_close:
        conn.close()


def ensure_default_food_categories(conn_or_path):
    conn, should_close = _coerce_connection(conn_or_path)
    cur = conn.cursor()
    cur.execute("SELECT COUNT(*) FROM categories")
    count = int(cur.fetchone()[0] or 0)
    if count == 0:
        for name in DEFAULT_FOOD_CATEGORIES:
            cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (name,))
        conn.commit()
    if should_close:
        conn.close()


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
