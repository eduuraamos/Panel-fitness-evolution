#!/usr/bin/env python3
"""Servidor HTTP simple que muestra una pestaña (página) con los alimentos de la DB."""
from http.server import HTTPServer, BaseHTTPRequestHandler
import sqlite3
import html
import socket
import urllib.parse


DB_PATH = "data/foods.db"
HOST = "127.0.0.1"
PORT = 8000


def get_foods():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute(
        "SELECT f.id, f.name, c.name as category, f.calories, f.protein, f.carbs, f.fats, f.serving_size FROM foods f LEFT JOIN categories c ON f.category_id = c.id"
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


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path not in ("/", "/index.html", "/add"):
            self.send_response(404)
            self.end_headers()
            self.wfile.write(b"Not found")
            return

        foods = get_foods()
        categories = get_categories()
        html_rows = []
        for r in foods:
            id_, name, category, cal, prot, carbs, fats, serving = r
            html_rows.append(
                f"<tr><td>{id_}</td><td>{html.escape(name)}</td><td>{html.escape(category or '')}</td>"
                f"<td>{cal}</td><td>{prot}</td><td>{carbs}</td><td>{fats}</td><td>{html.escape(serving or '')}</td></tr>"
            )

        page = f"""
        <!doctype html>
        <html>
        <head>
          <meta charset="utf-8" />
          <title>Alimentos</title>
          <style>
            body{{font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial; padding:20px}}
            table{{border-collapse:collapse; width:100%}}
            th,td{{border:1px solid #ddd; padding:8px}}
            th{{background:#f4f4f4; text-align:left}}
          </style>
        </head>
        <body>
                    <h1>Alimentos</h1>
                    <h2>Añadir alimento</h2>
                    <form method="post" action="/add" style="margin-bottom:20px">
                        <input name="name" placeholder="Nombre" required />
                        <select name="category">
                            <option value="">-- Sin categoría --</option>
                            {''.join([f'<option value="{c[0]}">{html.escape(c[1])}</option>' for c in categories])}
                        </select>
                        <input name="calories" placeholder="Calorías" size="6" />
                        <input name="protein" placeholder="Proteína" size="6" />
                        <input name="carbs" placeholder="Carbs" size="6" />
                        <input name="fats" placeholder="Fats" size="6" />
                        <input name="serving_size" placeholder="Porción" />
                        <button type="submit">Añadir</button>
                    </form>

                    <h2>Categorías</h2>
                    <form method="post" action="/add_category" style="margin-bottom:12px">
                        <input name="name" placeholder="Nueva categoría" required />
                        <button type="submit">Crear categoría</button>
                    </form>
                    <ul>
                        {''.join([f'<li>{html.escape(c[1])} '
                                            f'<form method="post" action="/delete_category" style="display:inline;margin-left:8px">'
                                            f'<input type="hidden" name="id" value="{c[0]}" />'
                                            f'<button type="submit">Borrar</button></form></li>' for c in categories])}
                    </ul>
          <table>
            <thead><tr><th>ID</th><th>Nombre</th><th>Categoría</th><th>Cal</th><th>Prot</th><th>Carbs</th><th>Fats</th><th>Porción</th></tr></thead>
            <tbody>
              {''.join(html_rows)}
            </tbody>
          </table>
        </body>
        </html>
        """

        body = page.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self):
        length = int(self.headers.get('Content-Length', 0))
        data = self.rfile.read(length).decode('utf-8')
        params = urllib.parse.parse_qs(data)

        def get(field, default=''):
            return params.get(field, [default])[0]

        if self.path == '/add':
            name = get('name').strip()
            cat_param = get('category').strip()
            try:
                calories = float(get('calories') or 0)
            except ValueError:
                calories = 0
            try:
                protein = float(get('protein') or 0)
            except ValueError:
                protein = 0
            try:
                carbs = float(get('carbs') or 0)
            except ValueError:
                carbs = 0
            try:
                fats = float(get('fats') or 0)
            except ValueError:
                fats = 0
            serving = get('serving_size')

            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cat_id = None
            if cat_param:
                try:
                    cat_id = int(cat_param)
                except Exception:
                    cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (cat_param,))
                    cur.execute("SELECT id FROM categories WHERE name=?", (cat_param,))
                    row = cur.fetchone()
                    cat_id = row[0] if row else None

            cur.execute(
                "INSERT INTO foods(name, category_id, calories, protein, carbs, fats, serving_size) VALUES(?,?,?,?,?,?,?)",
                (name, cat_id, calories, protein, carbs, fats, serving),
            )
            conn.commit()
            conn.close()

            # Redirect back to main page
            self.send_response(303)
            self.send_header('Location', '/')
            self.end_headers()
            return

        if self.path == '/add_category':
            # reuse helper
            self.do_POST_add_category(params)
            self.send_response(303)
            self.send_header('Location', '/')
            self.end_headers()
            return

        if self.path == '/delete_category':
            self.do_POST_delete_category(params)
            self.send_response(303)
            self.send_header('Location', '/')
            self.end_headers()
            return

        # unknown POST
        self.send_response(404)
        self.end_headers()
        
    def do_POST_add_category(self, params):
        name = params.get('name', [''])[0].strip()
        if not name:
            return
        conn = sqlite3.connect(DB_PATH)
        cur = conn.cursor()
        cur.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (name,))
        conn.commit()
        conn.close()

    def do_POST_delete_category(self, params):
        cid = params.get('id', [''])[0]
        try:
            cid_i = int(cid)
        except Exception:
            return
        conn = sqlite3.connect(DB_PATH)
        cur = conn.cursor()
        # detach foods from category, then delete category
        cur.execute("UPDATE foods SET category_id = NULL WHERE category_id = ?", (cid_i,))
        cur.execute("DELETE FROM categories WHERE id = ?", (cid_i,))
        conn.commit()
        conn.close()

    # override handle to route other POST actions
    def handle_one_request(self):
        try:
            super().handle_one_request()
        except Exception:
            pass

    def parse_and_route_post(self):
        # helper not used
        pass


def find_free_port(start=8000, end=9000):
    for p in range(start, end):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind((HOST, p))
                return p
            except OSError:
                continue
    return PORT


def run():
    port = find_free_port(PORT, PORT+50)
    server = HTTPServer((HOST, port), Handler)
    print(f"Servidor iniciado en http://{HOST}:{port} — Ctrl-C para detener")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("Detenido")
        server.server_close()


if __name__ == '__main__':
    run()
