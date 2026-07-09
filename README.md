# Nutrition app — base de datos de alimentos

Script sencillo para crear y poblar una base de datos SQLite de ejemplo con alimentos.

Instrucciones rápidas:

1. Ejecutar el script:

```bash
python3 scripts/create_foods_db.py
```

2. El archivo de base de datos resultante será `data/foods.db`.

## Despliegue

La aplicación se puede subir a un hosting Python como Render o PythonAnywhere.

### Opción recomendada: Render (rápido)

1. Sube este proyecto a GitHub.
2. Entra en Render: https://render.com
3. Crea un `New +` -> `Blueprint`.
4. Selecciona tu repositorio.
5. Render detectará automáticamente `render.yaml` y creará el servicio web con disco persistente.
6. Pulsa `Apply` para desplegar.
7. Al terminar, Render te dará una URL pública tipo:
	`https://nutrition-app.onrender.com`

Con eso ya tienes el sitio online.

### Importante sobre datos (SQLite)

Con el `render.yaml` actual, la app usa:

1. `DATA_DIR=/var/data`
2. `UPLOADS_DIR=/var/data/uploads`

Esto permite persistencia real para:

1. Base de datos SQLite (`foods.db`)
2. Fotos subidas (`/static/uploads/foods/...`)

Nota: para usar disco persistente en Render necesitas un plan con soporte de discos (por eso el blueprint está en `starter`).

### Opción alternativa: PythonAnywhere

1. Crea cuenta en https://www.pythonanywhere.com
2. Sube el proyecto.
3. Crea un `Web app` (Python 3).
4. Configura el comando de arranque para ejecutar:
	`python3 scripts/serve_foods.py`
5. Apunta la app al puerto/host que te da la plataforma.

Si quieres, te preparo también la versión para Railway o Fly.io con un solo comando.

Notas importantes:

1. En local, la base de datos vive en `data/foods.db`.
2. En Render, la base y uploads van al disco persistente (`/var/data`).
3. Las fotos siguen sirviéndose por URL web bajo `/static/uploads/foods/...`.

Archivos de despliegue incluidos:

1. `Procfile` para hosts tipo Heroku.
2. `render.yaml` para Render.
