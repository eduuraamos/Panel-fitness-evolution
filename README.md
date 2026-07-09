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
5. Render detectará automáticamente `render.yaml` y creará el servicio web.
6. Pulsa `Apply` para desplegar.
7. Al terminar, Render te dará una URL pública tipo:
	`https://nutrition-app.onrender.com`

Con eso ya tienes el sitio online.

### Importante sobre datos (SQLite)

Si usas plan `free`, el sistema de archivos es efímero y los datos pueden perderse al redeploy/restart.

Para mantener datos de forma persistente:

1. Cambia a un plan que permita disco persistente.
2. Añade un disco al servicio en Render (`Disks`).
3. Usa ese disco para guardar la base de datos SQLite y los uploads.

### Opción alternativa: PythonAnywhere

1. Crea cuenta en https://www.pythonanywhere.com
2. Sube el proyecto.
3. Crea un `Web app` (Python 3).
4. Configura el comando de arranque para ejecutar:
	`python3 scripts/serve_foods.py`
5. Apunta la app al puerto/host que te da la plataforma.

Si quieres, te preparo también la versión para Railway o Fly.io con un solo comando.

Notas importantes:

1. La base de datos SQLite vive en `data/foods.db`.
2. Las fotos de alimentos se guardan en `scripts/static/uploads/foods/`.
3. Para no perder datos, usa un hosting con almacenamiento persistente o haz copias de seguridad.

Archivos de despliegue incluidos:

1. `Procfile` para hosts tipo Heroku.
2. `render.yaml` para Render.
