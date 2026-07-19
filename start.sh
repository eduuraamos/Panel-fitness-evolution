#!/bin/bash

# Ir a la carpeta del proyecto
cd "$(dirname "$0")"

# Activar el entorno virtual
source .venv/bin/activate

# Comprobar que DATABASE_URL existe
if [ -z "$DATABASE_URL" ]; then
    echo ""
    echo "❌ ERROR: DATABASE_URL no está configurada."
    echo ""
    echo "Ejecuta primero:"
    echo 'export DATABASE_URL="TU_DATABASE_URL"'
    exit 1
fi

echo ""
echo "✅ PostgreSQL detectado."
echo "🚀 Iniciando aplicación..."
echo ""

python3 scripts/serve_foods.py
