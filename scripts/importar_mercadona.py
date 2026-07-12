import csv
from pathlib import Path

from .openfoodfacts import buscar_productos
from .clasificador import obtener_categoria
from .sqlite_utils import insertar_producto


BUSQUEDA = "Hacendado"
LIMITE = 500
RUTA_SIN_CATEGORIA = Path("data/sin_categoria.csv")


def descargar_productos():
    return buscar_productos(BUSQUEDA, LIMITE)


def _normalizar_campo_texto(valor, usar_primero=False):
    if isinstance(valor, str):
        texto = valor.strip()
        return texto or None

    if isinstance(valor, list):
        if usar_primero:
            if not valor:
                return None
            primero = valor[0]
            if isinstance(primero, str):
                texto = primero.strip()
                return texto or None
            return None

        for item in valor:
            if isinstance(item, str):
                texto = item.strip()
                if texto:
                    return texto
        return None

    return None


def procesar_productos(productos):
    insertados = 0
    duplicados = 0
    sin_categoria = 0
    sin_categoria_unicos = set()

    for producto in productos:
        nombre = _normalizar_campo_texto(producto.get("product_name")) or ""
        marca = _normalizar_campo_texto(producto.get("brands"), usar_primero=True)

        if not nombre:
            continue

        category_id = obtener_categoria(nombre)
        if category_id is None:
            sin_categoria += 1
            sin_categoria_unicos.add((nombre, marca or ""))
            continue

        if insertar_producto(nombre, marca, category_id):
            insertados += 1
        else:
            duplicados += 1

    return {
        "descargados": len(productos),
        "insertados": insertados,
        "duplicados": duplicados,
        "sin_categoria": sin_categoria,
        "sin_categoria_unicos": sorted(sin_categoria_unicos),
    }


def guardar_sin_categoria(filas):
    RUTA_SIN_CATEGORIA.parent.mkdir(parents=True, exist_ok=True)
    with RUTA_SIN_CATEGORIA.open("w", newline="", encoding="utf-8") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["Nombre", "Marca"])
        for nombre, marca in filas:
            writer.writerow([nombre, marca])


def imprimir_resumen(resumen):
    print(f"Productos descargados: {resumen['descargados']}")
    print(f"Insertados: {resumen['insertados']}")
    print(f"Duplicados: {resumen['duplicados']}")
    print(f"Sin categoría: {resumen['sin_categoria']}")


def main():
    productos = descargar_productos()
    resumen = procesar_productos(productos)
    guardar_sin_categoria(resumen["sin_categoria_unicos"])
    imprimir_resumen(resumen)
    print("Archivo generado:")
    print("data/sin_categoria.csv")


if __name__ == "__main__":
    main()
    