import requests
import time

OPENFOODFACTS_SEARCH_URL = "https://search.openfoodfacts.org/search"
USER_AGENT = "nutrition-app/1.0 (+https://example.com)"
MAX_PAGE_SIZE = 100
MAX_RETRIES = 3


def _buscar_pagina(busqueda, page, page_size, headers):
    params = {
        "q": busqueda,
        "page": page,
        "page_size": page_size,
        "fields": "product_name,brands",
    }

    last_error = None
    for intento in range(1, MAX_RETRIES + 1):
        try:
            response = requests.get(
                OPENFOODFACTS_SEARCH_URL,
                params=params,
                headers=headers,
                timeout=30,
            )

            if response.status_code in (429, 500, 502, 503, 504) and intento < MAX_RETRIES:
                time.sleep(0.8 * intento)
                continue

            response.raise_for_status()
            return response.json()
        except requests.RequestException as exc:
            last_error = exc
            if intento < MAX_RETRIES:
                time.sleep(0.8 * intento)
            else:
                raise

    if last_error:
        raise last_error


def buscar_productos(busqueda, limite=100):
    limite_total = int(limite)
    if limite_total <= 0:
        return []

    headers = {
        "User-Agent": USER_AGENT,
    }

    productos = []
    page = 1

    while len(productos) < limite_total:
        restantes = limite_total - len(productos)
        page_size = min(MAX_PAGE_SIZE, restantes)

        payload = _buscar_pagina(busqueda, page, page_size, headers)
        hits = payload.get("hits") or []

        if not hits:
            break

        productos.extend(hits)

        page_count = payload.get("page_count")
        if isinstance(page_count, int) and page >= page_count:
            break

        page += 1

    return productos[:limite_total]