import unicodedata


def _normalizar_texto(texto):
    base = unicodedata.normalize("NFKD", str(texto or ""))
    sin_acentos = "".join(ch for ch in base if not unicodedata.combining(ch))
    return sin_acentos.lower().strip()


def obtener_categoria(nombre_producto):
    texto = _normalizar_texto(nombre_producto)

    reglas = {
        1: [
            "pollo", "pavo", "ternera", "vacuno", "cerdo", "cordero", "conejo",
            "hamburguesa", "solomillo", "lomo", "costilla", "pechuga", "muslo",
            "alitas", "carne picada",
        ],
        2: [
            "atun", "salmon", "merluza", "bacalao", "dorada", "lubina", "caballa",
            "sardina", "bonito", "emperador",
        ],
        18: [
            "gamba", "gambon", "langostino", "mejillon", "almeja", "pulpo",
            "calamar", "sepia",
        ],
        3: ["huevo", "claras"],
        4: [
            "leche", "queso", "yogur", "yogurt", "skyr", "kefir", "cottage",
            "mozzarella", "feta", "parmesano", "gouda", "havarti", "mascarpone",
            "ricotta", "requeson", "cuajada", "nata", "mantequilla",
        ],
        6: [
            "macarrones", "espaguetis", "espirales", "tallarines", "ravioli",
            "tortellini", "pasta", "fideos", "lasana",
        ],
        7: ["patata", "batata", "boniato"],
        8: [
            "manzana", "platano", "banana", "pera", "kiwi", "naranja", "mandarina",
            "limon", "lima", "pina", "mango", "melon", "sandia", "uva", "cereza",
            "fresa", "arandano", "frambuesa", "mora", "melocoton", "nectarina", "paraguayo",
        ],
        9: [
            "tomate", "lechuga", "cebolla", "zanahoria", "espinaca", "espinacas",
            "brocoli", "coliflor", "pepino", "pimiento", "calabacin", "berenjena",
            "esparrago", "champinon", "setas",
        ],
        10: ["garbanzo", "garbanzos", "lenteja", "lentejas", "alubia", "alubias", "judia", "judias", "soja"],
        11: [
            "almendra", "nuez", "nueces", "pistacho", "pistachos", "avellana",
            "avellanas", "anacardo", "anacardos", "cacahuete", "cacahuetes",
        ],
        14: ["ketchup", "mayonesa", "mostaza", "tomate frito", "salsa", "pesto", "barbacoa"],
        15: ["jamon", "chorizo", "salchichon", "salchicha", "mortadela", "fuet", "lomo embuchado", "pavo cocido"],
        17: [
            "chocolate", "cacao", "galleta", "galletas", "donut", "croissant",
            "brownie", "bizcocho", "magdalena", "helado", "crema cacao",
        ],
    }

    mejor_categoria = None
    mejor_longitud = -1

    for category_id, palabras_clave in reglas.items():
        for palabra in palabras_clave:
            palabra_norm = _normalizar_texto(palabra)
            if palabra_norm and palabra_norm in texto:
                longitud = len(palabra_norm)
                if longitud > mejor_longitud:
                    mejor_longitud = longitud
                    mejor_categoria = category_id

    return mejor_categoria
