from typing import Set

def set_to_str(x: Set) -> str:
    return "{" + ", ".join((str(xi) for xi in x)) + "}"
