from typing import Set

def immutable(_self, _name, _value):
    raise Exception("Model values are immutable")

def set_to_str(x: Set) -> str:
    return "{" + ", ".join((str(xi) for xi in x)) + "}"
