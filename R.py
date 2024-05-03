"""
Modeling the logic R
"""
from logic import (
    PropositionalVariable,
    Rule,
    Logic,
    Implication,
    Conjunction,
    Negation,
    Disjunction,
    Rule,
)
from model import Model, ModelFunction, ModelValue, violates_vsp
from generate_model import generate_model


# ===================================================

# Defining the logic of R

x = PropositionalVariable("x")
y = PropositionalVariable("y")
z = PropositionalVariable("z")

implication_rules = {
    Rule(set(), Implication(x, x)),
    Rule({Implication(x, y), Implication(y,  z)}, Implication(x, z)),
    Rule({Implication(x, Implication(x, y)),}, Implication(x, y)),
    Rule({Implication(x, Implication(y, z)),}, Implication(y, Implication(x, z))),
    Rule({Implication(x, y),}, Implication(Implication(z, x), Implication(z, y))),
    Rule({Implication(x, y),}, Implication(Implication(y, z), Implication(x, z))),
    Rule({Implication(x, y), x}, y)
}

negation_rules = {
    Rule({Negation(Negation(x)),}, x),
    Rule({x,}, Negation(Negation(x))),
    Rule({Implication(x, y)}, Implication(Negation(y), Negation(x))),
    Rule({Implication(x, y),}, Implication(Negation(y), Negation(x)))
}

conjunction_rules = {
    Rule({y, z}, Conjunction(y, z)),
    Rule({Conjunction(x, y),}, x),
    Rule({Conjunction(x, y),}, y),
    Rule({Conjunction(Implication(x, y), Implication(x, z)),}, Implication(x, Conjunction(y, z)))
}

disjunction_rules = {
    Rule({x,}, Disjunction(x, y)),
    Rule({y,}, Disjunction(x, y)),
    Rule({Conjunction(Implication(x, z), Implication(y, z)),}, Implication(Disjunction(x, y), z)),
    Rule({Conjunction(x, Disjunction(y, z)),}, Disjunction(Conjunction(x, y), Conjunction(x, z)))
}


logic_rules = implication_rules | negation_rules | conjunction_rules | disjunction_rules

operations = {Negation, Conjunction, Disjunction, Implication}

R_logic = Logic(operations, logic_rules)

# ===============================

# Example Model of R


a0 = ModelValue("a0")
a1 = ModelValue("a1")

carrier_set = {a0, a1}

mnegation = ModelFunction(1, {
    a0: a1,
    a1: a0
})

mimplication = ModelFunction(2, {
    (a0, a0): a1,
    (a0, a1): a1,
    (a1, a0): a0,
    (a1, a1): a1
})

mconjunction = ModelFunction(2, {
    (a0, a0): a0,
    (a0, a1): a0,
    (a1, a0): a0,
    (a1, a1): a1  
})

mdisjunction = ModelFunction(2, {
    (a0, a0): a0,
    (a0, a1): a1,
    (a1, a0): a1,
    (a1, a1): a1  
})


designated_values = {a1}

logical_operations = {
    mnegation, mimplication, mconjunction, mdisjunction
}
R_model_2 = Model(carrier_set, logical_operations, designated_values)

interpretation = {
    Negation: mnegation,
    Conjunction: mconjunction,
    Disjunction: mdisjunction,
    Implication: mimplication
}


# =================================

# Generate models of R of a given size

model_size = 2
satisfiable_models = generate_model(R_logic, model_size, print_model=True)

print(f"There are {len(satisfiable_models)} satisfiable models of element length {model_size}")

for smodel in satisfiable_models:
    print(violates_vsp(smodel[0], smodel[1]))

