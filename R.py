"""
Modeling the logic R
"""
from logic import (
    Conjunction,
    Disjunction,
    Implication,
    Logic,
    Negation,
    PropositionalVariable,
    Rule,
)
from model import Model, ModelFunction, ModelValue, satisfiable
from generate_model import generate_model
# from vsp import has_vsp


# ===================================================

"""
Defining the Logic of R
"""

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

R_logic = Logic(operations, logic_rules, "R")

# ===============================

"""
Example 2-Element Model of R
"""

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
R_model_2 = Model(carrier_set, logical_operations, designated_values, None, "R2")

interpretation = {
    Negation: mnegation,
    Conjunction: mconjunction,
    Disjunction: mdisjunction,
    Implication: mimplication
}

print(R_model_2)


# =================================

"""
Generate models of R of a specified size
"""

print("*" * 30)

model_size = 2
print("Generating models of Logic", R_logic.name, "of size", model_size)
solutions = generate_model(R_logic, model_size, print_model=False)

print(f"Found {len(solutions)} satisfiable models")

# for model, interpretation in solutions:
#     print(has_vsp(model, interpretation))

print("*" * 30)

######

"""
Showing the smallest model for R that has the
variable sharing property.

This model has 6 elements.
"""

a0 = ModelValue("a0")
a1 = ModelValue("a1")
a2 = ModelValue("a2")
a3 = ModelValue("a3")
a4 = ModelValue("a4")
a5 = ModelValue("a5")

carrier_set = { a0, a1, a2, a3, a4, a5 }
designated_values = {a1, a2, a3, a4, a5 }

mnegation = ModelFunction(1, {
    a5: a0,
    a4: a1,
    a3: a3,
    a2: a2,
    a1: a4,
    a0: a5
}, "¬")

mimplication = ModelFunction(2, {
    (a5, a5): a5,
    (a5, a4): a0,
    (a5, a3): a0,
    (a5, a2): a0,
    (a5, a1): a0,
    (a5, a0): a0,

    (a4, a5): a5,
    (a4, a4): a1,
    (a4, a3): a0,
    (a4, a2): a0,
    (a4, a1): a0,
    (a4, a0): a0,

    (a3, a5): a5,
    (a3, a4): a3,
    (a3, a3): a3,
    (a3, a2): a0,
    (a3, a1): a0,
    (a3, a0): a0,

    (a2, a5): a5,
    (a2, a4): a2,
    (a2, a3): a0,
    (a2, a2): a2,
    (a2, a1): a0,
    (a2, a0): a0,

    (a1, a5): a5,
    (a1, a4): a4,
    (a1, a3): a3,
    (a1, a2): a2,
    (a1, a1): a1,
    (a1, a0): a0,

    (a0, a5): a5,
    (a0, a4): a5,
    (a0, a3): a5,
    (a0, a2): a5,
    (a0, a1): a5,
    (a0, a0): a5
}, "→")


mconjunction = ModelFunction(2, {
    (a5, a5): a5,
    (a5, a4): a4,
    (a5, a3): a3,
    (a5, a2): a2,
    (a5, a1): a1,
    (a5, a0): a0,

    (a4, a5): a4,
    (a4, a4): a4,
    (a4, a3): a3,
    (a4, a2): a2,
    (a4, a1): a1,
    (a4, a0): a0,

    (a3, a5): a3,
    (a3, a4): a3,
    (a3, a3): a3,
    (a3, a2): a1,
    (a3, a1): a1,
    (a3, a0): a0,

    (a2, a5): a2,
    (a2, a4): a2,
    (a2, a3): a1,
    (a2, a2): a2,
    (a2, a1): a1,
    (a2, a0): a0,

    (a1, a5): a1,
    (a1, a4): a1,
    (a1, a3): a1,
    (a1, a2): a1,
    (a1, a1): a1,
    (a1, a0): a0,

    (a0, a5): a0,
    (a0, a4): a0,
    (a0, a3): a0,
    (a0, a2): a0,
    (a0, a1): a0,
    (a0, a0): a0
}, "∧")

mdisjunction = ModelFunction(2, {
    (a5, a5): a5,
    (a5, a4): a5,
    (a5, a3): a5,
    (a5, a2): a5,
    (a5, a1): a5,
    (a5, a0): a5,

    (a4, a5): a5,
    (a4, a4): a4,
    (a4, a3): a4,
    (a4, a2): a4,
    (a4, a1): a4,
    (a4, a0): a4,

    (a3, a5): a5,
    (a3, a4): a4,
    (a3, a3): a3,
    (a3, a2): a4,
    (a3, a1): a3,
    (a3, a0): a3,

    (a2, a5): a5,
    (a2, a4): a4,
    (a2, a3): a4,
    (a2, a2): a2,
    (a2, a1): a2,
    (a2, a0): a2,

    (a1, a5): a5,
    (a1, a4): a4,
    (a1, a3): a3,
    (a1, a2): a2,
    (a1, a1): a1,
    (a1, a0): a1,

    (a0, a5): a5,
    (a0, a4): a4,
    (a0, a3): a3,
    (a0, a2): a2,
    (a0, a1): a1,
    (a0, a0): a0
}, "∨")

logical_operations = {
    mnegation, mimplication, mconjunction, mdisjunction
}
R_model_6 = Model(carrier_set, logical_operations, designated_values, None, "R6")

interpretation = {
    Negation: mnegation,
    Conjunction: mconjunction,
    Disjunction: mdisjunction,
    Implication: mimplication
}

print(R_model_6)
print(f"Model {R_model_6.name} satisfies logic {R_logic.name}?", satisfiable(R_logic, R_model_6, interpretation))
# print(has_vsp(R_model_6, interpretation))
