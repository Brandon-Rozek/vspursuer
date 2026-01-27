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
from vsp import has_vsp
from smt import smt_is_loaded


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

falsification_rules = {
    # At least one value is non-designated
    Rule(set(), x)
}


logic_rules = implication_rules | negation_rules | conjunction_rules | disjunction_rules

operations = {Negation, Conjunction, Disjunction, Implication}

R_logic = Logic(operations, logic_rules, falsification_rules, "R")

# ===============================

"""
Example 2-Element Model of R
"""

a0 = ModelValue("0")
a1 = ModelValue("1")

carrier_set = {a0, a1}

mnegation = ModelFunction(1, {
    a0: a1,
    a1: a0
}, "¬")

mimplication = ModelFunction(2, {
    (a0, a0): a1,
    (a0, a1): a1,
    (a1, a0): a0,
    (a1, a1): a1
}, "→")

mconjunction = ModelFunction(2, {
    (a0, a0): a0,
    (a0, a1): a0,
    (a1, a0): a0,
    (a1, a1): a1
}, "∧")

mdisjunction = ModelFunction(2, {
    (a0, a0): a0,
    (a0, a1): a1,
    (a1, a0): a1,
    (a1, a1): a1
}, "∨")


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

print(f"Does {R_model_2.name} satisfy the logic R?", satisfiable(R_logic, R_model_2, interpretation))

if smt_is_loaded():
    print(has_vsp(R_model_2, mimplication, True, True))
else:
    print("Z3 not setup, skipping VSP check...")


# =================================

"""
Generate models of R of a specified size using the slow approach
"""

print("*" * 30)

model_size = 2
print("Generating models of Logic", R_logic.name, "of size", model_size)
solutions = generate_model(R_logic, model_size, print_model=False)

if smt_is_loaded():
    num_satisfies_vsp = 0
    for model, interpretation in solutions:
        negation_defined = Negation in interpretation
        conj_disj_defined = Conjunction in interpretation and Disjunction in interpretation
        if has_vsp(model, interpretation[Implication], negation_defined, conj_disj_defined).has_vsp:
            num_satisfies_vsp += 1

    print(f"Found {len(solutions)} satisfiable models of size {model_size}, {num_satisfies_vsp} of which satisfy VSP")


print("*" * 30)

# =================================

"""
Showing the smallest model for R that has the
variable sharing property.

This model has 6 elements.
"""

a0 = ModelValue("0")
a1 = ModelValue("1")
a2 = ModelValue("2")
a3 = ModelValue("3")
a4 = ModelValue("4")
a5 = ModelValue("5")

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
if smt_is_loaded():
    print(has_vsp(R_model_6, mimplication, True, True))
else:
    print("Z3 not loaded, skipping VSP check...")

"""
Generate models of R of a specified size using the SMT approach
"""

from vsp import logic_has_vsp

size = 7
print(f"Searching for a model of size {size} which witness VSP...")
if smt_is_loaded():
    solution = logic_has_vsp(R_logic, size)
    if solution is None:
        print(f"No models found of size {size} which witness VSP")
    else:
        model, vsp_result = solution
        print(vsp_result)
        print(model)
else:
    print("Z3 not setup, skipping...")