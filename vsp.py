"""
Check to see if the model has the variable
sharing property.
"""
from itertools import product
from typing import List, Optional, Set, Tuple
from common import set_to_str
from model import (
    Model, model_closure, ModelFunction, ModelValue
)

SMT_LOADED = True
try:
    from z3 import And, Or, Implies, sat
    from smt import SMTModelEncoder
except ImportError:
    SMT_LOADED = False

class VSP_Result:
    def __init__(
            self, has_vsp: bool, model_name: Optional[str] = None,
            subalgebra1: Optional[Set[ModelValue]] = None,
            subalgebra2: Optional[Set[ModelValue]] = None):
        self.has_vsp = has_vsp
        self.model_name = model_name
        self.subalgebra1 = subalgebra1
        self.subalgebra2 = subalgebra2

    def __str__(self):
        if not self.has_vsp:
            return f"Model {self.model_name} does not have the variable sharing property."
        return f"""Model {self.model_name} has the variable sharing property.
Subalgebra 1: {set_to_str(self.subalgebra1)}
Subalgebra 2: {set_to_str(self.subalgebra2)}
"""

def has_vsp_magical(model: Model, impfunction: ModelFunction,
            negation_defined: bool) -> VSP_Result:
    """
    Checks whether a MaGIC model has the variable
    sharing property.
    """
    # NOTE: No models with only one designated
    # value satisfies VSP
    if len(model.designated_values) == 1:
        return VSP_Result(False, model.name)

    assert model.ordering is not None, "Expected ordering table in model"

    top = model.ordering.top()
    bottom = model.ordering.bottom()

    # Compute I the set of tuples (x, y) where
    # x -> y does not take a designiated value
    I: List[Tuple[ModelValue, ModelValue]] = []

    for (x, y) in product(model.designated_values, model.designated_values):
        if impfunction(x, y) not in model.designated_values:
            I.append((x, y))

    # Find the subalgebras which falsify implication
    for xys in I:

        xi = xys[0]

        # Discard ({⊥} ∪ A', B) subalgebras
        if bottom is not None and xi == bottom:
            continue

        # Discard ({⊤} ∪ A', B) subalgebras when negation is defined
        if top is not None and negation_defined and xi == top:
            continue

        yi = xys[1]

        # Discard (A, {⊤} ∪ B') subalgebras
        if top is not None and yi == top:
            continue

        # Discard (A, {⊥} ∪ B') subalgebras when negation is defined
        if bottom is not None and negation_defined and yi == bottom:
            continue

        # Discard ({a} ∪ A', {b} ∪ B') subalgebras when a <= b
        if model.ordering.is_lt(xi, yi):
            continue

        # Discard ({a} ∪ A', {b} ∪ B') subalgebras when b <= a and negation is defined
        if negation_defined and model.ordering.is_lt(yi, xi):
            continue

        # Compute the left closure of the set containing xi under all the operations
        carrier_set_left: Set[ModelValue] = model_closure({xi,}, model.logical_operations, bottom)

        # Discard ({⊥} ∪ A', B) subalgebras
        if bottom is not None and bottom in carrier_set_left:
            continue

        # Discard ({⊤} ∪ A', B) subalgebras when negation is defined
        if top is not None and negation_defined and top in carrier_set_left:
            continue

        # Compute the closure of all operations
        # with just the ys
        carrier_set_right: Set[ModelValue] = model_closure({yi,}, model.logical_operations, top)

        # Discard (A, {⊤} ∪ B') subalgebras
        if top is not None and top in carrier_set_right:
            continue

        # Discard (A, {⊥} ∪ B') subalgebras when negation is defined
        if bottom is not None and negation_defined and bottom in carrier_set_right:
            continue

        # Discard subalgebras that intersect
        if not carrier_set_left.isdisjoint(carrier_set_right):
            continue

        # Check whether for all pairs in the subalgebra,
        # that implication is falsified.
        falsified = True
        for (x2, y2) in product(carrier_set_left, carrier_set_right):
            if impfunction(x2, y2) in model.designated_values:
                falsified = False
                break

        if falsified:
            return VSP_Result(True, model.name, carrier_set_left, carrier_set_right)

    return VSP_Result(False, model.name)

def has_vsp_smt(model: Model, impfn: ModelFunction) -> VSP_Result:
    """
    Checks whether a given model satisfies the variable
    sharing property via SMT
    """
    if not SMT_LOADED:
        raise Exception("Z3 is not property installed, cannot check via SMT")

    encoder = SMTModelEncoder(model)

    # Create predicates for our two subalgebras
    IsInK1 = encoder.create_predicate("IsInK1", 1)
    IsInK2 = encoder.create_predicate("IsInK2", 1)

    # Enforce that our two subalgebras are non-empty
    encoder.solver.add(Or([IsInK1(x) for x in encoder.smt_carrier_set]))
    encoder.solver.add(Or([IsInK2(x) for x in encoder.smt_carrier_set]))

    # K1/K2 are closed under the operations
    for model_fn, smt_fn in encoder.model_function_map.items():
        for xs in product(encoder.smt_carrier_set, repeat=model_fn.arity):
            encoder.solver.add(
                Implies(
                    And([IsInK1(x) for x in xs]),
                    IsInK1(smt_fn(*xs))
                )
            )
            encoder.solver.add(
                Implies(
                    And([IsInK2(x) for x in xs]),
                    IsInK2(smt_fn(*xs))
                )
            )

    # x -> y is non-designated
    smt_imp = encoder.model_function_map[impfn]
    for (x, y) in product(encoder.smt_carrier_set, encoder.smt_carrier_set):
        encoder.solver.add(
            Implies(
                And(IsInK1(x), IsInK2(y)),
                encoder.is_designated(smt_imp(x, y)) == False
            )
        )

    # Execute solver
    if encoder.solver.check() == sat:
        # Extract subalgebras
        smt_model = encoder.solver.model()
        K1_smt = [x for x in encoder.smt_carrier_set if smt_model.evaluate(IsInK1(x))]
        K1 = {ModelValue(str(x)) for x in K1_smt}

        K2_smt = [x for x in encoder.smt_carrier_set if smt_model.evaluate(IsInK2(x))]
        K2 = {ModelValue(str(x)) for x in K2_smt}

        return VSP_Result(True, model.name, K1, K2)
    else:
        return VSP_Result(False, model.name)


def has_vsp(model: Model, impfunction: ModelFunction,
            negation_defined: bool) -> VSP_Result:
    if model.is_magical:
        return has_vsp_magical(model, impfunction, negation_defined)

    return has_vsp_smt(model)
