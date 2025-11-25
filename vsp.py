"""
Check to see if the model has the variable
sharing property.
"""
from itertools import product
from typing import Dict, List, Optional, Set, Tuple
from common import set_to_str
from model import (
    Model, model_closure, ModelFunction, ModelValue
)

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

def has_vsp(model: Model, impfunction: ModelFunction,
            negation_defined: bool) -> VSP_Result:
    """
    Checks whether a model has the variable
    sharing property.
    """
    # NOTE: No models with only one designated
    # value satisfies VSP
    if len(model.designated_values) == 1:
        return VSP_Result(False, model.name)

    assert model.ordering is not None, "Expected ordering table in model"

    top = model.ordering.top()
    bottom = model.ordering.bottom()

    # Cache of closures
    C: Dict[ModelValue, Set[ModelValue]] = {}

    for x in model.designated_values:
        # Discard ({⊥} ∪ A', B) subalgebras
        if bottom is not None and x == bottom:
            continue

        # Discard ({⊤} ∪ A', B) subalgebras when negation is defined
        if top is not None and negation_defined and x == top:
            continue

        candidate_ys = [y for y in model.designated_values if impfunction(x, y) not in model.designated_values]

        if len(candidate_ys) == 0:
            continue

        carrier_set_left: Set[ModelValue] = model_closure(C.get(x, {x,}), model.logical_operations, bottom)
        C[x] = carrier_set_left

        # Discard ({⊥} ∪ A', B) subalgebras
        if bottom is not None and bottom in carrier_set_left:
            continue

        # Discard ({⊤} ∪ A', B) subalgebras when negation is defined
        if top is not None and negation_defined and top in carrier_set_left:
            continue
            
        for y in candidate_ys:
            # Discard ({a} ∪ A', {b} ∪ B') subalgebras when a <= b
            if model.ordering.is_lt(x, y):
                continue

            # Discard ({a} ∪ A', {b} ∪ B') subalgebras when b <= a and negation is defined
            if negation_defined and model.ordering.is_lt(y, x):
                continue


            # Discard (A, {⊤} ∪ B') subalgebras
            if top is not None and y == top:
                continue

            # Discard (A, {⊥} ∪ B') subalgebras when negation is defined
            if bottom is not None and negation_defined and y == bottom:
                continue

            carrier_set_right: Set[ModelValue] = model_closure(C.get(y, {y,}), model.logical_operations, top)
            C[y] = carrier_set_right

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
