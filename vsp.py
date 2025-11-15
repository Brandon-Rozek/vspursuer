"""
Check to see if the model has the variable
sharing property.
"""
from itertools import product, chain, combinations
from typing import List, Optional, Set, Tuple
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


class SVSP_Result:
    def __init__(
            self, has_svsp: bool, model_name: Optional[str] = None,
            subalgebra1: Optional[Set[ModelValue]] = None,
            subalgebra2: Optional[Set[ModelValue]] = None,
            U: Optional[Set[ModelValue]] = None,
            L: Optional[Set[ModelValue]] = None):
        self.has_svsp = has_svsp
        self.model_name = model_name
        self.subalgebra1 = subalgebra1
        self.subalgebra2 = subalgebra2
        self.U = U
        self.L = L

    def __str__(self):
        if not self.has_svsp:
            return f"Model {self.model_name} does not have the signed variable sharing property."
        return f"""Model {self.model_name} has the signed variable sharing property.
Subalgebra 1: {set_to_str(self.subalgebra1)}
Subalgebra 2: {set_to_str(self.subalgebra2)}
U: {set_to_str(self.U)}
L: {set_to_str(self.L)}
"""

def powerset_minus_empty(s):
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s) + 1))

def find_k1_k2(model, impfunction: ModelFunction,
            negation_defined: bool) -> List[Tuple[Set[ModelValue], Set[ModelValue]]]:
    """
    Returns a list of possible subalgebra pairs (K1, K2)
    """
    assert model.ordering is not None, "Expected ordering table in model"

    result = []
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
            result.append((carrier_set_left, carrier_set_right))

    return result

def find_candidate_u_l(model: Model, impfn: ModelFunction, negfn: Optional[ModelFunction]) -> List[Tuple[Set[ModelValue], Set[ModelValue]]]:
    result: List[Tuple[Set[ModelValue], Set[ModelValue]]] = []
    F = model.carrier_set - model.designated_values
    Us = powerset_minus_empty(model.carrier_set)
    Ls = powerset_minus_empty(model.carrier_set)
    for (U, L) in product(Us, Ls):
        unsat = False
        U = set(U)
        L = set(L)
        LFi = F.intersection(L)
        # Required property: ∀x ∈ U, y ∈ L(x → y ∈ L ∩ F)
        for (x, y) in product(U, L):
            if impfn(x, y) not in LFi:
                unsat = True
                break

        if unsat:
            continue

        # Required Property: ∀x ∈ L, y ∈ U(x → y ∈ U)
        for (x, y) in product(L, U):
            if impfn(x, y) not in U:
                unsat = True
                break

        if unsat:
            continue

        if negfn is not None:
            for x in L:
                # Required Property: ∀x(x ∈ L ⇒ ¬x ∈ U)
                if negfn(x) not in U:
                    unsat = True
                    break

            if unsat:
                continue

            for x in U:
                # Required Property: ∀x(x ∈ U ⇒ ¬x ∈ L)
                if negfn(x) not in L:
                    unsat = True
                    break

            if unsat:
                continue

        # Passed all required properties
        result.append((U, L))

    return result

def has_svsp(model: Model, impfn: ModelFunction,
            conjfn: Optional[ModelFunction],
            disjfn: Optional[ModelFunction],
            negfn: Optional[ModelFunction]) -> SVSP_Result:
    """
    Checks whether a model has the signed
    variable sharing property.
    """
    # NOTE: No models with only one designated
    # value satisfies SVSP
    if len(model.designated_values) == 1:
        return SVSP_Result(False, model.name)

    F = model.carrier_set - model.designated_values
    starops = [conjfn, disjfn]

    K1K2s = find_k1_k2(model, impfn, negfn is not None)
    ULs = find_candidate_u_l(model, impfn, negfn)

    candidates = ((k1, k2, u, l) for (k1, k2), (u, l) in product(K1K2s, ULs))
    for K1, K2, U, L in candidates:
        unsat = False
        K1Uu = K1 | U
        K1Lu = K1 | L
        K1LuFi = K1Lu.intersection(F) # (K1 ∪ L) ∩ F
        K2Uu = K2 | U
        K2Lu = K2 | L
        K2LuFi = K2Lu.intersection(F) # (K2 ∪ L) ∩ F

        # (6)
        for x, y in product(K1, U):
            # b) x → y ∈ K1 ∪ U
            if impfn(x, y) not in K1Uu:
                unsat = True
                break

            # c) y → x ∈ K1 ∪ L
            if impfn(y, x) not in K1Lu:
                unsat = True
                break

            # a) x ∗ y, y ∗ x, y ∗ z ∈ K1 ∪ U
            for z in U:
                for op in starops:
                    if op is not None:
                        if op(x, y) not in K1Uu:
                            unsat = True
                            break
                        if op(y, x) not in K1Uu:
                            unsat = True
                            break
                        if op(y, z) not in K1Uu:
                            unsat = True
                            break
                if unsat:
                    break

            if unsat:
                # Verification for these set of matrices failed
                break

        if unsat:
            # Move onto the next candidates K1, K2, U, L
            continue

        # (7)
        for x, y in product(K1, L):
            # b) x → y ∈ (K1 ∪ L) ∩ F
            if impfn(x, y) not in K1LuFi:
                unsat = True
                break

            # c) y → x ∈ K1 ∪ U
            if impfn(y, x) not in K1Uu:
                unsat = True
                break

            # a) x ∗ y, y ∗ x, y ∗ z ∈ K1 ∪ L
            for z in L:
                for op in starops:
                    if op is not None:
                        if op(x, y) not in K1Lu:
                            unsat = True
                            break

                        if op(y, x) not in K1Lu:
                            unsat = True
                            break

                        if op(y, z) not in K1Lu:
                            unsat = True
                            break
                if unsat:
                    break

            if unsat:
                break

        if unsat:
            continue

        # (8)
        for x, y in product(K2, U):
            # b) x → y ∈ K2 ∪ U
            if impfn(x, y) not in K2Uu:
                unsat = True
                break

            # c) y → x ∈ (K2 ∪ L) ∩ F
            if impfn(y, x) not in K2LuFi:
                unsat = True
                break

            # a) x ∗ y, y ∗ x, y ∗ z ∈ K2 ∪ U
            for z in U:
                for op in starops:
                    if op is not None:
                        if op(x, y) not in K2Uu:
                            unsat = True
                            break
                        if op(y, x) not in K2Uu:
                            unsat = True
                            break
                        if op(y, z) not in K2Uu:
                            unsat = True
                            break
                if unsat:
                    break

            if unsat:
                break

        if unsat:
            continue

        # (9)
        for x, y in product(K2, L):
            # b) x → y ∈ K2 ∪ L
            if impfn(x, y) not in K2Lu:
                unsat = True
                break

            # c) y → x ∈ K2 ∪ U
            if impfn(y, x) not in K2Uu:
                unsat = True
                break

            # a) x ∗ y, y ∗ x, y ∗ z ∈ K2 ∪ L
            for z in L:
                for op in starops:
                    if op is not None:
                        if op(x, y) not in K2Lu:
                            unsat = True
                            break
                        if op(y, x) not in K2Lu:
                            unsat = True
                            break
                        if op(y, z) not in K2Lu:
                            unsat = True
                            break
                if unsat:
                    break

            if unsat:
                break


        if not unsat:
            return SVSP_Result(True, model.name, K1, K2, U, L)

    return SVSP_Result(False, model.name)
