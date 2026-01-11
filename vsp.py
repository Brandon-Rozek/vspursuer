"""
Check to see if the model has the variable
sharing property.
"""
from itertools import product, chain, combinations
from typing import List, Generator, Optional, Set, Tuple
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
            return f"Matrix {self.model_name} does not have the variable sharing property."
        return f"""Matrix {self.model_name} has the variable sharing property.
Subalgebra 1: {set_to_str(self.subalgebra1)}
Subalgebra 2: {set_to_str(self.subalgebra2)}
"""

def has_vsp(model: Model, impfunction: ModelFunction,
            negation_defined: bool, conjunction_disjunction_defined: bool) -> VSP_Result:
    """
    Checks whether a model has the variable
    sharing property.
    """
    # NOTE: No models with only one designated
    # value satisfies VSP
    if len(model.designated_values) == 1:
        return VSP_Result(False, model.name)

    if len(model.carrier_set) in [2,3,4,5,7] \
        and conjunction_disjunction_defined and negation_defined:
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

def find_k1_k2(model: Model, impfunction: ModelFunction,
            negation_defined: bool) -> Generator[Tuple[Set[ModelValue], Set[ModelValue]], None, None]:
    """
    Returns a list of possible subalgebra pairs (K1, K2)
    for SVSP. This is less efficient than the VSP version
    due to interaction with the L and U sets in SVSP.
    """
    assert model.ordering is not None, "Expected ordering table in model"

    top = model.ordering.top()
    bottom = model.ordering.bottom()

    # Compute I the set of tuples (x, y) where
    # x -> y does not take a designiated value
    I: List[Tuple[ModelValue, ModelValue]] = []

    for (x, y) in product(model.carrier_set, model.carrier_set):
        if impfunction(x, y) not in model.designated_values:
            I.append((x, y))

    Is = powerset_minus_empty(I)

    # Find the subalgebras which falsify implication
    for xys in Is:

        xs = {xy[0] for xy in xys}

        # Discard ({⊥} ∪ A', B) subalgebras
        if bottom is not None and bottom in xs:
            continue

        # Discard ({⊤} ∪ A', B) subalgebras when negation is defined
        if top is not None and negation_defined and top in xs:
            continue

        ys = {xy[1] for xy in xys}

        # Discard (A, {⊤} ∪ B') subalgebras
        if top is not None and top in ys:
            continue

        # Discard (A, {⊥} ∪ B') subalgebras when negation is defined
        if bottom is not None and negation_defined and bottom in ys:
            continue

        order_dependent = False
        for (xi, yi) in product(xs, ys):
            # Discard ({a} ∪ A', {b} ∪ B') subalgebras when a <= b
            if model.ordering.is_lt(xi, yi):
                order_dependent = True
                break
            # Discard ({a} ∪ A', {b} ∪ B') subalgebras when b <= a and negation is defined
            if negation_defined and model.ordering.is_lt(yi, xi):
                order_dependent = True
                break

        if order_dependent:
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
            yield (carrier_set_left, carrier_set_right)

def find_candidate_u_l(
        model: Model, impfn: ModelFunction, negfn: Optional[ModelFunction],
        K1: Set[ModelValue], K2: Set[ModelValue]) -> Generator[Tuple[Set[ModelValue], Set[ModelValue]], None, None]:

    # Compute I the set of tuples (x, y) where
    # x -> y does not take a designiated value
    I: List[Tuple[ModelValue, ModelValue]] = []

    if negfn is None:
        # NOTE: K2 ∩ U = ∅ if ∀x(x → x) ∈ T
        # NOTE: K1 ∩ L = ∅ if ∀x(x → x) ∈ T
        for (x, y) in product(model.carrier_set - K2, model.carrier_set - K1):
            if impfn(x, y) not in model.designated_values:
                I.append((x, y))
    else:
        # NOTE: K1, K2, L, and U are pairwise distinct
        CmK1uK2 = model.carrier_set - (K1 | K2)
        for (x, y) in product(CmK1uK2, CmK1uK2):
            if impfn(x, y) not in model.designated_values:
                I.append((x, y))

    Is = powerset_minus_empty(I)
    F = model.carrier_set - model.designated_values

    has_double_negation_eq = False

    if negfn is not None:
        has_double_negation_eq = True
        for x in model.carrier_set:
            if negfn(negfn(x)) != x:
                has_double_negation_eq = False
                break

    for ULs in Is:
        unsat = False
        U = {UL[0] for UL in ULs}
        L = {UL[1] for UL in ULs}

        # U and L are distinct
        if U.intersection(L):
            continue

        if has_double_negation_eq:
            # NOTE: U is the negation image of L, that is, U = {¬x | x ∈ L}, if ∀x(x = ¬¬x).
            U2 = {negfn(x) for x in L}
            if U != U2:
                continue
            yield (U, L)

        LFi = F.intersection(L)

        for (x, y) in product(U, L):
            # Required property: ∀x ∈ U, y ∈ L(x → y ∈ L ∩ F)
            if impfn(x, y) not in LFi:
                unsat = True
                break
            # Required Property: ∀x ∈ L, y ∈ U(x → y ∈ U)
            if impfn(y, x) not in U:
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
        yield (U, L)


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

    for K1, K2 in K1K2s:
        ULs = find_candidate_u_l(model, impfn, negfn, K1, K2)
        for U, L in ULs:
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
