"""
Check to see if the model has the variable
sharing property.
"""
from itertools import chain, combinations, product
from typing import Dict, List, Optional, Set, Tuple
from common import set_to_str
from model import (
    Model, model_closure, ModelFunction, ModelValue
)
from logic import Conjunction, Disjunction, Implication, Operation

def preseed(
        initial_set: Set[ModelValue],
        cache:List[Tuple[Set[ModelValue], Set[ModelValue]]]):
    """
    Given a cache of previous model_closure calls,
    use this to compute an initial model closure
    set based on the initial set.

    Basic Idea:
    Let {1, 2, 3} -> X be in the cache.
    If {1,2,3} is a subset of initial set,
    then X is the subset of the output of model_closure.

    This is used to speed up subsequent calls to model_closure
    """
    candidate_preseed: Tuple[Set[ModelValue], int] = (None, None)

    for i, o in cache:
        if i < initial_set:
            cost = len(initial_set - i)
            # If i is a subset with less missing elements than
            # the previous candidate, then it's the new candidate.
            if candidate_preseed[1] is None or cost < candidate_preseed[1]:
                candidate_preseed = o, cost

    same_set = candidate_preseed[1] == 0
    return candidate_preseed[0], same_set

def has_top_bottom(subalgebra: Set[ModelValue], mconjunction: Optional[ModelFunction], mdisjunction: Optional[ModelFunction]):
    """
    Checks the subalgebra to see whether it
    contains a top or bottom element.

    Note: This does not compute the closure.

    By definition,
    The top element is any element x where x || x = x
    The bottom element is any element x where x && x = x
    """
    if mconjunction is None or mdisjunction is None:
        return False

    for x in subalgebra:
        if mconjunction(x, x) == x:
            # print("Bottom Element Found")
            return True

        if mdisjunction(x, x) == x:
            # print("Top Element Found")
            return True

    return False



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

def has_vsp(model: Model, interpretation: Dict[Operation, ModelFunction]) -> VSP_Result:
    """
    Checks whether a model has the variable
    sharing property.
    """
    impfunction = interpretation[Implication]
    mconjunction = interpretation.get(Conjunction)
    mdisjunction = interpretation.get(Disjunction)

    # Compute I the set of tuples (x, y) where
    # x -> y does not take a designiated value
    I: Set[Tuple[ModelValue, ModelValue]] = set()

    for (x, y) in product(model.carrier_set, model.carrier_set):
        if impfunction(x, y) not in model.designated_values:
            I.add((x, y))

    # Construct the powerset of I without the empty set
    s = list(I)
    I_power = chain.from_iterable(combinations(s, r) for r in range(1, len(s) + 1))
    # ((x1, y1)), ((x1, y1), (x2, y2)), ...

    # Closure cache
    closure_cache: List[Tuple[Set[ModelValue], Set[ModelValue]]] = []

    # Find the subalgebras which falsify implication
    for xys in I_power:

        xs = {xy[0] for xy in xys}
        orig_xs = xs
        cached_xs = preseed(xs, closure_cache)
        if cached_xs[0] is not None:
            xs |= cached_xs[0]

        ys = {xy[1] for xy in xys}
        orig_ys = ys
        cached_ys = preseed(ys, closure_cache)
        if cached_ys[0] is not None:
            ys |= cached_ys[0]


        # NOTE: Optimziation before model_closure
        # If the two subalgebras intersect, move
        # onto the next pair
        if len(xs & ys) > 0:
            continue

        # NOTE: Optimization
        # if either subalgebra contains top or bottom, move
        # onto the next pair
        if has_top_bottom(xs, mconjunction, mdisjunction) or has_top_bottom(ys, mconjunction, mdisjunction):
            continue

        # Compute the closure of all operations
        # with just the xs
        carrier_set_left: Set[ModelValue] = model_closure(xs, model.logical_operations)

        # Save to cache
        if cached_xs[0] is not None and not cached_ys[1]:
            closure_cache.append((orig_xs, carrier_set_left))


        # Compute the closure of all operations
        # with just the ys
        carrier_set_right: Set[ModelValue] = model_closure(ys, model.logical_operations)

        # Save to cache
        if cached_ys[0] is not None and not cached_ys[1]:
            closure_cache.append((orig_ys, carrier_set_right))


        # If the carrier set intersects, then move on to the next
        # subalgebra
        if len(carrier_set_left & carrier_set_right) > 0:
            continue

        # See if for all pairs in the subalgebras, that
        # implication is falsified
        falsified = True
        for (x2, y2) in product(carrier_set_left, carrier_set_right):
            if impfunction(x2, y2) in model.designated_values:
                falsified = False
                break

        if falsified:
            return VSP_Result(True, model.name, carrier_set_left, carrier_set_right)

    return VSP_Result(False, model.name)
