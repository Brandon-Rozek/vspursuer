"""
Check to see if the model has the variable
sharing property.
"""
from itertools import chain, combinations, product
from typing import Dict, Set, Tuple, List
from model import (
    Model, ModelFunction, ModelValue, model_closure
)
from logic import Implication, Operation

def preseed(initial_set: Set[ModelValue], cache:List[Tuple[Set[ModelValue], Set[ModelValue]]]):
    """
    Cache contains caches of model closure calls:
    Ex:
    {1, 2, 3} -> {....}

    If {1,2,3} is a subset of initial set,
    then {....} is the subset of the output of model_closure.

    We'll use the output to speed up the saturation procedure
    """
    candidate_preseed: Tuple[Set[ModelValue], int] = (None, None)

    for i, o in cache:
        if i < initial_set:
            cost = len(initial_set - i)
            if candidate_preseed[1] is None or cost < candidate_preseed[1]:
                candidate_preseed = o, cost

    same_set = candidate_preseed[1] == 0
    return candidate_preseed[0], same_set

def has_vsp(model: Model, interpretation: Dict[Operation, ModelFunction]) -> bool:
    """
    Tells you whether a model has the
    variable sharing property.
    """

    impfunction = interpretation[Implication]

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
        # If the carrier set intersects, then move on to the next
        # subalgebra
        if len(xs & ys) > 0:
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
            return True

    return False
