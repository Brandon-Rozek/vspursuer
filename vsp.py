"""
Check to see if the model has the variable
sharing property.
"""
from collections import defaultdict
from itertools import chain, combinations, product
from typing import List, Optional, Set, Tuple
from common import set_to_str
from model import (
    Model, model_closure, ModelFunction, ModelValue, OrderTable
)

class Cache:
    def __init__(self):
        # input size -> cached (inputs, outputs)
        self.c = defaultdict(list)

    def add(self, i: Set[ModelValue], o: Set[ModelValue]):
        self.c[len(i)].append((i, o))

    def get_closest(self, initial_set: Set[ModelValue]) -> Optional[Tuple[Set[ModelValue], bool]]:
        """
        Iterate through our cache starting with the cached
        inputs closest in size to the initial_set and
        find the one that's a subset of initial_set.

        Returns cached_output, and whether the initial_set is the same
        as the cached_input.
        """
        initial_set_size = len(initial_set)
        sizes = range(initial_set_size, 0, -1)

        for size in sizes:
            if size not in self.c:
                continue

            for cached_input, cached_output in self.c[size]:
                if cached_input <= initial_set:
                    return cached_output, size == initial_set_size

        return None

def order_dependent(subalgebra1: Set[ModelValue], subalegbra2: Set[ModelValue], ordering: OrderTable):
    """
    Returns true if there exists a value in subalgebra1 that's less than a value in subalgebra2
    """
    for x in subalgebra1:
        for y in subalegbra2:
            if ordering.is_lt(x, y):
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

def quick_vsp_unsat_incomplete(xs, ys, model, top, bottom, negation_defined) -> bool:
    """
    Return True if VSP cannot be satisfied
    through some incomplete checks.
    """
    # If the left subalgebra contains bottom
    # or the right subalgebra contains top
    # skip this pair
    if top is not None and top in ys:
        return True
    if negation_defined and bottom is not None and bottom in ys:
        return True
    if bottom is not None and bottom in xs:
        return True
    if negation_defined and top is not None and top in xs:
        return True

    # If the two subalgebras intersect, move
    # onto the next pair.
    if not xs.isdisjoint(ys):
        return True

    # If the subalgebras are order-dependent, skip this pair
    if order_dependent(xs, ys, model.ordering):
        return True
    if negation_defined and order_dependent(ys, xs, model.ordering):
        return True

    # We can't immediately rule out that these
    # subalgebras don't exhibit VSP
    return False

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

    for (x, y) in product(model.carrier_set, model.carrier_set):
        if impfunction(x, y) not in model.designated_values:
            I.append((x, y))

    # Construct the powerset of I without the empty set
    I_power = chain.from_iterable(combinations(I, r) for r in range(1, len(I) + 1))
    # ((x1, y1)), ((x1, y1), (x2, y2)), ...

    closure_cache = Cache()

    # Find the subalgebras which falsify implication
    for xys in I_power:

        xs = { xy[0] for xy in xys }
        ys = { xy[1] for xy in xys }

        if quick_vsp_unsat_incomplete(xs, ys, model, top, bottom, negation_defined):
            continue

        orig_xs = xs
        cached_xs = closure_cache.get_closest(xs)
        if cached_xs is not None:
            xs |= cached_xs[0]

        orig_ys = ys
        cached_ys = closure_cache.get_closest(ys)
        if cached_ys is not None:
            ys |= cached_ys[0]

        xs_ys_updated = cached_xs is not None or cached_ys is not None
        if xs_ys_updated and quick_vsp_unsat_incomplete(xs, ys, model, top, bottom, negation_defined):
            continue

        # Compute the closure of all operations
        # with just the xs
        carrier_set_left: Set[ModelValue] = model_closure(xs, model.logical_operations, bottom)

        # Save to cache
        if cached_xs is None or (cached_xs is not None and not cached_xs[1]):
            closure_cache.add(orig_xs, carrier_set_left)

        if bottom is not None and bottom in carrier_set_left:
            continue

        # Compute the closure of all operations
        # with just the ys
        carrier_set_right: Set[ModelValue] = model_closure(ys, model.logical_operations, top)

        # Save to cache
        if cached_ys is None or (cached_ys is not None and not cached_ys[1]):
            closure_cache.add(orig_ys, carrier_set_right)

        if top is not None and top in carrier_set_right:
            continue

        # If the carrier set intersects, then move on to the next
        # subalgebra
        if not carrier_set_left.isdisjoint(carrier_set_right):
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
