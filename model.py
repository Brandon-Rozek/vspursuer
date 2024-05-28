"""
Matrix model semantics and satisfiability of
a given logic.
"""
from common import set_to_str
from logic import (
    get_propostional_variables, Logic,
    Operation, PropositionalVariable, Term
)
from collections import defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement, permutations, product
from typing import Dict, List, Set, Tuple


__all__ = ['ModelValue', 'ModelFunction', 'Model', 'Interpretation']


class ModelValue:
    def __init__(self, name):
        self.name = name
        self.hashed_value = hash(self.name)
        def immutable(self, name, value):
            raise Exception("Model values are immutable")
        self.__setattr__ = immutable
    def __str__(self):
        return self.name
    def __hash__(self):
        return self.hashed_value
    def __eq__(self, other):
        return isinstance(other, ModelValue) and self.name == other.name
    def __deepcopy__(self, _):
        return ModelValue(self.name)


class ModelFunction:
    def __init__(self, arity: int, mapping, operation_name = ""):
        self.operation_name = operation_name
        self.arity = arity

        # Transform the mapping such that the
        # key is always a tuple of model values
        corrected_mapping: Dict[Tuple[ModelValue], ModelValue] = {}
        for k, v in mapping.items():
            if isinstance(k, tuple):
                assert len(k) == arity
                corrected_mapping[k] = v
            elif isinstance(k, list):
                assert len(k) == arity
                corrected_mapping[tuple(k)] = v
            else: # Assume it's atomic
                assert arity == 1
                corrected_mapping[(k,)] = v

        self.mapping = corrected_mapping

    def __str__(self):
        str_dict = dict()
        for k, v in self.mapping.items():
            inputstr = "(" + ", ".join(str(ki) for ki in k) + ")"
            str_dict[inputstr] = str(v)
        return self.operation_name + " " + str(str_dict)

    def __call__(self, *args):
        return self.mapping[args]

Interpretation = Dict[Operation, ModelFunction]

class Model:
    def __init__(
            self,
            carrier_set: Set[ModelValue],
            logical_operations: Set[ModelFunction],
            designated_values: Set[ModelValue],
    ):
        assert designated_values <= carrier_set
        self.carrier_set = carrier_set
        self.logical_operations = logical_operations
        self.designated_values = designated_values

    def __str__(self):
        result = f"""Carrier Set: {set_to_str(self.carrier_set)}
Designated Values: {set_to_str(self.designated_values)}
"""
        for function in self.logical_operations:
            result += f"{str(function)}\n"

        return result


def evaluate_term(
        t: Term, f: Dict[PropositionalVariable, ModelValue],
        interpretation: Dict[Operation, ModelFunction]) -> ModelValue:
    """
    Given a term in a logic, mapping
    between terms and model values,
    as well as an interpretation
    of operations to model functions,
    return the evaluated model value.
    """

    if isinstance(t, PropositionalVariable):
        return f[t]

    model_function = interpretation[t.operation]
    model_arguments: List[ModelValue] = []
    for logic_arg in t.arguments:
        model_arg = evaluate_term(logic_arg, f, interpretation)
        model_arguments.append(model_arg)

    return model_function(*model_arguments)

def all_model_valuations(
        pvars: Tuple[PropositionalVariable],
        mvalues: Tuple[ModelValue]):
    """
    Given propositional variables and model values,
    produce every possible mapping between the two.
    """

    all_possible_values = product(mvalues, repeat=len(pvars))

    for valuation in all_possible_values:
        mapping: Dict[PropositionalVariable, ModelValue] = {}
        assert len(pvars) == len(valuation)
        for pvar, value in zip(pvars, valuation):
            mapping[pvar] = value
        yield mapping

@lru_cache
def all_model_valuations_cached(
        pvars: Tuple[PropositionalVariable],
        mvalues: Tuple[ModelValue]):
    return list(all_model_valuations(pvars, mvalues))


def satisfiable(logic: Logic, model: Model, interpretation: Dict[Operation, ModelFunction]) -> bool:
    """
    Determine whether a model satisfies a logic
    given an interpretation.
    """
    pvars = tuple(get_propostional_variables(tuple(logic.rules)))
    mappings = all_model_valuations_cached(pvars, tuple(model.carrier_set))

    for mapping in mappings:
        # Make sure that the model satisfies each of the rules
        for rule in logic.rules:
            # The check only applies if the premises are designated
            premise_met = True
            premise_ts: Set[ModelValue] = set()

            for premise in rule.premises:
                premise_t = evaluate_term(premise, mapping, interpretation)
                # As soon as one premise is not designated,
                # move to the next rule.
                if premise_t not in model.designated_values:
                    premise_met = False
                    break
                # If designated, keep track of the evaluated term
                premise_ts.add(premise_t)

            if not premise_met:
                continue

            # With the premises designated, make sure the consequent is designated
            consequent_t = evaluate_term(rule.conclusion, mapping, interpretation)
            if consequent_t not in model.designated_values:
                return False

    return True



def model_closure(initial_set: Set[ModelValue], mfunctions: Set[ModelFunction]):
    """
    Given an initial set of model values and a set of model functions,
    compute the complete set of model values that are closed
    under the operations.
    """
    closure_set: Set[ModelValue] = initial_set
    last_new: Set[ModelValue] = initial_set
    changed: bool = True

    while changed:
        changed = False
        new_elements: Set[ModelValue] = set()
        old_closure: Set[ModelValue] = closure_set - last_new

        # arity -> args
        cached_args = defaultdict(list)

        # Pass elements into each model function
        for mfun in mfunctions:

            # If a previous function shared the same arity,
            # we'll use the same set of computed arguments
            # to pass into the model functions.
            if mfun.arity in cached_args:
                for args in cached_args[mfun.arity]:
                    # Compute the new elements
                    # given the cached arguments.
                    element = mfun(*args)
                    if element not in closure_set:
                        new_elements.add(element)

                # We don't need to compute the arguments
                # thanks to the cache, so move onto the
                # next function.
                continue

            # At this point, we don't have cached arguments, so we need
            # to compute this set.

            # Each argument must have at least one new element to not repeat
            # work. We'll range over the number of new model values within our
            # argument.
            for num_new in range(1, mfun.arity + 1):
                new_args = combinations_with_replacement(last_new, r=num_new)
                old_args = combinations_with_replacement(old_closure, r=mfun.arity - num_new)
                # Determine every possible ordering of the concatenated
                # new and old model values.
                for new_arg, old_arg in product(new_args, old_args):
                    for args in permutations(new_arg + old_arg):
                        cached_args[mfun.arity].append(args)
                        element = mfun(*args)
                        if element not in closure_set:
                            new_elements.add(element)

        closure_set.update(new_elements)
        changed = len(new_elements) > 0
        last_new = new_elements

    return closure_set
