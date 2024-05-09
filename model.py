"""
Defining what it means to be a model
"""
from common import set_to_str
from logic import (
PropositionalVariable, get_propostional_variables, Logic, Term,
Operation, Conjunction, Disjunction, Implication
)
from typing import Set, Dict, Tuple, Optional
from functools import lru_cache
from itertools import combinations, chain, product
from copy import deepcopy


__all__ = ['ModelValue', 'ModelFunction', 'Model']



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
    def __lt__(self, other):
        assert isinstance(other, ModelValue)
        return ModelOrderConstraint(self, other)


class ModelFunction:
    def __init__(self, arity: int, mapping, operation_name = ""):
        self.operation_name = operation_name
        self.arity = arity

        # Correct input to always be a tuple
        corrected_mapping = dict()
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

    # def __eq__(self, other):
    #     return isinstance(other, ModelFunction) and self.name == other.name and self.arity == other.arity

class ModelOrderConstraint:
    # a < b
    def __init__(self, a: ModelValue, b: ModelValue):
        self.a = a
        self.b = b
    def __hash__(self):
        return hash(self.a) * hash(self.b)
    def __eq__(self, other):
        return isinstance(other, ModelOrderConstraint) and \
            self.a == other.a and self.b == other.b

class Model:
    def __init__(
            self,
            carrier_set: Set[ModelValue],
            logical_operations: Set[ModelFunction],
            designated_values: Set[ModelValue],
            ordering: Optional[Set[ModelOrderConstraint]] = None
    ):
        assert designated_values <= carrier_set
        self.carrier_set = carrier_set
        self.logical_operations = logical_operations
        self.designated_values = designated_values
        self.ordering = ordering  if ordering is not None else set()
        # TODO: Make sure ordering is "valid"
        # That is: transitive, etc.

    def __str__(self):
        result = f"""Carrier Set: {set_to_str(self.carrier_set)}
Designated Values: {set_to_str(self.designated_values)}
"""
        for function in self.logical_operations:
            result += f"{str(function)}\n"

        return result


def evaluate_term(t: Term, f: Dict[PropositionalVariable, ModelValue], interpretation: Dict[Operation, ModelFunction]) -> ModelValue:
    if isinstance(t, PropositionalVariable):
        return f[t]

    model_function = interpretation[t.operation]
    model_arguments = []
    for logic_arg in t.arguments:
        model_arg = evaluate_term(logic_arg, f, interpretation)
        model_arguments.append(model_arg)

    return model_function(*model_arguments)

def all_model_valuations(
        pvars: Tuple[PropositionalVariable],
        mvalues: Tuple[ModelValue]):

    all_possible_values = product(mvalues, repeat=len(pvars))

    for valuation in all_possible_values:
        mapping: Dict[PropositionalVariable, ModelValue] = dict()
        assert len(pvars) == len(valuation)
        for pvar, value in zip(pvars, valuation):
            mapping[pvar] = value
        yield mapping

@lru_cache
def all_model_valuations_cached(
        pvars: Tuple[PropositionalVariable],
        mvalues: Tuple[ModelValue]):
    return list(all_model_valuations(pvars, mvalues))

def rule_ordering_satisfied(model: Model, interpretation: Dict[Operation, ModelFunction]) -> bool:
    """
    Currently testing whether this function helps with runtime...
    """
    if Conjunction in interpretation:
        possible_inputs = ((a, b) for (a, b) in product(model.carrier_set, model.carrier_set))
        for a, b in possible_inputs:
            output = interpretation[Conjunction](a, b)
            if a < b in model.ordering and output != a:
                print("RETURNING FALSE")
                return False
            if b < a in model.ordering and output != b:
                print("RETURNING FALSE")
                return False

    if Disjunction in interpretation:
        possible_inputs = ((a, b) for (a, b) in product(model.carrier_set, model.carrier_set))
        for a, b in possible_inputs:
            output = interpretation[Disjunction](a, b)
            if a < b in model.ordering and output != b:
                print("RETURNING FALSE")
                return False
            if b < a in model.ordering and output != a:
                print("RETURNING FALSE")
                return False

    return True



def satisfiable(logic: Logic, model: Model, interpretation: Dict[Operation, ModelFunction]) -> bool:
    pvars = tuple(get_propostional_variables(tuple(logic.rules)))
    mappings = all_model_valuations_cached(pvars, tuple(model.carrier_set))

    # NOTE: Does not look like rule ordering is helping for finding
    # models of R...
    if not rule_ordering_satisfied(model, interpretation):
        return False

    for mapping in mappings:
        for rule in logic.rules:
            premise_met = True
            premise_ts = set()
            for premise in rule.premises:
                premise_t = evaluate_term(premise, mapping, interpretation)
                if premise_t not in model.designated_values:
                    premise_met = False
                    break
                premise_ts.add(premise_t)

            if not premise_met:
                continue

            consequent_t = evaluate_term(rule.conclusion, mapping, interpretation)

            if consequent_t not in model.designated_values:
                return False

    return True


def model_closure(initial_set: Set[ModelValue], mfunctions: Set[ModelFunction]):
    last_set: Set[ModelValue] = set()
    current_set: Set[ModelValue] = initial_set

    while last_set != current_set:
        last_set = deepcopy(current_set)

        for mfun in mfunctions:
            # Get output for every possible input configuration
            # from last_set
            for args in product(last_set, repeat=mfun.arity):
                current_set.add(mfun(*args))

    return current_set

def has_vsp(model: Model, interpretation: Dict[Operation, ModelFunction]) -> bool:
    """
    Tells you whether a model violates the
    variable sharing property.
    """

    impfunction = interpretation[Implication]

    # Compute I the set of tuples (x, y) where
    # x -> y does not take a designiated value
    I: Set[Tuple[ModelValue, ModelValue]] = set()

    for (x, y) in product(model.carrier_set, model.carrier_set):
        if impfunction(x, y) not in model.designated_values:
            I.add((x, y))

    # Construct the powerset without the empty set
    s = list(I)
    I_power = chain.from_iterable(combinations(s, r) for r in range(1, len(s) + 1))
    # ((x1, y1)), ((x1, y1), (x2, y2)), ...

    for xys in I_power:
        # Compute the closure of all operations
        # with just the xs
        xs = {xy[0] for xy in xys}
        carrier_set_left: Set[ModelValue] = model_closure(xs, model.logical_operations)

        # Compute the closure of all operations
        # with just the ys
        ys = {xy[1] for xy in xys}
        carrier_set_right: Set[ModelValue] = model_closure(ys, model.logical_operations)

        # If the carrier set intersects, then we violate VSP
        if len(carrier_set_left & carrier_set_right) > 0:
            continue

        invalid = False
        for (x2, y2) in product(carrier_set_left, carrier_set_right):
            if impfunction(x2, y2) in model.designated_values:
                invalid = True
                break
        
        if not invalid:
            return True

    return False

