"""
Defining what it means to be a model
"""
from common import set_to_str
from logic import (
PropositionalVariable, get_propostional_variables, Logic, Term,
Operation
)
from typing import Set, List, Dict, Tuple, Optional
from itertools import product
from functools import lru_cache

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
    def __init__(self, mapping, operation_name = ""):
        self.operation_name = operation_name

        # Correct input to always be a tuple
        corrected_mapping = dict()
        for k, v in mapping.items():
            if isinstance(k, tuple):
                corrected_mapping[k] = v
            elif isinstance(k, list):
                corrected_mapping[tuple(k)] = v
            else: # Assume it's atomic
                corrected_mapping[(k,)] = v

        self.mapping = corrected_mapping

    def __str__(self):
        str_dict = dict()
        for k, v in self.mapping.items():
            inputstr = "(" + ", ".join(str(ki) for ki in k) + ")"
            str_dict[inputstr] = str(v)
        return str(str_dict)

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

    possible_valuations = [mvalues for _ in pvars]
    all_possible_values = product(*possible_valuations)

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

def satisfiable(logic: Logic, model: Model, interpretation: Dict[Operation, ModelFunction]) -> bool:
    pvars = tuple(get_propostional_variables(tuple(logic.rules)))
    mappings = all_model_valuations_cached(pvars, tuple(model.carrier_set))

    """
    TODO: Make sure that ordering for conjunction and disjunction
    at the model function level.
    """

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

            # Make sure ordering constraint is met
            for premise_t in premise_ts:
                if consequent_t < premise_t in model.ordering:
                    return False

    return True
