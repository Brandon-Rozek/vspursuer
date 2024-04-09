"""
Defining what it means to be a model
"""
from logic import (
PropositionalVariable, get_propostional_variables, Logic, Term,
Operation
) 
from typing import Set, List, Dict
from itertools import product

__all__ = ['ModelValue', 'ModelFunction', 'Model']


def set_to_str(x):
    return "{" + ", ".join((str(xi) for xi in x)) + "}"

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

class Model:
    def __init__(
            self,
            carrier_set: Set[ModelValue],
            logical_operations: Set[ModelFunction],
            designated_values: Set[ModelValue]
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


def evaluate_term(t: Term, f: Dict[PropositionalVariable, ModelValue], interpretation: Dict[Operation, ModelFunction]):
    if isinstance(t, PropositionalVariable):
        return f[t]

    model_function = interpretation[t.operation]
    model_arguments = []
    for logic_arg in t.arguments:
        model_arg = evaluate_term(logic_arg, f, interpretation)
        model_arguments.append(model_arg)
    
    return model_function(*model_arguments)

def all_model_valuations(
        pvars: Set[PropositionalVariable],
        mvalues: Set[ModelValue]):
    
    pvars = list(pvars)
    possible_valuations = [mvalues for _ in pvars]
    all_possible_values = product(*possible_valuations)

    for valuation in all_possible_values:
        mapping = dict()
        assert len(pvars) == len(valuation)
        for pvar, value in zip(pvars, valuation):
            mapping[pvar] = value
        yield mapping
    

def satisfiable(logic: Logic, model: Model, interpretation: Dict[Operation, ModelFunction]):
    pvars = get_propostional_variables(logic.rules)
    mappings = all_model_valuations(pvars, model.carrier_set)

    for mapping in mappings:
        for rule in logic.rules:
            premise_met = True
            for premise in rule.premises:
                t = evaluate_term(premise, mapping, interpretation)
                if t not in model.designated_values:
                    premise_met = False
                    break
            if not premise_met:
                continue
            
            t = evaluate_term(rule.conclusion, mapping, interpretation)
            if t not in model.designated_values:
                return False
    
    return True
