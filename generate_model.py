"""
File which generates all the models
"""
from common import set_to_str
from logic import Logic, Operation, Rule, get_operations_from_term, PropositionalVariable
from model import ModelValue, Model, satisfiable, ModelFunction
from itertools import combinations, chain, product
from typing import Set

def possible_designations(iterable):
    """Powerset without the empty and complete set"""
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s)))

def possible_functions(operation, carrier_set):
    arity = operation.arity

    inputs = list(product(*(carrier_set for _ in range(arity))))
    possible_outputs = product(*(carrier_set for _ in range(len(inputs))))
    for outputs in possible_outputs:
        assert len(inputs) == len(outputs)
        new_function = dict()
        for input, output in zip(inputs, outputs):
            new_function[input] = output
        
        yield ModelFunction(new_function, operation.symbol)


def only_rules_with(rules: Set[Rule], operation: Operation) -> Set[Rule]:
    result_rules = []
    for rule in rules:
        is_valid = True
        for t in (rule.premises | {rule.conclusion,}):
            t_operations = get_operations_from_term(t)
            if len(t_operations) > 1:
                is_valid = False
                break
            if len(t_operations) == 0:
                continue
            t_operation = next(iter(t_operations))
            if t_operation != operation:
                is_valid = False
                break
        if is_valid:
            result_rules.append(rule)
    return result_rules



def possible_interpretations(
        logic: Logic, carrier_set: Set[ModelValue],
        designated_values: Set[ModelValue]):
    operations = []
    model_functions = []

    for operation in logic.operations:
        operations.append(operation)
        candidate_functions = list(possible_functions(operation, carrier_set))
        passed_functions = []
        """
        Only consider functions that at least pass
        in the rules with the operation by itself.
        """
        restricted_rules = only_rules_with(logic.rules, operation)
        if len(restricted_rules) > 0:
            small_logic = Logic({operation,}, restricted_rules)
            for f in candidate_functions:
                small_model = Model(carrier_set, {f,}, designated_values)
                interp = {operation: f}
                if satisfiable(small_logic, small_model, interp):
                    passed_functions.append(f)
        else:
            passed_functions = candidate_functions
        if len(passed_functions) == 0:
            raise Exception("No interpretation satisfies the axioms for the operation " + str(operation))
        else:
            print(
                  f"Operation {operation.symbol} has {len(passed_functions)} candidate functions"
            )
        model_functions.append(passed_functions)

    functions_choice = product(*model_functions)
    for functions in functions_choice:
        assert len(operations) == len(functions)
        interpretation = dict()
        for operation, function in zip(operations, functions):
            interpretation[operation] = function
        yield interpretation

def generate_model(logic: Logic, number_elements: int, num_solutions: int = -1, print_model=False):
    carrier_set = {
        ModelValue("a" + str(i)) for i in range(number_elements)
    }

    possible_designated_values = possible_designations(carrier_set)

    satisfied_models = []
    for designated_values in possible_designated_values:
        designated_values = set(designated_values)
        print("Considering models for designated values", set_to_str(designated_values))
        possible_interps = possible_interpretations(logic, carrier_set, designated_values)

        for interpretation in possible_interps:
            is_valid = True
            model = Model(carrier_set, set(interpretation.values()), designated_values)
            # Iteratively test possible interpretations
            # by adding one axiom at a time
            for rule in logic.rules:
                small_logic = Logic(logic.operations, {rule,})
                if not satisfiable(small_logic, model, interpretation):
                    is_valid = False
                    break
            
            if is_valid:
                satisfied_models.append(model)
                if print_model:
                    print(model, flush=True)
            
            if num_solutions >= 0 and len(satisfied_models) >= num_solutions:
                return satisfied_models

    return satisfied_models
