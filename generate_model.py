"""
Generate all the models for a given logic
with a specified number of elements.
"""
from common import set_to_str
from logic import Logic, Operation, Rule, get_operations_from_term
from model import (
    Interpretation, ModelValue, Model,
    satisfiable, ModelFunction
)
from itertools import combinations, chain, product
from typing import Set, List, Dict, Tuple

def possible_designations(iterable):
    """Powerset without the empty and complete set"""
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s)))

def possible_functions(operation, carrier_set):
    """
    Create every possible input, output pair
    for a given model function based on an
    operation and a carrier set.
    """
    arity = operation.arity

    inputs = list(product(carrier_set, repeat=arity))
    possible_outputs = product(carrier_set, repeat=len(inputs))
    for outputs in possible_outputs:
        assert len(inputs) == len(outputs)
        new_function = dict()
        for input, output in zip(inputs, outputs):
            new_function[input] = output

        yield ModelFunction(arity, new_function, operation.symbol)


def only_rules_with(rules: Set[Rule], operation: Operation) -> List[Rule]:
    """
    Filter the list of rules in a logic to those
    that only contain the logical operation specified.
    """
    result_rules: List[Rule] = []
    for rule in rules:
        is_valid = True
        # Go through every term in the premises and conclusion
        for t in (rule.premises | {rule.conclusion,}):
            t_operations = get_operations_from_term(t)
            # Make sure there's only one operation
            # and that it matches the operation specified
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
    """
    Consider every possible interpretation of operations
    within the specified logic given the carrier set of
    model values, and the set of designated values.
    """
    operations: List[Operation] = []
    model_functions: List[List[ModelFunction]] = []

    for operation in logic.operations:
        operations.append(operation)
        candidate_functions = list(possible_functions(operation, carrier_set))
        passed_functions: List[ModelFunction] = []
        """
        Discard candidate functions that don't pass
        the rules that only contain the given
        logical operation.
        """
        restricted_rules = only_rules_with(logic.rules, operation)
        if len(restricted_rules) > 0:
            small_logic = Logic({operation,}, restricted_rules)
            # Add candidate functions whose small model
            # and logic are satisfied given the restricted
            # rule set.
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

    # The model_functions variables contains
    # the candidate functions for each operation.

    functions_choice = product(*model_functions)
    # Assign a function to each operation
    for functions in functions_choice:
        assert len(operations) == len(functions)
        interpretation: Interpretation = dict()
        for operation, function in zip(operations, functions):
            interpretation[operation] = function
        yield interpretation

def generate_model(
        logic: Logic, number_elements: int, num_solutions: int = -1,
        print_model=False) -> List[Tuple[Model, Interpretation]]:
    """
    Generate the specified number of models that
    satisfy a logic of a certain size.
    """
    assert number_elements > 0
    carrier_set = {
        ModelValue("a" + str(i)) for i in range(number_elements)
    }

    possible_designated_values = possible_designations(carrier_set)

    solutions: List[Tuple[Model, Interpretation]] = []

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
                solutions.append((model, interpretation))
                if print_model:
                    print(model, flush=True)

            if num_solutions >= 0 and len(solutions) >= num_solutions:
                return solutions

    return solutions
