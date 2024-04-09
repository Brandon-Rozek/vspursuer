"""
File which generates all the models
"""
from logic import Logic
from model import ModelValue, Model, satisfiable, ModelFunction
from itertools import combinations, chain, product

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

def possible_interpretations(logic, carrier_set):
    operations = []
    model_functions = []

    for operation in logic.operations:
        operations.append(operation)
        model_functions.append(possible_functions(operation, carrier_set))

    functions_choice = product(*model_functions)
    for functions in functions_choice:
        assert len(operations) == len(functions)
        interpretation = dict()
        for operation, function in zip(operations, functions):
            interpretation[operation] = function
        yield interpretation

def generate_model(logic: Logic, number_elements: int):
    carrier_set = {
        ModelValue("a" + str(i)) for i in range(number_elements)
    }

    possible_designated_values = possible_designations(carrier_set)
    possible_interps = possible_interpretations(logic, carrier_set)

    satisfied_models = []
    checked = 0
    for designated_values, interpretation in product(possible_designated_values, possible_interps):
        checked += 1
        designated_values = set(designated_values)
        
        model = Model(carrier_set, set(interpretation.values()), designated_values)
        if satisfiable(logic, model, interpretation):
            satisfied_models.append(model)
            print(model)
        
    print("Checked", checked)
    
    return satisfied_models
