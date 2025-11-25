from itertools import product
from typing import Dict, Generator, Optional, Tuple

from logic import Logic, Operation, Rule, PropositionalVariable, Term, OpTerm, get_prop_vars_from_rule
from model import Model, ModelValue, ModelFunction

from z3 import EnumSort, Function, BoolSort, z3, And, Implies, Solver, sat, Context

# TODO: Add an assumption that a partial order exists over the carrier set.
# This adds three restrictions to the logic
# 1) A -> A is always designated
# 2) If A -> B is designated and B -> C is designated then A -> C is designated
# 3) If A -> B is designated and B -> A is designated then A and B share the same truth value

def term_to_smt(t: Term, op_mapping: Dict[Operation, z3.FuncDeclRef], var_mapping: Dict[PropositionalVariable, z3.DatatypeRef]) -> z3.DatatypeRef:
    if isinstance(t, PropositionalVariable):
        return var_mapping[t]

    assert isinstance(t, OpTerm)

    arguments = [term_to_smt(a, op_mapping, var_mapping) for a in t.arguments]
    fn = op_mapping[t.operation]

    return fn(*arguments)


def logic_rule_to_smt_constraints(rule: Rule, IsDesignated: z3.FuncDeclRef, smt_carrier_set, op_mapping: Dict[Operation, z3.FuncDeclRef]) -> Generator[z3.BoolRef, None, None]:
    prop_vars = get_prop_vars_from_rule(rule)

    for smt_vars in product(smt_carrier_set, repeat=len(prop_vars)):
        assert len(prop_vars) == len(smt_vars)

        var_mapping = {
            prop_var : smt_var
            for (prop_var, smt_var) in zip(prop_vars, smt_vars)
        }

        premises = [IsDesignated(term_to_smt(premise, op_mapping, var_mapping)) == True for premise in rule.premises]
        conclusion = IsDesignated(term_to_smt(rule.conclusion, op_mapping, var_mapping)) == True

        if len(premises) == 0:
            yield conclusion
        else:
            premise = premises[0]
            for p in premises[1:]:
                premise = And(premise, p)

            yield Implies(premise, conclusion)


def find_model(l: Logic, size: int) -> Optional[Model]:
    assert size > 0

    ctx = Context()
    solver = Solver(ctx=ctx)

    element_names = [f'{i}' for i in range(size)]
    Carrier_sort, smt_carrier_set = EnumSort("C", element_names, ctx=ctx)

    operation_function_map: Dict[Operation, z3.FuncDeclRef] = {}

    for operation in l.operations:
        operation_function_map[operation] = Function(
            operation.symbol,
            *(Carrier_sort for _ in range(operation.arity + 1))
        )

    IsDesignated = Function("D", Carrier_sort, BoolSort(ctx=ctx))

    for rule in l.rules:
        for constraint in logic_rule_to_smt_constraints(rule, IsDesignated, smt_carrier_set, operation_function_map):
            solver.add(constraint)

    smt_result = solver.check()

    if smt_result == sat:
        smt_model = solver.model()

        carrier_set = {ModelValue(f"{i}") for i in range(size)}

        smt_designated = [x for x in smt_carrier_set if smt_model.evaluate(IsDesignated(x))]
        designated_values = {ModelValue(str(x)) for x in smt_designated}

        model_functions = set()
        for (operation, smt_function) in operation_function_map.items():
            mapping: Dict[Tuple[ModelValue], ModelValue] = {}
            for smt_inputs in product(smt_carrier_set, repeat=operation.arity):
                model_inputs = tuple((ModelValue(str(i)) for i in smt_inputs))
                smt_output = smt_model.evaluate(smt_function(*smt_inputs))
                model_output = ModelValue(str(smt_output))
                mapping[model_inputs] = model_output
            model_functions.add(ModelFunction(operation.arity, mapping, operation.symbol, ))

        solver.reset()
        del ctx

        return Model(carrier_set, model_functions, designated_values)


    else:
        return None
