from itertools import product
from typing import Dict, Generator, Optional, Tuple

from logic import Logic, Operation, Rule, PropositionalVariable, Term, OpTerm, get_prop_vars_from_rule
from model import Model, ModelValue, ModelFunction

from z3 import (
    And, BoolSort, Context, EnumSort, Function, Implies, Or, sat, Solver, z3
)

def term_to_smt(
    t: Term,
    op_mapping: Dict[Operation, z3.FuncDeclRef],
    var_mapping: Dict[PropositionalVariable, z3.DatatypeRef]
) -> z3.DatatypeRef:
    """Convert a logic term to its SMT representation."""
    if isinstance(t, PropositionalVariable):
        return var_mapping[t]

    assert isinstance(t, OpTerm)

    arguments = [term_to_smt(arg, op_mapping, var_mapping) for arg in t.arguments]
    fn = op_mapping[t.operation]

    return fn(*arguments)

def logic_rule_to_smt_constraints(
    rule: Rule,
    IsDesignated: z3.FuncDeclRef,
    smt_carrier_set,
    op_mapping: Dict[Operation, z3.FuncDeclRef]
) -> Generator[z3.BoolRef, None, None]:
    """
    Encode a logic rule as SMT constraints.

    For all valuations: if premises are designated, then conclusion is designated.
    """
    prop_vars = get_prop_vars_from_rule(rule)

    # Requires that the rule holds under all valuations
    for smt_vars in product(smt_carrier_set, repeat=len(prop_vars)):
        assert len(prop_vars) == len(smt_vars)

        var_mapping = {
            prop_var: smt_var
            for (prop_var, smt_var) in zip(prop_vars, smt_vars)
        }

        premises = [
            IsDesignated(term_to_smt(premise, op_mapping, var_mapping)) == True
            for premise in rule.premises
        ]
        conclusion = IsDesignated(term_to_smt(rule.conclusion, op_mapping, var_mapping)) == True

        if len(premises) == 0:
            yield conclusion
        else:
            premise = premises[0]
            for p in premises[1:]:
                premise = And(premise, p)

            yield Implies(premise, conclusion)

def logic_falsification_rule_to_smt_constraints(
    rule: Rule,
    IsDesignated: z3.FuncDeclRef,
    smt_carrier_set,
    op_mapping: Dict[Operation, z3.FuncDeclRef]
) -> z3.BoolRef:
    """
    Encode a falsification rule as an SMT constraint.

    There exists at least one valuation where premises are designated
    but conclusion is not designated.
    """
    prop_vars = get_prop_vars_from_rule(rule)

    # Collect all possible counter-examples (valuations that falsify the rule)
    counter_examples = []

    for smt_vars in product(smt_carrier_set, repeat=len(prop_vars)):
        assert len(prop_vars) == len(smt_vars)

        var_mapping = {
            prop_var: smt_var
            for (prop_var, smt_var) in zip(prop_vars, smt_vars)
        }

        premises = [
            IsDesignated(term_to_smt(premise, op_mapping, var_mapping)) == True
            for premise in rule.premises
        ]
        conclusion = IsDesignated(term_to_smt(rule.conclusion, op_mapping, var_mapping)) == False

        if len(premises) == 0:
            counter_examples.append(conclusion)
        else:
            premise = premises[0]
            for p in premises[1:]:
                premise = And(premise, p)

            counter_examples.append(And(premise, conclusion))

    # At least one counter-example must exist (disjunction of all possibilities)
    return Or(counter_examples)


class SMTLogicEncoder:
    """
    Encapsulates the SMT encoding of a logic system with a fixed carrier set size.

    This class handles:
    - Creating the SMT sorts and functions
    - Encoding logic rules as SMT constraints
    - Managing the solver state
    - Converting between Model objects and SMT representations
    """

    def __init__(self, logic: Logic, size: int):
        """
        Initialize the SMT encoding for a logic with given carrier set size.

        Args:
            logic: The logic system to encode
            size: The size of the carrier set
        """
        assert size > 0

        self.logic = logic
        self.size = size

        # Create Z3 context and solver
        self.ctx = Context()
        self.solver = Solver(ctx=self.ctx)

        # Create carrier set
        element_names = [f'{i}' for i in range(size)]
        self.carrier_sort, self.smt_carrier_set = EnumSort("C", element_names, ctx=self.ctx)

        # Create operation functions
        self.operation_function_map: Dict[Operation, z3.FuncDeclRef] = {}
        for operation in logic.operations:
            self.operation_function_map[operation] = Function(
                operation.symbol,
                *(self.carrier_sort for _ in range(operation.arity + 1))
            )

        # Create designation function
        self.is_designated = Function("D", self.carrier_sort, BoolSort(ctx=self.ctx))

        # Add logic rules as constraints
        self._add_logic_constraints()
        self._add_designation_symmetry_constraints()

    def _add_logic_constraints(self):
        """Add all logic rules and falsification rules as SMT constraints."""
        # Add regular rules
        for rule in self.logic.rules:
            for constraint in logic_rule_to_smt_constraints(
                rule,
                self.is_designated,
                self.smt_carrier_set,
                self.operation_function_map
            ):
                self.solver.add(constraint)

        # Add falsification rules
        for falsification_rule in self.logic.falsifies:
            constraint = logic_falsification_rule_to_smt_constraints(
                falsification_rule,
                self.is_designated,
                self.smt_carrier_set,
                self.operation_function_map
            )
            self.solver.add(constraint)

    def extract_model(self, smt_model) -> Model:
        """
        Extract a Model object from an SMT model.

        Args:
            smt_model: The Z3 model to extract from

        Returns:
            A Model object representing the logic model
        """
        carrier_set = {ModelValue(f"{i}") for i in range(self.size)}

        # Extract designated values
        smt_designated = [
            x for x in self.smt_carrier_set
            if smt_model.evaluate(self.is_designated(x))
        ]
        designated_values = {ModelValue(str(x)) for x in smt_designated}

        # Extract operation functions
        model_functions = set()
        for (operation, smt_function) in self.operation_function_map.items():
            mapping: Dict[Tuple[ModelValue], ModelValue] = {}
            for smt_inputs in product(self.smt_carrier_set, repeat=operation.arity):
                model_inputs = tuple(ModelValue(str(i)) for i in smt_inputs)
                smt_output = smt_model.evaluate(smt_function(*smt_inputs))
                model_output = ModelValue(str(smt_output))
                mapping[model_inputs] = model_output
            model_functions.add(ModelFunction(operation.arity, mapping, operation.symbol))

        return Model(carrier_set, model_functions, designated_values)


    def _add_designation_symmetry_constraints(self):
        """
        Add symmetry breaking constraints to avoid isomorphic models.

        Strategy: Enforce a lexicographic ordering on designated values.
        If element i is not designated, then no element j < i can be designated.
        This ensures designated elements are "packed to the right".
        """
        for i in range(1, len(self.smt_carrier_set)):
            elem_i = self.smt_carrier_set[i]
            elem_j = self.smt_carrier_set[i - 1]

            # If i is not designated, then j (which comes before i) cannot be designated
            self.solver.add(
                Implies(
                    self.is_designated(elem_i) == False,
                    self.is_designated(elem_j) == False
                )
            )

    def create_exclusion_constraint(self, model: Model) -> z3.BoolRef:
        """
        Create a constraint that excludes the given model from future solutions.

        Args:
            model: The model to exclude

        Returns:
            An SMT constraint ensuring at least one aspect differs
        """
        constraints = []

        # Create mapping from ModelValue to SMT element
        model_value_to_smt = {
            ModelValue(str(smt_elem)): smt_elem
            for smt_elem in self.smt_carrier_set
        }

        # Exclude operation function mappings
        for model_func in model.logical_operations:
            operation = Operation(model_func.operation_name, model_func.arity)
            smt_func = self.operation_function_map[operation]

            for inputs, output in model_func.mapping.items():
                smt_inputs = tuple(model_value_to_smt[inp] for inp in inputs)
                smt_output = model_value_to_smt[output]

                # This input->output mapping should differ
                constraints.append(smt_func(*smt_inputs) != smt_output)

        # Exclude designated value set
        for smt_elem in self.smt_carrier_set:
            model_val = ModelValue(str(smt_elem))
            is_designated_in_model = model_val in model.designated_values

            # Designation should differ
            if is_designated_in_model:
                constraints.append(self.is_designated(smt_elem) == False)
            else:
                constraints.append(self.is_designated(smt_elem) == True)

        return Or(constraints)

    def find_model(self) -> Optional[Model]:
        """
        Find a single model satisfying the logic constraints.

        Returns:
            A Model if one exists, None otherwise
        """
        if self.solver.check() == sat:
            return self.extract_model(self.solver.model())
        return None

    def reset(self):
        """Reset the solver state."""
        self.solver.reset()

    def __del__(self):
        """Cleanup resources."""
        try:
            self.solver.reset()
            del self.ctx
        except:
            pass


def find_model(logic: Logic, size: int) -> Optional[Model]:
    """Find a single model for the given logic and size."""
    encoder = SMTLogicEncoder(logic, size)
    return encoder.find_model()

def find_all_models(logic: Logic, size: int) -> Generator[Model, None, None]:
    """
    Find all models for the given logic and size.

    Args:
        logic: The logic system to encode
        size: The size of the carrier set

    Yields:
        Model instances that satisfy the logic
    """
    encoder = SMTLogicEncoder(logic, size)

    while True:
        # Try to find a model
        model = encoder.find_model()
        if model is None:
            break

        yield model

        # Add constraint to exclude this model from future solutions
        exclusion_constraint = encoder.create_exclusion_constraint(model)
        encoder.solver.add(exclusion_constraint)