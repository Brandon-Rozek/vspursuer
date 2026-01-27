from functools import lru_cache
from itertools import product
from typing import Dict, Generator, Optional, Set, Tuple

from logic import Logic, Operation, Rule, PropositionalVariable, Term, OpTerm, get_prop_vars_from_rule
from model import Model, ModelValue, ModelFunction

SMT_LOADED = True
try:
    from z3 import (
        And, BoolSort, Context, EnumSort, Function, Implies, Or, sat, Solver, z3
    )
except ImportError:
    SMT_LOADED = False

def smt_is_loaded() -> bool:
    global SMT_LOADED
    return SMT_LOADED

def term_to_smt(
    t: Term,
    op_mapping: Dict[Operation, "z3.FuncDeclRef"],
    var_mapping: Dict[PropositionalVariable, "z3.DatatypeRef"]
) -> "z3.DatatypeRef":
    """Convert a logic term to its SMT representation."""
    if isinstance(t, PropositionalVariable):
        return var_mapping[t]

    assert isinstance(t, OpTerm)

    # Recursively convert all arguments to SMT
    arguments = [term_to_smt(arg, op_mapping, var_mapping) for arg in t.arguments]
    fn = op_mapping[t.operation]

    return fn(*arguments)

def all_smt_valuations(pvars: Tuple[PropositionalVariable], smtvalues):
    """
    Generator which maps all the propositional variable to
    smt variables representing the carrier set.

    Exhaust the generator to get all such mappings.
    """
    all_possible_values = product(smtvalues, repeat=len(pvars))
    for valuation in all_possible_values:
        mapping = dict()
        assert len(pvars) == len(valuation)
        for pvar, value in zip(pvars, valuation):
            mapping[pvar] = value
        yield mapping


@lru_cache
def all_smt_valuations_cached(pvars: Tuple[PropositionalVariable], smtvalues):
    return list(all_smt_valuations(pvars, smtvalues))

def logic_rule_to_smt_constraints(
    rule: Rule,
    IsDesignated: "z3.FuncDeclRef",
    smt_carrier_set,
    op_mapping: Dict[Operation, "z3.FuncDeclRef"]
) -> Generator["z3.BoolRef", None, None]:
    """
    Encode a logic rule as SMT constraints.

    For all valuations: if premises are designated, then conclusion is designated.
    """
    prop_vars = tuple(get_prop_vars_from_rule(rule))
    valuations = all_smt_valuations_cached(prop_vars, tuple(smt_carrier_set))

    for valuation in valuations:
        premises = [
            IsDesignated(term_to_smt(premise, op_mapping, valuation)) == True
            for premise in rule.premises
        ]
        conclusion = IsDesignated(term_to_smt(rule.conclusion, op_mapping, valuation)) == True

        if len(premises) == 0:
            # If there are no premises, then the conclusion must always be designated
            yield conclusion
        else:
            # Otherwise, combine all the premises with and
            # and have that if the premises are designated
            # then the conclusion is designated
            premise = premises[0]
            for p in premises[1:]:
                premise = And(premise, p)

            yield Implies(premise, conclusion)


def logic_falsification_rule_to_smt_constraints(
    rule: Rule,
    IsDesignated: "z3.FuncDeclRef",
    smt_carrier_set,
    op_mapping: Dict[Operation, "z3.FuncDeclRef"]
) -> "z3.BoolRef":
    """
    Encode a falsification rule as an SMT constraint.

    There exists at least one valuation where premises are designated
    but conclusion is not designated.
    """
    prop_vars = tuple(get_prop_vars_from_rule(rule))
    valuations = all_smt_valuations_cached(prop_vars, tuple(smt_carrier_set))

    # Collect all possible counter-examples (valuations that falsify the rule)
    counter_examples = []

    for valuation in valuations:
        # The rule is falsified when all of our premises
        # are designated but our conclusion is not designated

        premises = [
            IsDesignated(term_to_smt(premise, op_mapping, valuation)) == True
            for premise in rule.premises
        ]

        conclusion = IsDesignated(term_to_smt(rule.conclusion, op_mapping, valuation)) == False

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
        self.operation_function_map: Dict[Operation, "z3.FuncDeclRef"] = {}
        for operation in logic.operations:
            self.operation_function_map[operation] = self.create_function(operation.symbol, operation.arity)

        # Create designation function
        self.is_designated = self.create_predicate("D", 1)

        # Add logic rules as constraints
        self._add_logic_constraints()
        self._add_designation_symmetry_constraints()

    def create_predicate(self, name: str, arity: int) -> "z3.FuncDeclRef":
        return Function(name, *(self.carrier_sort for _ in range(arity)), BoolSort(ctx=self.ctx))

    def create_function(self, name: str, arity: int) -> "z3.FuncDeclRef":
        return Function(name, *(self.carrier_sort for _ in range(arity + 1)))

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

    def extract_model(self, smt_model) -> Tuple[Model, Dict[Operation, ModelFunction]]:
        """
        Extract a Model object and interpretation from an SMT model.
        """
        carrier_set = {ModelValue(f"{i}") for i in range(self.size)}

        # Extract designated values
        smt_designated = [
            x for x in self.smt_carrier_set
            if smt_model.evaluate(self.is_designated(x))
        ]
        designated_values = {ModelValue(str(x)) for x in smt_designated}

        # Extract operation functions
        model_functions: Set[ModelFunction] = set()
        interpretation: Dict[Operation, ModelFunction] = dict()
        for (operation, smt_function) in self.operation_function_map.items():
            mapping: Dict[Tuple[ModelValue], ModelValue] = {}
            for smt_inputs in product(self.smt_carrier_set, repeat=operation.arity):
                model_inputs = tuple(ModelValue(str(i)) for i in smt_inputs)
                smt_output = smt_model.evaluate(smt_function(*smt_inputs))
                model_output = ModelValue(str(smt_output))
                mapping[model_inputs] = model_output
            model_function = ModelFunction(operation.arity, mapping, operation.symbol)
            model_functions.add(model_function)
            interpretation[operation] = model_function


        return Model(carrier_set, model_functions, designated_values), interpretation


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

    def create_exclusion_constraint(self, model: Model) -> "z3.BoolRef":
        """
        Create a constraint that excludes the given model from future solutions.
        """
        constraints = []

        # Create mapping from ModelValue to SMT element
        model_value_to_smt = {
            ModelValue(str(smt_elem)): smt_elem
            for smt_elem in self.smt_carrier_set
        }

        # Iterate over all logical operations
        for model_func in model.logical_operations:
            operation = Operation(model_func.operation_name, model_func.arity)
            smt_func = self.operation_function_map[operation]

            for inputs, output in model_func.mapping.items():
                smt_inputs = tuple(model_value_to_smt[inp] for inp in inputs)
                smt_output = model_value_to_smt[output]

                # It may be the case that the output of f(input) differs
                constraints.append(smt_func(*smt_inputs) != smt_output)

        for smt_elem in self.smt_carrier_set:
            model_val = ModelValue(str(smt_elem))
            is_designated_in_model = model_val in model.designated_values

            # Designation may differ
            if is_designated_in_model:
                constraints.append(self.is_designated(smt_elem) == False)
            else:
                constraints.append(self.is_designated(smt_elem) == True)

        return Or(constraints)

    def find_model(self) -> Optional[Tuple[Model, Dict[Operation, ModelFunction]]]:
        """
        Find a single model satisfying the logic constraints.

        Returns:
            A Model if one exists, None otherwise
        """
        if self.solver.check() == sat:
            return self.extract_model(self.solver.model())
        return None

    def __del__(self):
        """Cleanup resources."""
        try:
            self.solver.reset()
            del self.ctx
        except:
            pass


def find_model(logic: Logic, size: int) -> Optional[Tuple[Model, Dict[Operation, ModelFunction]]]:
    """Find a single model for the given logic and size."""
    encoder = SMTLogicEncoder(logic, size)
    return encoder.find_model()

def find_all_models(logic: Logic, size: int) -> Generator[Tuple[Model, Dict[Operation, ModelFunction]], None, None]:
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
        solution = encoder.find_model()
        if solution is None:
            break

        yield solution

        # Add constraint to exclude this model from future solutions
        model, _ = solution
        exclusion_constraint = encoder.create_exclusion_constraint(model)
        encoder.solver.add(exclusion_constraint)

class SMTModelEncoder:
    """
    Creates an SMT encoding for a specific Model.
    This can be used for checking whether a model satisfies
    various constraints.
    """

    def __init__(self, model: Model):
        self.model = model
        self.size = len(model.carrier_set)

        # Create the Z3 context and solver
        self.ctx = Context()
        self.solver = Solver(ctx=self.ctx)

        # Encode model values
        model_value_names = [model_value.name for model_value in model.carrier_set]
        self.carrier_sort, self.smt_carrier_set = EnumSort(
            "C", model_value_names, ctx=self.ctx
        )

        # Create mapping from ModelValue to SMT element
        self.model_value_to_smt = {
            ModelValue(str(smt_elem)): smt_elem
            for smt_elem in self.smt_carrier_set
        }

        # Encode model functions
        self.model_function_map: Dict[ModelFunction, z3.FuncDeclRel] = {}
        for model_fn in model.logical_operations:
            smt_fn = self.create_function(model_fn.operation_name, model_fn.arity)
            self.model_function_map[model_fn] = smt_fn
            self.add_function_constraints_from_table(smt_fn, model_fn)


        # Encode designated values
        self.is_designated = self.create_predicate("D", 1)

        for model_value in model.carrier_set:
            is_designated = model_value in model.designated_values
            self.solver.add(self.is_designated(self.model_value_to_smt[model_value]) == is_designated)

    def create_predicate(self, name: str, arity: int) -> "z3.FuncDeclRef":
        return Function(name, *(self.carrier_sort for _ in range(arity)), BoolSort(ctx=self.ctx))

    def create_function(self, name: str, arity: int) -> "z3.FuncDeclRef":
        return Function(name, *(self.carrier_sort for _ in range(arity + 1)))

    def add_function_constraints_from_table(self, smt_fn: "z3.FuncDeclRef", model_fn: ModelFunction):
        for inputs, output in model_fn.mapping.items():
            smt_inputs = tuple(self.model_value_to_smt[inp] for inp in inputs)
            smt_output = self.model_value_to_smt[output]
            self.solver.add(smt_fn(*smt_inputs) == smt_output)

    def __del__(self):
        """Cleanup resources."""
        try:
            self.solver.reset()
            del self.ctx
        except:
            pass