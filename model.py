"""
Matrix model semantics and satisfiability of
a given logic.
"""
from common import set_to_str, immutable
from logic import (
    get_propostional_variables, Logic,
    Operation, PropositionalVariable, Term
)
from collections import defaultdict
from functools import cached_property, lru_cache, reduce
from itertools import (
    chain, combinations_with_replacement,
    permutations, product
)
from typing import Dict, List, Optional, Set, Tuple


__all__ = ['ModelValue', 'ModelFunction', 'Model', 'Interpretation']

class ModelValue:
    def __init__(self, name: str, hashed_value: Optional[int] = None):
        self.name = name
        self.hashed_value = hashed_value if hashed_value is not None else hash(self.name)
        self.__setattr__ = immutable
    def __str__(self):
        return self.name
    def __hash__(self):
        return self.hashed_value
    def __eq__(self, other):
        return isinstance(other, ModelValue) and self.name == other.name
    def __deepcopy__(self, _):
        return ModelValue(self.name, self.hashed_value)

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

    @cached_property
    def domain(self):
        result_set: Set[ModelValue] = set()
        for args in self.mapping.keys():
            for v in args:
                result_set.add(v)
        return result_set

    def __str__(self):
        if self.arity == 1:
            return unary_function_str(self)
        elif self.arity == 2:
            return binary_function_str(self)

        # Default return dictionary representation
        str_dict = dict()
        for k, v in self.mapping.items():
            inputstr = "(" + ", ".join(str(ki) for ki in k) + ")"
            str_dict[inputstr] = str(v)
        return self.operation_name + " " + str(str_dict)

    def __call__(self, *args):
        return self.mapping[args]


def unary_function_str(f: ModelFunction) -> str:
    assert isinstance(f, ModelFunction) and f.arity == 1
    sorted_domain = sorted(f.domain, key=lambda v : v.name)
    header_line = f" {f.operation_name} | " + " ".join((str(v) for v in sorted_domain))
    sep_line = "-" + ("-" * len(f.operation_name)) + "-+-" +\
         ("-" * len(sorted_domain)) +\
         ("-" * reduce(lambda sum, v : sum + len(v.name), sorted_domain, 0))
    data_line = (" " * (len(f.operation_name) + 2)) + "| " + " ".join((str(f.mapping[(v,)]) for v in sorted_domain))
    return "\n".join((header_line, sep_line, data_line)) + "\n"

def binary_function_str(f: ModelFunction) -> str:
    assert isinstance(f, ModelFunction) and f.arity == 2
    sorted_domain = sorted(f.domain, key=lambda v : v.name)
    max_col_width = max(chain((len(v.name) for v in sorted_domain), (len(f.operation_name),)))
    header_line = f" {f.operation_name} " +\
         (" " * (max_col_width - len(f.operation_name))) + "| " +\
         " ".join((str(v) for v in sorted_domain))
    sep_line = "-" + ("-" * max_col_width) + "-+-" +\
         ("-" * len(sorted_domain)) +\
         ("-" * reduce(lambda sum, v : sum + len(v.name), sorted_domain, 0))
    data_lines = ""
    for row_v in sorted_domain:
        data_line = f" {row_v.name} | " + " ".join((str(f.mapping[(row_v, col_v)]) for col_v in sorted_domain))
        data_lines += data_line + "\n"
    return "\n".join((header_line, sep_line, data_lines))

Interpretation = Dict[Operation, ModelFunction]

class OrderTable:
    def __init__(self):
        # a : {x | x <= a }
        self.le_map: Dict[ModelValue, Set[ModelValue]] = defaultdict(set)
        # a : {x | x >= a}
        self.ge_map: Dict[ModelValue, Set[ModelValue]] = defaultdict(set)

    def add(self, x, y):
        """
        Add x <= y
        """
        self.le_map[y].add(x)
        self.ge_map[x].add(y)

    def is_lt(self, x, y):
        return x in self.le_map[y]

    def meet(self, x, y) -> Optional[ModelValue]:
        X = self.le_map[x]
        Y = self.le_map[y]

        candidates = X.intersection(Y)

        # Grab all elements greater than each of the candidates
        candidate_ge_maps = (self.ge_map[candidate] for candidate in candidates)
        common_ge_values = reduce(set.intersection, candidate_ge_maps)

        # Intersect with candidates to get the values that satisfy
        # the meet properties
        result_set = candidates.intersection(common_ge_values)

        # NOTE: The meet may not exist, in which case return None
        result = next(iter(result_set), None)
        return result

    def join(self, x, y) -> Optional[ModelValue]:
        X = self.ge_map[x]
        Y = self.ge_map[y]

        candidates = X.intersection(Y)

        # Grab all elements smaller than each of the candidates
        candidate_le_maps = (self.le_map[candidate] for candidate in candidates)
        common_le_values = reduce(set.intersection, candidate_le_maps)

        # Intersect with candidatse to get the values that satisfy
        # the join properties
        result_set = candidates.intersection(common_le_values)

        # NOTE: The join may not exist, in which case return None
        result = next(iter(result_set), None)
        return result

    def top(self) -> Optional[ModelValue]:
        ge_maps = (self.ge_map[candidate] for candidate in self.ge_map)
        result_set = reduce(set.intersection, ge_maps)

        # Either not unique or does not exist
        if len(result_set) != 1:
            return None

        return next(iter(result_set))

    def bottom(self) -> Optional[ModelValue]:
        le_maps = (self.le_map[candidate] for candidate in self.le_map)
        result_set = reduce(set.intersection, le_maps)

        # Either not unique or does not exist
        if len(result_set) != 1:
            return None

        return next(iter(result_set))


class Model:
    def __init__(
            self,
            carrier_set: Set[ModelValue],
            logical_operations: Set[ModelFunction],
            designated_values: Set[ModelValue],
            ordering: Optional[OrderTable] = None,
            name: Optional[str] = None
    ):
        assert designated_values <= carrier_set
        self.carrier_set = carrier_set
        self.logical_operations = logical_operations
        self.designated_values = designated_values
        self.ordering = ordering
        self.name = str(abs(hash((
            frozenset(carrier_set),
            frozenset(logical_operations),
            frozenset(designated_values)
        ))))[:5] if name is None else name

    def __str__(self):
        result = ("=" * 25) + f"""
Model Name: {self.name}
Carrier Set: {set_to_str(self.carrier_set)}
Designated Values: {set_to_str(self.designated_values)}
"""
        for function in self.logical_operations:
            result += f"{str(function)}\n"

        return result + ("=" * 25) + "\n"


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


def model_closure(initial_set: Set[ModelValue], mfunctions: Set[ModelFunction], forbidden_element: Optional[ModelValue]) -> Set[ModelValue]:
    """
    Given an initial set of model values and a set of model functions,
    compute the complete set of model values that are closed
    under the operations.

    If the forbidden element is encountered, then we end the saturation procedure early.
    """
    closure_set: Set[ModelValue] = initial_set
    last_new: Set[ModelValue] = initial_set
    changed: bool = True
    forbidden_found = False

    arities = set()
    for mfun in mfunctions:
        arities.add(mfun.arity)

    while changed:
        changed = False
        new_elements: Set[ModelValue] = set()
        old_closure: Set[ModelValue] = closure_set - last_new

        # arity -> args
        args_by_arity = defaultdict(list)

        # Motivation: We want to only compute arguments that we have not
        # seen before
        for arity in arities:
            for num_new in range(1, arity + 1):
                new_args = combinations_with_replacement(last_new, r=num_new)
                old_args = combinations_with_replacement(old_closure, r=arity - num_new)
                # Determine every possible ordering of the concatenated new and
                # old model values.
                for new_arg, old_arg in product(new_args, old_args):
                    for combined_args in permutations(new_arg + old_arg):
                        args_by_arity[arity].append(combined_args)


        # Pass each argument into each model function
        for mfun in mfunctions:
            for args in args_by_arity[mfun.arity]:
                # Compute the new elements
                # given the cached arguments.
                element = mfun(*args)
                if element not in closure_set:
                    new_elements.add(element)

                # Optimization: Break out of computation
                # early when forbidden element is found
                if forbidden_element is not None and element == forbidden_element:
                    forbidden_found = True
                    break

            if forbidden_found:
                break

        closure_set.update(new_elements)
        changed = len(new_elements) > 0
        last_new = new_elements

        if forbidden_found:
            break

    return closure_set

def model_equivalence(model1: Model, model2: Model) -> bool:
    """
    Takes two models and determines if they are equivalent.
    Assumes for the model to be equilvalent that their
    value names are equivalent as well.
    """

    if model1.carrier_set != model2.carrier_set:
        return False

    if model1.designated_values != model2.designated_values:
        return False

    model1_fn_names = set((fn.operation_name for fn in model1.logical_operations))
    model2_fn_names = set((fn.operation_name for fn in model2.logical_operations))

    if model1_fn_names != model2_fn_names:
        return False

    for fn_name in model1_fn_names:
        fn1 = next((fn for fn in model1.logical_operations if fn.operation_name == fn_name))
        fn2 = next((fn for fn in model2.logical_operations if fn.operation_name == fn_name))

        if fn1.arity != fn2.arity:
            return False

        # Check for functional equilvance
        # That is for all inputs in the carrier set, the outputs are the same
        for args in product(model1.carrier_set, repeat=fn1.arity):
            if fn1(*args) != fn2(*args):
                return False

    return True
