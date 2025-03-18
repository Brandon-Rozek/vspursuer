"""
Parses the Magic Ugly Data File Format

Assumes the base logic is R with no extra connectives
"""
import re
from typing import TextIO, List, Iterator, Optional, Tuple, Set, Dict

from model import Model, ModelValue, ModelFunction, OrderTable
from logic import (
    Implication,
    Conjunction,
    Negation,
    Necessitation,
    Disjunction,
    Operation
)

class SourceFile:
    def __init__(self, fileobj: TextIO):
        self.fileobj = fileobj
        self.current_line = 0
        self.reststr = ""

    def next_line(self):
        """
        Grabs the next line.
        If reststr is populated return that, otherwise
        consume generator
        """
        if self.reststr != "":
            reststr = self.reststr
            self.reststr = ""
            return reststr

        contents = next(self.fileobj).strip()
        self.current_line += 1
        return contents

    def __next__(self):
        """
        Grabs the next word token from the stream
        """
        if self.reststr == "":
            self.reststr = next(self.fileobj).strip()
            self.current_line += 1

        next_token, _, self.reststr = self.reststr.partition(" ")
        return next_token

class UglyHeader:
    def __init__(self, negation: bool, necessitation: bool, custom_model_functions: List[Tuple[int, str]]):
        # Booleans describing the logical fragment
        self.negation = negation
        self.necessitation = necessitation
        # List of custom model functions described as
        # a sequence of (adicity, symbol) pairs
        self.custom_model_functions = custom_model_functions

class ModelBuilder:
    def __init__(self):
        self.size : int = 0
        self.carrier_set : Set[ModelValue] = set()
        self.mnegation: Optional[ModelFunction] = None
        self.ordering: Optional[OrderTable] = None
        self.mconjunction: Optional[ModelFunction] = None
        self.mdisjunction: Optional[ModelFunction] = None
        self.designated_values: Set[ModelValue] = set()
        self.mimplication: Optional[ModelFunction] = None
        self.mnecessitation: Optional[ModelFunction] = None
        # Map symbol to model function
        self.custom_model_functions: Dict[str,  ModelFunction] = {}

class Stage:
    def __init__(self, name: str):
        self.name = name
        self.next: Optional['Stage'] = None
        self.previous: Optional['Stage'] = None
        # This corresponds to a portion of the model name in MaGIC
        self.num = 0

    def increment(self):
        self.num += 1

    def reset(self):
        self.num = 0

    def __str__(self):
        return self.name

class Stages:
    def __init__(self):
        end_stage = Stage("end")
        self.stages: Dict[str, Stage] = {"end": end_stage}
        self.last_added_stage: Stage = end_stage
        self.first_stage: Optional[Stage] = None

    def add(self, name: str):
        stage = Stage(name)
        stage.next = stage

        stage.previous = self.last_added_stage

        # End stage is a sink so don't
        # mark any stages as next
        if self.last_added_stage.name != "end":
            self.last_added_stage.next = stage
        else:
            # If this is triggered, than this is the first
            # stage added
            self.first_stage = stage

        self.stages[name] = stage
        self.last_added_stage = stage

    def reset_after(self, name):
        """
        Resets the stage counters after a given stage.
        This is to accurately reflect the name of the
        model within MaGIC.
        """
        stage = self.stages[name]
        while stage.name != "process_model":
            stage.reset()
            stage = stage.next

    def get(self, name):
        return self.stages[name]

    def name(self):
        result = ""
        stage = self.first_stage
        if stage is None:
            return ""

        result = f"{stage.num}"
        if stage.next == "process_model":
            return result

        stage = stage.next
        while stage is not None:
            result += f".{stage.num}"
            if stage.next.name != "process_model":
                stage = stage.next
            else:
                stage = None

        return result


def derive_stages(header: UglyHeader) -> Stages:
    stages = Stages()
    stages.add("size")
    if header.negation:
        stages.add("negation")
    stages.add("order")
    stages.add("designated")
    stages.add("implication")
    if header.necessitation:
        stages.add("necessitation")
    for (adicity, symbol) in header.custom_model_functions:
        stages.add(f"custom--{adicity}--{symbol}")
    stages.add("process_model")

    # After processing the model, go to the previous stage
    stages.get("process_model").next = stages.get("process_model").previous

    return stages

def parse_matrices(infile: SourceFile) -> Iterator[Tuple[Model, Dict[Operation, ModelFunction]]]:
    header = parse_header(infile)
    stages = derive_stages(header)
    first_run = True
    current_model_parts = ModelBuilder()
    stage = stages.first_stage
    while True:
        match stage.name:
            case "end":
                break
            case "process_model":
                yield process_model(stages.name(), current_model_parts)
                stage = stage.next
            case "size":
                processed = process_sizes(infile, current_model_parts, first_run)
                first_run = False
                if processed:
                    stage.num = current_model_parts.size + 1
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous
            case "negation":
                processed = process_negations(infile, current_model_parts)
                if processed:
                    stage.increment()
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous
            case "order":
                processed = process_orders(infile, current_model_parts)
                if processed:
                    stage.increment()
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous
            case "designated":
                processed = process_designateds(infile, current_model_parts)
                if processed:
                    stage.increment()
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous
            case "implication":
                processed = process_implications(infile, current_model_parts)
                if processed:
                    stage.increment()
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous
            case "necessitation":
                processed = process_necessitations(infile, current_model_parts)
                if processed:
                    stage.increment()
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous
            case _:
                custom_stage = re.search(r"custom--(\d+)--(\S+)", stage.name)
                if custom_stage is None or len(custom_stage.groups()) != 2:
                    raise NotImplementedError(f"Unrecognized Stage: {stage.name}")
                adicity, symbol = custom_stage.groups()
                adicity = int(adicity)
                processed = process_custom_connective(infile, symbol, adicity, current_model_parts)

                if processed:
                    stage.increment()
                    stage = stage.next
                else:
                    stages.reset_after(stage.name)
                    stage = stage.previous

def process_sizes(infile: SourceFile, current_model_parts: ModelBuilder, first_run: bool) -> bool:
    try:
        size = parse_size(infile, first_run)
    except StopIteration:
        return False
    if size is None:
        return False

    carrier_set = carrier_set_from_size(size)
    current_model_parts.carrier_set = carrier_set
    current_model_parts.size = size

    return True

def process_negations(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 2 (Optional)"""
    mnegation = parse_single_monadic_connective(infile, "¬", current_model_parts.size)
    if mnegation is None:
        return False

    current_model_parts.mnegation = mnegation
    return True

def process_orders(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 3"""
    result = parse_single_order(infile, current_model_parts.size)
    if result is None:
        return False

    ordering, mconjunction, mdisjunction = result
    current_model_parts.ordering = ordering
    current_model_parts.mconjunction = mconjunction
    current_model_parts.mdisjunction = mdisjunction

    return True

def process_designateds(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 4"""
    designated_values = parse_single_designated(infile, current_model_parts.size)
    if designated_values is None:
        return False

    current_model_parts.designated_values = designated_values
    return True

def process_implications(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 5"""
    mimplication = parse_single_dyadic_connective(infile, "→", current_model_parts.size)
    if mimplication is None:
        return False

    current_model_parts.mimplication = mimplication
    return True

def process_necessitations(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    mnecessitation = parse_single_monadic_connective(infile, "!", current_model_parts.size)
    if mnecessitation is None:
        return False

    current_model_parts.mnecessitation = mnecessitation
    return True

def process_custom_connective(infile: SourceFile, symbol: str, adicity: int, current_model_parts: ModelBuilder) -> bool:
    if adicity == 0:
        mfunction = parse_single_nullary_connective(infile, symbol)
    elif adicity == 1:
        mfunction = parse_single_monadic_connective(infile, symbol, current_model_parts.size)
    elif adicity == 2:
        mfunction = parse_single_dyadic_connective(infile, symbol, current_model_parts.size)
    else:
        raise NotImplementedError("Unable to process connectives of adicity greater than 2")

    if mfunction is None:
        return False

    current_model_parts.custom_model_functions[symbol] = mfunction
    return True

def process_model(model_name: str, mp: ModelBuilder) -> Tuple[Model, Dict[Operation, ModelFunction]]:
    """Create Model"""
    assert mp.size > 0
    assert mp.size + 1 == len(mp.carrier_set)
    assert len(mp.designated_values) <= len(mp.carrier_set)
    assert mp.mimplication is not None

    logical_operations = { mp.mimplication }
    interpretation = {
        Implication: mp.mimplication
    }
    if mp.mnegation is not None:
        logical_operations.add(mp.mnegation)
        interpretation[Negation] = mp.mnegation
    if mp.mconjunction is not None:
        logical_operations.add(mp.mconjunction)
        interpretation[Conjunction] = mp.mconjunction
    if mp.mdisjunction is not None:
        logical_operations.add(mp.mdisjunction)
        interpretation[Disjunction] = mp.mdisjunction
    if mp.mnecessitation is not None:
        logical_operations.add(mp.mnecessitation)
        interpretation[Necessitation] = mp.mnecessitation

    for custom_mf in mp.custom_model_functions.values():
        if custom_mf is not None:
            logical_operations.add(custom_mf)
            op = Operation(custom_mf.operation_name, custom_mf.arity)
            interpretation[op] = custom_mf
    
    model = Model(mp.carrier_set, logical_operations, mp.designated_values, ordering=mp.ordering, name=model_name)
    return (model, interpretation)


def parse_header(infile: SourceFile) -> UglyHeader:
    """
    Parse the header line from the ugly data format.
    """
    header_line = infile.next_line()
    header_tokens = header_line.split(" ")
    assert header_tokens[0] in ["0", "1"]
    assert header_tokens[6] in ["0", "1"]
    assert len(header_tokens) >= 7
    negation_defined = bool(int(header_tokens[0]))
    necessitation_defined = bool(int(header_tokens[6]))
    num_custom_connectives = int(header_tokens[7])
    custom_model_functions: List[Tuple[int, str]] = []
    for i in range(num_custom_connectives):
        arity = int(header_tokens[7 + (2 * i) + 1])
        symbol = header_tokens[7 + (2 * i) + 2]
        custom_model_functions.append((arity, symbol))
    return UglyHeader(negation_defined, necessitation_defined, custom_model_functions)

def carrier_set_from_size(size: int) -> Set[ModelValue]:
    """
    Construct a carrier set of model values
    based on the desired size.
    """
    return {
        mvalue_from_index(i) for i in range(size + 1)
    }

def parse_size(infile: SourceFile, first_run: bool) -> Optional[int]:
    """
    Parse the line representing the matrix size.
    """

    size = int(infile.next_line())

    # HACK: When necessitation and custom connectives are enabled
    # MaGIC may produce -1s at the beginning of the file
    if first_run:
        while size == -1:
            size = int(infile.next_line())

    if size == -1:
        return None
    assert size > 0, f"Unexpected size at line {infile.current_line}"
    return size

def mvalue_from_index(i: int) -> ModelValue:
    """
    Given an index, return the
    representation of the model value.
    """
    return ModelValue(f"{i}")

def parse_mvalue(x: str) -> ModelValue:
    """
    Parse an element and return the model value.
    """
    return mvalue_from_index(int(x))

def determine_cresult(size: int, ordering: Dict[ModelValue, ModelValue], a: ModelValue, b: ModelValue) -> ModelValue:
    """
    Determine what a ∧ b should be given the ordering table.
    """
    for i in range(size + 1):
        c = mvalue_from_index(i)

        if not ordering[(c, a)]:
            continue
        if not ordering[(c, b)]:
            continue

        invalid = False
        for j in range(size + 1):
            d = mvalue_from_index(j)
            if c == d:
                continue
            if ordering[(c, d)]:
                if ordering[(d, a)] and ordering [(d, b)]:
                    invalid = True

        if not invalid:
            return c

def determine_dresult(size: int, ordering: Dict[ModelValue, ModelValue], a: ModelValue, b: ModelValue) -> ModelValue:
    """
    Determine what a ∨ b should be given the ordering table.
    """
    for i in range(size + 1):
        c = mvalue_from_index(i)
        if not ordering[(a, c)]:
            continue
        if not ordering[(b, c)]:
            continue

        invalid = False

        for j in range(size + 1):
            d = mvalue_from_index(j)
            if d == c:
                continue
            if ordering[(d, c)]:
                if ordering[(a, d)] and ordering[(b, d)]:
                    invalid = True

        if not invalid:
            return c

def parse_single_order(infile: SourceFile, size: int) -> Optional[Tuple[OrderTable, ModelFunction, ModelFunction]]:
    """
    Parse the line representing the ordering table
    """
    line = infile.next_line()
    if line == '-1':
        return None

    table = line.split(" ")

    assert len(table) == (size + 1)**2, f"Order table doesn't match expected size at line {infile.current_line}"

    ordering = OrderTable()
    omapping = {}
    table_i = 0

    for i in range(size + 1):
        x = mvalue_from_index(i)
        for j in range(size + 1):
            y = mvalue_from_index(j)
            omapping[(x, y)] = table[table_i] == '1'
            if table[table_i] == '1':
                ordering.add(x, y)
            table_i += 1

    cmapping = {}
    dmapping = {}

    for i in range(size + 1):
        x = mvalue_from_index(i)
        for j in range(size + 1):
            y = mvalue_from_index(j)

            cresult = determine_cresult(size, omapping, x, y)
            if cresult is None:
                print("[Warning] Conjunction and Disjunction are not well-defined")
                print(f"{x} ∧ {y} = ??")
                return None, None
            cmapping[(x, y)] = cresult

            dresult = determine_dresult(size, omapping, x, y)
            if dresult is None:
                print("[Warning] Conjunction and Disjunction are not well-defined")
                print(f"{x} ∨ {y} = ??")
                return None, None
            dmapping[(x, y)] = dresult


    mconjunction = ModelFunction(2, cmapping, "∧")
    mdisjunction = ModelFunction(2, dmapping, "∨")

    return ordering, mconjunction, mdisjunction

def parse_single_designated(infile: SourceFile, size: int) -> Optional[Set[ModelValue]]:
    """
    Parse the line representing which model values are designated.
    """
    line = infile.next_line()
    if line == '-1':
        return None

    row = line.split(" ")
    assert len(row) == size + 1, f"Designated table doesn't match expected size at line {infile.current_line}"

    designated_values = set()

    for i, j in zip(range(size + 1), row):
        if j == '1':
            x = mvalue_from_index(i)
            designated_values.add(x)

    return designated_values


def parse_single_nullary_connective(infile: SourceFile, symbol: str) -> Optional[ModelFunction]:
    line = infile.next_line()
    if line == "-1":
        return None

    row = line.split(" ")
    assert len(row) == 1, f"More than one assignment for a nullary connective was provided at line {infile.current_line}"

    mapping = {}
    mapping[()] = parse_mvalue(row[0])
    return ModelFunction(0, mapping, symbol)

def parse_single_monadic_connective(infile: SourceFile, symbol: str, size: int) -> Optional[ModelFunction]:
    line = infile.next_line()
    if line == '-1':
        return None

    row = line.split(" ")
    assert len(row) == size + 1, f"{symbol} table doesn't match size at line {infile.current_line}"
    mapping = {}

    for i, j in zip(range(size + 1), row):
        x = mvalue_from_index(i)
        y = parse_mvalue(j)
        mapping[(x, )] = y

    return ModelFunction(1, mapping, symbol)

def parse_single_dyadic_connective(infile: SourceFile, symbol: str, size: int) -> Optional[ModelFunction]:
    first_token = next(infile)
    if first_token == "-1":
        return None

    table = []
    try:
        table = [first_token] + [next(infile) for _ in range((size + 1)**2 - 1)]
    except StopIteration:
        pass

    assert len(table) == (size + 1)**2, f"{symbol} table does not match expected size at line {infile.current_line}"

    mapping = {}
    table_i = 0
    for i in range(size + 1):
        x = mvalue_from_index(i)
        for j in range(size + 1):
            y = mvalue_from_index(j)

            r = parse_mvalue(table[table_i])
            table_i += 1

            mapping[(x, y)] = r

    return ModelFunction(2, mapping, symbol)
