"""
Parses the Magic Ugly Data File Format

Assumes the base logic is R with no extra connectives
"""
import argparse
import re
import sys
from typing import TextIO, List, Optional, Tuple, Set, Dict

from model import Model, ModelValue, ModelFunction
from logic import (
    Implication,
    Conjunction,
    Negation,
    Necessitation,
    Disjunction
)
from vsp import has_vsp

class SourceFile:
    def __init__(self, fileobj: TextIO):
        self.fileobj = fileobj
        self.current_line = 0
        self.reststr = ""

    def next_line(self):
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

        tokens = self.reststr.split(" ")
        next_token = tokens[0]
        self.reststr = " ".join(tokens[1:])

        return next_token


    def set_reststr(self, reststr: str):
        self.reststr = reststr

class UglyHeader:
    def __init__(self, negation: bool, necessitation: bool, custom_model_functions: List[Tuple[int, str]]):
        self.negation = negation
        self.necessitation = necessitation
        self.custom_model_functions = custom_model_functions

class ModelBuilder:
    def __init__(self):
        self.size : int = 0
        self.carrier_set : Set[ModelValue] = set()
        self.num_negation: int = 0
        self.mnegation: Optional[ModelFunction] = None
        self.num_order: int = 0
        self.mconjunction: Optional[ModelFunction] = None
        self.mdisjunction: Optional[ModelFunction] = None
        self.num_designated: int = 0
        self.designated_values: Set[ModelValue] = set()
        self.num_implication: int = 0
        self.mimplication: Optional[ModelFunction] = None
        self.num_necessitation: int = 0
        self.mnecessitation: Optional[ModelFunction] = None
        self.custom_model_functions: Dict[str,  ModelFunction] = {}

class Stage:
    def __init__(self, name: str):
        self.name = name
        self.next: Optional['Stage'] = None
        self.previous: Optional['Stage'] = None
    def __str__(self):
        return self.name

class Stages:
    def __init__(self):
        self.stages: Dict[str, Stage] = {}
        self.last_stage: Optional[Stage] = None
    def add(self, name: str):
        stage = Stage(name)
        stage.next = stage

        if self.last_stage is not None:
            stage.previous = self.last_stage
            self.last_stage.next = stage
        else:
            # The previous of the first stage
            # is the end
            stage.previous = Stage("end")

        self.stages[name] = stage
        self.last_stage = stage
    def next_stage(self, name):
        return self.stages[name].next
    def previous_stage(self, name):
        return self.stages[name].previous
    def get(self, name):
        return self.stages[name]

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

def parse_matrices(infile: SourceFile) -> List[Tuple[Model, Dict]]:
    solutions = [] # Reset
    header = parse_header(infile)
    stages = derive_stages(header)
    first_run = True
    current_model_parts = ModelBuilder()
    stage = stages.get("size")
    while True:
        print("Current stage:", stage)
        match stage.name:
            case "end":
                break
            case "process_model":
                process_model(current_model_parts, solutions)
                stage = stage.next
            case "size":
                processed = process_sizes(infile, current_model_parts, first_run)
                first_run = False
                stage = stage.next if processed else stage.previous
            case "negation":
                processed = process_negations(infile, current_model_parts)
                stage = stage.next if processed else stage.previous
            case "order":
                processed = process_orders(infile, current_model_parts)
                stage = stage.next if processed else stage.previous
            case "designated":
                processed = process_designateds(infile, current_model_parts)
                stage = stage.next if processed else stage.previous
            case "implication":
                processed = process_implications(infile, current_model_parts)
                stage = stage.next if processed else stage.previous
            case "necessitation":
                processed = process_necessitations(infile, current_model_parts)
                stage = stage.next if processed else stage.previous
            case _:
                custom_stage = re.search(r"custom--(\d+)--(\S+)", stage.name)
                if custom_stage is None or len(custom_stage.groups()) != 2:
                    raise NotImplementedError(f"Unrecognized Stage: {stage.name}")
                adicity, symbol = custom_stage.groups()
                adicity = int(adicity)
                if adicity == 0:
                    # We don't need to do anything here
                    stage = stage.next
                elif adicity == 1:
                    processed = process_monadic_connective(infile, symbol, current_model_parts)
                    stage = stage.next if processed else stage.previous
                elif adicity == 2:
                    processed = process_dyadic_connective(infile, symbol, current_model_parts)
                    stage = stage.next if processed else stage.previous
                else:
                    raise NotImplementedError("Unable to process connectives of adicity greater than 2")


    return solutions

def process_sizes(infile: SourceFile, current_model_parts: ModelBuilder, first_run: bool) -> bool:
    try:
        size = parse_size(infile, first_run)
    except StopIteration:
        return False
    if size is None:
        return False

    carrier_set = carrier_set_from_size(size)
    current_model_parts.size = size
    current_model_parts.carrier_set = carrier_set

    # Reset counts
    current_model_parts.num_negation = 0
    current_model_parts.num_order = 0
    current_model_parts.num_designated = 0
    current_model_parts.num_implication = 0
    current_model_parts.num_necessitation = 0

    return True

def process_negations(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 2 (Optional)"""
    mnegation = parse_single_negation(infile, current_model_parts.size)
    if mnegation is None:
        return False

    current_model_parts.num_negation += 1
    current_model_parts.mnegation = mnegation

    # Reset counts
    current_model_parts.num_order = 0
    current_model_parts.num_designated = 0
    current_model_parts.num_implication = 0
    current_model_parts.num_necessitation = 0

    return True

def process_orders(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 3"""
    result = parse_single_order(infile, current_model_parts.size)
    if result is None:
        return False

    mconjunction, mdisjunction = result
    current_model_parts.num_order += 1
    current_model_parts.mconjunction = mconjunction
    current_model_parts.mdisjunction = mdisjunction

    # Reset counts
    current_model_parts.num_designated = 0
    current_model_parts.num_implication = 0
    current_model_parts.num_necessitation = 0

    return True

def process_designateds(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 4"""
    designated_values = parse_single_designated(infile, current_model_parts.size)
    if designated_values is None:
        return False

    current_model_parts.num_designated += 1
    current_model_parts.designated_values = designated_values

    # Reset counts
    current_model_parts.num_implication = 0
    current_model_parts.num_necessitation = 0

    return True

def process_implications(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    """Stage 5"""
    mimplication = parse_single_implication(infile, current_model_parts.size)
    if mimplication is None:
        return False

    current_model_parts.num_implication += 1
    current_model_parts.mimplication = mimplication

     # Reset counts
    current_model_parts.num_necessitation = 0

    return True

def process_necessitations(infile: SourceFile, current_model_parts: ModelBuilder) -> bool:
    mnecessitation = parse_single_necessitation(infile, current_model_parts.size)
    if mnecessitation is None:
        return False

    current_model_parts.num_necessitation += 1
    current_model_parts.mnecessitation = mnecessitation

    return True

def process_monadic_connective(infile: SourceFile, symbol: str, current_model_parts: ModelBuilder) -> bool:
    mfunction = parse_single_monadic_connective(infile, symbol, current_model_parts.size)
    if mfunction is None:
        return False

    current_model_parts.custom_model_functions[symbol] = mfunction
    return True

def process_dyadic_connective(infile: SourceFile, symbol: str, current_model_parts: ModelBuilder) -> bool:
    mfunction = parse_single_dyadic_connective(infile, symbol, current_model_parts.size)
    if mfunction is None:
        return False

    current_model_parts.custom_model_functions[symbol] = mfunction
    return True

def process_model(mp: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Create Model"""
    assert mp.mimplication is not None
    assert mp.size + 1 == len(mp.carrier_set)

    logical_operations = { mp.mimplication }
    model_name = f"{mp.size + 1}{'.' + str(mp.num_negation) if mp.num_negation != 0 else ''}.{mp.num_order}.{mp.num_designated}.{mp.num_implication}{'.' + str(mp.num_necessitation) if mp.num_necessitation != 0 else ''}"
    model = Model(mp.carrier_set, logical_operations, mp.designated_values, name=model_name)
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
        if custom_mf is None:
            logical_operations.add(custom_mf)
        # NOTE: No need to assign interpretation
        # for VSP check

    solutions.append((model, interpretation))
    print(f"Parsed Matrix {model.name}")

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

def parse_single_negation(infile: SourceFile, size: int) -> Optional[ModelFunction]:
    """
    Parse the line representing the negation table.
    """
    return parse_single_monadic_connective(infile, "¬", size)

def mvalue_from_index(i: int) -> ModelValue:
    """
    Given an index, return the
    representation of the model value.
    """
    return ModelValue(f"a{i}")

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

def parse_single_order(infile: SourceFile, size: int) -> Optional[Tuple[ModelFunction, ModelFunction]]:
    """
    Parse the line representing the ordering table
    """
    line = infile.next_line()
    if line == '-1':
        return None

    table = line.split(" ")

    assert len(table) == (size + 1)**2, f"Order table doesn't match expected size at line {infile.current_line}"

    omapping = {}
    table_i = 0

    for i in range(size + 1):
        x = mvalue_from_index(i)
        for j in range(size + 1):
            y = mvalue_from_index(j)
            omapping[(x, y)] = table[table_i] == '1'
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

    return mconjunction, mdisjunction

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

def parse_single_implication(infile: SourceFile, size: int) -> Tuple[ModelFunction]:
    """
    Take the current string, parse an implication table from it.
    """
    return parse_single_dyadic_connective(infile, "→", size)

def parse_single_necessitation(infile: SourceFile, size: int) -> Optional[ModelFunction]:
    """
    Parse the line representing the necessitation table.
    """
    return parse_single_monadic_connective(infile, "!", size)

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
    try:
        first_token = next(infile)
        if first_token == "-1":
            return None
    except StopIteration:
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="VSP Checker")
    parser.add_argument("--verbose", action='store_true', help="Print out all parsed matrices")
    args = vars(parser.parse_args())
    solutions = parse_matrices(SourceFile(sys.stdin))
    print(f"Parsed {len(solutions)} matrices")
    num_has_vsp = 0
    for i, (model, interpretation) in enumerate(solutions):
        vsp_result = has_vsp(model, interpretation)
        print(vsp_result)

        if args['verbose'] or vsp_result.has_vsp:
            print(model)

        if vsp_result.has_vsp:
            num_has_vsp += 1
    print(f"Tested {len(solutions)} models, {num_has_vsp} of which satisfy VSP")
