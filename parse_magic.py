"""
Parses the Magic Ugly Data File Format

Assumes the base logic is R with no extra connectives
"""
import argparse
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

    def __next__(self):
        contents = next(self.fileobj)
        self.current_line += 1
        return contents

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

def parse_matrices(infile: SourceFile) -> List[Tuple[Model, Dict]]:
    solutions = [] # Reset
    header = parse_header(infile)
    current_model_parts = ModelBuilder()
    process_sizes(infile, header, current_model_parts, solutions)
    return solutions

def process_sizes(infile: SourceFile, header: UglyHeader, current_model_parts: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Stage 1"""

    first_run = True

    while True:
        print("Processing next size")
        try:
            size = parse_size(infile, first_run)
            first_run = False
        except StopIteration:
            # For some reason, when necessitation is enabled this doesn't
            # have a -1 on the last line
            break
        if size is None:
            break

        carrier_set = carrier_set_from_size(size)
        current_model_parts.size = size
        current_model_parts.carrier_set = carrier_set
        process_negations(infile, header, current_model_parts, solutions)

def process_negations(infile: SourceFile, header: UglyHeader, current_model_parts: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Stage 2 (Optional)"""
    num_negation = 0
    while True:
        print("Processing next negation")
        mnegation = None
        if header.negation:
            mnegation = parse_single_negation(infile, current_model_parts.size)
            if mnegation is None:
                break
            num_negation += 1

        current_model_parts.num_negation = num_negation
        current_model_parts.mnegation = mnegation

        process_orders(infile, header, current_model_parts, solutions)

        if not header.negation:
            break

def process_orders(infile: SourceFile, header: UglyHeader, current_model_parts: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Stage 3"""
    num_order = 0
    while True:
        print("Processing next order")
        result = parse_single_order(infile, current_model_parts.size)
        if result is None:
            break
        num_order += 1
        mconjunction, mdisjunction = result
        current_model_parts.num_order = num_order
        current_model_parts.mconjunction = mconjunction
        current_model_parts.mdisjunction = mdisjunction
        process_designateds(infile, header, current_model_parts, solutions)

def process_designateds(infile: SourceFile, header: UglyHeader, current_model_parts: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Stage 4"""
    num_designated = 0
    while True:
        print("Processing next designated")
        designated_values = parse_single_designated(infile, current_model_parts.size)
        if designated_values is None:
            break
        num_designated += 1
        current_model_parts.num_designated = num_designated
        current_model_parts.designated_values = designated_values
        process_implications(infile, header, current_model_parts, solutions)

def process_implications(
    infile: SourceFile, header: UglyHeader, current_model_parts: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Stage 5"""
    if header.necessitation:
        num_implication = 0
        while True:
            print("Processing next implication")
            instr = next(infile).strip()
            mimplication, reststr = parse_single_implication(instr, infile.current_line, current_model_parts.size)
            if mimplication is None:
                break
            num_implication += 1
            current_model_parts.num_implication = num_implication
            current_model_parts.mimplication = mimplication
            process_necessitations(infile, reststr, header, current_model_parts, solutions)
    else:
        results = parse_implications(infile, current_model_parts.size)
        for num_implication, mimplication in enumerate(results, 1):
            current_model_parts.num_implication = num_implication
            current_model_parts.mimplication = mimplication
            process_model(current_model_parts, solutions)

def process_necessitations(infile: SourceFile, instr: str, header: UglyHeader, current_model_parts: ModelBuilder, solutions: List[Tuple[Model, Dict]]):

    # NOTE: For some reason, one necessitation table will be on the same line as the implication table
    mnecessitation = parse_single_necessitation_from_str(instr, infile.current_line, current_model_parts.size)
    assert mnecessitation is not None, f"Expected Necessitation Table at line {infile.current_line}"
    num_necessitation = 1

    current_model_parts.num_necessitation = num_necessitation
    current_model_parts.mnecessitation = mnecessitation
    process_model(current_model_parts, solutions)

    while True:
        print("Processing next necessitation")
        mnecessitation = parse_single_necessitation(infile, current_model_parts.size)
        if mnecessitation is None:
            break
        num_necessitation += 1

        current_model_parts.num_necessitation = num_necessitation
        current_model_parts.mnecessitation = mnecessitation
        process_model(current_model_parts, solutions)

def process_model(mp: ModelBuilder, solutions: List[Tuple[Model, Dict]]):
    """Create Model"""
    assert mp.mimplication is not None
    assert len(mp.carrier_set) > 0

    logical_operations = { mp.mimplication }
    model_name = f"{mp.size}{'.' + str(mp.num_negation) if mp.num_negation != 0 else ''}.{mp.num_order}.{mp.num_designated}.{mp.num_implication}{'.' + str(mp.num_necessitation) if mp.num_necessitation != 0 else ''}"
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

    solutions.append((model, interpretation))
    print(f"Parsed Matrix {model.name}")

def parse_header(infile: SourceFile) -> UglyHeader:
    """
    Parse the header line from the ugly data format.
    """
    header_line = next(infile).strip()
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

def carrier_set_from_size(size: int):
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

    size = int(next(infile))
    # HACK: When necessitation and custom connectives are enabled
    # MaGIC may produce -1s at the beginning of the file
    if first_run:
        while size == -1:
            size = int(next(infile))

    if size == -1:
        return None
    assert size > 0, f"Unexpected size at line {infile.current_line}"
    return size

def parse_single_negation(infile: SourceFile, size: int) -> Optional[ModelFunction]:
    """
    Parse the line representing the negation table.
    """
    line = next(infile).strip()
    if line == '-1':
        return None

    row = line.split(" ")
    assert len(row) == size + 1, f"Negation table doesn't match size at line {infile.current_line}"
    mapping = {}

    for i, j in zip(range(size + 1), row):
        x = mvalue_from_index(i)
        y = parse_mvalue(j)
        mapping[(x, )] = y

    return ModelFunction(1, mapping, "¬")


def mvalue_from_index(i: int):
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
    line = next(infile).strip()
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
    line = next(infile).strip()
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


def parse_single_implication(instr: str, line: int, size: int) -> Tuple[ModelFunction, str]:
    """
    Take the current string, parse an implication table from it,
    and return along with it the remainder of the string
    """
    if instr == "-1":
        return None, ""

    table = instr.split(" ")

    assert len(table) >= (size + 1)**2, f"Implication table does not match expected size at line {line}"

    mapping = {}
    table_i = 0
    for i in range(size + 1):
        x = mvalue_from_index(i)
        for j in range(size + 1):
            y = mvalue_from_index(j)

            r = parse_mvalue(table[table_i])
            table_i += 1

            mapping[(x, y)] = r

    mimplication = ModelFunction(2, mapping, "→")
    reststr = " ".join(table[(size + 1)**2:])
    return mimplication, reststr


def parse_implications(infile: SourceFile, size: int) -> List[ModelFunction]:
    """
    Parse the line representing the list of implication
    tables.
    """
    line = next(infile).strip()

    # Split and remove the last '-1' character
    table = line.split(" ")[:-1]

    assert len(table) % (size + 1)**2 == 0, f"Implication table does not match expected size at line {infile.current_line}"

    table_i = 0
    mimplications: List[ModelFunction] = []

    for _ in range(len(table) // (size + 1)**2):
        mapping = {}

        for i in range(size + 1):
            x = mvalue_from_index(i)
            for j in range(size + 1):
                y = mvalue_from_index(j)

                r = parse_mvalue(table[table_i])
                table_i += 1

                mapping[(x, y)] = r

        mimplication = ModelFunction(2, mapping, "→")
        mimplications.append(mimplication)

    return mimplications

def parse_single_necessitation_from_str(instr: str, line: int, size: int) -> Optional[ModelFunction]:
    """
    Parse the line representing the necessitation table.
    """
    if instr == "-1":
        return None

    row = instr.split(" ")
    assert len(row) == size + 1, f"Necessitation table doesn't match size at line {line}"
    mapping = {}

    for i, j in zip(range(size + 1), row):
        x = mvalue_from_index(i)
        y = parse_mvalue(j)
        mapping[(x, )] = y

    return ModelFunction(1, mapping, "!")

def parse_single_necessitation(infile: SourceFile, size: int) -> Optional[ModelFunction]:
    line = next(infile).strip()
    return parse_single_necessitation_from_str(line, infile.current_line, size)


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
