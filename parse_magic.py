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
    def __init__(self, negation: bool, necessitation: bool):
        self.negation = negation
        self.necessitation = necessitation

# NOTE: Global variable used to keep track of solution models
solutions: List[Tuple[Model, Dict]] = []

def parse_matrices(infile: SourceFile) -> List[Tuple[Model, Dict]]:
    global solutions
    solutions = [] # Reset
    header = parse_header(infile)
    process_sizes(infile, header)

def process_sizes(infile: SourceFile, header: UglyHeader):
    """Stage 1"""
    while True:
        size = parse_size(infile)
        if size is None:
            break
        carrier_set = carrier_set_from_size(size)
        process_negations(infile, header, size, carrier_set)

def process_negations(infile: SourceFile, header: UglyHeader, size: int, carrier_set: Set[ModelValue]):
    """Stage 2 (Optional)"""
    num_negation = 0
    while True:
        mnegation = None
        if header.negation:
            mnegation = parse_single_negation(infile, size)
            if mnegation is None:
                break
            num_negation += 1

        process_orders(infile, header, size, carrier_set, num_negation, mnegation)

        if not header.negation:
            break

def process_orders(infile: SourceFile, header: UglyHeader, size: int, carrier_set: Set[ModelValue], num_negation: int, mnegation: Optional[ModelFunction]):
    """Stage 3"""
    num_order = 0
    while True:
        result = parse_single_order(infile, size)
        if result is None:
            break
        mconjunction, mdisjunction = result
        num_order += 1
        process_designateds(infile, header, size, carrier_set, num_negation, mnegation, num_order, mconjunction, mdisjunction)

def process_designateds(infile: SourceFile, header: UglyHeader, size: int, carrier_set: Set[ModelValue], num_negation: int, mnegation: Optional[ModelFunction], num_order: int, mconjunction: Optional[ModelFunction], mdisjunction: Optional[ModelFunction]):
    """Stage 4"""
    num_designated = 0
    while True:
        designated_values = parse_single_designated(infile, size)
        if designated_values is None:
            break
        num_designated += 1
        process_implications(infile, header, size, carrier_set, num_negation, mnegation, num_order, mconjunction, mdisjunction, num_designated, designated_values)

def process_implications(
    infile: SourceFile, header: UglyHeader, size: int, carrier_set: Set[ModelValue], num_negation: int, mnegation: Optional[ModelFunction],
    num_order: int, mconjunction: Optional[ModelFunction], mdisjunction: Optional[ModelFunction], num_designated: int, designated_values: Set[ModelValue]):
    """Stage 5"""
    results = parse_implications(infile, size)
    for num_implication, mimplication in enumerate(results, 1):
        process_model(size, carrier_set, num_negation, mnegation, num_order, mconjunction, mdisjunction, num_designated, designated_values, num_implication, mimplication)

def process_model(
    size: int, carrier_set: Set[ModelValue], num_negation: int, mnegation: Optional[ModelFunction],
    num_order: int, mconjunction: Optional[ModelFunction], mdisjunction: Optional[ModelFunction], num_designated: int,
    designated_values: Set[ModelValue], num_implication: int, mimplication: ModelFunction):
    """Create Model"""
    global solutions

    logical_operations = { mimplication }
    model_name = f"{size}{'.' + str(num_negation) if num_negation != 0 else ''}.{num_order}.{num_designated}.{num_implication}"
    model = Model(carrier_set, logical_operations, designated_values, name=model_name)
    interpretation = {
        Implication: mimplication
    }
    if mnegation is not None:
        logical_operations.add(mnegation)
        interpretation[Negation] = mnegation
    if mconjunction is not None:
        logical_operations.add(mconjunction)
        interpretation[Conjunction] = mconjunction
    if mdisjunction is not None:
        logical_operations.add(mdisjunction)
        interpretation[Disjunction] = mdisjunction

    solutions.append((model, interpretation))
    print(f"Parsed Matrix {model.name}")

def parse_header(infile: SourceFile) -> UglyHeader:
    """
    Parse the header line from the ugly data format.
    NOTE: Currently Incomplete.
    """
    header_line = next(infile).strip()
    header_tokens = header_line.split(" ")
    print(header_tokens)
    assert header_tokens[0] in ["0", "1"]
    assert header_tokens[6] in ["0", "1"]
    negation_defined = bool(int(header_tokens[0]))
    necessitation_defined = bool(int(header_tokens[6]))
    return UglyHeader(negation_defined, necessitation_defined)

def carrier_set_from_size(size: int):
    """
    Construct a carrier set of model values
    based on the desired size.
    """
    return {
        mvalue_from_index(i) for i in range(size + 1)
    }

def parse_size(infile: SourceFile) -> Optional[int]:
    """
    Parse the line representing the matrix size.
    """
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

def parse_single_order(infile: TextIO, size: int) -> Optional[Tuple[ModelFunction, ModelFunction]]:
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

def parse_single_designated(infile: TextIO, size: int) -> Optional[Set[ModelValue]]:
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


def parse_implications(infile: TextIO, size: int) -> List[ModelFunction]:
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="VSP Checker")
    parser.add_argument("--verbose", action='store_true', help="Print out all parsed matrices")
    args = vars(parser.parse_args())
    parse_matrices(SourceFile(sys.stdin))
    print(f"Parsed {len(solutions)} matrices")
    for i, (model, interpretation) in enumerate(solutions):
        vsp_result = has_vsp(model, interpretation)
        print(vsp_result)
        if args['verbose'] or vsp_result.has_vsp:
            print(model)
