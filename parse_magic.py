"""
Parses the Magic Ugly Data File Format

Assumes the base logic is R with no extra connectives
"""
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

def parse_matrices(infile: TextIO) -> List[Tuple[Model, Dict]]:
    next(infile) # Skip header line

    solutions: List[Tuple[Model, Dict]] = []

    while True:
        size = parse_size(infile)
        if size is None:
            break

        carrier_set = carrier_set_from_size(size)

        while True:
            mnegation = parse_negation(infile, size)
            if mnegation is None:
                break

            while True:
                result = parse_order(infile, size)
                if result is None:
                    break
                mconjunction, mdisjunction = result

                while True:
                    designated_values = parse_designated(infile, size)
                    if designated_values is None:
                        break

                    results = parse_implication(infile, size)
                    if result is None:
                        break

                    for mimplication in results:
                        logical_operations = {
                            mnegation, mimplication
                        }
                        model = Model(carrier_set, logical_operations, designated_values, name=str(len(solutions)))
                        interpretation = {
                            Negation: mnegation,
                            Implication: mimplication
                        }
                        if mconjunction is not None:
                            logical_operations.add(mconjunction)
                            interpretation[Conjunction] = mconjunction
                        if mdisjunction is not None:
                            logical_operations.add(mdisjunction)
                            interpretation[Disjunction] = mdisjunction

                        solutions.append((model, interpretation))
                        print(f"Parsed Matrix {model.name}")

    return solutions

def carrier_set_from_size(size: int):
    """
    Construct a carrier set of model values
    based on the desired size.
    """
    return {
        mvalue_from_index(i) for i in range(size + 1)
    }

def parse_size(infile: TextIO) -> Optional[int]:
    """
    Parse the line representing the matrix size.
    """
    size = int(next(infile))
    if size == -1:
        return None
    assert size > 0, "Unexpected size"
    return size

def parse_negation(infile: TextIO, size: int) -> Optional[ModelFunction]:
    """
    Parse the line representing the negation table.
    """
    line = next(infile).strip()
    if line == '-1':
        return None

    row = line.split(" ")
    assert len(row) == size + 1, "Negation table doesn't match size"
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

def parse_order(infile: TextIO, size: int) -> Optional[Tuple[ModelFunction, ModelFunction]]:
    """
    Parse the line representing the ordering table
    """
    line = next(infile).strip()
    if line == '-1':
        return None

    table = line.split(" ")

    assert len(table) == (size + 1)**2

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

def parse_designated(infile: TextIO, size: int) -> Optional[Set[ModelValue]]:
    """
    Parse the line representing which model values are designated.
    """
    line = next(infile).strip()
    if line == '-1':
        return None

    row = line.split(" ")
    assert len(row) == size + 1, "Designated table doesn't match size"

    designated_values = set()

    for i, j in zip(range(size + 1), row):
        if j == '1':
            x = mvalue_from_index(i)
            designated_values.add(x)

    return designated_values


def parse_implication(infile: TextIO, size: int) -> Optional[List[ModelFunction]]:
    """
    Parse the line representing the list of implication
    tables.
    """
    line = next(infile).strip()
    if line == '-1':
        return None

    # Split and remove the last '-1' character
    table = line.split(" ")[:-1]

    assert len(table) % (size + 1)**2 == 0

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
    solutions: List[Model] = parse_matrices(sys.stdin)
    print(f"Parsed {len(solutions)} matrices")
    for i, (model, interpretation) in enumerate(solutions):
        print(model)
        print(has_vsp(model, interpretation))
