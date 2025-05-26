"""
Given two MaGIC ugly data files that correspond to
the same logic. Report any differences in the models
that exhibit VSP.

Overall process:
- Determine which models in file 1 have VSP
- Print if model does not exist in file 2
- For models in file 2 that were not already encountered for,
  check if they have VSP.
- Print models that do
"""
import argparse
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import argparse

from model import model_equivalence
from parse_magic import SourceFile, parse_matrices
from vsp import has_vsp
from vspursuer import restructure_solutions

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Compare models that have VSP in two ugly files")
    parser.add_argument("ugly1", type=str, help="First ugly data file")
    parser.add_argument("ugly2", type=str, help="Second ugly data file")
    args = vars(parser.parse_args())

    data_file1 = open(args['ugly1'], "r")
    solutions1 = parse_matrices(SourceFile(data_file1))
    solutions1 = restructure_solutions(solutions1, None)

    data_file2 = open(args['ugly2'], "r")
    solutions2 = parse_matrices(SourceFile(data_file2))
    solutions2 = list(restructure_solutions(solutions2, None))

    # Total count of models
    total_models1 = 0
    total_models2 = 0

    # Models that exhibit VSP
    good_models1 = 0
    good_models2 = 0

    # Models that don't exhibit VSP
    bad_models1 = 0
    bad_models2 = 0

    # Models that exhibit VSP but does
    # not exist in the other file.
    extra_models1 = 0
    extra_models2 = 0

    for model, impfunction, negation_defined in solutions1:
        total_models1 += 1
        vsp_result = has_vsp(model, impfunction, negation_defined)

        if vsp_result.has_vsp:
            good_models1 += 1
            # Check to see if model exists in file 2
            match_found_index = (False, -1)
            for i in range(len(solutions2) - 1, -1, -1):
                if model_equivalence(model, solutions2[i][0]):
                    match_found_index = (True, i)
                    break

            if match_found_index[0]:
                # If so, remove the model from the second set
                total_models2 += 1
                good_models2 += 1
                del solutions2[match_found_index[1]]
            else:
                extra_models1 += 1
                print(f"VSP Model {model.name} not found in file 2.")
                print(model)
        else:
            bad_models1 += 1


    # Check through the remaining models in the second set
    for model, impfunction, negation_defined in solutions2:
        total_models2 += 1
        vsp_result = has_vsp(model, impfunction, negation_defined)

        if not vsp_result.has_vsp:
            bad_models2 += 1
        else:
            print("VSP model", model.name, "does not appear in file 1")
            good_models2 += 1
            extra_models2 += 1


    print("File 1 has a total of", total_models1, "models.")
    print("Out of which,", good_models1, "exhibit VSP while", bad_models1, "do not.")
    print("File 1 has a total of", extra_models1, "which exhibit VSP but do not appear in file 2.")

    print("")
    print("File 2 has a total of", total_models2, "models")
    print("Out of which,", good_models2, "exhibit VSP while", bad_models2, "do not.")
    print("File 2 has a total of", extra_models2, "which exhibit VSP but do not appear in file 1.")
