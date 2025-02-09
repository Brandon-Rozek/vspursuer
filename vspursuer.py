#!/usr/bin/env python3
from os import cpu_count
import argparse
import multiprocessing as mp

from logic import Conjunction, Disjunction, Implication
from parse_magic import SourceFile, parse_matrices
from vsp import has_vsp, VSP_Result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="VSP Checker")
    parser.add_argument("--verbose", action='store_true', help="Print out all parsed matrices")
    parser.add_argument("-i", type=str, help="Path to MaGIC ugly data file")
    parser.add_argument("-c", type=int, help="Number of CPUs to use. Default: MAX - 2.")
    args = vars(parser.parse_args())

    data_file_path = args.get("i")
    if data_file_path is None:
        data_file_path = input("Path to MaGIC Ugly Data File: ")

    solutions = []
    with open(data_file_path, "r") as data_file:
        solutions = parse_matrices(SourceFile(data_file))
    print(f"Parsed {len(solutions)} matrices")

    # NOTE: When subprocess gets spawned, the logical operations will
    # have a different memory address than what's expected in interpretation.
    # This will make it so that we can pass the model functions directly instead.
    solutions_expanded = []
    for model, interpretation in solutions:
        impfunction = interpretation[Implication]
        mconjunction = interpretation.get(Conjunction)
        mdisjunction = interpretation.get(Disjunction)
        solutions_expanded.append((model, impfunction, mconjunction, mdisjunction))

    num_has_vsp = 0
    num_cpu = args.get("c", max(cpu_count() - 2, 1))
    with mp.Pool(processes=num_cpu) as pool:
        results = [
            pool.apply_async(has_vsp, (model, impfunction, mconjunction, mdisjunction,))
            for model, impfunction, mconjunction, mdisjunction in solutions_expanded
        ]

        for i, result in enumerate(results):
            vsp_result: VSP_Result = result.get()
            print(vsp_result)

            if args['verbose'] or vsp_result.has_vsp:
                model = solutions[i][0]
                print(model)

            if vsp_result.has_vsp:
                num_has_vsp += 1

    print(f"Tested {len(solutions)} models, {num_has_vsp} of which satisfy VSP")
