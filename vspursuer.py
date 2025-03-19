#!/usr/bin/env python3

# NOTE: Perhaps we should use process_cpu_count but that's not available to all Python versions
from os import cpu_count
from time import sleep
from typing import Dict, Iterator, Optional, Tuple
import argparse
import multiprocessing as mp

from logic import Conjunction, Disjunction, Negation, Implication, Operation
from model import Model, ModelFunction
from parse_magic import SourceFile, parse_matrices
from vsp import has_vsp

def restructure_solutions(solutions: Iterator[Tuple[Model, Dict[Operation, ModelFunction]]], args) -> \
    Iterator[Tuple[Model, ModelFunction, Optional[ModelFunction], Optional[ModelFunction], Optional[ModelFunction]]]:
    """
    When subprocess gets spawned, the logical operations will
    have a different memory address than what's expected in interpretation.
    Therefore, we need to pass the model functions directly instead.

    While we're at it, filter out models until we get to --skip-to
    if applicable.
    """
    start_processing = args.get("skip_to") is None
    for model, interpretation in solutions:
        # If skip_to is defined, then don't process models
        # until then.
        if not start_processing and model.name == args.get("skip_to"):
            start_processing = True
        if not start_processing:
            continue
        impfunction = interpretation[Implication]
        mconjunction = interpretation.get(Conjunction)
        mdisjunction = interpretation.get(Disjunction)
        mnegation = interpretation.get(Negation)
        yield (model, impfunction, mconjunction, mdisjunction, mnegation)

def has_vsp_plus_model(model, impfunction, mconjunction, mdisjunction, mnegation):
    """
    Wrapper so that we can save the model that satisfies VSP.
    NOTE: At the time of writing, models that don't satisfy VSP
    get discarded from memory for efficiency sake.
    """
    vsp_result = has_vsp(model, impfunction, mconjunction, mdisjunction, mnegation)
    if vsp_result.has_vsp:
        return (model, vsp_result)
    return (None, vsp_result)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="VSP Checker")
    parser.add_argument("--verbose", action='store_true', help="Print out all parsed matrices")
    parser.add_argument("-i", type=str, help="Path to MaGIC ugly data file")
    parser.add_argument("-c", type=int, help="Number of CPUs to use. Default: MAX - 2.")
    parser.add_argument("--skip-to", type=str, help="Skip until a model name is found and process from then onwards.")
    args = vars(parser.parse_args())

    data_file_path = args.get("i")
    if data_file_path is None:
        data_file_path = input("Path to MaGIC Ugly Data File: ")

    data_file = open(data_file_path, "r")

    solutions = parse_matrices(SourceFile(data_file))
    solutions = restructure_solutions(solutions, args)

    num_cpu = args.get("c")
    if num_cpu is None:
        num_cpu = max(cpu_count() - 2, 1)

    # Set up parallel verification
    num_tested = 0
    num_has_vsp = 0
    with mp.Pool(processes=num_cpu) as pool:
        task_pool = []
        done_parsing = False

        # Populate initial task pool
        for _ in range(num_cpu):
            try:
                model, impfunction, mconjunction, mdisjunction, mnegation = next(solutions)
            except StopIteration:
                done_parsing = True
                break
            result_async = pool.apply_async(has_vsp_plus_model, (model, impfunction, mconjunction, mdisjunction, mnegation))
            task_pool.append(result_async)

        while len(task_pool) > 0:
            next_task_pool = []
            # Check the status of all the tasks, and spawn
            # new ones if finished
            for result_async in task_pool:
                if result_async.ready():
                    model, vsp_result = result_async.get()
                    print(vsp_result)
                    num_tested += 1

                    if args['verbose'] or vsp_result.has_vsp:
                        print(model)

                    if vsp_result.has_vsp:
                        num_has_vsp += 1

                    if done_parsing:
                        continue

                    # Submit new task if available
                    try:
                        model, impfunction, mconjunction, mdisjunction, mnegation = next(solutions)
                        next_result_async = pool.apply_async(has_vsp_plus_model, (model, impfunction, mconjunction, mdisjunction, mnegation))
                        next_task_pool.append(next_result_async)
                    except StopIteration:
                        done_parsing = True
                else:
                    # Otherwise the task is still working,
                    # add it to the next task pool
                    next_task_pool.append(result_async)
            task_pool = next_task_pool
            sleep(0.01)

    print(f"Tested {num_tested} models, {num_has_vsp} of which satisfy VSP")

    data_file.close()
