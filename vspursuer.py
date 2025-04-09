#!/usr/bin/env python3

# NOTE: Perhaps we should use process_cpu_count but that's not available to all Python versions
from os import cpu_count
from typing import Dict, Iterator, Optional, Tuple
from queue import Empty as QueueEmpty
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
    Wrapper which also stores the models along with its vsp result
    """
    vsp_result = has_vsp(model, impfunction, mconjunction, mdisjunction, mnegation)
    return (model, vsp_result)

def worker(task_queue, result_queue):
    """
    Worker process which processes models from the task
    queue and adds the result to the result_queue.

    Adds the sentinal value None when exception occurs and when there's
    no more to process.
    """
    try:
        while True:
            task = task_queue.get()
            # If sentinal value, break
            if task is None:
                result_queue.put(None)
                break
            (model, impfunction, mconjunction, mdisjunction, mnegation) = task
            result = has_vsp_plus_model(model, impfunction, mconjunction, mdisjunction, mnegation)
            result_queue.put(result)
    except Exception:
        # Process failed somehow, push sentinal value
        result_queue.put(None)

def add_to_queue(gen, queue, num_sentinal_values) -> bool:
    """
    Consumes an item from gen and puts
    it in the queue.

    If there are no items left in gen,
    return false and send sentinal values,
    otherwise true.
    """
    try:
        item = next(gen)
        queue.put(item)
        return True
    except StopIteration:
        for _ in range(num_sentinal_values):
            queue.put(None)
        return False


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

    # Create queues
    task_queue = mp.Queue()
    result_queue = mp.Queue()

    # Create worker processes
    processes = []
    for _ in range(num_cpu):
        p = mp.Process(target=worker, args=(task_queue, result_queue))
        processes.append(p)
        p.start()

    # Populate initial task queue
    # NOTE: Adding more than number of processes
    # to make sure there's always work to do.
    done_parsing = False
    for _ in range(num_cpu * 2):
        added = add_to_queue(solutions, task_queue, num_cpu)
        if not added:
            done_parsing = True
            break

    # Check results and add new tasks until finished
    result_sentinal_count = 0
    while True:

        # Read a result
        try:
            result = result_queue.get(True, 60)
        except QueueEmpty:
            # Health check in case processes crashed
            num_dead = 0 
            for p in processes:
                if not p.is_alive():
                    num_dead += 1
            if num_dead == len(processes):
                print("[ERROR] No child processes remain")
                break
            elif num_dead > 0:
                print("[WARNING] Number of dead processes:", num_dead)
            # Otherwise continue
            continue

        # When we receive None, it means a child process has finished
        if result is None:
            result_sentinal_count += 1
            # If all workers have finished break
            if result_sentinal_count == num_cpu:
                break
            continue

        # Process result
        model, vsp_result = result
        print(vsp_result)
        num_tested += 1

        if vsp_result.has_vsp:
            print(model)

        if vsp_result.has_vsp:
            num_has_vsp += 1

        # Submit new task if available
        if done_parsing:
            continue

        added = add_to_queue(solutions, task_queue, num_cpu)
        if not added:
            done_parsing = True


    print(f"Tested {num_tested} models, {num_has_vsp} of which satisfy VSP")

    data_file.close()
