#!/usr/bin/env python3
"""
Experimental Runner file to find the signed variable sharing property
"""


from datetime import datetime
from typing import Dict, Iterator, Optional, Tuple
from queue import Empty as QueueEmpty
import argparse
import multiprocessing as mp

from logic import Negation, Implication, Operation, Conjunction, Disjunction
from model import Model, ModelFunction
from parse_magic import SourceFile, parse_matrices
from vsp import has_svsp, SVSP_Result

def print_with_timestamp(message):
    current_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{current_time}] {message}", flush=True)

def restructure_solutions(solutions: Iterator[Tuple[Model, Dict[Operation, ModelFunction]]], skip_to: Optional[str]) -> \
    Iterator[Tuple[Model, ModelFunction, Optional[ModelFunction], Optional[ModelFunction], Optional[ModelFunction]]]:
    """
    When subprocess gets spawned, the logical operations will
    have a different memory address than what's expected in interpretation.
    Therefore, we need to pass the model functions directly instead.

    While we're at it, filter out models until we get to --skip-to
    if applicable.
    """
    start_processing = skip_to is None
    for model, interpretation in solutions:
        # If skip_to is defined, then don't process models
        # until then.
        if not start_processing and model.name != skip_to:
            continue
        start_processing = True

        # NOTE: Implication must be defined, the rest may not
        impfunction = interpretation[Implication]
        conjfn = interpretation.get(Conjunction)
        disjfn = interpretation.get(Disjunction)
        negfn = interpretation.get(Negation)
        yield (model, impfunction, conjfn, disjfn, negfn)

def has_svsp_plus_model(model, impfn, conjfn, disjfn, negfn) -> Tuple[Optional[Model], SVSP_Result]:
    """
    Wrapper which also stores the models along with its vsp result
    """
    svsp_result = has_svsp(model, impfn, conjfn, disjfn, negfn)
    # NOTE: Memory optimization - Don't return model if it doesn't have SVSP
    model = model if svsp_result.has_svsp else None
    return (model, svsp_result)

def worker_vsp(task_queue: mp.Queue, result_queue: mp.Queue):
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
                break
            (model, impfn, conjfn, disjfn, negfn) = task
            result = has_svsp_plus_model(model, impfn, conjfn, disjfn, negfn)
            result_queue.put(result)
    finally:
        # Either an exception occured or the worker finished
        # Push sentinal value
        result_queue.put(None)

def worker_parser(data_file_path: str, num_sentinal_values: int, task_queue: mp.Queue, skip_to: Optional[str]):
    """
    Function which parses the MaGIC file
    and adds models to the task_queue.

    Intended to be deployed with a dedicated process.
    """
    try:
        data_file = open(data_file_path, "r")
        solutions = parse_matrices(SourceFile(data_file))
        solutions = restructure_solutions(solutions, skip_to)

        while True:
            try:
                item = next(solutions)
                task_queue.put(item)
            except StopIteration:
                break
    finally:
        data_file.close()
        for _ in range(num_sentinal_values):
            task_queue.put(None)

def multi_process_runner(num_cpu: int, data_file_path: str, skip_to: Optional[str]):
    """
    Run SVSPursuer in a multi-process configuration.
    """
    assert num_cpu > 1

    num_tested = 0
    num_has_svsp = 0
    num_workers = num_cpu - 1

    # Create queues
    task_queue = mp.Queue(maxsize=1000)
    result_queue = mp.Queue()

    # Create dedicated process to parse the MaGIC file
    process_parser = mp.Process(target=worker_parser, args=(data_file_path, num_workers, task_queue, skip_to))
    process_parser.start()

    # Create dedicated processes which check SVSP
    process_workers = []
    for _ in range(num_workers):
        p = mp.Process(target=worker_vsp, args=(task_queue, result_queue))
        process_workers.append(p)
        p.start()


    # Check results and add new tasks until finished
    result_sentinal_count = 0
    while True:
        # Read a result
        try:
            result = result_queue.get(True, 60)
        except QueueEmpty:
            if all((not p.is_alive() for p in process_workers)):
                # All workers finished without us receiving all the
                # sentinal values.
                break

            task_queue_size = 0
            try:
                task_queue_size = task_queue.qsize()
            except NotImplementedError:
                # MacOS doesn't implement this
                pass

            if task_queue_size == 0 and not process_parser.is_alive():
                # For Linux/Windows this means that the process_parser
                # died before sending the sentinal values.
                # For Mac, this doesn't guarentee anything but might
                # as well push more sentinal values.
                for _ in range(num_workers):
                    task_queue.put(None)

            # Don't do anymore work, wait again for a result
            continue


        # When we receive None, it means a child process has finished
        if result is None:
            result_sentinal_count += 1
            # If all workers have finished break
            if result_sentinal_count == len(process_workers):
                break
            continue

        # Process result
        model, vsp_result = result
        print_with_timestamp(vsp_result)
        num_tested += 1

        if vsp_result.has_svsp:
            print(model)

        if vsp_result.has_svsp:
            num_has_svsp += 1

    print_with_timestamp(f"Tested {num_tested} models, {num_has_svsp} of which satisfy SVSP")

def single_process_runner(data_file_path: str, skip_to: Optional[str]):
    num_tested = 0
    num_has_svsp = 0

    data_file = open(data_file_path, "r")
    solutions = parse_matrices(SourceFile(data_file))
    solutions = restructure_solutions(solutions, skip_to)

    for model, impfn, conjfn, disjfn, negfn in solutions:
        model, svsp_result = has_svsp_plus_model(model, impfn, conjfn, disjfn, negfn)
        print_with_timestamp(svsp_result)
        num_tested += 1

        if svsp_result.has_svsp:
            print(model)

        if svsp_result.has_svsp:
            num_has_svsp += 1

    print_with_timestamp(f"Tested {num_tested} models, {num_has_svsp} of which satisfy SVSP")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="SVSP Checker")
    parser.add_argument("--verbose", action='store_true', help="Print out all parsed matrices")
    parser.add_argument("-i", type=str, help="Path to MaGIC ugly data file")
    parser.add_argument("-c", type=int, help="Number of CPUs to use. Default: 1")
    parser.add_argument("--skip-to", type=str, help="Skip until a model name is found and process from then onwards.")
    args = vars(parser.parse_args())

    data_file_path = args.get("i")
    if data_file_path is None:
        data_file_path = input("Path to MaGIC Ugly Data File: ")

    num_cpu = args.get("c")
    if num_cpu is None:
        num_cpu = 1

    if num_cpu == 1:
        single_process_runner(data_file_path, args.get("skip_to"))
    else:
        multi_process_runner(num_cpu, data_file_path, args.get("skip_to"))
