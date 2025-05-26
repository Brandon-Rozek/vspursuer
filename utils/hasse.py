"""
Given a model, create a Hasse diagram.

Note: This has a dependency on the hasse-diagram library
https://pypi.org/project/hasse-diagram/
"""
import argparse
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from model import Model
from parse_magic import SourceFile, parse_matrices

import numpy as np
import hassediagram

__all__ = ['plot_model_hassee']

def plot_model_hassee(model: Model):
    assert model.ordering is not None
    carrier_list = list(model.carrier_set)
    hasse_ordering = []
    for elem1 in carrier_list:
        elem_ordering = []
        for elem2 in carrier_list:
            elem_ordering.append(
                1 if model.ordering.is_lt(elem1, elem2) else 0
            )
        hasse_ordering.append(elem_ordering)
    hassediagram.plot_hasse(np.array(hasse_ordering), carrier_list)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Show hassee diagram for model")
    parser.add_argument("uglyfile", type=str, help="Path to ugly data file")
    parser.add_argument("modelname", type=str, help="Name of model within file")
    args = vars(parser.parse_args())

    data_file = open(args['uglyfile'], "r")
    solutions = parse_matrices(SourceFile(data_file))

    requested_model = None

    for model, _ in solutions:
        if model.name == args['modelname']:
            requested_model = model
            break

    if requested_model is None:
        print("Model name", args['modelname'], "not found.")
        sys.exit(0)

    plot_model_hassee(requested_model)
