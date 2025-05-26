"""
Print a model given it's name
and ugly data file
"""
import argparse
import os
import sys
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from parse_magic import SourceFile, parse_matrices

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Show hassee diagram for model")
    parser.add_argument("uglyfile", type=str, help="Path to ugly data file")
    parser.add_argument("modelname", type=str, help="Name of model within file")
    args = vars(parser.parse_args())

    data_file = open(args['uglyfile'], "r")
    solutions = parse_matrices(SourceFile(data_file))

    model_found = False

    for model, _ in solutions:
        if model.name == args['modelname']:
            model_found = True
            print(model)
            break
    
    if not model_found:
        print("Model", args['modelname'], "not found.")
