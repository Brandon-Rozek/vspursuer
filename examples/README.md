# Example Ugly Data Format Files

These are example files that you can use with the `parse_magic.py` script.

## R6

Contains all models of R up to size 6.

## R4-MN

Contains all models of a fragment of R without negation up to size 4.

## R3-PN

Extends R to have necessitation with the following additional axioms:

1) p / !p
2) !(p -> q) -> (!p -> !q)
3) (!p & !q) -> !(p & q)

Output contains all satisfiable models up to size 3.

## R5-S5

Extends R with axioms that classically are adequate for S5 giving rise to an R-ish version of S5 with necessitation.

