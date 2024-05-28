from typing import Set, Tuple
from functools import lru_cache

class Operation:
    def __init__(self, symbol: str, arity: int):
        self.symbol = symbol
        self.arity = arity
        self.hashed_value = hash(self.symbol) + self.arity
        def immutable(self, name, value):
            raise Exception("Operations are immutable")
        self.__setattr__ = immutable
    
    def __hash__(self):
        return self.hashed_value
    
    def __call__(self, *args):
        # Ensure the arity is met
        assert len(args) == self.arity
        # Ensure every argument is a term
        for t in args:
            assert isinstance(t, Term)
        return OpTerm(self, args)
        

class Term:
    def __init__(self):
        pass
    def __lt__(self, y):
        return Inequation(self, y)

class PropositionalVariable(Term):
    def __init__(self, name):
        self.name = name
        self.hashed_value = hash(self.name)
        def immutable(self, name, value):
            raise Exception("Propositional variables are immutable")
        self.__setattr__ = immutable
    
    def __hash__(self):
        return self.hashed_value

    def __str__(self):
        return self.name


class OpTerm(Term):
    def __init__(self, operation: Operation, arguments):
        assert len(arguments) == operation.arity
        self.operation = operation
        self.arguments = arguments

        self.hashed_value = hash(self.operation) * hash(self.arguments)
        def immutable(self, name, value):
            raise Exception("Terms are immutable")
        self.__setattr__ = immutable
    
    def __hash__(self):
        return self.hashed_value
    
    def __str__(self):
        arg_strs = [str(a) for a in self.arguments]
        return self.operation.symbol + "(" + ",".join(arg_strs) + ")"

# Standard operators
Negation = Operation("¬", 1)
Conjunction = Operation("∧", 2)
Disjunction = Operation("∨", 2)
Implication = Operation("→", 2)

class Inequation:
    def __init__(self, antecedant : Term, consequent: Term):
        self.antecedant = antecedant
        self.consequent = consequent
    def __str__(self):
        return str(self.antecedant) + "≤" + str(self.consequent) 

class InequalityRule:
    def __init__(self, premises : Set[Inequation], conclusion: Inequation):
        self.premises = premises
        self.conclusion = conclusion
    
    def __str__(self):
        str_premises = [str(p) for p in self.premises]
        str_premises2 = "{" + ",".join(str_premises) + "}"
        return str(str_premises2) + "=>" + str(self.conclusion)

class Rule:
    def __init__(self, premises : Set[Term], conclusion: Term):
        self.premises = premises
        self.conclusion = conclusion
    
    def __str__(self):
        str_premises = [str(p) for p in self.premises]
        str_premises2 = "{" + ",".join(str_premises) + "}"
        return str(str_premises2) + "=>" + str(self.conclusion)

class Logic:
    def __init__(self, operations: Set[Operation], rules: Set[Rule]):
        self.operations = operations
        self.rules = rules


def get_prop_var_from_term(t: Term) -> Set[PropositionalVariable]:
    if isinstance(t, PropositionalVariable):
        return {t,}

    result: Set[PropositionalVariable] = set()
    for arg in t.arguments:
        result |= get_prop_var_from_term(arg)
    
    return result

@lru_cache
def get_propostional_variables(rules: Tuple[Rule]) -> Set[PropositionalVariable]:
    vars: Set[PropositionalVariable] = set()

    for rule in rules:
        # Get all vars in premises
        for premise in rule.premises:
            vars |= get_prop_var_from_term(premise)
    
        # Get vars in conclusion
        vars |= get_prop_var_from_term(rule.conclusion)

    return vars

def get_operations_from_term(t: Term) -> Set[Operation]:
    if isinstance(t, PropositionalVariable):
        return set()
    
    result: Set[Operation] = {t.operation,}
    for arg in t.arguments:
        result |= get_operations_from_term(arg)
    
    return result
