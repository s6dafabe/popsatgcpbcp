"""
Base class for using Logic Formulas

"""
import math
import itertools
import numpy as np
import random

class LogicFormula:
    """
    This class essentially keeps track of the variable indices and the clauses of a cnf formula.
    It also provides a method to write the formula in DIMACS format
    """
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def addVar(self)->int:
        self.variables+=1

        return self.variables

    def addVars(self, n)->list:
        self.variables += n

        return list(range(self.variables-n,self.variables))

    def addClause(self, literals:list):
        self.clauses.append(literals)

    def addClauses(self, clauses:list):
        self.clauses += clauses
    def parseAsString(self):
        # Temporary edit: Randomize order of clauses to see if it changes performance
        shuffleClauses = False
        shuffleLiterals = False
        if shuffleClauses:
            random.shuffle(self.clauses)
        if shuffleLiterals:
            for c in self.clauses:
                random.shuffle(c)
        # ---------------------------------------------------------------------------
        return f"p cnf {self.variables} {len(self.clauses)}\n" \
               + "\n".join(" ".join(str(lit) for lit in clause)+" 0" for clause in self.clauses)

def bit_one(i,j):
    """
    Checks if the jth bit of number i is set to 1. Used for binary encodings
    """
    if i < (1<<(j-1)):
        return False

    return str(bin(i))[-j] == "1"

def at_least_1_const(vars:list, formula:LogicFormula):
    """
    at_least_1_const: single clause if at least one var is 1
    """
    formula.addClause(vars.copy())

def less_than_n(vars: list, formula: LogicFormula):
    """
    at_least_1_const: single clause if at least one var is 0
    """
    formula.addClause([-x for x in vars])

def card_enc_binominal(X:list,formula:LogicFormula,k:int):
    """
    binomial at-most-k encoding: for every subset of size k+1, at least one variable needs to be 0
    """
    formula.addClauses([list(map(lambda x:-x,I)) for I in itertools.combinations(X,k+1)])

def card_enc_sequential(X:list,formula:LogicFormula,k:int):
    """
    sequential at-most-k encoding, see:
    """
    n = len(X)
    R = {(i, j): formula.addVar() for i, j in itertools.product(range(n), range(k))}
    formula.addClauses([[-X[i],R[i,0]] for i in range(n-1)])
    formula.addClauses([[-R[0,j]] for j in range(1,k)])
    formula.addClauses([[-R[i-1,j],R[i,j]] for i,j in itertools.product(range(1,n-1),range(k))])
    formula.addClauses([[-X[i],-R[i - 1, j-1], R[i, j]] for i, j in itertools.product(range(1, n - 1), range(1,k))])
    formula.addClauses([[-X[i],-R[i-1,k-1]] for i in range(1,n)])

def card_enc_commander(X:list,formula:LogicFormula,k:int):
    """
    commander at-most-k encoding, see:
    """
    n = len(X)
    g = int(math.ceil(n/(k+2)))
    if n <= k*g:
        card_enc_sequential(X,formula,k)
        return
    C = {(i, j): formula.addVar() for i, j in itertools.product(range(g), range(k))}
    for i,G in enumerate(np.array_split(X,g)):
        group_vars = G.tolist()+[-C[i,j] for j in range(k)]
        card_enc_sequential(group_vars,formula,k)
        card_enc_sequential(list(map(lambda x:-x,group_vars)),formula,len(group_vars)-k)
        formula.addClauses([[-C[i,j],C[i,j+1]] for j in range(k-1)])
        card_enc_commander(list(C.values()),formula,k)


def card_enc_binary(vars:list, formula:LogicFormula,k:int):
    """
    binary at-most-k encoding, see:
    """
    n = len(vars)
    log_ceil = int(math.ceil(math.log(n, 2)))
    B = {(i, g): formula.addVar() for i, g in itertools.product(range(k), range(1, log_ceil + 1))}
    T = {(g, i): formula.addVar() for i, g in itertools.product(range(n), range(k))}
    for i, g, j in itertools.product(range(n), range(k), range(1, log_ceil + 1)):
        formula.addClause([-T[(g, i)], (1 if bit_one(i, j) else -1) * B[g, j]])

    for i in range(n):
        formula.addClause([-vars[i]] + [T[g, i] for g in range(k)])

def at_most_one(vars:list, formula:LogicFormula,encoding_type="sequential"):
    match encoding_type:
        case "sequential":
            return card_enc_sequential(vars,formula,1)
        case "binomial":
            return card_enc_binominal(vars, formula, 1)
        case "commander":
            return card_enc_commander(vars, formula, 1)
        case "binary":
            return card_enc_binary(vars, formula, 1)
        case "product":
            return product_amo(vars,formula)
        case "bimander":
            return bimander_amo(vars,formula)
def product_amo(vars:list, formula:LogicFormula):
    """
    product encoding, only implemented the at-most-1 encoding
    """
    n = len(vars)
    p = math.ceil(math.sqrt(n))
    q = math.ceil(n/p)
    U = [formula.addVar() for _ in range(p)]
    V = [formula.addVar() for _ in range(q)]
    card_enc_sequential(U,formula,1)
    card_enc_sequential(V, formula, 1)
    formula.addClauses(list(itertools.chain.from_iterable([[-x,U[i % p]],[-x,V[math.floor(i/p)]]] for i,x in enumerate(vars))))

def bimander_amo(vars:list,formula:LogicFormula):
    """
    bimander encoding, only implemented the at-most-1 encoding
    """
    n = len(vars)
    m = math.ceil(math.sqrt(n))
    B = [formula.addVar() for _ in range(int(math.ceil(math.log(m, 2))))]
    groups = np.array_split(vars,m)
    for i,G in enumerate(groups):
        card_enc_sequential(G,formula,1)
        for G_h,j in itertools.product(G,range(len(B))):
            formula.addClause([-G_h,(1 if bit_one(i,j+1) else -1)*B[j]])



def k_card_const(vars:list, formula:LogicFormula,k:int,atmost:bool,encoding_type="sequential"):
    """
    general cardinality encoding (at-least/at-most k)
    atmost=True means sum(vars) <= k is encoded, otherwise sum(vars) >= k is encoded
    """
    n = len(vars)
    if not atmost:
        k = n-k
        vars = list(map(lambda x: -x,vars))
    match encoding_type:
        case "sequential":
            return card_enc_sequential(vars,formula,k)
        case "binomial":
            return card_enc_binominal(vars, formula, k)
        case "commander":
            return card_enc_commander(vars, formula, k)
        case "binary":
            return card_enc_binary(vars, formula, k)











