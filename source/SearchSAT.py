"""
Functions to solve coloring problems using the SAT models
"""
import ModelsSAT as models
import subprocess
import SatParser as SatParser
import networkx as nx
import Utility as util
import time
import os
import random

def SATcoloring(model:models.ColoringModel,G:nx.Graph, H:int,lb:int, timeout:int = None,output = "SAT.cnf", parameters=None,seed=0):
    """
    Given a graph and a SAT-Model, finds an optimal coloring using binary search
    :param model: the SAT-Model used
    :param G: the colored graph
    :param H: an upper bound on the chromatic number
    :param lb: a lower bound on the chromatic number
    :param timeout: time limit
    :param output: output directory for the temporarily generated .cnf files used by the sat solver
    :return:
    """
    runtime = 0

    def solveSatFile():
        nonlocal runtime
        nonlocal timeout
        remaining = None
        if timeout is not None:
            remaining = timeout - runtime
        checkpoint = time.time()
        try:
            run = subprocess.run([os.path.join(os.path.dirname(__file__), "solver"), f"--seed={seed}", output],
                                 stdout=subprocess.PIPE, timeout=remaining)
            os.remove(output)
        except subprocess.TimeoutExpired:
            raise
        runtime += time.time() - checkpoint
        return run

    lowerLimit = lb
    upperLimit = H
    currentColoring = None
    
    print(H)
    while upperLimit - lowerLimit > 1:
        print(lowerLimit, upperLimit,flush=True)
        middle = lowerLimit + int((upperLimit - lowerLimit) / 2)
        timer = time.time()
        model.k_coloring_formula(G, middle,output=output)
        print(f"Time for Construction:{round(time.time() - timer, 3)}s")
        try:
            run = solveSatFile()
        except subprocess.TimeoutExpired:
            print(f"Timeout: Runtime exceeded {timeout} seconds",flush=True)
            model.lb,model.ub,model.runtime = lowerLimit,upperLimit,timeout
            return lowerLimit, upperLimit,currentColoring
        result = SatParser.parseSatResult(run.stdout.decode('utf-8'))
        if result is None:
            lowerLimit = middle
        else:
            upperLimit = middle
            currentColoring = model.coloring_from_vars(result)
    print(lowerLimit, upperLimit,flush=True)
    timer = time.time()
    model.k_coloring_formula(G, lowerLimit, output=output)
    print(f"Time for Construction:{round(time.time() - timer, 3)}s")
    try:
        run = solveSatFile()
    except subprocess.TimeoutExpired:
        print(f"Timeout: Runtime exceeded {timeout} seconds",flush=True)
        model.lb, model.ub, model.runtime = lowerLimit, upperLimit, timeout
        return lowerLimit, upperLimit,currentColoring
    result = SatParser.parseSatResult(run.stdout.decode('utf-8'))
    if result is not None:
        print("Runtime:", runtime,flush=True)
        model.lb, model.ub, model.runtime = lowerLimit, lowerLimit, runtime
        return model.coloring_from_vars(result)
    else:
        timer = time.time()
        model.k_coloring_formula(G, upperLimit, output=output)
        print(f"Time for Construction:{round(time.time() - timer, 3)}s")
        try:
            run = solveSatFile()
        except subprocess.TimeoutExpired:
            print(f"Timeout: Runtime exceeded {timeout} seconds")
            model.lb, model.ub, model.runtime = lowerLimit, upperLimit, timeout
            return lowerLimit, upperLimit,currentColoring
        result = SatParser.parseSatResult(run.stdout.decode('utf-8'))
        print("Runtime:", runtime,flush=True)
        model.lb, model.ub, model.runtime = upperLimit, upperLimit, runtime
        return model.coloring_from_vars(result)


def SATcoloringLinear(model: models.ColoringModel, G: nx.Graph, H: int, lb: int, timeout: int = None,
                output="SAT.cnf", parameters = None,seed=0):
    """
    Given a graph and a SAT-Model, finds an optimal equitable coloring using ascending linear search
    :param model: the SAT-Model used
    :param G: the colored graph
    :param H: an upper bound on the chromatic number
    :param lb: a lower bound on the chromatic number
    :param timeout: time limit
    :param output: output directory for the temporarily generated .cnf files used by the sat solver
    :return:
    """
    runtime = 0

    def solveSatFile():
        nonlocal runtime
        nonlocal timeout
        remaining = None
        if timeout is not None:
            remaining = timeout - runtime
        checkpoint = time.time()
        try:
            run = subprocess.run([os.path.join(os.path.dirname(__file__), "solver"), f"--seed={seed}", output],
                                 stdout=subprocess.PIPE, timeout=remaining)
        except subprocess.TimeoutExpired:
            raise
        runtime += time.time() - checkpoint
        return run

    print(H)
    for k in range(lb,H+1):
        print(k,flush=True)
        model.k_coloring_formula(G, k, output=output)
        try:
            run = solveSatFile()
        except subprocess.TimeoutExpired:
            print(f"Timeout: Runtime exceeded {timeout} seconds",flush=True)
            model.lb,model.ub,model.runtime = max(k-1,lb), H,timeout
            return max(k-1,lb), H,None
        result = SatParser.parseSatResult(run.stdout.decode('utf-8'))
        if result is not None:
            print("Runtime:", runtime,flush=True)
            model.runtime = runtime
            return model.coloring_from_vars(result)


def SATcoloringLinearDesceding(model: models.ColoringModel, G: nx.Graph, H: int, lb: int,timeout: int = None,
                output="SAT.cnf",seed=0):
    """
        Given a graph and a SAT-Model, finds an optimal equitable coloring using DESCENDING linear search
        (not in use, the idea was that finding a solution is easier than proving insatisfiability, but there did not
        seem to be a consistent performance improvement)
        :param model: the SAT-Model used
        :param G: the colored graph
        :param H: an upper bound on the chromatic number
        :param lb: a lower bound on the chromatic number
        :param timeout: time limit
        :param output: output directory for the temporarily generated .cnf files used by the sat solver
        :return:
        """
    runtime = 0

    def solveSatFile():
        nonlocal runtime
        nonlocal timeout
        remaining = None
        if timeout is not None:
            remaining = timeout - runtime
        checkpoint = time.time()
        try:
            run = subprocess.run([os.path.join(os.path.dirname(__file__), "solver"), f"--seed={seed}", output],
                                 stdout=subprocess.PIPE, timeout=remaining)
        except subprocess.TimeoutExpired:
            raise
        runtime += time.time() - checkpoint
        return run

    print(H)
    result = None
    for k in range(H,lb-1,-1):
        print(k)
        model.k_coloring_formula(G, k, output=output)

        try:
            run = solveSatFile()
        except subprocess.TimeoutExpired:
            print(f"Timeout: Runtime exceeded {timeout} seconds")
            model.lb,model.ub,model.runtime = max(k-1,lb), H,timeout
            return lb, k,result
        newResult = SatParser.parseSatResult(run.stdout.decode('utf-8'))
        if newResult is None:
            print("Runtime:", runtime)
            model.runtime = runtime
            return result
        result = model.coloring_from_vars(newResult)
    model.runtime = runtime
    print("Runtime:", runtime,flush=True)
    return result

def runSATModel(modConstruct:callable,G:nx.Graph, H:int,clq:list,parameters:dict = None, timeout:int = None,
                lb = 0,output = "SAT.cnf",seed=0) -> dict:
    """
    executes SAT-Model for coloring and collects results
    :param modConstruct: coloring model
    :param G: graph to color
    :param H: upper bound chrom.number
    :param clq: clique
    :param parameters: model parameters
    :param timeout: time limit
    :param lb: lower bound chrom. number
    :param output: output file for temporary .cnf files
    :return: dict of results of graph coloring (chromatic number, runtime, graph properties, etc)
    """
    output = str(random.randint(0,10000))+output    # make sure the file names are different (they should be but somehow it does not work)
    # setting up cliques
    if lb == 0: lb = len(clq)
    model = modConstruct(**parameters) if parameters is not None else modConstruct()
    model.setClique(clq)
    # Case distinction for equitable coloring
    if "search" in parameters and parameters["search"] == "binary":
        col = SATcoloring(model, G,H,lb,parameters=parameters, timeout=timeout,output=output,seed=seed)
    else:
        if "search" in parameters and parameters["search"] == "descending":
            col = SATcoloringLinearDesceding(model, G,H,lb,parameters=parameters, timeout=timeout,output=output,seed=seed)
        else:
            col = SATcoloringLinear(model, G,H,lb,parameters=parameters, timeout=timeout,output=output,seed=seed)
    #clean up
    if os.path.exists(output):
        os.remove(output)
    #if coloring returned, parse it, otherwise return lower/upper bounds
    if type(col) == tuple:
        lower, upper = model.lb,model.ub
        if col[2] is not None:
            if not util.checkColoringEq(G,col[2]):
                print(col)
                raise Exception("Not a Coloring")
    else:
        if not util.checkColoringEq(G,col):
            print(col)
            raise Exception("Not a Coloring")
        lower = upper = max(col.keys())+1

    n = G.number_of_nodes()
    m = G.number_of_edges()
    if parameters is None or len(parameters) == 0:
        parameter_string = "-"
    else:
        parameter_string = ",".join(":".join((name, str(val))) for name, val in parameters.items() if name != "q")
    return {
        "model": model.type+"-SAT",
        "parameters": parameter_string,
        "nodes": n,
        "edges": m,
        "density": round(m / ((n * (n - 1)) / 2),6),
        "heuristic": H,
        "max_clique": len(clq),
        "max_degree": max(G.degree, key=lambda x: x[1])[1] + 1,
        "upper_bound":  upper,
        "lower_bound": lower,
        "runtime": round(model.runtime,6),
    }

def runSATModelBCP(modConstruct:callable,G:nx.Graph, H:int,parameters:dict = None, timeout:int = None,lb = 0,
                   output = "SAT.cnf",seed=0):
    """
       executes SAT-Model for coloring and collects results
       :param modConstruct: coloring model
       :param G: graph to color
       :param H: upper bound chrom.number
       :param clq: clique
       :param parameters: model parameters
       :param timeout: time limit
       :param lb: lower bound chrom. number
       :param output: output file for temporary .cnf files
       :return: dict of results of graph coloring (chromatic number, runtime, graph properties, etc)
       """
    output = str(random.randint(0,10000))+output    # make sure the file names are different (they should be but somehow it does not work)

    model = modConstruct(**parameters) if parameters is not None else modConstruct()
    if parameters is not None and "search" in parameters:
        match parameters["search"]:
            case "ascending":
                col = SATcoloringLinear(model, G, H, lb, timeout=timeout, output=output, seed=seed)
            case "descending":
                col = SATcoloringLinearDesceding(model, G, H, lb, timeout=timeout, output=output, seed=seed)
            case _:
                col = SATcoloring(model, G, H, lb, timeout=timeout, output=output)
    else:
        col = SATcoloring(model, G, H, lb, timeout=timeout, output=output)
    #clean up
    if os.path.exists(output):
        os.remove(output)
    #if coloring returned, parse it, otherwise return lower/upper bounds
    if type(col) == tuple:
        lower, upper = model.lb,model.ub
        if col[2] is not None:
            if not util.checkColoringBCP(G,col[2]):
                print(col)
                raise Exception("Not a Coloring")
    else:
        if not util.checkColoringBCP(G,col):
            print(col)
            raise Exception("Not a Coloring")
        lower = upper = max(col.keys())+1

    n = G.number_of_nodes()
    m = G.number_of_edges()
    if parameters is None or len(parameters) == 0:
        parameter_string = "-"
    else:
        parameter_string = ",".join(":".join((name, str(val))) for name, val in parameters.items() if name != "q")
    return {
        "model": model.type+"-SAT",
        "parameters": parameter_string,
        "nodes": n,
        "edges": m,
        "density": round(m / ((n * (n - 1)) / 2),6),
        "heuristic": H,
        "max_clique": lb,
        "max_degree": max(G.degree, key=lambda x: x[1])[1] + 1,
        "upper_bound":  upper,
        "lower_bound": lower,
        "runtime": round(model.runtime,6),
    }

def solveFormula(formula:str):
    """
    Simple function so solve a logic formula using the external sat-solver. Used for debugging
    :param formula: the formula
    :return:
    """
    with open("SAT.cnf", "w") as f:
        f.write(formula)
    run = subprocess.run([os.path.join(os.path.dirname(__file__), "solver"), 'SAT.cnf'], stdout=subprocess.PIPE)
    result = SatParser.parseSatResult(run.stdout.decode('utf-8'))
    return result
