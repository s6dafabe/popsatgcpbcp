import networkx as nx
import Preprocessing as Preprocessing
import Utility as Utility
import ModelsILP as ILP
import Heuristiken as heur
import SearchSAT as search
import ModelsSAT as SAT
import time

def runModel(model:callable,G:nx.Graph, H:int,clq:list,parameters:dict, m_attributes:dict = None) -> dict:

    M, var, *other = model(G, H, **parameters)
    Preprocessing.precolorCliqueILP(M, var, clq)
    M.setParam("TimeLimit", 3600)
    M.setParam("Seed", 0)
    M.setParam("Threads", 1)

    if m_attributes is not None:
        for key, value in m_attributes.items():
            M.setParam(key, value if not value.isnumeric() else int(value))
    M.optimize()
    n = G.number_of_nodes()
    m = G.number_of_edges()

    if M.SolCount > 0: 
        coloring = Utility.getColoringFromModel(M,var)
        if not Utility.checkColoringEq(G,coloring):
            raise Exception("Not an", "equitable" if M._eq else "","Coloring")
    return{
        "model": M.getAttr("ModelName"),
        "parameters": ",".join(":".join((name,str(val))) for name,val in parameters.items() if name != "q" and name !="lowBound"),
        "nodes": n,
        "edges": m,
        "density": round(m / ((n * (n - 1)) / 2),6),
        "heuristic": H,
        "max_clique": len(clq),
        "max_degree": max(G.degree, key=lambda x: x[1])[1] + 1,
        "upper_bound": M.getAttr("ObjVal"),
        "lower_bound": M.getAttr("ObjBound"),
        "runtime": round(M.getAttr("Runtime"),6),
        "bbnodes": M.getAttr("NodeCount"),
        "simplex_it": M.getAttr("IterCount")
    }

def runModelBCP(model:callable,G:nx.Graph, H:int,clq:list,parameters:dict, m_attributes:dict = None) -> dict:

    M, var, *other = model(G, H, **parameters)
    M.setParam("TimeLimit", 3600)
    M.setParam("Seed", 0)
    M.setParam("Threads", 1)

    if m_attributes is not None:
        for key, value in m_attributes.items():
            M.setParam(key, value if not value.isnumeric() else int(value))
    M.optimize()
    n = G.number_of_nodes()
    m = G.number_of_edges()

    if M.SolCount > 0:
        coloring = Utility.getColoringFromModel(M,var)
        if not Utility.checkColoringEq(G,coloring):
            raise Exception("Not an Coloring")
    return{
        "model": M.getAttr("ModelName"),
        "parameters": ",".join(":".join((name,str(val))) for name,val in parameters.items() if name != "q" and name !="lowBound"),
        "nodes": n,
        "edges": m,
        "density": round(m / ((n * (n - 1)) / 2),6),
        "heuristic": H,
        "max_clique": len(clq),
        "max_degree": max(G.degree, key=lambda x: x[1])[1] + 1,
        "upper_bound": M.getAttr("ObjVal"),
        "lower_bound": M.getAttr("ObjBound"),
        "runtime": round(M.getAttr("Runtime"),6),
        "bbnodes": M.getAttr("NodeCount"),
        "simplex_it": M.getAttr("IterCount")
    }

#Dies ist eine Methode zum Testen von verschiedenen Modellvarianten eines Modells auf einen Graphen
def GraphTester(modelList:list,G:nx.graph,m_attributes = None,parameters:list = None,clq = None,thread = "0") -> list:
    modelMap = {
        "ASS":ILP.createASS,
        "POP":ILP.createPOP,
        "POPHyb":ILP.createPOPHyb,
    }
    modelMapSAT = {
        "ASS_SAT": SAT.ASS_SAT,
        "POP_SAT": SAT.POP_SAT,
        "POPHyb_SAT": SAT.POPHyb_SAT,
    }
    results = []
    containsEquit = False

    timer = time.time()
    print("Caclulate heuristic solution",flush=True)
    H = heur.UpperBoundFJK2(G) if containsEquit else heur.UpperBoundDsatur(G)
    print(H)
    print(f"Time for heuristic:{round(time.time()-timer,3)}s")
    timer = time.time()
    print("Calculate Clique Bound",flush=True)
    if clq is None:
        cl,clRep = Preprocessing.maxCutClique(G,H)
    else:
        cl = clq
        clRep = clq
    # Data Reduction for Vertex Coloring
    print(f"Time for Clique:{round(time.time() - timer, 3)}s")
    timer = time.time()
    if not containsEquit:
        print("Graph reduction",flush=True)
        G = Preprocessing.graphReduction(G,len(clRep),clRep+cl)
        # Indices of vertices in graph and clique need to be fixed after removing vertices
        indexMapping = {v:i for i,v in enumerate(G.nodes())}
        G = nx.relabel_nodes(G,indexMapping)
        Preprocessing.remapVertices(clRep, indexMapping)
        Preprocessing.remapVertices(cl, indexMapping)
    GRep, clRep = Preprocessing.relabelModel(G, clRep, H, POP=False)
    G, cl = Preprocessing.relabelModel(G, cl, H, POP=False)
    H = heur.UpperBoundFJK2(G) if containsEquit else heur.UpperBoundDsatur(G) # Need upper bound on new graph
    print(f"Time for Relabeling/Reduction:{round(time.time() - timer, 3)}s")
    print("Construct Model",flush=True)
    for i,MStr in enumerate(modelList):
        # Memory cap for rep model
        if MStr[:3] == "REP":
            complG = nx.complement(G)
            num_const = sum(nx.subgraph(G,complG.neighbors(u)).number_of_edges() for u in G.nodes())
            if num_const > 2E8 or complG.number_of_edges()> 1E8:
                results.append(None)
                print("Instance too large, skipped")
                continue
        else:
            if G.number_of_edges() > 1000000:
                print("Instance too large, skipped")
                continue
        if MStr[-4:] == "_SAT":
            if "Clique" in m_attributes and m_attributes["Clique"] == "largest":
                G,cl = GRep, clRep
            result = search.runSATModel(modelMapSAT[MStr],
                                             G=G, H=H, clq=cl, timeout = int(m_attributes.get("TimeLimit")),
                                             lb=len(clRep),parameters=parameters[i],
                                             output = f"SAT_{thread}.cnf",seed = m_attributes["Seed"] if "Seed" in m_attributes else 0)
        else:
            if "LogFile" in m_attributes:
                m_attributes["LogFile"] += MStr + ".lg"
            model_params = {}
            if MStr == "POP" or MStr == "POPHyb":
                model_params = dict(q=cl[-1],strength = "false",symm = "none", equitConst = 'none',branching='-',lowBound=len(cl)-1)
                if "symm" in parameters[i] and parameters[i]["symm"] == "strong":
                    model_params["q"] = G.number_of_nodes()
                    model_params["lowBound"] = len(cl)
            if MStr == "REP":
                model_params = dict(symm = True,lowBound = len(clRep))
                cl = clRep
                G = GRep
            if MStr == "ASS":
                model_params = dict(symm="none",equitConst='none',branching='-',lowBound=len(cl))
            if parameters is not None and len(parameters) > i:
                model_params.update(parameters[i])

            result = runModel(modelMap[MStr],G,H,cl,model_params,m_attributes)

        results.append(result)

    return results

def GraphTesterBandwidth(modelList:list,G:nx.graph,m_attributes = None,parameters:list = None,clq = None,thread = "0") -> list:
    modelMap = {
        "ASS_BCP": ILP.createASSBCP,
        "POP_BCP": ILP.createPOPBCP,
        "POPHyb_BCP": ILP.createPOPHybBCP,
    }

    modelMapSAT = {
        "ASS_BCP_SAT": SAT.ASS_SAT_BCP,
        "POP_BCP_SAT": SAT.POP_SAT_BCP,
        "POPHyb_BCP_SAT": SAT.POPHyb_SAT_BCP,
    }

    results = []
    H = heur.DSaturBandwidth(G)
    if clq is None:
        cl,clRep = Preprocessing.maxCutClique(G,H)
    else:
        cl = clq
        clRep = clq

    print(H)
    # Data Reduction for Vertex Coloring

    print("Construct Model")
    for i,MStr in enumerate(modelList):

        if MStr[-4:] == "_SAT":
            result = search.runSATModelBCP(modelMapSAT[MStr],
                                                 G=G, H=H, timeout = int(m_attributes.get("TimeLimit")),
                                                 lb=len(clRep),parameters=parameters[i], #if len(parameters) > i else None,
                                                 output = f"SAT_{thread}.cnf")
        else:
            result = runModelBCP(modelMap[MStr],G,H,clRep,parameters[i],m_attributes)
        results.append(result)

    return results


def paperModelsGCP(model:str,G:nx.graph,timeout:int = 3600) -> dict|None:

    results = []

    timer = time.time()
    print("Caclulate heuristic solution", flush=True)
    H = heur.UpperBoundDsatur(G)
    print(H)
    print(f"Time for heuristic:{round(time.time() - timer, 3)}s")
    timer = time.time()
    print("Calculate Clique Bound", flush=True)

    _,cl = Preprocessing.maxCutClique(G, H)

    # Data Reduction for Vertex Coloring
    print(f"Time for Clique:{round(time.time() - timer, 3)}s")
    timer = time.time()

    print("Graph reduction", flush=True)
    G = Preprocessing.graphReduction(G, len(cl), cl)
    # Indices of vertices in graph and clique need to be fixed after removing vertices
    indexMapping = {v: i for i, v in enumerate(G.nodes())}
    G = nx.relabel_nodes(G, indexMapping)
    Preprocessing.remapVertices(cl, indexMapping)
    G, cl = Preprocessing.relabelModel(G, cl, H, POP=False)
    H = heur.UpperBoundDsatur(G)  # Need upper bound on new graph
    print(f"Time for Relabeling/Reduction:{round(time.time() - timer, 3)}s")
    print("Construct Model", flush=True)
    modelMap = {
        "ASS-I": ILP.createASS,
        "POP-I": ILP.createPOP,
        "POPH-I": ILP.createPOPHyb
    }
    modelMapSAT = {
        "ASS-S": SAT.ASS_SAT,
        "POP-S": SAT.POP_SAT,
        "POPH-S": SAT.POPHyb_SAT
    }

    # Memory cap for rep model

    if G.number_of_edges() > 1000000:
        print("Instance too large, skipped")
        return None
    if model.split("-")[1] == "S":
        params = dict(symm="true",atmost_const="sequential")
        result = search.runSATModel(modelMapSAT[model],
                                    G=G, H=H, clq=cl, timeout=timeout,
                                    lb=len(cl), parameters=params,
                                    output=f"SAT.cnf")
    else:
        model_params = {}
        if model == "POP" or model == "POPHyb":
            model_params = dict(q=G.number_of_nodes, symm="true",lowBound=len(cl))

        if model == "ASS":
            model_params = dict(symm="true", lowBound=len(cl))


        result = runModel(modelMap[model], G, H, cl,model_params, m_attributes=dict(Timelimit=str(timeout)))

    return result


def paperModelsBCP(model:str,G:nx.graph,timeout:int = 3600) -> list:
    modelMap = {
        "ASS-I-B": ILP.createASSBCP,
        "POP-I-B": ILP.createPOPBCP,
        "POPH-I-B": ILP.createPOPHybBCP,
    }

    modelMapSAT = {
        "ASS-S-B": SAT.ASS_SAT_BCP,
        "POP-S-B": SAT.POP_SAT_BCP,
        "POPH-S-B": SAT.POPHyb_SAT_BCP,
    }

    results = []
    H = heur.DSaturBandwidth(G)

    _,cl = Preprocessing.maxCutClique(G,H)


    print(H)
    # Data Reduction for Vertex Coloring

    print("Construct Model")

    if model.split("-")[1] == "S":
        result = search.runSATModelBCP(modelMapSAT[model],
                                             G=G, H=H, timeout=timeout,
                                             lb=len(cl),output = f"SAT.cnf")
    else:
        result = runModelBCP(modelMap[model],G,H,clq=cl,parameters={},m_attributes=dict(Timelimit=str(timeout)))

    return result