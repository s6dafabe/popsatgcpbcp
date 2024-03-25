"""
Precoloring for SAT models
"""
import LogicFormula as logic
from ModelsSAT import ColoringModel
import networkx as nx
import time
import numpy as np

def preassignVars(zero_vars:list, one_vars:list,formula:logic.LogicFormula):
    """
    Preassigns variables in the logic formula by adding unit clauses.
    Note that the manual elimination of variables and clauses was removed, as the SAT-Solver itself does this much
    faster (performance difference is neglegible)
    """
    for zero in zero_vars:
        formula.addClause([-zero])
    for one in one_vars:
        formula.addClause([one])
def precolorCliqueSAT(model:ColoringModel,formula:logic.LogicFormula,max_clique):
    """
    given a coloring model, the corresponding logic formula and a clique, precolors the model with the clique.
    (Yes, the fact that the model and it's corresponding formula are given seperately is inelegeant and confusing, but
    is has to do with the fact that the formula constructed in the model is not a class attribute. I will probably
    change this to make more sense)
    """
    match model.type:
        case "POP":
            zero_vars = []
            one_vars = []
            for i, v in enumerate(max_clique):

                one_vars+=[model.x[v, j] for j in range(i)]
                zero_vars+=[model.x[v, j] for j in range(i,len(max_clique))]
            preassignVars(zero_vars, one_vars, formula)
        case "ASS":
            zero_vars = []
            one_vars = []
            for i,v in enumerate(max_clique):
                one_vars.append(model.x[v,i])
                zero_vars += [model.x[v,j] for j in range(len(max_clique)) if j != i]
            preassignVars(zero_vars,one_vars,formula)

        case "POPH":
            zero_vars = []
            one_vars = []
            for i, v in enumerate(max_clique):
                one_vars += [model.y[v, j] for j in range(i)]
                zero_vars += [model.y[v, j] for j in range(i, len(max_clique))]
            preassignVars(zero_vars, one_vars, formula)

def maxCutClique(G:nx.Graph, H): #Finden einer Clique für REP und ASS/POP/POPH-Modell
    max_clique = None
    max_clique_rep = None
    clique_val = 0
    clique_val_rep = 0
    m = G.number_of_edges()
    n = G.number_of_nodes()
    #if the graph is small enough: iterate over all possible cliques
    if (2*m/(n**2-n)) <= 0.2 and n < 200:
        max_clique = max(nx.find_cliques(G),key=lambda x:len(x)*H+nx.cut_size(G,x))

        max_clique_rep = max(nx.find_cliques(G),key=lambda x:len(x)*m+nx.cut_size(G,x))
    else:
        #else find maximal independent sets in the antigraph
        start = time.time()
        antiG = nx.complement(G)
        for i in range(300*int(round(m/n))):
            clique = nx.maximal_independent_set(antiG, seed=i)
            new_val = H * len(clique) + nx.cut_size(G, clique)
            if new_val > clique_val:
                max_clique = clique
                clique_val = new_val

            new_val = m * len(clique) + nx.cut_size(G, clique)

            if new_val > clique_val_rep:
                max_clique_rep = clique
                clique_val_rep = new_val
            if time.time()-start > 100:
                break

    return max_clique.copy(), max_clique_rep.copy()


def precolorCliqueILP(M, var,max_clique): #Vorfärbung der Clique


    match M._type:
        case "POP":
            y = var
            q = M._q

            #precoloring q will not work
            if q in max_clique:
                max_clique = max_clique.copy()
                max_clique.remove(q)

            for i, v in enumerate(max_clique):

                M.addConstr(y[(v, i)] == 0)

                if i > 0:
                    M.addConstr(y[(v, i - 1)] == 1)
            M.addConstr(y[(q, len(max_clique)-(2 if M._dummy else 1))] == 1)
        case "ASS":
            x = var
            for i, v in enumerate(max_clique):
                M.addConstr(x[(v, i)] == 1)

        case "REP":

            x = var

            for v in max_clique:
                M.addConstr(x[(v, v)] == 1)

#deletes vertices whose neighbourhood is deleted by other vertices
def deleteDominated(G:nx.Graph,clq:list) -> nx.Graph:

    while True:
        redundant = []
        for v in G.nodes():
            redundant += [w for w in G.nodes() if v != w
                          and w not in clq
                          and set(G.neighbors(w)) <= set(G.neighbors(v))]
        if len(redundant) == 0:
            break
        G.remove_nodes_from(redundant)
    return G

#deletes vertices with lower degree than the lower bound
def deleteLowDegree(G:nx.Graph,lb:int,clq:list)->nx.Graph:
    redundant = [v for v in G.nodes() if G.degree(v) < lb and v not in clq]
    G.remove_nodes_from(redundant)
    return G


def graphReduction(G:nx.Graph,lb:int,clq:list)->nx.Graph:
    while True:
        G_temp = deleteDominated(deleteLowDegree(G,lb,clq),clq)
        if G_temp.number_of_nodes() == G.number_of_nodes():
            G = G_temp
            break
        G = G_temp
    return G

def remapVertices(vertices:list,mapping:dict)->None:
    for i in range(len(vertices)):
        vertices[i] = mapping[vertices[i]]

def relabelModel(G:nx.Graph,cl,H=0,POP=False): #Umindexiert Knoten eines Graphen abhängig vom Modell und der Clique
    #for the POP models, q = maxColor, so we need to guarantee that 1...H-1 are neighbours of q
    if POP:
        print("POP Relabel")
        if H == 0:
            print("No upper bound")
            return None,None
        mDegInd = np.argmax([G.degree(cl[i]) for i in range(len(cl))])

        cl[-1],cl[mDegInd] = cl[mDegInd],cl[-1]
    #because we precolor clique, with 1...Clq, the indices of the clique must be 1...Clq
    mapping1 = relabelMapping(cl,range(len(cl)))

    cl = list(range(len(cl)))
    G = nx.relabel_nodes(G, mapping1, copy=True)
    n = G.number_of_nodes()
    if POP and H > len(cl):
        if len(list(G.neighbors(cl[-1]))) < H-1:
            print("Not enough neighbours")
            return None,None
        mapping2 = relabelMapping(list(G.subgraph(range(len(cl)-1,n)).neighbors(cl[-1]))[:H-len(cl)],range(len(cl),H))

        G = nx.relabel_nodes(G, mapping2, copy=True)

    return G,cl




def relabelMapping(nds:list,rng:range):#Nimmt eine Liste von Knotenindizes und ein Intevall als Paramter und vertauscht die Indizes im Graphen so, dass die Knoten mit den Indizes aus der Liste danach die Indizes aus dem Intervall besitzen
    if len(rng) == 0:
        return {}
    a,b = rng[0],rng[-1]
    if b-a+1 != len(nds):
        print("Wrong range size")
        return
    missing1 = list(rng)
    missing2 = []
    for v in nds:
        if a <= v <= b:
            missing1.remove(v)
        else:
            missing2.append(v)
    listA = nds+missing1
    listB = list(rng)+missing2

    mapping = {listA[i]:listB[i] for i in range(len(listA))}
    return mapping
def relabelNodes(G:nx.Graph,cl):#Umindexiert die Knoten in einer Clique
    cl.sort()
    missing = []
    lastInd = 0
    for i,v in enumerate(cl):

        if v >= len(cl):
            lastInd = i
            break
        if i == 0:
            missing += list(range(v))
        else:
            missing += list(range(cl[i-1]+1,v))


    missing += list(range(cl[lastInd-1]+1 if lastInd > 0 else 0,len(cl)))

    mapping = {missing[i]:cl[lastInd+i] for i in range(len(missing))}
    mapping.update({cl[lastInd+i]:missing[i] for i in range(len(missing))})
    G_relabel = nx.relabel_nodes(G,mapping,copy=True)

    return G_relabel,list(range(len(cl)))