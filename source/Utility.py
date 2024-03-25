"""

"""

import networkx as nx
import gurobipy as gb
import math


#Paket zum Einlesen von Graphen
def readDimacs(path): #Liest Instanzen im DIMACS-Standardformat ein und speichert sie als networkx-Graphen

    G = None
    with open(path,"r") as f:
        for line in f:
            if line[0] == "p":
                form = line.split()

                G = nx.empty_graph(int(form[2]))

            if line[0] == "e":
                edge = line.split()
                if len(edge) == 3:
                    u, v = int(edge[1]), int(edge[2])
                    if u != v:
                        G.add_edge(u-1,v-1)
                else:
                    u,v,weight = int(edge[1]), int(edge[2]),int(edge[3])
                    if u != v:
                        G.add_edge(u-1,v-1,weight = weight)

            if line[0] == "n":
                v, demand = map(int,line.split()[1:])
                G.nodes[v-1]["demand"] = demand

    return G
def getColoringFromModel(M:gb.Model,m_vars:dict):
    coloring = {}
    for (i,j),val in m_vars.items():
        rval = round(val.X)
        if M._type == "ASS":
            if rval == 1:
                if j not in coloring:
                    coloring[j] = []
                coloring[j].append(i)
        elif M._type == "REP":
            if rval == 1:
                if i not in coloring:
                    coloring[i] = []
                coloring[i].append(j)
        else:
            try:
                if M._dummy and i==M._q:
                    continue
            except AttributeError:
                if i==M._q:continue
            if (j == 0 and rval == 0) or (j > 0 and round(m_vars[(i,j-1)].X)-rval == 1):
                if j not in coloring:
                    coloring[j] = []
                coloring[j].append(i)
    return coloring




def checkColoringEq(G:nx.Graph,c_groups:dict,eqCheck = False)->bool: #Überprüft ob die Färbung eine gültige equitable Färbung ist
    if eqCheck:
        frequencies = [len(c) for c in c_groups.values()]
        frequencies.sort()
        if frequencies[0]+1 < frequencies[-1]:
            print("Not balanced:", frequencies)
            return False
    coloring = [0]*G.number_of_nodes()
    colored = set()
    for c, colorset in c_groups.items():
        for v in colorset:
            coloring[v] = c
            colored.add(v)
    if len(colored) < G.number_of_nodes():
        print("Not all nodes colored")
        return False

    for u,v in G.edges:
        if coloring[u] == coloring[v]:
            print("Conflict:",u,",",v)
            return False
    return True

def checkColoringBCP(G:nx.Graph,c_groups:dict)->bool: #Überprüft ob die Färbung eine gültige bandwidth Färbung ist
    coloring = [0]*G.number_of_nodes()
    colored = set()
    for c,colorset in c_groups.items():
        for v in colorset:
            coloring[v] = c
            colored.add(v)
    if len(colored) < G.number_of_nodes():
        print("Not all nodes colored")
        return False

    for u,v,w in G.edges(data="weight"):
        if abs(coloring[u] - coloring[v]) < w:
            print(f"Conflict: c({u}) = {coloring[u]}, c({v}) = {coloring[v]}, weight({u},{v}) = {w}")
            return False
    return True

def checkColoringConsistent(results:list,database:dict = None):

    def roundInf(x:float):
        if math.isinf(x):
            return x
        return round(x)
    lowerBound = -math.inf
    upperBound = math.inf
    instance = results[0]["instance"]
    if database is not None and instance in database:
        lowerBound = database[instance][0]
        upperBound = database[instance][1]
    for result in results:
        if roundInf(result["lower_bound"]) > roundInf(upperBound) or roundInf(result["upper_bound"]) < roundInf(lowerBound):
            print(f"LB: {result['lower_bound']} UB: {result['upper_bound']} LB:{lowerBound} UB:{upperBound}")
            return False
        lowerBound = max(lowerBound,result["lower_bound"])
        upperBound = min(upperBound,result["upper_bound"])
    return True

