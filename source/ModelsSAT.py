"""
This module implements the SAT-Models of the coloring problems
Fum fact:
The reason it was called DecideColorable comes from the fact that SAT-Problems always encode decision problems
(wheras ILPs can also encode optimization problems)
"""
import networkx as nx
import LogicFormula as Logic
import SatParser as SatParser
import math
import Preprocessing as preproc
import itertools
from abc import ABC, abstractmethod

class ColoringModel(ABC):
    """
    Base class for Coloring Models
    Each coloring model must implement:
    - a constructor initializing the model parameters
    - a method k_coloring_formula implementing the SAT encoding of a k-coloring decision problem of the model
    - a method coloring_from_vars which translates a variable assignment of the model to a coloring
    - set Clique simply sets the Pre coloring clique of the model
    """
    @abstractmethod
    def __init__(self):
        self.type = ""
        self.lb = -math.inf
        self.ub = math.inf
        self.eq = False
        self.runtime = 0
        self.clq = None
    @abstractmethod
    def k_coloring_formula(self,G: nx.Graph, k: int,output:str):
        pass

    @abstractmethod
    def coloring_from_vars(self, vars):
        pass
    def setClique(self,clq):
        self.clq = clq

class ASS_SAT(ColoringModel):
    """
    The classical assignment model for graph coloring/equitable coloring
    """
    def __init__(self,symm= "none", atmost_const = "none", **arbitrary):
        """
        :param symm: the type of symmetry-breaking constraint added:
        - none is no constraint
        - ordering breaks the symmetry of which colors are being used (enforces colors 1...k being used)
        - weak enforces all vertices with index < k to be colored with a color with lower index
        - strong breaks all symmetries
        - strong reduced
        :param equitConst: the type of equitable constraints added:
        - none is no equitability
        - standard uses the constraints floor(n/k)<= |C| <= ceil(n/k) for every color class C
        the default cardinality encoding used is sequential encoding (fastest in preliminary tests)
        :param atmost_const: encodes that each vertex has at most one color
        - none means that this constraint is not encoded (so the only constraint
        is that each vertex has at least one colour)
        - binomial: encode sum(Variables of v) <= 1 using the binomial encoding
        - default: use the default cardinality encoding (in this case the sequential encoding)
        """
        self.type = "ASS"
        self.symm = symm
        self.x = {}
        self.clq = None
        self.atmost_const = atmost_const

    def k_coloring_formula(self,G: nx.Graph, k: int,output:str = "SAT.cnf"):
        sat_formulation = Logic.LogicFormula()
        x = {}
        nodeList = list(G.nodes())
        edgeList = list(G.edges())

        for v in nodeList:
            x.update({(v, i): sat_formulation.addVar() for i in range(k)})
            Logic.at_least_1_const([x[v, i] for i in range(k)], sat_formulation)
            if self.atmost_const != "none":
                Logic.at_most_one([x[v, i] for i in range(k)],sat_formulation,encoding_type=self.atmost_const)

        for v, w in edgeList:
            for i in range(k):
                Logic.less_than_n([x[v, i], x[w, i]], sat_formulation)
        self.x = x.copy()
        if self.clq is not None:
            preproc.precolorCliqueSAT(self,sat_formulation,self.clq)
        # if colors i is not used, then i+1 cannot be used
        if self.symm == "ordering":
            t = sat_formulation.addVars(k)
            for i in range(k):
                sat_formulation.addClauses(list(itertools.chain.from_iterable([[-x[v,i],t[i]],[-x[w,i],t[i]]] for v,w in G.edges())))
                if i < k-1:
                    sat_formulation.addClause([t[i],-t[i+1]])
        #weak symmetry constraints: vertex cannot have color with higher index
        #pi = self.clq + [v for v, d in sorted(nx.degree(G), key=lambda x: x[1], reverse=True) if v not in self.clq]
        if self.symm == "true":
            for v in range(len(self.clq) + 1, G.number_of_nodes() - 1):
                for i in range(len(self.clq) + 1, min(k, v)):
                    #sat_formulation.addClause([-x[v, i]]+[x[u, i-1] for u in pi[i - 1:v]])
                    sat_formulation.addClause([-x[v, i]]+[x[u, i-1] for u in range(i-1, v)])

        with open(output, "w") as f:
            f.write( sat_formulation.parseAsString())

        return x

    def coloring_from_vars(self,vars):

        return SatParser.varsToColor(vars,self.x)


class POP_SAT(ColoringModel):
    """
    Partial Ordering model for coloring/ equitable coloring
    """
    def __init__(self, symm = "none", **arbitrary):
        """
        :param symm: the type of symmetry-breaking constraint added:
        - none is no constraint
        - ordering breaks the symmetry of which colors are being used (enforces colors 1...k being used)
        - weak enforces all vertices with index < k to be colored with a color with lower index
        - strong breaks all symmetries
        - strong reduced
        :param equitConst: the type of equitable constraints added:
        - none is no equitability
        - standard uses the constraints floor(n/k)<= |C| <= ceil(n/k) for every color class C
        the default cardinality encoding used is sequential encoding (fastest in preliminary tests)
        :param strength: use the strengthened partial ordering model
        """
        self.type = "POP"
        self.symm = symm
        self.q = None
        self.x = {}
        self.clq = None

    def k_coloring_formula(self,G: nx.Graph, k: int,output:str = "SAT.cnf"):
        sat_formulation = Logic.LogicFormula()
        y = {}
        nodeList = list(G.nodes())
        edgeList = list(G.edges())

        for v in nodeList:
            y.update({(v, i): sat_formulation.addVar() for i in range(k)})
            sat_formulation.addClause([-y[v, k - 1]])
            for i in range(1, k):
                Logic.at_least_1_const([y[v, i - 1], -y[v, i]], sat_formulation)
        for v, w in edgeList:
            Logic.at_least_1_const([y[v, 0], y[w, 0]], sat_formulation)
            for i in range(1, k):
                Logic.less_than_n([y[v, i - 1], -y[v, i], y[w, i - 1], -y[w, i]], sat_formulation)
        self.x = y.copy()

        if self.clq is not None:
            preproc.precolorCliqueSAT(self, sat_formulation, self.clq)

        if self.symm == "true" and self.q is not None:
            raise Exception("Invalid attribute combination")
        # weak symmetry constraints: vertex cannot have color with higher index
        #pi = self.clq + [v for v,d in sorted(nx.degree(G), key=lambda x: x[1], reverse=True) if v not in self.clq]
        if self.symm == "true":
            for v in range(len(self.clq)+1, G.number_of_nodes() - 1):
                for i in range(len(self.clq) + 1, min(k, v)):
                    #sat_formulation.addClause([-y[pi[v], i]] + [y[u, i - 1] for u in pi[i-1:v]])
                    sat_formulation.addClause([-y[v, i]] + [y[u, i - 1] for u in range(i - 1, v)])

        if self.q is not None:
            for v, w in G.edges():
                for i in range(1, k):
                    sat_formulation.addClause([-y[v, i-1], y[v, i], y[self.q, i - 1]])
                    sat_formulation.addClause([-y[w, i-1], y[w, i], y[self.q, i - 1]])
            for v in G.nodes():
                if v != self.q:
                    for i in range(1, k):
                        sat_formulation.addClause([-y[v, i], y[self.q, i]])

        with open(output, "w") as f:
            f.write(sat_formulation.parseAsString())

        return y

    def coloring_from_vars(self, vars):
        return SatParser.varsToColor_POP(vars, self.x)

class POPHyb_SAT(ColoringModel):
    """
    The hybrid partial ordering model for coloring/equitable coloring
    """
    def __init__(self,symm = "none", **arbitrary):
        """
        :param symm: the type of symmetry-breaking constraint added:
        - none is no constraint
        - ordering breaks the symmetry of which colors are being used (enforces colors 1...k being used)
        - weak enforces all vertices with index < k to be colored with a color with lower index
        - strong breaks all symmetries
        - strong reduced
        :param equitConst: the type of equitable constraints added:
        - none is no equitability
        - standard uses the constraints floor(n/k)<= |C| <= ceil(n/k) for every color class C
        the default cardinality encoding used is sequential encoding (fastest in preliminary tests)
        :param strength: use the strengthened partial ordering model
        """
        self.type = "POPH"
        self.symm = symm
        self.q = None
        self.x = {}
        self.y = {}
        self.clq = None

    def k_coloring_formula(self,G: nx.Graph, k: int,clique = None,output:str = "SAT.cnf"):
        sat_formulation = Logic.LogicFormula()
        y = {}
        x = {}
        nodeList = list(G.nodes())
        edgeList = list(G.edges())

        for v in nodeList:
            y.update({(v, i): sat_formulation.addVar() for i in range(k)})
            sat_formulation.addClause([-y[v, k - 1]])
            x.update({(v, i): sat_formulation.addVar() for i in range(k)})
            sat_formulation.addClauses([[x[v,0],y[v,0]],[-x[v,0],-y[v,0]]])
            for i in range(1, k):
                Logic.at_least_1_const([y[v, i - 1], -y[v, i]], sat_formulation)
                sat_formulation.addClauses([
                    [-x[v, i], y[v, i-1]],
                    [-x[v, i], -y[v, i]],
                    [x[v, i], -y[v, i-1],y[v,i]]
                ])

        for v, w in edgeList:
            for i in range(k):
                Logic.less_than_n([x[v, i], x[w, i]], sat_formulation)

        self.y = y.copy()
        self.x = x.copy()

        if self.clq is not None:
            preproc.precolorCliqueSAT(self, sat_formulation, self.clq)

        if self.symm == "strong" and self.q is not None:
            raise Exception("Invalid attribute combination")
        # weak symmetry constraints: vertex cannot have color with higher index
        #pi = self.clq + [v for v, d in sorted(nx.degree(G), key=lambda x: x[1], reverse=True) if v not in self.clq]
        if self.symm == "weak" or self.symm == "strong":
            for v in range(0*len(self.clq), k):
                #sat_formulation.addClause([-y[(pi[v], v)]])
                sat_formulation.addClause([-y[(v, v)]])
        if self.symm == "strong":
            for v in range(len(self.clq) + 1, G.number_of_nodes() - 1):
                for i in range(len(self.clq) + 1, min(k, v)):
                    #sat_formulation.addClause([-x[v, i]] + [x[u, i - 1] for u in pi[i - 1:v]])
                    sat_formulation.addClause([-x[v, i]]+[x[u, i-1] for u in range(i-1, v)])

        # only consider first (second) degree neighbors of the clique nodes to break symmetries
        if self.q is not None:
            for v, w in G.edges():
                for i in range(1,k):
                    sat_formulation.addClause([-x[v, i], y[self.q, i-1]])
                    sat_formulation.addClause([-x[w, i], y[self.q, i-1]])
            for v in G.nodes():
                if v != self.q:
                    for i in range(1, k):
                        sat_formulation.addClause([-y[v, i], y[self.q, i]])

        with open(output, "w") as f:
            f.write(sat_formulation.parseAsString())


        return y,x

    def coloring_from_vars(self,vars):
        return SatParser.varsToColor(vars,self.x)


class ASS_SAT_BCP(ColoringModel):
    """
    The assignment model for Bandwidth coloring:
    The edge constraints are encoded like this:
    -x[v,i] or -x[w,j] for every edge (v,w) and all pairs of colours |i-j| < c,
    where c is the edge weight
    """
    def __init__(self,sort = "none",atmost_const="none",**arbitrary):
        self.type = "ASS"
        self.x = {}
        self.clq = None
        self.sort = sort
        self.atmost_const = atmost_const
    def k_coloring_formula(self,G: nx.Graph, k: int,output:str = "SAT.cnf"):
        sat_formulation = Logic.LogicFormula()
        x = {}
        nodeList = list(G.nodes())
        edgeList = list(G.edges(data="weight"))
        if "clauses" in self.sort:
            nodeList.sort(key=lambda x, G=G: G.degree(x), reverse=True)
            edgeList.sort(key=lambda x, G=G: G.degree(x[0]) + G.degree(x[1]), reverse=True)
        for v in nodeList:
            x.update({(v, i): sat_formulation.addVar() for i in range(k)})
            Logic.at_least_1_const([x[v, i] for i in range(k)], sat_formulation)
            if self.atmost_const != "none":
                Logic.at_most_one([x[v, i] for i in range(k)], sat_formulation, encoding_type=self.atmost_const)
        for v, w, c in edgeList:
            for i in range(k):
                for j in range(max(0,i-c+1),min(k,i+c)):
                    sat_formulation.addClause([-x[v, i], -x[w, j]])
        self.x = x.copy()

        with open(output, "w") as f:
            f.write(sat_formulation.parseAsString())

        return x

    def coloring_from_vars(self,vars):

        return SatParser.varsToColor(vars,self.x)


class POP_SAT_BCP(ColoringModel):
    """
    The partial ordering model for Bandwidth coloring:
    The edge constraints are encoded like this:
    y[v,i] or -y[v,i-1] or y[w,i+c] or -y[w,i-c-1] for every edge (v,w) and all colours i,
    where c is the edge weight
    """
    def __init__(self, strength="false",sort = "none",**arbitrary):
        self.type = "POP"
        self.strength = strength
        self.q = None
        self.x = {}
        self.clq = None
        self.sort=sort

    def k_coloring_formula(self, G: nx.Graph, k: int, output: str = "SAT.cnf"):
        sat_formulation = Logic.LogicFormula()
        y = {}
        nodeList = list(G.nodes())
        edgeList = list(G.edges(data="weight"))
        if "clauses" in self.sort:
            nodeList.sort(key=lambda x, G=G: G.degree(x), reverse=True)
            edgeList.sort(key=lambda x, G=G: G.degree(x[0]) + G.degree(x[1]), reverse=True)
        for v in nodeList:
            y.update({(v, i): sat_formulation.addVar() for i in range(k)})
            sat_formulation.addClause([-y[v, k - 1]])
            for i in range(1, k):
                Logic.at_least_1_const([y[v, i - 1], -y[v, i]], sat_formulation)

        for v, w, c in edgeList:
            edge_clause = [y[v, 0]]
            if c-1 <= k-1: edge_clause += [y[w, c-1]]
            sat_formulation.addClause(edge_clause)
            for i in range(1, k):
                edge_clause = [-y[v, i - 1], y[v, i]]
                if i-c >= 0: edge_clause += [-y[w, i-c]]
                if i+c-1 <= k-1: edge_clause += [y[w, i + c - 1]]
                sat_formulation.addClause(edge_clause)

        self.x = y.copy()

        if self.clq is not None:
            preproc.precolorCliqueSAT(self, sat_formulation, self.clq)

        with open(output, "w") as f:
            f.write(sat_formulation.parseAsString())

        return y

    def coloring_from_vars(self, vars):
        return SatParser.varsToColor_POP(vars, self.x)


class POPHyb_SAT_BCP(ColoringModel):
    """
    The hybrid partial ordering model for Bandwidth coloring. Analogous to the regular pop-model
    """
    def __init__(self, symm="none", equitConst='none', strength="false",**arbitrary):
        self.type = "POPHyb"
        self.symm = symm
        self.strength = strength
        self.q = None
        self.equitConst = equitConst
        self.x = {}
        self.clq = None

    def k_coloring_formula(self, G: nx.Graph, k: int, output: str = "SAT.cnf"):
        sat_formulation = Logic.LogicFormula()
        y = {}
        x = {}
        for v in G.nodes():
            y.update({(v, i): sat_formulation.addVar() for i in range(k)})
            sat_formulation.addClause([-y[v, k - 1]])
            x.update({(v, i): sat_formulation.addVar() for i in range(k)})
            sat_formulation.addClauses([[x[v, 0], y[v, 0]], [-x[v, 0], -y[v, 0]]])
            for i in range(1, k):
                Logic.at_least_1_const([y[v, i - 1], -y[v, i]], sat_formulation)
                sat_formulation.addClauses([
                    [-x[v, i], y[v, i - 1]],
                    [-x[v, i], -y[v, i]],
                    [x[v, i], -y[v, i - 1], y[v, i]]
                ])
        for v, w, c in G.edges(data="weight"):
            edge_clause = [y[v, 0]]
            if c-1 <= k-1: edge_clause += [y[w, c-1]]
            sat_formulation.addClause(edge_clause)
            for i in range(1, k):
                edge_clause = [-x[v,i]]
                if i-c >= 0: edge_clause += [-y[w, i-c]]
                if i+c-1 <= k-1: edge_clause += [y[w, i + c - 1]]
                sat_formulation.addClause(edge_clause)
        self.x = x.copy()
        self.y = y.copy()
        with open(output, "w") as f:
            f.write(sat_formulation.parseAsString())

        return y,x

    def coloring_from_vars(self, vars):
        return SatParser.varsToColor(vars, self.x)
