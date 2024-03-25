"""
Author: Daniel Faber
This module constructs the ILP model presented in the paper using the Gurobi api
"""

import gurobipy as gb
from gurobipy import GRB
import networkx as nx



def createASS(g:nx.Graph,H,symm="none",lowBound=1):
    """
    Assignment model for GCP
    :param g: Input graph
    :param H: Upper bound on chrom. number
    :param symm:
    :param lowBound: Lower bound on chrom. number
    :return: Gurobi.Model object encoding the GCP for g
    """
    M = gb.Model("ASS")

    w = []      # variables indicating if color used
    x = {}      # variables indicating if vertex assigned to color
    for v in g.nodes:

        node_sum = 0
        #every vertex needs to be assigned one color
        for i in range(H):
            variable = M.addVar(vtype = GRB.BINARY)
            x[(v,i)] = variable
            node_sum += variable

        M.addConstr(node_sum == 1)

    #adding constraint for every color and every edge
    # adding w variables to objective function
    for i in range(H):
        w_i = M.addVar(obj=1, vtype=GRB.BINARY)
        w.append(w_i)
        if i >= 1:
            M.addConstr(w[i] <= w[i-1])

        M.addConstrs(x[(u, i)] + x[(v, i)] <= w_i for u, v in g.edges)


    #symmetry breaking from Mendenz & Zabala
    if symm == "true":
        for v in range(H):

            for i in range(v+1,H):
                M.addConstr(x[(v,i)] == 0)
        for v in range(lowBound,g.number_of_nodes()-1):
            for i in range(lowBound+1,min(H,v)):
                M.addConstr(x[v,i] <= sum(x[u,i-1] for u in range(i-1,v)))
    M._H = H
    M._G = g
    M._type = "ASS"
    M.update()
    return M,x,w


def createPOP(g:nx.graph,H,q=0,symm ="none",lowBound=1):
    """
    Partial ordering model for GCP
    :param g: Input graph
    :param H: Upper bound
    :param q: vertex q (needs to be dummy for symm breaking constraints)
    :param symm: symm-breaking constraints
    :param lowBound: lower bound for chrom number
    :return:
    """

    M = gb.Model("POP")
    n = g.number_of_nodes()

    y = {}
    # adding variables for the special vertex q for every color
    for i in range(H):
        y[(q,i)] = M.addVar(vtype=GRB.BINARY,obj = 1)

    # adding variables for all other nodes and colors
    for v in g.nodes:
        if v != q:
            y[(v,0)] = M.addVar(vtype=GRB.BINARY)

        for i in range(1,H):
            if v != q:
                y[(v,i)] = M.addVar(vtype=GRB.BINARY)


            M.addConstr(y[(v,i-1)]-y[(v,i)] >= 0)
            M.addConstr(y[(q, i - 1)] - y[(v, i-1)] >= 0)

        M.addConstr(y[(v, H-1)] == 0)


    if q not in g.nodes:
        for i in range(1, H):
            M.addConstr(y[(q, i - 1)] - y[(q, i)] >= 0)
        M.addConstr(y[(q,H-1)]==0)

    #adding constraints for every edge and color 0
    M.addConstrs(y[(u, 0)] + y[(v, 0)] >= 1 for u,v in g.edges)

    # adding constraints for every edge and every other color
    for i in range(1, H):
        M.addConstrs(y[(u, i - 1)] - y[(u, i)] + y[(v, i - 1)] - y[(v, i)] <= 1 for u,v in g.edges)

    if symm == "true":
        for v in range(lowBound,g.number_of_nodes()-1):
            for i in range(lowBound+1,min(H,v)):
                M.addConstr(y[v,i] <= sum(y[u,i-1]-y[u,i] for u in range(i-1,v)))
    M._H = H
    M._G = g
    M._q = q
    M._dummy = (q==n)
    M._type = "POP"
    M.setAttr("ObjCon", 1)
    M.update()
    return M,y


def createPOPHyb(g: nx.graph, H, q=0,symm = "none",lowBound=1):
    """
    hybrid Partial ordering model for GCP
    :param g: Input graph
    :param H: Upper bound
    :param q: vertex q (needs to be dummy for symm breaking constraints)
    :param symm: symm-breaking constraints
    :param lowBound: lower bound for chrom number
    :return:
    """

    M = gb.Model("POPHyb")
    n = g.number_of_nodes()
    y = {}

    max_deg = max(g.degree(), key=lambda x: x[1])[1]
    # adding variables for the special vertex q for every color
    for i in range(H):
        y[(q, i)] = M.addVar(vtype=GRB.BINARY, obj=1)


    # adding variables for all other nodes and colors
    for v in g.nodes:

        if v != q:
            y[(v, 0)] = M.addVar(vtype=GRB.BINARY)

        for i in range(1, H):
            if v != q:
                y[(v, i)] = M.addVar(vtype=GRB.BINARY)

            M.addConstr(y[(v, i - 1)] - y[(v, i)] >= 0)
            M.addConstr(y[(q, i - 1)] - y[(v, i - 1)] >= 0)

        M.addConstr(y[(v, H - 1)] == 0)


    # adding  x variables that correspond to variables from ass model
    x = {}
    for v in g.nodes:
        x[(v, 0)] = M.addVar(vtype=GRB.BINARY)

        M.addConstr(x[(v, 0)] == 1 - y[(v, 0)])
        for i in range(1, H):
            x[(v, i)] = M.addVar(vtype=GRB.BINARY)

            M.addConstr(x[(v, i)] == y[(v, i - 1)] - y[(v, i)])


    #adding constraints for every edge andd color 0
    M.addConstrs(x[(u, 0)] + x[(v, 0)] <=1  for u, v in g.edges)

    # adding constraints for every edge and every other color
    for i in range(1, H):
        M.addConstrs(x[(u, i)] + x[(v, i)] <=  1 for u, v in g.edges)


    if symm == "true":
        for v in range(lowBound,g.number_of_nodes()-1):
            for i in range(lowBound+1,min(H,v)):
                M.addConstr(x[v,i] <= sum(x[u,i-1] for u in range(i-1,v)))
    M._H = H
    M._G = g
    M._q = q
    M._dummy = (q==n)
    M._type = "POP"
    M.setAttr("ObjCon",1)
    M.update()
    return M, y, x

def createASSBCP(g:nx.Graph,H):
    """
    assignment model for BCP
    :param g: Input graph
    :param H: upper bound on BCP
    :return:
    """

    M = gb.Model("ASS")
    n = g.number_of_nodes()

    x = {}

    for v in g.nodes:
        node_sum = 0
        #adding variables for every node and every color

        for i in range(H):
            variable = M.addVar(vtype = GRB.BINARY)
            x[(v,i)] = variable
            node_sum += variable

        M.addConstr(node_sum == 1)


    z = M.addVar(obj=1, vtype=GRB.CONTINUOUS)
    #adding constraint for every color and every edge
    for i in range(H):
        M.addConstrs(z >= (i+1)*x[v,i] for v in g.nodes)

        M.addConstrs(x[(u, i)] + x[(v, j)] <= 1 for u,v,c in g.edges(data="weight")
                                                for j in range(max(0,i-c+1),min(H,i+c)))


    M._H = H
    M._G = g
    M._type = "ASS"
    M.update()
    return M,x


def createPOPBCP(g:nx.graph,H):
    """
      partial ordering model for BCP
      :param g: Input graph
      :param H: upper bound on BCP
      :return:
    """
    M = gb.Model("POP")
    n = g.number_of_nodes()
    y = {}
    q = n # must be dummy

    # adding variables for the special vertex q for every color
    for i in range(H):
        y[(q,i)] = M.addVar(vtype=GRB.BINARY,obj = 1)


    # adding variables for all other nodes and colors
    for v in g.nodes:
        if v != q:
            y[(v,0)] = M.addVar(vtype=GRB.BINARY)

        for i in range(1,H):
            if v != q:
                y[(v,i)] = M.addVar(vtype=GRB.BINARY)

            M.addConstr(y[(v,i-1)]-y[(v,i)] >= 0)
            M.addConstr(y[(q, i - 1)] - y[(v, i-1)] >= 0)

        M.addConstr(y[(v, H-1)] == 0)

    for i in range(1, H):
        M.addConstr(y[(q, i - 1)] - y[(q, i)] >= 0)
    M.addConstr(y[(q,H-1)]==0)

    #adding constraints for every edge and color 0
    for v,w,c in g.edges(data="weight"):
        edge_sum = y[v,0]
        if c-1 <= H-1:
            edge_sum+=y[w,c-1]
        M.addConstr(edge_sum >= 1)
        for i in range(1,H):
            edge_sum = y[v,i-1]-y[v,i]
            edge_sum += y[w,i-c] if i-c >= 0 else 1
            if i+c-1 <= H-1: edge_sum -= y[w,i+c-1]
            M.addConstr(edge_sum <= 1)

    M._H = H
    M._G = g
    M._q = q
    M._type = "POP"
    M.setAttr("ObjCon", 1)
    M.update()
    return M,y

def createPOPHybBCP(g: nx.graph, H):
    """
      hybrid partial ordering model for BCP
      :param g: Input graph
      :param H: upper bound on BCP
      :return:
  """

    M = gb.Model("POPHyb")
    n = g.number_of_nodes()
    y = {}
    q = n #must be dummy
    max_deg = max(g.degree(), key=lambda x: x[1])[1]
    # adding variables for the special vertex q for every color
    for i in range(H):
        y[(q, i)] = M.addVar(vtype=GRB.BINARY, obj=1)


    # adding variables for all other nodes and colors
    for v in g.nodes:

        if v != q:
            y[(v, 0)] = M.addVar(vtype=GRB.BINARY)

        for i in range(1, H):
            if v != q:
                y[(v, i)] = M.addVar(vtype=GRB.BINARY)

            M.addConstr(y[(v, i - 1)] - y[(v, i)] >= 0)
            M.addConstr(y[(q, i - 1)] - y[(v, i - 1)] >= 0)

        M.addConstr(y[(v, H - 1)] == 0)


    # adding  x variables that correspond to variables from ass model
    x = {}
    for v in g.nodes:
        x[(v, 0)] = M.addVar(vtype=GRB.BINARY)
        M.addConstr(x[(v, 0)] == 1 - y[(v, 0)])
        for i in range(1, H):
            x[(v, i)] = M.addVar(vtype=GRB.BINARY)
            M.addConstr(x[(v, i)] == y[(v, i - 1)] - y[(v, i)])

    # adding constraints for every edge and color
    for v, w, c in g.edges(data="weight"):
        edge_sum = y[v, 0]
        if c - 1 <= H - 1:
            edge_sum += y[w, c - 1]
        M.addConstr(edge_sum >= 1)
        for i in range(1, H):
            edge_sum = x[v,i]
            edge_sum += y[w, i - c] if i - c >= 0 else 1
            if i + c - 1 <= H - 1: edge_sum -= y[w, i + c - 1]
            M.addConstr(edge_sum <= 1)


    M._H = H
    M._G = g
    M._q = q
    M._type = "POP"
    M.setAttr("ObjCon",1)
    M.update()
    return M, y, x
