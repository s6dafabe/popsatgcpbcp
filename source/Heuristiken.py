#Author: Daniel Faber
from queue import PriorityQueue
import networkx as nx
import colorsys
import itertools
import Utility as Utility
#Bemerkung: dieses Paket enthält die benutzten Heuristiken



def UpperBoundDsatur(G:nx.Graph):
    return max(nx.greedy_color(G, strategy="DSATUR").values())+1
def colorGraph(color_groups,colored,path): #Visualisiert die Färbung

    col = max(color_groups.keys())+1
    for i in range(col):

        rgbcolor = '#%02x%02x%02x' % tuple([round(c*255) for c in colorsys.hsv_to_rgb(i/col,1,1)])

        for v in color_groups[i]:
            colored.nodes[v]["graphics"] = {"hasFill":True,"fill":rgbcolor}

    nx.write_gml(colored, path)

def checkColoringEq(G:nx.Graph,c_groups:dict)->bool:#Überprüft ob die Färbung eine gültige equitable Färbung ist
    coloring = [0]*G.number_of_nodes()
    for c in c_groups.values():
        for v in c:
            coloring[v] = c

    for u,v in G.edges:
        if coloring[u] == coloring[v]:
            print("Conflict:",u,",",v)
            return False
    return True

def DSaturBandwidth(G:nx.Graph)->int:
    """
    Calculates a Greedy coloring for the BCP and returns the number of colors used
    :param G: Graph to color according to BCP
    :return: number of colors in calculated coloring
    """
    n = G.number_of_nodes()
    # initialize color as -1 -> not colored
    colors = [-1]*n
    neighbouring_colors = [set() for i in range(n)]
    saturations = PriorityQueue()

    max_color = 0
    while min(colors) == -1:
        saturations.put((max(filter(lambda x: colors[x] ==-1,G.nodes),key = lambda x: G.degree(x)),0))
        while not saturations.empty():
            v = saturations.get()[0]
            if colors[v] > -1:
                continue
            colors[v] = 0
            # intervals of conflicting colors
            intervals = [(colors[w] - G[v][w]["weight"],colors[w] + G[v][w]["weight"])
                         for w in G.neighbors(v) if colors[w] > -1]
            # check the smallest upper bound such that not in conflicting interval
            intervals.sort()
            invIndx = 0
            while invIndx < len(intervals) and colors[v] > intervals[invIndx][0]:
                colors[v] = max(colors[v],intervals[invIndx][1])
                invIndx+=1
            max_color = max(max_color,colors[v])
            for w in G.neighbors(v):
                if colors[w] == -1:
                    neighbouring_colors[w].add(v)
                    saturations.put((w,len(neighbouring_colors)))

    c_groups = {}
    for v,c in enumerate(colors):
        if c not in c_groups:
            c_groups[c] = []
        c_groups[c].append(v)

    Utility.checkColoringBCP(G,c_groups)


    return max_color


def DSaturConsMultiBandwidth(G:nx.Graph)->int:
    """
    Calculates a Greedy coloring for the BCP and returns the number of colors used
    :param G: Graph to color according to BCP
    :return: number of colors in calculated coloring
    """
    n = G.number_of_nodes()
    # initialize color as -1 -> not colored
    colors = [-1]*n
    neighbouring_colors = [set() for i in range(n)]
    saturations = PriorityQueue()

    max_color = 0
    while min(colors) == -1:
        saturations.put((max(filter(lambda x: colors[x] ==-1,G.nodes),key = lambda x: G.degree(x)),0))
        while not saturations.empty():
            v = saturations.get()[0]
            if colors[v] > -1:
                continue
            colors[v] = 0
            # intervals of conflicting colors
            intervals = [(colors[w] - G[v][w]["weight"]-G.nodes[v]["demand"]+1,
                          colors[w] + G[v][w]["weight"]+G.nodes[w]["demand"]-1)
                         for w in G.neighbors(v) if colors[w] > -1]
            # check the smallest upper bound such that not in conflicting interval
            intervals.sort()
            invIndx = 0
            while invIndx < len(intervals) and colors[v] > intervals[invIndx][0]:
                colors[v] = max(colors[v],intervals[invIndx][1])
                invIndx+=1
            max_color = max(max_color,colors[v]+G.nodes[v]["demand"]-1)
            for w in G.neighbors(v):
                if colors[w] == -1:
                    neighbouring_colors[w].add(v)
                    saturations.put((w,len(neighbouring_colors)))

    c_groups = {}
    for v,c in enumerate(colors):
        if c not in c_groups:
            c_groups[c] = []
        c_groups[c].append(v)

    Utility.checkColoringBCP(G,c_groups)

    return max_color











