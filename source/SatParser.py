"""
Parsing outputs of a SAT-Solver in DIMACS format and convert variable assignments to colorings
"""
def parseSatResult(result:str)-> list:
    variables = [0]   #placeholer
    reachedVars = False
    for line in result.splitlines():

        if line[0] == "s" and line.split()[1] == "UNSATISFIABLE":
            return None
        if line[0] == "v":
            #print(line)
            variables += [0 if lit[0] == "-" else 1 for lit in line.split() if lit != "v" and lit != "0"]
            reachedVars = True
        else:
            if reachedVars: return variables



def varsToColor2(vars, n):
    coloring = {}

    for idx,val in enumerate(vars):
        v = idx % n
        i = int(idx/n)
        if val == 1:
            if i not in coloring:
                coloring[i] = []
            coloring[i].append(v)
    return coloring

def varsToColor(vars,x):

    coloring = {}
    colored = set()

    for v,i in x:
        if v in colored:
            continue
        if vars[x[v,i]] == 1:
            if i not in coloring:
                coloring[i] = []
            coloring[i].append(v)
            colored.add(v)
    return coloring

def varsToColor_POP(vars,y):
    coloring = {}

    k = max(y.keys(),key=lambda x: x[1])[1]+1
    n = max(y.keys(),key=lambda x: x[0])[0]+1

    for v in range(n):
        if vars[y[v,0]]==0:
            if 0 not in coloring:
                coloring[0] = []
            coloring[0].append(v)
        for i in range(1,k):
          if vars[y[v,i-1]]-vars[y[v,i]] == 1:
                if i not in coloring:
                    coloring[i] = []
                coloring[i].append(v)

    return coloring



def varsToColor_REP(vars,x):

    coloring = {}
    colored = set()

    for u,v in x:
        if v in colored:
            continue
        if vars[x[u,v]] == 1:
            if u not in coloring:
                coloring[u] = []
            coloring[u].append(v)
            colored.add(v)
    coloring_cannon = {i:coloring[v] for i,v in enumerate(coloring.keys())}
    return coloring_cannon