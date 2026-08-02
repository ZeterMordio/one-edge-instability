import itertools
import numpy as np
import networkx as nx
from scipy.optimize import linear_sum_assignment


def build(m):
    V=['s','t']+[f'u{j}' for j in range(1,m+1)]
    E=[('e','s','t')]
    for j in range(1,m+1):
        E += [(f'a{j}','s',f'u{j}'),(f'b{j}',f'u{j}','t')]
    f={v:(0,0,0) for v in V}; g=dict(f)
    f['e']=(2,0,0);g['e']=(1,0,0)
    for j in range(1,m+1):
        f[f'a{j}']=g[f'a{j}']=(0,j,0)
        f[f'b{j}']=g[f'b{j}']=(0,0,m+1-j)
    return V,E,f,g

def b0(V,E,h,x):
    inc=[v for v in V if all(a<=b for a,b in zip(h[v],x))]
    G=nx.Graph(); G.add_nodes_from(inc)
    for name,u,v in E:
        if all(a<=b for a,b in zip(h[name],x)):
            G.add_edge(u,v)
    return nx.number_connected_components(G) if inc else 0

def expected(m):
    d={}
    plus=[(0,0)]+[(j+1,m+1-j) for j in range(1,m)]
    minus=[(j,m+1-j) for j in range(1,m+1)]
    for yz in plus:
        d[(1,*yz)]=d.get((1,*yz),0)+1; d[(2,*yz)]=d.get((2,*yz),0)-1
    for yz in minus:
        d[(1,*yz)]=d.get((1,*yz),0)-1; d[(2,*yz)]=d.get((2,*yz),0)+1
    return {k:v for k,v in d.items() if v}

for m in range(1,16):
    V,E,f,g=build(m)
    D=np.zeros((4,m+2,m+2),dtype=int)
    for x,y,z in itertools.product(range(4),range(m+2),range(m+2)):
        D[x,y,z]=b0(V,E,f,(x,y,z))-b0(V,E,g,(x,y,z))
    # pad negative predecessor with zeros, then successive np.diff recovers atoms
    H=np.pad(D,((1,0),(1,0),(1,0)),constant_values=0)
    M=np.diff(np.diff(np.diff(H,axis=0),axis=1),axis=2)
    rec={(x,y,z):int(M[x,y,z]) for x,y,z in itertools.product(range(4),range(m+2),range(m+2)) if M[x,y,z]}
    assert rec==expected(m),(m,rec,expected(m))
    pos=[]; neg=[]
    for p,c in rec.items():
        (pos if c>0 else neg).extend([p]*abs(c))
    C=np.array([[sum(abs(a-b) for a,b in zip(p,q)) for q in neg] for p in pos])
    rows,cols=linear_sum_assignment(C)
    cost=int(C[rows,cols].sum())
    assert cost==2*m,(m,cost)
print('Independent NetworkX/NumPy/SciPy verification passed for m=1,...,15.')
