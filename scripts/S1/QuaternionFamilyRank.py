import sympy as sp
from sympy.algebras.quaternion import Quaternion as Q
one,i,j,k=Q(1,0,0,0),Q(0,1,0,0),Q(0,0,1,0),Q(0,0,0,1)
e=[one,i,j,k]
def real_rank(rows):
    # right-module real 16x16: map y -> sum_a C_ra y_a
    import itertools
    M=[]
    ys=sp.symbols('y0:16')
    yq=[Q(*ys[4*a:4*a+4]) for a in range(4)]
    out=[]
    for r in rows:
        s=Q(0,0,0,0)
        for a in range(4): s=s+r[a]*yq[a]
        out+= [s.a,s.b,s.c,s.d]
    J=sp.Matrix([[sp.diff(o,y) for y in ys] for o in out])
    return J.rank()
Z4=[[e[(m+a)%4] for a in range(4)] for m in range(4)]
V4perm=[[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]]
V4=[[e[p[a]] for a in range(4)] for p in V4perm]
print("Z4 real rank",real_rank(Z4),"V4 real rank",real_rank(V4))
