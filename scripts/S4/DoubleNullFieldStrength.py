import sympy as sp
u,v,th,ph=sp.symbols('u v th ph'); X=[u,v,th,ph]
Om=sp.Function('Om')(u,v); r=sp.Function('r')(u,v); W=sp.Function('W')(u,v); l=sp.symbols('l')
s=sp.sin(th); c=sp.cos(th)
g=sp.Matrix([[0,-Om,0,0],[-Om,0,0,0],[0,0,r**2,0],[0,0,0,r**2*s**2]]); gi=g.inv()
Aym=[[0,0,W,0],[0,0,0,W*s],[0,0,0,c]]
from sympy import LeviCivita as eps
F=[[[sp.diff(Aym[a][n],X[m])-sp.diff(Aym[a][m],X[n])+sum(eps(a,b,e)*Aym[b][m]*Aym[e][n] for b in range(3) for e in range(3)) for n in range(4)] for m in range(4)] for a in range(3)]
sg=Om*r**2*s
Fup=lambda a,m,n: sum(gi[m,al]*gi[n,be]*F[a][al][be] for al in range(4) for be in range(4))
def YM(a,n):
    return sp.simplify(sum(sp.diff(sg*Fup(a,m,n),X[m]) for m in range(4)) + sg*sum(eps(a,b,e)*Aym[b][m]*Fup(e,m,n) for m in range(4) for b in range(3) for e in range(3)))
for a in range(3):
    for n in range(4):
        y=YM(a,n)
        if y!=0: print(a,n,sp.factor(y))
