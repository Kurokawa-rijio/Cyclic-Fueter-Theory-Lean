import sympy as sp
# toy check with abstract functions in 2 coords: mu,nu in {0,1}
t,x=sp.symbols('t x'); X=[t,x]
A=[[sp.Function(f'A{a}{m}')(t,x) for m in range(2)] for a in range(3)]
ep=[sp.Function(f'e{a}')(t,x) for a in range(3)]
f=lambda a,b,c: sp.LeviCivita(a,b,c)
c=sp.Symbol('c')
def F(Ax,a,m,n): return sp.diff(Ax[a][n],X[m])-sp.diff(Ax[a][m],X[n])+c*sum(f(a,b,cc)*Ax[b][m]*Ax[cc][n] for b in range(3) for cc in range(3))
s=sp.Symbol('s')
Ad=[[A[a][m]+s*(sp.diff(ep[a],X[m])+sum(f(a,b,cc)*A[b][m]*ep[cc] for b in range(3) for cc in range(3))) for m in range(2)] for a in range(3)]
dF=sp.diff(F(Ad,0,0,1),s).subs(s,0)
target=sum(f(0,b,cc)*F(A,b,0,1)*ep[cc] for b in range(3) for cc in range(3))
print(sp.factor(sp.expand(dF-target)))
