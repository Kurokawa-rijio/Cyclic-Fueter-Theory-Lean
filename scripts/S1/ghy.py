import sympy as sp
t,x,th,ph=sp.symbols('t x theta phi')
N=sp.Function('N')(t,x);A=sp.Function('A')(t,x);R=sp.Function('R')(t,x)
g=sp.diag(-N**2,A**2,R**2,R**2*sp.sin(th)**2); X=[t,x,th,ph]; gi=g.inv()
Gam=[[[sum(gi[a,d]*(sp.diff(g[d,b],X[c])+sp.diff(g[d,c],X[b])-sp.diff(g[b,c],X[d])) for d in range(4))/2 for c in range(4)] for b in range(4)] for a in range(4)]
def Ric(b,c):
    return sp.simplify(sum(sp.diff(Gam[a][b][c],X[a])-sp.diff(Gam[a][b][a],X[c])+sum(Gam[a][a][d]*Gam[d][b][c]-Gam[a][c][d]*Gam[d][b][a] for d in range(4)) for a in range(4)))
Rs=sp.simplify(sum(gi[b,b]*Ric(b,b) for b in range(4)))
L=sp.simplify(N*A*R**2*Rs)   # sqrt(-g)/sin
print("L =",sp.expand(L))
# guess: P_t = 2*(Adot R^2 + 2 A R Rdot)/N ; P_x = -2*(N' R^2 + 2 N R R')/A
Pt=2*(sp.diff(A,t)*R**2+2*A*R*sp.diff(R,t))/N
Px=-2*(sp.diff(N,x)*R**2+2*N*R*sp.diff(R,x))/A
L1=sp.expand(sp.simplify(L-sp.diff(Pt,t)-sp.diff(Px,x)))
print("L1 =",L1)
print("second derivs in L1:",[d for d in L1.atoms(sp.Derivative) if sum(c for _,c in d.variable_count)>=2])
