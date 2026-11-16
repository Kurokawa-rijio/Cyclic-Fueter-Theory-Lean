import sympy as sp
t,x,th,ph=sp.symbols('t x th ph')
def einstein(g,X):
    gi=sp.simplify(g.inv()); n=4
    Gam=[[[sp.simplify(sum(gi[a,d]*(sp.diff(g[d,c],X[b])+sp.diff(g[d,b],X[c])-sp.diff(g[b,c],X[d])) for d in range(n))/2) for c in range(n)] for b in range(n)] for a in range(n)]
    Ric=sp.zeros(n)
    for b in range(n):
        for c in range(n):
            Ric[b,c]=sp.simplify(sum(sp.diff(Gam[a][b][c],X[a])-sp.diff(Gam[a][b][a],X[c]) for a in range(n))+sum(Gam[a][a][e]*Gam[e][b][c]-Gam[a][c][e]*Gam[e][b][a] for a in range(n) for e in range(n)))
    Rs=sp.simplify(sum(gi[a,b]*Ric[a,b] for a in range(n) for b in range(n)))
    G=sp.simplify(Ric-g*Rs/2)
    return Gam,Ric,Rs,G
# diagonal
N=sp.Function('N')(t,x);A=sp.Function('A')(t,x);R=sp.Function('R')(t,x)
g=sp.diag(-N**2,A**2,R**2,R**2*sp.sin(th)**2)
_,_,_,G=einstein(g,[t,x,th,ph])
for (i,j) in [(0,0),(1,1),(0,1),(2,2)]:
    print('diag G',i,j,'=',sp.expand(sp.simplify(G[i,j])))
print('offdiag', [sp.simplify(G[i,j]) for i in range(4) for j in range(4) if i!=j and (i,j)!=(0,1) and (i,j)!=(1,0)])
print('G33/sin2-G22',sp.simplify(G[3,3]/sp.sin(th)**2-G[2,2]))
# double null
u,v=t,x
Om=sp.Function('Om')(u,v);r=sp.Function('r')(u,v)
g2=sp.Matrix([[0,-Om,0,0],[-Om,0,0,0],[0,0,r**2,0],[0,0,0,r**2*sp.sin(th)**2]])
_,_,_,G2=einstein(g2,[u,v,th,ph])
for (i,j) in [(0,0),(1,1),(0,1),(2,2)]:
    print('null G',i,j,'=',sp.expand(sp.simplify(G2[i,j])))
print('offdiag', [sp.simplify(G2[i,j]) for i in range(4) for j in range(4) if i!=j and (i,j)!=(0,1) and (i,j)!=(1,0)])
print('G33/sin2-G22',sp.simplify(G2[3,3]/sp.sin(th)**2-G2[2,2]))
