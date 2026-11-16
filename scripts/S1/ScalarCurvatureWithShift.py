import sympy as sp, pickle
t,x,th,ph=sp.symbols('t x theta phi')
F=lambda n: sp.Function(n)(t,x)
N,A,R,b=F('N'),F('A'),F('R'),F('b')
X=[t,x,th,ph]
g=sp.zeros(4); g[0,0]=-N**2+A**2*b**2; g[0,1]=g[1,0]=A**2*b; g[1,1]=A**2; g[2,2]=R**2; g[3,3]=R**2*sp.sin(th)**2
gi=sp.simplify(g.inv())
Gam=[[[sp.simplify(sum(gi[a,d]*(sp.diff(g[d,bb],X[c])+sp.diff(g[d,c],X[bb])-sp.diff(g[bb,c],X[d])) for d in range(4))/2) for c in range(4)] for bb in range(4)] for a in range(4)]
def Ric(bb,c):
    return sum(sp.diff(Gam[a][bb][c],X[a])-sp.diff(Gam[a][bb][a],X[c])+sum(Gam[a][a][d]*Gam[d][bb][c]-Gam[a][c][d]*Gam[d][bb][a] for d in range(4)) for a in range(4))
Rs=sum(gi[i,j]*Ric(i,j) for i in range(4) for j in range(4) if gi[i,j]!=0)
L=sp.simplify(sp.expand(N*A*R**2*Rs))
dt=lambda f: sp.diff(f,t); dx=lambda f: sp.diff(f,x)
K=(dt(A)-dx(A*b))/(N*A)+2*(dt(R)-b*dx(R))/(N*R)
Pt=2*A*R**2*K
Px0=-2*(dx(N)*R**2+2*N*R*dx(R))/A
for name,Px in [("Px0",Px0),("Px0 - b*Pt",Px0-b*Pt)]:
    L1=sp.expand(sp.simplify(L-dt(Pt)-dx(Px)))
    sec=[d for d in L1.atoms(sp.Derivative) if sum(c for _,c in d.variable_count)>=2]
    print(name,"second derivs:",sec)
    if not sec:
        print("L1 =",L1); pickle.dump((L,Pt,Px,L1),open('shiftL.pkl','wb'))
