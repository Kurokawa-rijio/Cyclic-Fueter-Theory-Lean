import sympy as sp, pickle
t,x,th,ph=sp.symbols('t x th ph'); X=[t,x,th,ph]
N=sp.Function('N')(t,x);A=sp.Function('A')(t,x);R=sp.Function('R')(t,x)
s=sp.sin(th);c=sp.cos(th)
d=lambda i,e: sp.diff(e,X[i])
GD=[[[d(0,N)/N,d(1,N)/N,0,0],[d(1,N)/N,d(0,A)*A/N**2,0,0],[0,0,d(0,R)*R/N**2,0],[0,0,0,d(0,R)*R*s**2/N**2]],
 [[d(1,N)*N/A**2,d(0,A)/A,0,0],[d(0,A)/A,d(1,A)/A,0,0],[0,0,-d(1,R)*R/A**2,0],[0,0,0,-d(1,R)*R*s**2/A**2]],
 [[0,0,d(0,R)/R,0],[0,0,d(1,R)/R,0],[d(0,R)/R,d(1,R)/R,0,0],[0,0,0,-s*c]],
 [[0,0,0,d(0,R)/R],[0,0,0,d(1,R)/R],[0,0,0,c/s],[d(0,R)/R,d(1,R)/R,c/s,0]]]
def Ric(b,cc):
    return sum(d(a,GD[a][b][cc])-d(cc,GD[a][b][a]) for a in range(4))+sum(GD[a][a][e]*GD[e][b][cc]-GD[a][cc][e]*GD[e][b][a] for a in range(4) for e in range(4))
r00=sp.simplify(Ric(0,0))
D=lambda f,*k: sp.Derivative(f,*k)
target=-d(0,d(0,A))/A - 2*d(0,d(0,R))/R + d(0,A)*d(0,N)/(A*N) + 2*d(0,N)*d(0,R)/(N*R) + d(1,d(1,N))*N/A**2 - d(1,A)*d(1,N)*N/A**3 + 2*d(1,N)*d(1,R)*N/(A**2*R)
print(sp.simplify(r00-target))
