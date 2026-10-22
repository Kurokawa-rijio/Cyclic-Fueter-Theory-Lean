import sympy as sp, re
t,x,th,ph=sp.symbols('t x th ph')
X=[t,x,th,ph]
def christ(g):
    gi=sp.simplify(g.inv()); n=4
    return gi,[[[sp.simplify(sum(gi[a,d]*(sp.diff(g[d,c],X[b])+sp.diff(g[d,b],X[c])-sp.diff(g[b,c],X[d])) for d in range(n))/2) for c in range(n)] for b in range(n)] for a in range(n)]
def ricci(g,Gam):
    n=4;Ric=sp.zeros(n)
    for b in range(n):
        for c in range(n):
            Ric[b,c]=sp.simplify(sum(sp.diff(Gam[a][b][c],X[a])-sp.diff(Gam[a][b][a],X[c]) for a in range(n))+sum(Gam[a][a][e]*Gam[e][b][c]-Gam[a][c][e]*Gam[e][b][a] for a in range(n) for e in range(n)))
    return Ric
S,C=sp.symbols('s c')
def lean(e,funs):
    e=sp.simplify(e)
    e=e.subs({sp.sin(th):S,sp.cos(th):C})
    # replace derivatives
    rep={}
    for f in funs:
        F=sp.Function(f)(t,x)
        for (k,nm) in [((t,t),'d 0 (d 0 %s)'),((t,x),'d 0 (d 1 %s)'),((x,x),'d 1 (d 1 %s)'),((t,),'d 0 %s'),((x,),'d 1 %s')]:
            rep[sp.Derivative(F,*k)]=sp.Symbol('('+nm%f+')')
    order=sorted(rep.keys(),key=lambda d:-len(d.variables))
    for k in order: e=e.subs(k,rep[k])
    for f in funs: e=e.subs(sp.Function(f)(t,x),sp.Symbol(f))
    s=sp.sstr(e)
    s=s.replace('**','^')
    # inverse powers: use x⁻¹
    return s
def table(Gam,funs):
    rows=[]
    for a in range(4):
        rb=[]
        for b in range(4):
            rb.append('!['+', '.join(lean(Gam[a][b][c],funs) for c in range(4))+']')
        rows.append('![' + ', '.join(rb)+']')
    return '![' + ',\n    '.join(rows)+']'
N=sp.Function('N')(t,x);A=sp.Function('A')(t,x);R=sp.Function('R')(t,x)
g=sp.diag(-N**2,A**2,R**2,R**2*sp.sin(th)**2)
gi,Gam=christ(g)
print(table(Gam,['N','A','R']))
Om=sp.Function('Om')(t,x);r=sp.Function('r')(t,x)
g2=sp.Matrix([[0,-Om,0,0],[-Om,0,0,0],[0,0,r**2,0],[0,0,0,r**2*sp.sin(th)**2]])
gi2,Gam2=christ(g2)
print(table(Gam2,['Om','r']))
