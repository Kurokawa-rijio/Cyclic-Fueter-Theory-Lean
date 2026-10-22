import sympy as sp, itertools
l=sp.Symbol('l')
fields=['N','A','R','b','W']
inv={'N':'n','A':'a','R':'r'}
J={}
def jet(f,i,j):
    k=(f,i,j)
    if k not in J: J[k]=sp.Symbol(f'{f}_{i}{j}')
    return J[k]
dJ={}
def djet(f,i,j):
    k=(f,i,j)
    if k not in dJ: dJ[k]=sp.Symbol(f'd{f}_{i}{j}')
    return dJ[k]
IV={f:sp.Symbol(s) for f,s in inv.items()}
def parse(s):
    nm=str(s)
    if nm in inv.values():
        return ('inv',[f for f,v in inv.items() if v==nm][0])
    if nm.startswith('d') and nm[1] in 'NARbW' and '_' in nm:
        return ('var',nm[1],int(nm[-2]),int(nm[-1]))
    if '_' in nm: return ('jet',nm[0],int(nm[-2]),int(nm[-1]))
    return ('const',)
def D(e,which):  # which: 't','x','d' (variation)
    e=sp.expand(e); res=0
    for s in e.free_symbols:
        p=parse(s); de=sp.diff(e,s)
        if p[0]=='const': continue
        if p[0]=='inv':
            f=p[1]; ds=-IV[f]**2*D(jet(f,0,0),which)
        elif p[0]=='jet':
            _,f,i,j=p
            ds = jet(f,i+1,j) if which=='t' else jet(f,i,j+1) if which=='x' else djet(f,i,j)
        else:
            _,f,i,j=p
            if which=='d': raise Exception
            ds = djet(f,i+1,j) if which=='t' else djet(f,i,j+1)
        res+=de*ds
    return sp.expand(res)
N,A,R,b,W=[jet(f,0,0) for f in fields]
n,a,r=IV['N'],IV['A'],IV['R']
Dt=lambda e: D(e,'t'); Dx=lambda e: D(e,'x')
u=Dt(R)-b*Dx(R); v=Dt(A)-Dx(A*b); w=Dt(W)-b*Dx(W)
L1=2*A*N+(2*N*Dx(R)**2+4*R*Dx(N)*Dx(R))*a-2*A*u**2*n-4*R*v*u*n
LYM=-4*l**2*(N*Dx(W)**2*a-A*w**2*n+N*A*(1-W**2)**2*r**2/2)
Lag=sp.expand(L1+LYM)
def pd(e,s):  # partial with chain rule through inverses
    out=sp.diff(e,s)
    for f,iv in IV.items():
        if s==jet(f,0,0): out+= sp.diff(e,iv)*(-iv**2)
    return sp.expand(out)
E={};Tt=0;Tx=0
for f in fields:
    s0,st,sx=jet(f,0,0),jet(f,1,0),jet(f,0,1)
    E[f]=sp.expand(pd(Lag,s0)-Dt(pd(Lag,st))-Dx(pd(Lag,sx)))
    Tt+=djet(f,0,0)*pd(Lag,st); Tx+=djet(f,0,0)*pd(Lag,sx)
Tt=sp.expand(Tt); Tx=sp.expand(Tx)
check=sp.expand(D(Lag,'d')-sum(djet(f,0,0)*E[f] for f in fields)-Dt(Tt)-Dx(Tx))
print("formal identity residual:",check)
def lean(e):
    def atom(s):
        p=parse(s)
        if p[0]=='inv': return f'{p[1]}⁻¹'
        if p[0]=='const': return 'l'
        if p[0]=='jet':
            _,f,i,j=p; t=f
            for _ in range(i): t=f'dt ({t})' if ' ' in t else f'dt {t}'
            for _ in range(j): t=f'dx ({t})' if ' ' in t else f'dx {t}'
            return t
        _,f,i,j=p; t=f'δ {f}'
        for _ in range(i): t=f'dt ({t})'
        for _ in range(j): t=f'dx ({t})'
        return t
    e=sp.expand(e)
    terms=[]
    for mon,c in sp.Poly(e,*sorted(e.free_symbols,key=str)).terms():
        gens=sorted(e.free_symbols,key=str)
        fac=[]
        for g,p in zip(gens,mon):
            if p==0: continue
            at=atom(g); at=f'({at})' if ' ' in at else at
            fac.append(at if p==1 else f'{at}^({p}:ℕ)')
        cs = f'({c})' if c<0 or not c.is_Integer else str(c)
        if c.is_Rational and not c.is_Integer: cs=f'({c.p}/{c.q} : S)'
        terms.append(' * '.join([cs]+fac) if fac else cs)
    return ' + '.join(terms) if terms else '0'
import pickle
pickle.dump((Lag,E,Tt,Tx),open('stage2.pkl','wb'))
out=open('defs.lean','w')
out.write(f"def Lag : S := {lean(Lag)}\n\n")
for f in fields: out.write(f"def E{f} : S := {lean(E[f])}\n\n")
out.write(f"def Tht : S := {lean(Tt)}\n\ndef Thx : S := {lean(Tx)}\n")
out.close()
print({f:len(E[f].args) for f in fields}, len(Tt.args), len(Tx.args))
