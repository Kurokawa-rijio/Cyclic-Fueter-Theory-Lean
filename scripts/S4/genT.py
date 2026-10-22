import sympy as sp, pickle
from gen3 import *
from sympy import LeviCivita
res={}
for kind in ['D','N']:
    funs=['N','A','R','W'] if kind=='D' else ['Om','r','W']
    J,inv,sc,D,rels,gens_=setup(funs)
    s,c,is_=sc
    W=J['W']['']
    if kind=='D':
        N,A,R=[J[f][''] for f in ['N','A','R']]; iN,iA,iR=[inv[f] for f in ['N','A','R']]
        g=sp.diag(-N**2,A**2,R**2,R**2*s**2); gi=sp.diag(-iN**2,iA**2,iR**2,iR**2*is_**2)
        rels=[N*iN-1,A*iA-1,R*iR-1,s*is_-1]; gens=[iN,iA,iR,is_,N,A,R,s]
    else:
        O,r=[J[f][''] for f in ['Om','r']]; iO,ir=[inv[f] for f in ['Om','r']]
        g=sp.Matrix([[0,-O,0,0],[-O,0,0,0],[0,0,r**2,0],[0,0,0,r**2*s**2]]); gi=sp.Matrix([[0,-iO,0,0],[-iO,0,0,0],[0,0,ir**2,0],[0,0,0,ir**2*is_**2]])
        rels=[O*iO-1,r*ir-1,s*is_-1]; gens=[iO,ir,is_,O,r,s]
    Aym=[[0,0,W,0],[0,0,0,W*s],[0,0,0,c]]
    F=[[[sp.expand(Der(m,Aym[a][n],D)-Der(n,Aym[a][m],D)+sum(LeviCivita(a,b,cc)*Aym[b][m]*Aym[cc][n] for b in range(3) for cc in range(3))) for n in range(4)] for m in range(4)] for a in range(3)]
    res[kind,'F']=[[[tolean(F[a][m][n],J,inv,sc) for n in range(4)] for m in range(4)] for a in range(3)]
    F2=sp.expand(sum(F[a][al][be]*gi[al,ga]*gi[be,de]*F[a][ga][de] for a in range(3) for al in range(4) for be in range(4) for ga in range(4) for de in range(4)))
    for (m,n) in [(0,0),(1,1),(0,1),(2,2)]+([(1,2),(1,3)] if kind=='N' else []):
        T=sp.expand(sum(F[a][m][la]*gi[la,ka]*F[a][n][ka] for a in range(3) for la in range(4) for ka in range(4))-sp.Rational(1,4)*g[m,n]*F2)
        Q,rem=sp.reduced(T,rels,*gens)
        res[kind,'T',m,n]=(tolean(sp.expand(rem),J,inv,sc),[tolean(q,J,inv,sc) for q in Q],sp.expand(rem))
        print(kind,m,n,tolean(sp.expand(rem),J,inv,sc))
    res[kind,'gens']=None
pickle.dump(res,open('certT.pkl','wb'))
