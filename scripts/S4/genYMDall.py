import sympy as sp, pickle
from gen3 import setup, Der, tolean
from sympy import LeviCivita
funs=['N','A','R','W']
J,inv,sc,D,rels,gens=setup(funs)
s,c,is_=sc
N,A,R,W=[J[f][''] for f in funs]; iN,iA,iR=inv['N'],inv['A'],inv['R']
rels=[N*iN-1,A*iA-1,R*iR-1,s*is_-1]; gens=[iN,iA,iR,is_,N,A,R,s]
gi=sp.diag(-iN**2,iA**2,iR**2,iR**2*is_**2)
Aym=[[0,0,W,0],[0,0,0,W*s],[0,0,0,c]]
F=[[[sp.expand(Der(m,Aym[a][n],D)-Der(n,Aym[a][m],D)+sum(LeviCivita(a,b,e)*Aym[b][m]*Aym[e][n] for b in range(3) for e in range(3))) for n in range(4)] for m in range(4)] for a in range(3)]
sg=N*A*R**2*s
Fup=lambda a,m,n: sp.expand(sum(gi[m,al]*gi[n,be]*F[a][al][be] for al in range(4) for be in range(4)))
def g(st):
    for f in ['N','A','R']: st=st.replace('%s⁻¹'%f,'i'+f)
    return st.replace('s⁻¹','is')
res={}
for a in range(3):
  for n in range(4):
    P=sp.expand(sum(Der(m,sg*Fup(a,m,n),D) for m in range(4))+sg*sum(LeviCivita(a,b,e)*Aym[b][m]*Fup(e,m,n) for m in range(4) for b in range(3) for e in range(3)))
    Q,rem=sp.reduced(P,rels,*gens); rem=sp.expand(rem)
    res[a,n]=(tolean(rem,J,inv,sc),[g(tolean(q,J,inv,sc)) for q in Q])
    print(a,n,tolean(rem,J,inv,sc)[:80])
pickle.dump(res,open('ymdall.pkl','wb'))
