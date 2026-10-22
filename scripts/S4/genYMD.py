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
P=sp.expand(sum(Der(m,sg*Fup(0,m,2),D) for m in range(4))+sg*sum(LeviCivita(0,b,e)*Aym[b][m]*Fup(e,m,2) for m in range(4) for b in range(3) for e in range(3)))
Q,rem=sp.reduced(P,rels,*gens); rem=sp.expand(rem)
print('YMD02 =',tolean(rem,J,inv,sc))
flux_x=N*s*J['W']['x']*iA; flux_t=-(A*s*J['W']['t']*iN)
split=sp.expand(Der(1,flux_x,D)+Der(0,flux_t,D))
Q2,rem2=sp.reduced(sp.expand(rem-split),rels,*gens); rem2=sp.expand(rem2)
print('rest =',tolean(rem2,J,inv,sc))
pickle.dump({'ymd':(tolean(rem,J,inv,sc),[g(tolean(q,J,inv,sc)) for q in Q]),'rest':tolean(rem2,J,inv,sc),'restq':[g(tolean(q,J,inv,sc)) for q in Q2]},open('ymd.pkl','wb'))
