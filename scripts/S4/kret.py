import sympy as sp, pickle, time
from gen3 import setup, Der, tolean
funs=['N','A','R']
J,inv,sc,D,rels,gens=setup(funs)
s,c,is_=sc
N,A,R=[J[f][''] for f in funs]; iN,iA,iR=[inv[f] for f in funs]
t=lambda f,k:J[f][k]
G=[[[t('N','t')*iN,t('N','x')*iN,0,0],[t('N','x')*iN,t('A','t')*A*iN**2,0,0],[0,0,t('R','t')*R*iN**2,0],[0,0,0,t('R','t')*R*s**2*iN**2]],
   [[t('N','x')*N*iA**2,t('A','t')*iA,0,0],[t('A','t')*iA,t('A','x')*iA,0,0],[0,0,-(t('R','x')*R*iA**2),0],[0,0,0,-(t('R','x')*R*s**2*iA**2)]],
   [[0,0,t('R','t')*iR,0],[0,0,t('R','x')*iR,0],[t('R','t')*iR,t('R','x')*iR,0,0],[0,0,0,-(s*c)]],
   [[0,0,0,t('R','t')*iR],[0,0,0,t('R','x')*iR],[0,0,0,c*is_],[t('R','t')*iR,t('R','x')*iR,c*is_,0]]]
G=[[[sp.sympify(e) for e in row] for row in m] for m in G]
gdiag=[-N**2,A**2,R**2,R**2*s**2]; gid=[-iN**2,iA**2,iR**2,iR**2*is_**2]
rels=[N*iN-1,A*iA-1,R*iR-1,s*is_-1]; gens=[iN,iA,iR,is_,N,A,R,s]
t0=time.time()
Riem={}
nz=0
for a in range(4):
  for b in range(4):
    for cc in range(4):
      for e in range(4):
        v=sp.expand(Der(cc,G[a][e][b],D)-Der(e,G[a][cc][b],D)+sum(G[a][cc][f]*G[f][e][b]-G[a][e][f]*G[f][cc][b] for f in range(4)))
        Riem[a,b,cc,e]=v
        if v!=0: nz+=1
print('nonzero Riem',nz,time.time()-t0)
K=sp.expand(sum(gdiag[a]*gid[b]*gid[cc]*gid[e]*Riem[a,b,cc,e]**2 for a in range(4) for b in range(4) for cc in range(4) for e in range(4) if Riem[a,b,cc,e]!=0))
Q,rem=sp.reduced(K,rels+[s**2+c**2-1],*([c]+gens))
rem=sp.expand(rem)
print('K terms',len(rem.args),time.time()-t0)
pickle.dump({'K':rem},open('kret.pkl','wb'))
