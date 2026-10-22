import sympy as sp, pickle, time
from gen3 import setup, Der, tolean
from cert5 import lean as clean, names, A_
exec(open('kret.py').read().split("t0=time.time()")[0])
Riem={}
for a in range(4):
  for b in range(4):
    for cc in range(4):
      for e in range(4):
        Riem[a,b,cc,e]=sp.expand(Der(cc,G[a][e][b],D)-Der(e,G[a][cc][b],D)+sum(G[a][cc][f]*G[f][e][b]-G[a][e][f]*G[f][cc][b] for f in range(4)))
K=sp.expand(sum(gdiag[a]*gid[b]*gid[cc]*gid[e]*Riem[a,b,cc,e]**2 for a in range(4) for b in range(4) for cc in range(4) for e in range(4)))
rr=rels+[s**2+c**2-1]
Q,rem=sp.reduced(K,rr,*([c]+gens))
rem=sp.expand(rem)
def g(st):
    for f in ['N','A','R']: st=st.replace('%s⁻¹'%f,'i'+f)
    return st.replace('s⁻¹','is')
qs=[g(tolean(q,J,inv,sc)) for q in Q]
out={'rhs':tolean(rem,J,inv,sc),'q':qs}
print('rhs len',len(out['rhs']),'q lens',[len(x) for x in qs])
pickle.dump(out,open('kret_cert.pkl','wb'))
# cap on shell certificate
sym=sp.Symbol
a_,at,att,X,Y,ia,iX,l=[A_(x,y) for x,y in [('a','a'),('at','(d 0 a)'),('att','(d 0 (d 0 a))'),('X','X'),('Y','Y'),('ia','ia'),('iX','iX'),('l','l')]]
sub={sym('N'):a_,sym('Nt'):at,sym('Nx'):0,sym('Ntt'):att,sym('Ntx'):0,sym('Nxx'):0,
 sym('A'):a_,sym('At'):at,sym('Ax'):0,sym('Att'):att,sym('Atx'):0,sym('Axx'):0,
 sym('R'):a_*X,sym('Rt'):at*X,sym('Rx'):a_*Y,sym('Rtt'):att*X,sym('Rtx'):at*Y,sym('Rxx'):-a_*X,
 sym('iN'):ia,sym('iA'):ia,sym('iR'):ia*iX}
Kc=sp.expand(rem.subs(sub))
GB=[Y**2+X**2-1, X*iX-1, att+a_, at**2+a_**2-l**2, a_*ia-1]
Q2,r2=sp.reduced(sp.expand(Kc-24*l**4*ia**8),GB,Y,iX,att,at,ia,X,a_,l,order='lex')
assert sp.expand(r2)==0, r2
out2=' + '.join('(%s) * %s'%(clean(q),h) for q,h in zip(Q2,['hXY','hiX','h22','h00','hia']) if sp.expand(q)!=0)
print('cap cert len',len(out2))
pickle.dump(out2,open('kret_cap.pkl','wb'))
