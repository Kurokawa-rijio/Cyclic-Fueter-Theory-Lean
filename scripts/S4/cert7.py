import sympy as sp, pickle
from cert5 import lean, names, A_
CD=pickle.load(open('cert.pkl','rb')); CT=pickle.load(open('certT.pkl','rb'))
sym=lambda n: sp.Symbol(n)
a,at,att,X,Y,ia,iX,l=[A_(x,y) for x,y in [('a','a'),('at','(d 0 a)'),('att','(d 0 (d 0 a))'),('X','X'),('Y','Y'),('ia','ia'),('iX','iX'),('l','l')]]
sub_cap={sym('N'):a,sym('Nt'):at,sym('Nx'):0,sym('Ntt'):att,sym('Ntx'):0,sym('Nxx'):0,
 sym('A'):a,sym('At'):at,sym('Ax'):0,sym('Att'):att,sym('Atx'):0,sym('Axx'):0,
 sym('R'):a*X,sym('Rt'):at*X,sym('Rx'):a*Y,sym('Rtt'):att*X,sym('Rtx'):at*Y,sym('Rxx'):-a*X,
 sym('iN'):ia,sym('iA'):ia,sym('iR'):ia*iX,sym('W'):Y,sym('Wt'):0,sym('Wx'):-X}
GB=[Y**2+X**2-1, X*iX-1, a*ia-1]; G_=[Y,iX,ia,X,a,at,att,l]
def red(P):
    Q,rem=sp.reduced(sp.expand(P),GB,*G_,order='lex'); return Q,sp.expand(rem)
def certstr(Q,hn=['hXY','hiX','hia']):
    return ' + '.join('(%s) * %s'%(lean(q),h) for q,h in zip(Q,hn) if sp.expand(q)!=0) or '0'
out={}
targets={(0,0):at**2+a**2-l**2,(2,2):2*a*att-at**2+a**2+l**2,(1,1):2*a*att-at**2+a**2+l**2}
for (i,j) in [(0,0),(1,1),(2,2),(0,1)]:
    E=CD['D'][('ein',i,j)][2].subs(sub_cap); T=CT[('D','T',i,j)][2].subs(sub_cap)
    P=sp.expand(E-2*l**2*T)
    Q,rem=red(P)
    print((i,j),'NF:',sp.factor(rem))
    out[(i,j),'nf']=rem
pickle.dump(out,open('cert7tmp.pkl','wb'))
cert={}
ks={(0,0):(3*ia**2, a**2/3),(1,1):(-ia**2,-a**2),(2,2):(-X**2*ia**2,-a**2*iX**2)}
for ij,(k,kinv) in ks.items():
    i,j=ij
    E=CD['D'][('ein',i,j)][2].subs(sub_cap); T=CT[('D','T',i,j)][2].subs(sub_cap)
    P=sp.expand(E-2*l**2*T); t0=targets[ij]
    Qf,rf=red(t0-kinv*P); assert rf==0,(ij,'f',rf)
    Qb,rb=red(P-k*t0); assert rb==0,(ij,'b',rb)
    cert[ij]=(lean(kinv),certstr(Qf),lean(k),certstr(Qb))
E=CD['D'][('ein',0,1)][2].subs(sub_cap); T=CT[('D','T',0,1)][2].subs(sub_cap)
Q,r0=red(E-2*l**2*T); assert r0==0; cert[(0,1)]=certstr(Q)
# neck
C_,S_,iC,il=[A_(x,y) for x,y in [('C','C'),('S','S'),('iC','iC'),('il','il')]]
sub_neck={sym('N'):1,sym('Nt'):0,sym('Nx'):0,sym('Ntt'):0,sym('Ntx'):0,sym('Nxx'):0,
 sym('A'):C_,sym('At'):-S_*il,sym('Ax'):0,sym('Att'):-C_*il**2,sym('Atx'):0,sym('Axx'):0,
 sym('R'):l,sym('Rt'):0,sym('Rx'):0,sym('Rtt'):0,sym('Rtx'):0,sym('Rxx'):0,
 sym('iN'):1,sym('iA'):iC,sym('iR'):il,sym('W'):0,sym('Wt'):0,sym('Wx'):0}
GBn=[C_*iC-1,l*il-1]
for (i,j) in [(0,0),(1,1),(2,2),(0,1)]:
    E=CD['D'][('ein',i,j)][2].subs(sub_neck); T=CT[('D','T',i,j)][2].subs(sub_neck)
    Q,rem=sp.reduced(sp.expand(E-2*l**2*T),GBn,iC,il,C_,l,S_)
    assert sp.expand(rem)==0,(i,j,rem)
    cert['neck',i,j]=' + '.join('(%s) * %s'%(lean(q),h) for q,h in zip(Q,['hiC','hil']) if sp.expand(q)!=0) or '0'
print({k:len(v) if isinstance(v,str) else [len(x) for x in v] for k,v in cert.items()})
pickle.dump(cert,open('cert7.pkl','wb'))
