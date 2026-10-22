import sympy as sp, pickle
from gen3 import setup, Der, tolean
CD={'D':pickle.load(open('certall.pkl','rb'))}; CT=pickle.load(open('certTall.pkl','rb')); YD=pickle.load(open('ymd.pkl','rb'))
funs=['A','R','W','l']
J,inv,sc,D,rels,gens=setup(funs)
s,c,is_=sc
A,R,W,l=[J[f][''] for f in funs]; iA,iR=inv['A'],inv['R']
# l constant
for k in ['t','x','tt','tx','xx']: pass
D[l]=[0,0,0,0]
d=lambda i,e: Der(i,e,D)
h=sp.Rational(1,2)
Dx=lambda f: iA*d(1,f)
Kx=-(d(0,A)*iA); KT=-(d(0,R)*iR); P=A*d(0,W); k=2*l**2
Hc=-2*Dx(Dx(R))*iR + 2*(1-Dx(R)**2-R*Dx(Dx(R)))*iR**2 + 4*Kx*KT + 2*KT**2 - 2*k*(((P*iA)**2+Dx(W)**2)*iR**2 + (1-W**2)**2*iR**4*h)
Mc=2*(Dx(R)*iR)*(Kx-KT) - 2*Dx(KT) - k*(-2*(P*iA)*Dx(W)*iR**2)
eP=d(0,A*d(0,W)) - (d(1,d(1,W)*iA) + A*W*(1-W**2)*iR**2)
eKx=d(0,Kx) - (-2*Dx(Dx(R))*iR + (Kx+2*KT)*Kx - k*(((P*iA)**2+Dx(W)**2)*iR**2 - (1-W**2)**2*iR**4*h))
eKT=d(0,KT) - ((1-Dx(R)**2-R*Dx(Dx(R)))*iR**2 + (Kx+2*KT)*KT - k*((1-W**2)**2*iR**4*h))
# substitute N=1 into 4D NFs (gen symbols named N, Nt, ... iN)
S=sp.Symbol
sub={S('N'):1,S('Nt'):0,S('Nx'):0,S('Ntt'):0,S('Ntx'):0,S('Nxx'):0,S('iN'):1}
# map gen symbol names to ours: the cert pickles used symbols with same names (A, At, ...), W, Wt..., l? 'l' symbol plain
def E(i,j): return sp.expand(CD['D'][('ein',i,j)][2].subs(sub) - 2*l**2*CT[('D','T',i,j)][2].subs(sub))
rr=[A*iA-1,R*iR-1,s*is_-1]; gg=[iA,iR,is_,A,R,s]
targets={(i,j):0 for i in range(4) for j in range(4)}
targets.update({(0,0):h*Hc,(0,1):-A*Mc,(1,0):-A*Mc,(1,1):A**2*(2*eKT+h*Hc),(2,2):R**2*(eKx+eKT+h*Hc),(3,3):s**2*R**2*(eKx+eKT+h*Hc)})
res={}
for ij,tg in targets.items():
    P_=sp.expand(E(*ij)-tg)
    Q,rem=sp.reduced(P_,rr,*gg)
    print(ij,'rem',sp.expand(rem))
    def g(st):
        for f in ['A','R']: st=st.replace('%s⁻¹'%f,'i'+f)
        return st.replace('s⁻¹','is')
    res[ij]=[g(tolean(q,J,inv,sc)) for q in Q]
pickle.dump(res,open('cert4dall.pkl','wb'))
