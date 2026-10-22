import sympy as sp, pickle, re
exec(open('gen.py').read().split("import pickle")[0].replace('print("formal identity residual:",check)',''))
# gauge: N=1, b=0
gsub={}
for (f,i,j),s in list(J.items()):
    if f=='N': gsub[s]= 1 if (i,j)==(0,0) else 0
    if f=='b': gsub[s]=0
gsub[n]=1
Eg={f:sp.expand(E[f].subs(gsub)) for f in fields}
# alpha side
Dxx=lambda e: sp.expand(a*Dx(e))
Kx=-Dt(A)*a; KT=-Dt(R)*r; P=A*Dt(W); k=2*l**2; h=sp.Rational(1,2)
DR=Dxx(R); DDR=Dxx(DR)
H=-2*DDR*r+2*(1-DR**2-R*DDR)*r**2+4*Kx*KT+2*KT**2-2*k*(((P*a)**2+Dxx(W)**2)*r**2+(1-W**2)**2*r**4*h)
M=2*(DR*r)*(Kx-KT)-2*Dxx(KT)-k*(-2*(P*a)*Dxx(W)*r**2)
eP=Dt(P)-(Dx(Dx(W)*a)+A*W*(1-W**2)*r**2)
eKx=Dt(Kx)-(-2*DDR*r+(Kx+2*KT)*Kx-k*(((P*a)**2+Dxx(W)**2)*r**2-(1-W**2)**2*r**4*h))
eKT=Dt(KT)-((1-DR**2-R*DDR)*r**2+(Kx+2*KT)*KT-k*((1-W**2)**2*r**4*h))
claims={'N':A*R**2*H,'b':-2*A**2*R**2*M,'W':-8*l**2*eP,'A':-4*R**2*eKT-R**2*H,'R':-4*A*R*(eKx+eKT)-2*A*R*H}
rels=[A*a-1,R*r-1]
certs={}
for f,c in claims.items():
    d=sp.expand(Eg[f]-c)
    gens=[a,r]+sorted(d.free_symbols-{a,r},key=str)
    Q,rem=sp.reduced(d,rels,*gens)
    print(f,'remainder',sp.expand(rem),'sizes',[len(sp.expand(q).args) for q in Q])
    certs[f]=Q
pickle.dump(certs,open('certs.pkl','wb'))
