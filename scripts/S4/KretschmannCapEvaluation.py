import sympy as sp, pickle
K=pickle.load(open('kret.pkl','rb'))['K']
sym=sp.Symbol
a,at,att,X,Y,ia,iX,l,s,c=sp.symbols('a at att X Y ia iX l s c')
sub={sym('N'):a,sym('Nt'):at,sym('Nx'):0,sym('Ntt'):att,sym('Ntx'):0,sym('Nxx'):0,
 sym('A'):a,sym('At'):at,sym('Ax'):0,sym('Att'):att,sym('Atx'):0,sym('Axx'):0,
 sym('R'):a*X,sym('Rt'):at*X,sym('Rx'):a*Y,sym('Rtt'):att*X,sym('Rtx'):at*Y,sym('Rxx'):-a*X,
 sym('iN'):ia,sym('iA'):ia,sym('iR'):ia*iX}
Kc=sp.expand(K.subs(sub))
print([str(x) for x in Kc.free_symbols])
GB=[Y**2+X**2-1, X*iX-1, a*ia-1]
Q,rem=sp.reduced(Kc,GB,Y,iX,ia,X,a,at,att,l,s,c,order='lex')
print('K cap =',sp.factor(rem))
# impose att=-a, at^2=l^2-a^2
r2=sp.expand(rem.subs(att,-a))
GB2=[at**2+a**2-l**2,a*ia-1]
Q2,rem2=sp.reduced(r2,GB2,at,ia,a,l,order='lex')
print('on shell:',sp.factor(rem2))
