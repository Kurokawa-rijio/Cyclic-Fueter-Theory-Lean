import sympy as sp, pickle
from cert5 import lean, names, A_
CD=pickle.load(open('cert.pkl','rb')); CT=pickle.load(open('certT.pkl','rb'))
out={}
# ---------- constraint propagation (null) ----------
O,r,W,l=[sp.Symbol(x) for x in ['Om','r','W','l']]
iO,ir=sp.Symbol('iOm'),sp.Symbol('ir')
ru,rv,ruu,ruv,rvv,ruuv,ruvv=[A_(a,b) for a,b in [('ru','(d 0 r)'),('rv','(d 1 r)'),('ruu','(d 0 (d 0 r))'),('ruv','(d 0 (d 1 r))'),('rvv','(d 1 (d 1 r))'),('ruuv','(d 0 (d 0 (d 1 r)))'),('ruvv','(d 1 (d 0 (d 1 r)))')]]
Ou,Ov,Ouv=[A_(a,b) for a,b in [('Ou','(d 0 Om)'),('Ov','(d 1 Om)'),('Ouv','(d 0 (d 1 Om))')]]
Wu,Wv,Wuv=[A_(a,b) for a,b in [('Wu','(d 0 W)'),('Wv','(d 1 W)'),('Wuv','(d 0 (d 1 W))')]]
for x,y in [(O,'Om'),(r,'r'),(W,'W'),(l,'l'),(iO,'iOm'),(ir,'ir')]: names[x]=y
h=sp.Rational(1,2)
Er=h*O*(l**2*(1-W**2)**2*ir**2-1)*ir - ru*rv*ir
EO=Ou*Ov*iO - 2*O*ruv*ir - O**2*l**2*(1-W**2)**2*ir**4
EW=h*O*W*(1-W**2)*ir**2
D0={O:Ou,r:ru,W:Wu,rv:ruv,ru:ruu,Ov:Ouv,Wv:Wuv,iO:-iO**2*Ou,ir:-ir**2*ru,l:0}
D1={O:Ov,r:rv,W:Wv,ru:ruv,rv:rvv,ruu:ruuv,Ou:Ouv,Wu:Wuv,ruv:ruvv,iO:-iO**2*Ov,ir:-ir**2*rv,l:0}
def Dd(e,Dm):
    e=sp.expand(e); out=0
    for a in e.free_symbols:
        if a not in Dm: raise Exception('no deriv '+str(a))
        out+=sp.diff(e,a)*Dm[a]
    return sp.expand(out)
rels=[O*iO-1,r*ir-1]
Cu=ruu-Ou*iO*ru+2*l**2*Wu**2*ir
Cv=rvv-Ov*iO*rv+2*l**2*Wv**2*ir
# u-constraint along v
H1=ruuv-Dd(Er,D0); H2=ruv-Er; H3=Ouv-EO; H4=Wuv-EW
G=Dd(Cu,D1)+rv*ir*Cu
gens=[ruuv,Ouv,Wuv,ruv,iO,ir,ruvv,rvv,ruu,ru,rv,Ou,Ov,Wu,Wv,O,r,W,l]
Q,rem=sp.reduced(G,[H1,H3,H4,H2]+rels,*gens,order='lex')
assert sp.expand(rem)==0, rem
out['cu']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hr1','hO','hW','hr','hiOm','hir']) if sp.expand(q)!=0)
# v-constraint along u: d0(Cv); d0 rvv = d1(d0(d1 r)) = ruvv ; d0 Ov = Ouv ; d0 Wv = Wuv; d0 rv = ruv
D0b=dict(D0); D0b[rvv]=ruvv; D0b[Ov]=Ouv; D0b[Wv]=Wuv; D0b[rv]=ruv
H1b=ruvv-Dd(Er,D1)
Gb=Dd(Cv,D0b)+ru*ir*Cv
gensb=[ruvv,Ouv,Wuv,ruv,iO,ir,ruuv,rvv,ruu,ru,rv,Ou,Ov,Wu,Wv,O,r,W,l]
Q,rem=sp.reduced(Gb,[H1b,H3,H4,H2]+rels,*gensb,order='lex')
assert sp.expand(rem)==0, rem
out['cv']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hr1','hO','hW','hr','hiOm','hir']) if sp.expand(q)!=0)
print('prop ok')
# ---------- goursat forms ----------
einN22=Ou*Ov*iO**3*r**2 - Ouv*iO**2*r**2 - 2*iO*r*ruv
tN22=h*W**4*ir**2 - W**2*ir**2 + h*ir**2
c=-O**2*ir**2
Q,rem=sp.reduced(sp.expand((Ouv-EO) - c*(einN22-2*l**2*tN22)),rels,iO,ir,O,r)
assert sp.expand(rem)==0
out['gO']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hiOm','hir']) if sp.expand(q)!=0) or '0'
out['gO_c']=lean(c)
s_=sp.Symbol('s'); is_=sp.Symbol('is'); names[s_]='s'; names[is_]='is'
ym02=-O*W**3*ir**2*s_ + O*W*ir**2*s_ - 2*Wuv*s_
c=-h*is_
Q,rem=sp.reduced(sp.expand((Wuv-EW) - c*ym02),rels+[s_*is_-1],iO,ir,is_,O,r,s_)
assert sp.expand(rem)==0
out['gW']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hiOm','hir','his']) if sp.expand(q)!=0) or '0'
mixed=r*ruv+ru*rv-(O/2*(l**2*(1-W**2)**2*ir**2-1))
Q,rem=sp.reduced(sp.expand((ruv-Er)-ir*mixed),rels,iO,ir,O,r)
assert sp.expand(rem)==0
out['gr']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hiOm','hir']) if sp.expand(q)!=0) or '0'
# constraints uu/vv equivalence: einN00 - 2 l^2 tN00 = -2 ir Cu
einN00=2*Ou*iO*ir*ru-2*ir*ruu; tN00=2*Wu**2*ir**2
Q,rem=sp.reduced(sp.expand((einN00-2*l**2*tN00)+2*ir*Cu),rels,iO,ir,O,r); assert sp.expand(rem)==0
out['cuu']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hiOm','hir']) if sp.expand(q)!=0) or '0'
print('goursat ok', out['gr'], '|', out['cuu'])
pickle.dump(out,open('cert6.pkl','wb'))
einN11=2*Ov*iO*ir*rv-2*ir*rvv; tN11=2*Wv**2*ir**2
Q,rem=sp.reduced(sp.expand((einN11-2*l**2*tN11)+2*ir*Cv),rels,iO,ir,O,r); assert sp.expand(rem)==0
out['cvv']=' + '.join('(%s) * %s'%(lean(q),hn) for q,hn in zip(Q,['hiOm','hir']) if sp.expand(q)!=0) or '0'
pickle.dump(out,open('cert6.pkl','wb'))
print('cvv',out['cvv'])
