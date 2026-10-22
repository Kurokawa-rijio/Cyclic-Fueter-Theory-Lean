import sympy as sp
from gen3 import tolean
# atoms
names={}
def A_(nm,lean):
    s=sp.Symbol(nm); names[s]=lean; return s
N,A,R,s,W=[A_(x,x) for x in ['N','A','R','s','W']]
iN,iA,iR,is_=[A_(x,x) for x in ['iN','iA','iR','is']]
Nt,Nx,At,Ax,Rt,Rx,Wt,Wx=[A_(a,'(d %d %s)'%(i,f)) for a,i,f in [('Nt',0,'N'),('Nx',1,'N'),('At',0,'A'),('Ax',1,'A'),('Rt',0,'R'),('Rx',1,'R'),('Wt',0,'W'),('Wx',1,'W')]]
Ntt,Nxx,Att,Rtt,Rxx=[A_(a,'(d %d (d %d %s))'%(i,j,f)) for a,i,j,f in [('Ntt',0,0,'N'),('Nxx',1,1,'N'),('Att',0,0,'A'),('Rtt',0,0,'R'),('Rxx',1,1,'R')]]
O,r,iO,ir=[A_(x,y) for x,y in [('Om','Om'),('r','r'),('iOm','iOm'),('ir','ir')]]
Ou,Ov,ru,rv,Wu,Wv,ruu,ruv,Ouv=[A_(a,b) for a,b in [('Ou','(d 0 Om)'),('Ov','(d 1 Om)'),('ru','(d 0 r)'),('rv','(d 1 r)'),('Wu','(d 0 W)'),('Wv','(d 1 W)'),('ruu','(d 0 (d 0 r))'),('ruv','(d 0 (d 1 r))'),('Ouv','(d 0 (d 1 Om))')]]
l=A_('l','l')
def lean(e):
    e=sp.expand(e)
    if e==0: return '0'
    out=[]
    gens=sorted(e.free_symbols,key=str)
    if not gens:
        q=sp.Rational(e); return '(%s : S)'%q
    for mon,c in sp.Poly(e,*gens).terms():
        f=['(%s : S)'%sp.Rational(c)]
        for g,p in zip(gens,mon):
            if p: f.append(names[g] if p==1 else '%s ^ %d'%(names[g],p))
        out.append(' * '.join(f))
    return ' + '.join(out)
def cert(P,rels,hn):
    P=sp.expand(P)
    gens=[]
    for x in rels: gens+=list(x.free_symbols)
    Q,rem=sp.reduced(P,rels,*gens)
    assert sp.expand(rem)==0,('REM',rem)
    return ' + '.join('(%s) * %s'%(lean(q),h) for q,h in zip(Q,hn) if sp.expand(q)!=0) or '0'
relD=[N*iN-1,A*iA-1,R*iR-1]; hD=['hiN','hiA','hiR']
relN=[O*iO-1,r*ir-1]; hN_=['hiOm','hir']
out={}
einD11=2*A**2*Nt*Rt*iN**3*iR - A**2*Rt**2*iN**2*iR**2 - 2*A**2*Rtt*iN**2*iR - A**2*iR**2 + 2*Nx*Rx*iN*iR + Rx**2*iR**2
Gnn=lambda N_,R_,Nt_,Rt_,Rtt_,k1,k2,iN_,iR_: -iR_**2 - 2*Rtt_*iN_**2*iR_ - Rt_**2*iN_**2*iR_**2 + 2*Nt_*Rt_*iN_**3*iR_ + k2**2*iR_**2 + 2*k1*k2*iN_*iR_
out['gauss']=cert(einD11*iA**2 - Gnn(N,R,Nt,Rt,Rtt,Nx*iA,Rx*iA,iN,iR),relD,hD)
einD00=2*At*Rt*iA*iR + 2*Ax*N**2*Rx*iA**3*iR - N**2*Rx**2*iA**2*iR**2 - 2*N**2*Rxx*iA**2*iR + N**2*iR**2 + Rt**2*iR**2
einD22=At*Nt*R**2*iA*iN**3 - At*R*Rt*iA*iN**2 - Att*R**2*iA*iN**2 - Ax*Nx*R**2*iA**3*iN - Ax*R*Rx*iA**3 + Nt*R*Rt*iN**3 + Nx*R*Rx*iA**2*iN + Nxx*R**2*iA**2*iN - R*Rtt*iN**2 + R*Rxx*iA**2
P22=(-Att*R**2*iA*iN**2 - R*Rtt*iN**2 + At*Nt*R**2*iA*iN**3 + Nt*R*Rt*iN**3 - Ax*Nx*R**2*iA**3*iN + Nx*R*Rx*iA**2*iN - Rx**2*iA**2/2 + sp.Rational(1,2) + Rt**2*iN**2/2)
out['ang']=cert(einD22 + R**2*iN**2/2*einD00 - (R**2*iA**2*iN*Nxx + P22),relD,hD)
# slice: Rt=At=0
e00s=einD00.subs({Rt:0,At:0})
out['slice']=cert(e00s*iN**2 - (1-(Rx*iA)**2 - 2*R*(Rxx*iA**2 - Ax*Rx*iA**3))*iR**2,relD,hD)
tD11=-sp.Rational(1,2)*A**2*W**4*iR**4 + A**2*W**2*iR**4 + A**2*Wt**2*iN**2*iR**2 - sp.Rational(1,2)*A**2*iR**4 + Wx**2*iR**2
tD00=sp.Rational(1,2)*N**2*W**4*iR**4 - N**2*W**2*iR**4 + N**2*Wx**2*iA**2*iR**2 + sp.Rational(1,2)*N**2*iR**4 + Wt**2*iR**2
tD01=2*Wt*Wx*iR**2
Tnn=lambda R_,W_,wt,wx,iR_: wx**2*iR_**2 + wt**2*iR_**2 - (1-W_**2)**2*iR_**4/2
Rho=lambda R_,W_,wt,wx,iR_: wx**2*iR_**2 + wt**2*iR_**2 + (1-W_**2)**2*iR_**4/2
out['tnn']=cert(tD11*iA**2 - Tnn(R,W,Wt*iN,Wx*iA,iR),relD,hD)
out['rho']=cert(tD00*iN**2 - Rho(R,W,Wt*iN,Wx*iA,iR),relD,hD)
out['flux']=cert(tD01*(iN*iA) - 2*(Wt*iN)*(Wx*iA)*iR**2,relD,hD)
# ym flux tube: (N A R^2 s) * iA^2 * iR^2 * Wx = N s Wx iA
out['ymflux']=cert(N*A*R**2*s*iA**2*iR**2*Wx - N*s*(Wx*iA),relD,hD)
out['ymnull']=cert(O*r**2*s*(-iO)*ir**2*Wv - (-(s*Wv)),relN,hN_)
# mixed: einN01 = 2 l^2 tN01  <=> ... ; forward: from h: E=T  derive target. linear_combination coefficient c*h + cert
einN01=O*ir**2 + 2*ir**2*ru*rv + 2*ir*ruv
tN01=sp.Rational(1,2)*O*W**4*ir**4 - O*W**2*ir**4 + sp.Rational(1,2)*O*ir**4
tgt=r*ruv + ru*rv - (O/2*(l**2*(1-W**2)**2*ir**2-1))
# forward: tgt - c*(einN01 - 2 l^2 tN01) in ideal with c = r^2/2
out['mixed_fwd']=cert(tgt - r**2/2*(einN01-2*l**2*tN01),relN,hN_)
# backward: (einN01 - 2 l^2 tN01) - c*tgt in ideal, c = 2 ir^2
out['mixed_bwd']=cert((einN01-2*l**2*tN01) - 2*ir**2*tgt,relN,hN_)
import pickle; pickle.dump(out,open('cert5.pkl','wb'))
for k,v in out.items(): print(k,len(v))
