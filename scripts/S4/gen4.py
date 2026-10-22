import sympy as sp, pickle
from gen3 import *
def tl(e,J,inv,sc,gen=False):
    s=tolean(e,J,inv,sc)
    if gen:
        for f in J: s=s.replace('%s⁻¹'%f,'i'+f)
        s=s.replace('s⁻¹','is')
    return s
out=[]
def build(kind):
    if kind=='D':
        funs=['N','A','R']
    else:
        funs=['Om','r']
    J,inv,sc,D,rels,gens=setup(funs)
    s,c,is_=sc
    z=0
    if kind=='D':
        N,A,R=[J[f][''] for f in funs]; iN,iA,iR=[inv[f] for f in funs]
        t=lambda f,k:J[f][k]
        G=[[[t('N','t')*iN,t('N','x')*iN,0,0],[t('N','x')*iN,t('A','t')*A*iN**2,0,0],[0,0,t('R','t')*R*iN**2,0],[0,0,0,t('R','t')*R*s**2*iN**2]],
           [[t('N','x')*N*iA**2,t('A','t')*iA,0,0],[t('A','t')*iA,t('A','x')*iA,0,0],[0,0,-(t('R','x')*R*iA**2),0],[0,0,0,-(t('R','x')*R*s**2*iA**2)]],
           [[0,0,t('R','t')*iR,0],[0,0,t('R','x')*iR,0],[t('R','t')*iR,t('R','x')*iR,0,0],[0,0,0,-(s*c)]],
           [[0,0,0,t('R','t')*iR],[0,0,0,t('R','x')*iR],[0,0,0,c*is_],[t('R','t')*iR,t('R','x')*iR,c*is_,0]]]
        g=sp.diag(-N**2,A**2,R**2,R**2*s**2); gi=sp.diag(-iN**2,iA**2,iR**2,iR**2*is_**2)
        comps=[(0,0),(1,1),(2,2),(3,3),(0,1)]; ecomps=[(0,0),(1,1),(2,2),(0,1)]
    else:
        O,r=[J[f][''] for f in funs]; iO,ir=[inv[f] for f in funs]
        t=lambda f,k:J[f][k]
        G=[[[t('Om','t')*iO,0,0,0],[0,0,0,0],[0,0,t('r','x')*r*iO,0],[0,0,0,t('r','x')*r*s**2*iO]],
           [[0,0,0,0],[0,t('Om','x')*iO,0,0],[0,0,t('r','t')*r*iO,0],[0,0,0,t('r','t')*r*s**2*iO]],
           [[0,0,t('r','t')*ir,0],[0,0,t('r','x')*ir,0],[t('r','t')*ir,t('r','x')*ir,0,0],[0,0,0,-(s*c)]],
           [[0,0,0,t('r','t')*ir],[0,0,0,t('r','x')*ir],[0,0,0,c*is_],[t('r','t')*ir,t('r','x')*ir,c*is_,0]]]
        g=sp.Matrix([[0,-O,0,0],[-O,0,0,0],[0,0,r**2,0],[0,0,0,r**2*s**2]]); gi=sp.Matrix([[0,-iO,0,0],[-iO,0,0,0],[0,0,ir**2,0],[0,0,0,ir**2*is_**2]])
        comps=[(0,0),(1,1),(2,2),(3,3),(0,1),(1,0)]; ecomps=[(0,0),(1,1),(2,2),(0,1)]
    G=[[[sp.sympify(e) for e in row] for row in m] for m in G]
    Ric=ric(G,D)
    NF={}
    res={'funs':funs}
    for (i,j) in comps:
        P=Ric[i,j]; Q,rem=sp.reduced(P,rels,*gens)
        NF[i,j]=sp.expand(rem)
        res['ric',i,j]=(tl(NF[i,j],J,inv,sc),[tl(q,J,inv,sc,True) for q in Q])
    rsc_poly=sp.expand(sum(gi[a,b]*NF[a,b] for a in range(4) for b in range(4) if gi[a,b]!=0))
    Q,rem=sp.reduced(rsc_poly,rels,*gens); NFs=sp.expand(rem)
    res['rsc']=(tl(NFs,J,inv,sc),[tl(q,J,inv,sc,True) for q in Q])
    for (i,j) in ecomps:
        P=sp.expand(NF[i,j]-sp.Rational(1,2)*g[i,j]*NFs)
        Q,rem=sp.reduced(P,rels,*gens)
        res['ein',i,j]=(tl(sp.expand(rem),J,inv,sc),[tl(q,J,inv,sc,True) for q in Q],sp.expand(rem))
    res['J']=J;res['inv']=inv;res['sc']=sc
    return res
RD=build('D'); RN=build('N')
for k in [('ein',0,0),('ein',1,1),('ein',0,1)]: print('D',k,RD[k][0][:400])
for k in [('ein',0,0),('ein',0,1),('ein',2,2)]: print('N',k,RN[k][0][:400])
pickle.dump({'D':{k:v for k,v in RD.items() if k not in('J','inv','sc')},'N':{k:v for k,v in RN.items() if k not in('J','inv','sc')}},open('cert.pkl','wb'))
