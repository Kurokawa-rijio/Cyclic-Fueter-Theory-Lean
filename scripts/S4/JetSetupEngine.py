import sympy as sp, itertools, pickle
# jets
def mk(f): 
    return {k:sp.Symbol(f+k) for k in ['','t','x','tt','tx','xx']}
def setup(funs):
    J={f:mk(f) for f in funs}
    inv={f:sp.Symbol('i'+f) for f in funs}
    s,c,is_=sp.symbols('s c is_')
    # derivative of atoms: dict atom -> list of 4 derivatives
    D={}
    z=sp.Integer(0)
    for f in funs:
        j=J[f]
        D[j['']]=[j['t'],j['x'],z,z]
        D[j['t']]=[j['tt'],j['tx'],z,z]
        D[j['x']]=[j['tx'],j['xx'],z,z]
        for k in ['tt','tx','xx']: D[j[k]]=None  # third derivatives should not appear
        D[inv[f]]=[-inv[f]**2*j['t'],-inv[f]**2*j['x'],z,z]
    D[s]=[z,z,c,z]; D[c]=[z,z,-s,z]; D[is_]=[z,z,-is_**2*c,z]
    rels=[J[f]['']*inv[f]-1 for f in funs]+[s*is_-1]
    gens=[inv[f] for f in funs]+[is_]+[J[f]['']for f in funs]+[s]
    return J,inv,(s,c,is_),D,rels,gens
def Der(i,e,D):
    e=sp.expand(e); out=0
    for a in e.free_symbols:
        da=D[a]
        if da is None: raise Exception('third derivative '+str(a))
        out+=sp.diff(e,a)*da[i]
    return sp.expand(out)
def ric(G,D):
    R={}
    for b in range(4):
        for cc in range(4):
            R[b,cc]=sp.expand(sum(Der(a,G[a][b][cc],D)-Der(cc,G[a][b][a],D) for a in range(4))+sum(G[a][a][e]*G[e][b][cc]-G[a][cc][e]*G[e][b][a] for a in range(4) for e in range(4)))
    return R
def tolean(e,J,inv,sc):
    s,c,is_=sc
    names={}
    for f,j in J.items():
        names[j['']]=f; names[j['t']]='d 0 %s'%f; names[j['x']]='d 1 %s'%f
        names[j['tt']]='d 0 (d 0 %s)'%f; names[j['tx']]='d 0 (d 1 %s)'%f; names[j['xx']]='d 1 (d 1 %s)'%f
        names[inv[f]]='%s⁻¹'%f
    names[s]='s';names[c]='c';names[is_]='s⁻¹'
    e=sp.expand(e)
    if e==0: return '0'
    if not e.free_symbols:
        q=sp.Rational(e); return '(%s : S)'%q if q.q!=1 else '(%d : S)'%q.p
    terms=[]
    for mon,coef in sp.Poly(e,*sorted(e.free_symbols,key=str)).terms():
        gens=sorted(e.free_symbols,key=str)
        fac=[]
        for g,p in zip(gens,mon):
            if p==0: continue
            nm=names[g]; nm2=nm if (' ' not in nm) else '('+nm+')'
            if nm.endswith('⁻¹') : nm2=nm
            fac.append(nm2 if p==1 else '%s ^ %d'%(nm2,p))
        coef=sp.Rational(coef)
        cs='(%s : S)'%(str(coef)) if coef.q!=1 else '(%d : S)'%coef.p
        terms.append(' * '.join([cs]+fac))
    return ' + '.join(terms)
def quot(P,rels,gens):
    P=sp.expand(P)
    if P==0: return [0]*len(rels)
    Q,r=sp.reduced(P,rels,*gens)
    assert sp.expand(r)==0, r
    assert sp.expand(P-sum(q*rl for q,rl in zip(Q,rels)))==0
    return Q
