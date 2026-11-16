import sympy as sp
O,r,W,l=sp.symbols('O r W l')
Ou,Ov,ru,rv,Wu,Wv,ruu,Ouu,Wuu=sp.symbols('Ou Ov ru rv Wu Wv ruu Ouu Wuu')
# evolution
ruv=(O/2*(l**2*(1-W**2)**2/r**2-1)-ru*rv)/r
# G22: -2 r ruv/O - r^2 Ouv/O^2 + r^2 Ou Ov/O^3 = l^2 (1-W^2)^2/r^2  (2 l^2 * T22, T22=(1-W^2)^2/(2 r^2))
Ouv=sp.solve(sp.Eq(-2*r*ruv/O - r**2*sp.Symbol('Ouv')/O**2 + r**2*Ou*Ov/O**3, l**2*(1-W**2)**2/r**2),sp.Symbol('Ouv'))[0]
Wuv=O*W*(1-W**2)/(2*r**2)
# total v-derivative of quantities (as functions on jets): d_v of u-jets
# need d_v of ruu = d_u(ruv) etc. Use chain: Dv on symbols
def Du(e):
    # derivative along u of expression in (O,r,W,Ou,Ov,ru,rv,Wu,Wv)
    m={O:Ou,r:ru,W:Wu,Ou:Ouu,ru:ruu,Wu:Wuu,Ov:Ouv,rv:ruv,Wv:Wuv}
    return sum(sp.diff(e,k)*m[k] for k in m)
def Dv(e):
    m={O:Ov,r:rv,W:Wv,Ou:Ouv,ru:ruv,Wu:Wuv,ruu:Du(ruv),Ouu:None,Wuu:None}
    out=0
    for k,val in m.items():
        de=sp.diff(e,k)
        if de!=0:
            assert val is not None
            out+=de*val
    return out
Cu=ruu - Ou/O*ru + 2*l**2*Wu**2/r
dv=sp.simplify(Dv(Cu))
print(sp.factor(dv))
print(sp.simplify(dv/Cu))
