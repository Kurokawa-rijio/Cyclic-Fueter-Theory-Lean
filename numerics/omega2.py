# conformally flat g = Omega^2 * ESU, traceless YM source (l=1).
# null-null: N_pm = 2O^2 - 2O(O_ee + O_uu +- 2 O_eu) + 4(O_e +- O_u)^2  must equal 4 (W_e +- W_u)^2 / sin^2 u
# plus-minus: M = O^2 * [ -2 - 2(O_ee - O_uu)/O + 2 box(O)/O + 2(O_e^2 - O_u^2)/O^2 ] must equal 2 (1-W^2)^2 / sin^4 u
import numpy as np
def parts(A,B,e,u):
    c,s=np.cos(e),np.sin(e); cu,su=np.cos(u),np.sin(u)
    O=A*c+B/su; Oe=-A*s; Oee=-A*c; Ou=-B*cu/su**2; Ouu=B*(1+cu**2)/su**3; Oeu=0*e
    box=-Oee+Ouu+2*cu/su*Ou
    Np=2*O**2-2*O*(Oee+Ouu+2*Oeu)+4*(Oe+Ou)**2
    Nm=2*O**2-2*O*(Oee+Ouu-2*Oeu)+4*(Oe-Ou)**2
    M=O**2*(-2-2*(Oee-Ouu)/O+2*box/O+2*(Oe**2-Ou**2)/O**2)
    return O,box,Np,Nm,M
# sanity: cap and neck
e,u=0.3,1.1
for A,B in [(1,0),(0,1)]:
    O,box,Np,Nm,M=parts(A,B,e,u); print((A,B),"box-O",box-O,"N+",Np,"N-",Nm,"M",M, "M*sin^4/2",M*np.sin(u)**4/2)
# superposition
E,U=np.meshgrid(np.linspace(-1.4,1.4,281),np.linspace(0.05,np.pi-0.05,301),indexing='ij')
for A,B in [(1,1),(1,0.3),(0.3,1),(1,-0.5)]:
    O,box,Np,Nm,M=parts(A,B,E,U)
    ok=O>0
    X=M*np.sin(U)**4/2   # = (1-W^2)^2
    # (W_e + W_u)^2 = Np sin^2/4,  (W_e - W_u)^2 = Nm sin^2/4  -> W_e*W_u = (Np-Nm) sin^2 /16
    print(f"A={A},B={B}: Omega>0 frac {ok.mean():.2f}; min N+ {Np[ok].min():.3g}, min N- {Nm[ok].min():.3g}, min M {M[ok].min():.3g}")

print("--- analytic N+- check")
rng=np.random.default_rng(0)
for _ in range(3):
    A,B,e,u=rng.uniform(-2,2),rng.uniform(-2,2),rng.uniform(-3,3),rng.uniform(0.1,3)
    O,box,Np,Nm,M=parts(A,B,e,u); su=np.sin(u)
    an=4*A*A+A*B*np.cos(e)*(8-4/su**2)/su
    print(Np-(an+8*A*B*np.sin(e)*np.cos(u)/su**2), Nm-(an-8*A*B*np.sin(e)*np.cos(u)/su**2))
print("--- integrability in window A=-1,B=1 (cos eta>0, N>=0 near poles)")
for A,B in [(-1,1),(-0.5,1),(-1,0.5)]:
    e=np.linspace(-0.6,0.6,121); u=np.linspace(0.15,1.2,211); E,U=np.meshgrid(e,u,indexing='ij')
    O,box,Np,Nm,M=parts(A,B,E,U); su=np.sin(U)
    good=(O>0)&(Np>=0)&(Nm>=0)&(M>=0)
    X=np.sqrt(np.maximum(M,0)*su**4/2)          # |1-W^2|
    best=np.inf
    for sgn in (+1,-1):                         # W^2 = 1 -+ X
        W2=1-sgn*X
        if (W2<0).all(): continue
        W=np.sqrt(np.maximum(W2,0))
        We=np.gradient(W,e,axis=0); Wu=np.gradient(W,u,axis=1)
        r1=(We+Wu)**2-Np*su**2/4; r2=(We-Wu)**2-Nm*su**2/4
        scale=np.abs(Np*su**2/4)+np.abs(Nm*su**2/4)+1e-12
        res=np.nanmedian(((np.abs(r1)+np.abs(r2))/scale)[good&(W2>0)])
        best=min(best,res)
    print(f"A={A},B={B}: frac admissible {good.mean():.2f}, median relative mismatch of W-gradient {best:.3f}")
print("--- control: pure cap A=1,B=0 and pure neck")
for A,B in [(1,0)]:
    e=np.linspace(-0.6,0.6,121); u=np.linspace(0.15,1.2,211); E,U=np.meshgrid(e,u,indexing='ij')
    O,box,Np,Nm,M=parts(A,B,E,U); su=np.sin(U)
    X=np.sqrt(M*su**4/2); W=np.sqrt(1-X)  # W=cos u (u<pi/2)
    We=np.gradient(W,e,axis=0); Wu=np.gradient(W,u,axis=1)
    print("cap mismatch",np.median(np.abs((We+Wu)**2-Np*su**2/4)/(Np*su**2/4)))
