# static EYM (l=1): shoot from the regular centre W=1-b r^2 ; watch approach to (r,W)=(1,0)
import numpy as np
def rhs(r,y):
    W,U,m=y; N=1-2*m/r
    dm=N*U*U+(1-W*W)**2/(2*r*r)
    dU=-((2*m-(1-W*W)**2/r)*U+(1-W*W)*W)/(r*r*N)
    return np.array([U,dU,dm])
def shoot(b,rmax=3.0,h=2e-5):
    r=1e-3; y=np.array([1-b*r*r,-2*b*r,2*b*b*r**3]); out=[]; nodes=0; Wold=y[0]
    while r<rmax:
        k1=rhs(r,y);k2=rhs(r+h/2,y+h/2*k1);k3=rhs(r+h/2,y+h/2*k2);k4=rhs(r+h,y+h*k3)
        y=y+h/6*(k1+2*k2+2*k3+k4); r+=h
        N=1-2*y[2]/r
        if y[0]*Wold<0: nodes+=1; out.append((r,N))
        Wold=y[0]
        if N<1e-6 or abs(y[0])>1.5: break
    return r,y,N,nodes,out
for b in [0.70,0.7060,0.70640,0.706420]:
    r,y,N,nodes,out=shoot(b)
    print("b=%.6f stops at r=%.5f W=%.5f N=%.2e nodes=%d ; zeros of W at r:"%(b,r,y[0],N,nodes),' '.join("%.4f"%o[0] for o in out[:6]))
