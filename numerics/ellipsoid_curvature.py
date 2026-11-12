# normalized total scalar curvature of the ellipsoid in R^10 with k axes = a and 10-k axes = b
import numpy as np
from numpy.polynomial.legendre import leggauss
D=10; n=D-1
xg,wg=leggauss(400); t=(xg+1)*np.pi/4; wt=wg*np.pi/4
def E(k,eps):
    la=eps/k; lb=-eps/(D-k); a=np.exp(la); b=np.exp(lb)       # traceless log-deformation
    c2=np.cos(t)**2; s2=np.sin(t)**2                           # y = (cos t * S^{k-1}, sin t * S^{D-k-1})
    # F = sum x_i^2/a_i^2, x=a*y : grad = 2 y_i/a_i ; A = diag(2/a_i^2)
    g2=4*(c2/a**2+s2/b**2); 
    trA=2*(k/a**2+(D-k)/b**2); trA2=4*(k/a**4+(D-k)/b**4)
    nAn=(4*c2/a**2*2/a**2+4*s2/b**2*2/b**2)/g2; nA2n=(4*c2/a**2*4/a**4+4*s2/b**2*4/b**4)/g2
    H=(trA-nAn)/np.sqrt(g2); II2=(trA2-2*nA2n+nAn**2)/g2
    R=H*H-II2
    dA=a**k*b**(D-k)*np.sqrt(c2/a**2+s2/b**2)*np.cos(t)**(k-1)*np.sin(t)**(D-k-1)
    V=np.sum(wt*dA); S=np.sum(wt*R*dA)
    return S/V**((n-2)/n), R.mean()
E0=E(5,0.0)[0]
print("round sphere check: R =",E(3,0.0)[1]," (expected n(n-1) = 72)")
print(" k  c2/trphi2      c3/trphi3      E(eps)/E0 at eps=-2,-1,-.5,.5,1,2")
for k in range(1,10):
    h=0.05; e=[E(k,j*h)[0]/E0 for j in (-2,-1,0,1,2)]
    c2=(e[3]-2*e[2]+e[1])/h**2/2; c3=(e[4]-2*e[3]+2*e[1]-e[0])/(2*h**3)/6
    tr2=1/k+1/(D-k); tr3=1/k**2-1/(D-k)**2
    print(" %d  %.5f  %s  "%(k,c2/tr2,("%.5f"%(c3/tr3)) if abs(tr3)>1e-12 else "  (trphi3=0, c3=%.1e)"%c3),' '.join("%.4f"%(E(k,x)[0]/E0) for x in (-2,-1,-.5,.5,1,2)))
