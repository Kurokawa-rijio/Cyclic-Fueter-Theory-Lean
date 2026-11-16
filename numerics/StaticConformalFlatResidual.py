import numpy as np
from scipy.integrate import solve_ivp
l=1.0
for B in [1/np.pi, 0.2, 0.5, 1.0]:
    a=B/(np.sqrt(12)*l)
    u0=1e-3
    W0=1-a*u0**2; Wp0=-2*a*u0
    def rhs(u,y):
        W,Wp=y; s=np.sin(u)
        return [Wp,-W*(1-W*W)/s**2]
    sol=solve_ivp(rhs,[u0,3.1],[W0,Wp0],rtol=1e-11,atol=1e-13,dense_output=True)
    out=[]
    for u in [0.05,0.3,0.8,1.5,2.2,2.9]:
        W,Wp=sol.sol(u); s=np.sin(u); c=np.cos(u)
        Om=B*u/s; Omp=B*(s-u*c)/s**2
        lhs=Om**2+Omp**2
        rhs_=2*l**2*(Wp**2/s**2+(1-W*W)**2/(2*s**4))
        out.append(f"u={u}: W={W:.3f} resid={lhs-rhs_:+.3e}")
    print('B=',round(B,4),' | '.join(out))
