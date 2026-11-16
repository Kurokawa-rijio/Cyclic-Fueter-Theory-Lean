# static EYM + Lambda in proper-distance gauge: ds^2 = -e^{2nu}dt^2 + ds^2 + r(s)^2 dOmega^2
# units: neck radius l = 1 (kappa/g^2 absorbed as in BM units)
import numpy as np
from scipy.integrate import solve_ivp
def rhs(s,y,L):
    r,rp,W,Wp,nup=y
    m=(1-W*W)**2/r**4; k=2*Wp*Wp/r**2
    rho=k+m; ps=k-m; pp=m
    rpp=(1-rp*rp-r*r*(rho+L))/(2*r)
    nupp=pp-L-rpp/r-nup*nup-nup*rp/r
    Wpp=-nup*Wp-W*(1-W*W)/r**2
    return [rp,rpp,Wp,Wpp,nupp]
def constraint(y,L):
    r,rp,W,Wp,nup=y
    m=(1-W*W)**2/r**4; k=2*Wp*Wp/r**2
    return 2*rp*nup/r-(1-rp*rp)/r**2+L-(k-m)
def init(b,L,s0=1e-4):
    r3=-(12*b*b+L)/18; c=4*b*b-L/3
    return s0,[s0+r3*s0**3,1+3*r3*s0**2,1-b*s0**2,-2*b*s0,c*s0]
def shoot(b,L,smax=200,dense=False):
    s0,y0=init(b,L)
    ev=lambda s,y,L: y[1]; ev.terminal=True; ev.direction=-1
    ev2=lambda s,y,L: y[0]-1e-3; ev2.terminal=True; ev2.direction=-1
    return solve_ivp(rhs,[s0,smax],y0,args=(L,),events=[ev,ev2],rtol=1e-11,atol=1e-13,dense_output=dense)
if __name__=="__main__":
    # test: ESU with YM, a^2=2, Lambda=3/4, b=1/4
    sol=shoot(0.25,0.75,dense=True)
    se=sol.t_events[0][0]; ye=sol.y_events[0][0]
    print("ESU test: s_eq",se,"expected",np.sqrt(2)*np.pi/2,"y",ye)
    for s in [0.5,1.0,2.0]:
        y=sol.sol(s); print(s, y[0]-np.sqrt(2)*np.sin(s/np.sqrt(2)), y[2]-np.cos(s/np.sqrt(2)), y[4], constraint(y,0.75))
