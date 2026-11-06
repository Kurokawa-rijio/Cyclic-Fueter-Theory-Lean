import numpy as np
from scipy.integrate import solve_ivp
from closed import rhs, init
def run(b,smax=1e9):
    s0,y0=init(b,0.0)
    ev=lambda s,y,L: abs(y[2])-1.2; ev.terminal=True
    return solve_ivp(rhs,[s0,smax],y0,args=(0.0,),events=[ev],method='DOP853',rtol=1e-13,atol=1e-15,dense_output=True)
def cls(b):
    sol=run(b); W=sol.y[2]
    n=int(np.sum(np.sign(W[1:])!=np.sign(W[:-1])))
    return (n,int(np.sign(W[-1])) if len(sol.t_events[0]) else 0),sol
def bis(lo,hi,tol=1e-15):
    cl=cls(lo)[0]
    while hi-lo>tol:
        mid=(lo+hi)/2
        if cls(mid)[0]==cl: lo=mid
        else: hi=mid
    return lo
if __name__=="__main__":
    import sys
    br=[(0.44,0.46),(0.64,0.66),(0.69,0.70),(0.704,0.7065),(0.7065,0.70698),(0.70690,0.70709),(0.70705,0.707107)]
    for lo,hi in br:
        print(f"bracket {lo},{hi}: {cls(lo)[0]} {cls(hi)[0]}",flush=True)
        b=bis(lo,hi); c,sol=cls(b); print(f"b={b:.15f} class {c} send={sol.t[-1]:.3g}",flush=True)
