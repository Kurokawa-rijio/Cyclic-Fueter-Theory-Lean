import numpy as np, pickle
from scipy.integrate import solve_ivp
from scipy.optimize import fsolve
from closed import rhs, init
def half(b,L,n):
    s0,y0=init(b,L)
    k = 2 if n%2==0 else 2   # placeholder
    ev = (lambda s,y,L: y[3]) if n%2==0 else (lambda s,y,L: y[2])
    m = n//2 if n%2==0 else (n+1)//2
    ev2=lambda s,y,L: y[0]-1e-4; ev2.terminal=True; ev2.direction=-1
    sol=solve_ivp(rhs,[s0,400],y0,args=(L,),events=[ev,ev2],method='DOP853',rtol=1e-12,atol=1e-14,dense_output=True)
    if len(sol.t_events[0])<m: return None,sol
    return (sol.t_events[0][m-1],sol.y_events[0][m-1]),sol
def F(p,n):
    r,_=half(p[0],p[1],n)
    if r is None: return [1e3,1e3]
    return [r[1][1],r[1][4]]
if __name__=="__main__":
    seeds={1:(0.25,0.75),2:(0.4296,0.3642),3:(0.5088,0.2932),4:(0.5405,0.2703),5:(0.5540,0.2609),6:(0.5604,0.2564),
           7:(0.5636,0.2541),8:(0.5656,0.2526),9:(0.5667,0.2518),10:(0.5675,0.2513)}
    res={}
    for n,(b0,L0) in seeds.items():
        if n>=8 and n-1 in res and n-2 in res:   # extrapolate seed
            b0=2*res[n-1][0]-res[n-2][0]+ (res[n-1][0]-res[n-2][0])*(-0.3); L0=res[n-1][1]-(res[n-2][1]-res[n-1][1])*0.75
        p,info,ier,msg=fsolve(F,[b0,L0],args=(n,),full_output=True,xtol=1e-14)
        rr,sol=half(*p,n); s_eq,y=rr
        m=sol.t<=s_eq; s=sol.t[m]; Y=sol.y[:,m]
        res[n]=(p[0],p[1],s_eq,y,s,Y)
        print(f"n={n}: b={p[0]:.8f} Lam={p[1]:.8f} res={max(abs(np.array(info['fvec']))):.1e} half-length={s_eq:.4f} r_eq={y[0]:.5f} W_eq={y[2]:+.5f}",flush=True)
    pickle.dump({n:(v[0],v[1],v[2]) for n,v in res.items()},open('family.pkl','wb'))
