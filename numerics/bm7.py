import numpy as np
from bmS3 import run
bs=np.load('bn.npy')
print(" n   b_n         1-M      nodes s_k (proper distance)                                    gaps")
rows=[]
for n,b in enumerate(bs,1):
    sol=run(b)
    s=np.linspace(sol.t[0],sol.t[-1],2_000_000) if sol.t[-1]<2e3 else np.concatenate([np.linspace(sol.t[0],200,2_000_000),np.geomspace(200,sol.t[-1],20000)])
    r,rp,W,Wp,nup=sol.sol(s)
    m=r*(1-rp**2)/2
    # mass: m at the point where |W| is closest to 1 after r>5
    idx=np.where(r>5)[0]
    i=idx[np.argmin(np.abs(np.abs(W[idx])-1))] if len(idx) else len(s)-1
    M=m[i]
    z=np.where(np.sign(W[1:])!=np.sign(W[:-1]))[0][:n]
    sk=s[z]; rk=r[z]
    nu=np.concatenate([[0],np.cumsum((nup[1:]+nup[:-1])/2*np.diff(s))])
    thr=(r>0.9)&(r<1.1); Lth=np.sum(np.diff(s)[thr[:-1]])
    rows.append((n,b,1-M,sk,rk,Lth,r[i],nu[z]))
    print(f"{n} {b:.9f} {1-M:.3e}  r_eval={r[i]:.1f}  L(0.9<r<1.1)={Lth:.3f}  nodes s={np.round(sk,3)}  r={np.round(rk,4)}  gaps={np.round(np.diff(sk),3)}",flush=True)
import pickle; pickle.dump(rows,open('bmrows.pkl','wb'))
print("2pi/sqrt3 =",2*np.pi/np.sqrt(3), " e^{pi/sqrt3} =",np.exp(np.pi/np.sqrt(3)))
print("b gaps ratios:",np.round(np.diff(bs)[:-1]/np.diff(bs)[1:],3))
