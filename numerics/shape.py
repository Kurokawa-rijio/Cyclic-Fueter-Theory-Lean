import numpy as np, pickle
from family import half
fam=pickle.load(open('family.pkl','rb'))
for n in [2,4,6,8,10]:
    b,L,se=fam[n]
    rr,sol=half(b,L,n)
    s=np.linspace(sol.t[0],se,200001); r,rp,W,Wp,nup=sol.sol(s)
    nu=np.concatenate([[0],np.cumsum((nup[1:]+nup[:-1])/2*np.diff(s))])
    cyl=np.abs(r-np.sqrt(2))<0.1
    s_in=s[np.argmax(r>np.sqrt(2)-0.1)]
    mid=s>s_in
    # local wavenumber of W in the middle: node spacing
    z=s[np.where(np.sign(W[1:])!=np.sign(W[:-1]))[0]]
    amp=np.max(np.abs(W[mid])) if mid.any() else np.nan
    print(f"n={n}: total length={2*se:.3f}; cap (r from 0 to sqrt2-0.1) length={s_in:.3f}; cylinder part |r-sqrt2|<0.1: {2*(se-s_in):.3f} ({(se-s_in)/se*100:.0f}%); r_max={r.max():.4f}; "
          f"node gaps={np.round(np.diff(z),3)}; max|W| on cylinder={amp:.3f}; redshift e^(nu_eq-nu_pole)={np.exp(nu[-1]):.4f}; max|nu'| on cyl={np.abs(nup[mid]).max():.3f}")
print("pi*sqrt2 =",np.pi*np.sqrt(2),"  pi/sqrt2 =",np.pi/np.sqrt(2))
