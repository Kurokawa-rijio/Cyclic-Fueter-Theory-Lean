import numpy as np, sys
s2=np.sqrt(2)
def F(r,Om,W,ru,rv,Ou,Ov):
    ruv=0.5*Om*((1-W*W)**2/r**2-1)/r-ru*rv/r
    Ouv=Ou*Ov/Om-2*Om*ruv/r-Om**2*(1-W*W)**2/r**4
    Wuv=0.5*Om*W*(1-W*W)/r**2
    return ruv,Ouv,Wuv
def run(N,L,eps,u0=0.3,wd=0.12):
    h=L/N; u=np.arange(N+1)*h
    r=np.zeros((N+1,N+1)); Om=r.copy(); W=r.copy()
    th=u/s2
    # v=0 ray: perturbed W, gauge Om=cos^2, r from constraint (fine RK4)
    Wf=lambda x: np.sin(x/s2)+eps*np.exp(-((x-u0)/wd)**2)
    dW=lambda x: np.cos(x/s2)/s2+eps*np.exp(-((x-u0)/wd)**2)*(-2*(x-u0)/wd**2)
    sig=lambda x: -2*np.tan(x/s2)/s2      # Om_u/Om
    f=lambda x,y: np.array([y[1], sig(x)*y[1]-2*dW(x)**2/y[0]])
    y=np.array([1.0,0.0]); rr=[1.0]; M=20; hh=h/M; x=0
    for i in range(N):
        for k in range(M):
            k1=f(x,y);k2=f(x+hh/2,y+hh/2*k1);k3=f(x+hh/2,y+hh/2*k2);k4=f(x+hh,y+hh*k3)
            y=y+hh/6*(k1+2*k2+2*k3+k4); x+=hh
        rr.append(y[0])
    r[:,0]=rr; Om[:,0]=np.cos(th)**2; W[:,0]=Wf(u)
    r[0,:]=np.cos(th)**2; Om[0,:]=np.cos(th)**2; W[0,:]=-np.sin(th)
    for i in range(N):
        a=np.array([r[i,:-1],Om[i,:-1],W[i,:-1]])
        for j in range(N):
            a=(r[i,j],Om[i,j],W[i,j]); b=(r[i+1,j],Om[i+1,j],W[i+1,j]); c=(r[i,j+1],Om[i,j+1],W[i,j+1])
            d=[b[k]+c[k]-a[k] for k in range(3)]
            for it in range(3):
                m=[(a[k]+b[k]+c[k]+d[k])/4 for k in range(3)]
                du=[((b[k]-a[k])+(d[k]-c[k]))/(2*h) for k in range(3)]
                dv=[((c[k]-a[k])+(d[k]-b[k]))/(2*h) for k in range(3)]
                g=F(m[0],m[1],m[2],du[0],dv[0],du[1],dv[1])
                d=[b[k]+c[k]-a[k]+h*h*g[k] for k in range(3)]
            r[i+1,j+1],Om[i+1,j+1],W[i+1,j+1]=d
    return u,r,Om,W,h
def Dinv(r,Om,W,h):
    ru=(r[2:,1:-1]-r[:-2,1:-1])/(2*h); rv=(r[1:-1,2:]-r[1:-1,:-2])/(2*h)
    rc=r[1:-1,1:-1]; return 1+2*ru*rv/Om[1:-1,1:-1]-(1-W[1:-1,1:-1]**2)**2/rc**2
if __name__=="__main__":
    N=int(sys.argv[1]); L=float(sys.argv[2])
    out={}
    for eps in [0.0,1e-3,2e-3]:
        u,r,Om,W,h=run(N,L,eps); out[eps]=(Dinv(r,Om,W,h),r,W)
    D0,D1,D2=out[0.0][0],out[1e-3][0],out[2e-3][0]
    print("N",N,"background max|D| (should be 0):",np.abs(D0).max())
    print("linearity max|D2|/max|D1|:",np.abs(D2).max()/np.abs(D1).max())
    # along the slice eta = const (u+v=const): max over slice of |D|/eps and of |D|/r^2/eps
    print(" eta   time-to-crunch  max|D|/eps   max|D/r^2|/eps   max|dW|/eps")
    r1=out[1e-3][1][1:-1,1:-1]; dW=(out[1e-3][2]-out[0.0][2])[1:-1,1:-1]
    n=D1.shape[0]
    for frac in [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,0.95,0.98]:
        k=int(frac*2*(n-1)); idx=[(i,k-i) for i in range(n) if 0<=k-i<n]
        ii=np.array([p[0] for p in idx]); jj=np.array([p[1] for p in idx])
        eta=(u[ii[0]+1]+u[jj[0]+1])/s2
        print(" %.3f  %.3f  %.4g  %.4g  %.4g"%(eta,np.pi/2-eta,np.abs(D1[ii,jj]).max()/1e-3,np.abs(D1[ii,jj]/r1[ii,jj]**2).max()/1e-3,np.abs(dW[ii,jj]).max()/1e-3))
