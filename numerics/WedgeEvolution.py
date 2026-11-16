import numpy as np, sys
def F(r,Om,W,ru,rv,Ou,Ov):
    ruv=0.5*Om*((1-W*W)**2/r**2-1)/r-ru*rv/r
    Ouv=Ou*Ov/Om-2*Om*ruv/r-Om**2*(1-W*W)**2/r**4
    Wuv=0.5*Om*W*(1-W*W)/r**2
    return ruv,Ouv,Wuv
def run(N,umax,vmax,cap_on_v0=True):
    hu=umax/N; hv=vmax/N; s2=np.sqrt(2)
    u=np.arange(N+1)*hu; v=np.arange(N+1)*hv
    r=np.full((N+1,N+1),np.nan); Om=r.copy(); W=r.copy()
    th=u/s2; r[:,0]=np.cos(th)**2; Om[:,0]=np.cos(th)**2; W[:,0]=np.sin(th)      # cap on v=0
    th=v/s2; r[0,:]=1; Om[0,:]=1/np.cosh(th)**2; W[0,:]=0                         # neck on u=0
    stop=None
    for i in range(N):
        for j in range(N):
            a=(r[i,j],Om[i,j],W[i,j]); b=(r[i+1,j],Om[i+1,j],W[i+1,j]); c=(r[i,j+1],Om[i,j+1],W[i,j+1])
            if not all(np.isfinite(x) for x in a+b+c): continue
            d=[b[k]+c[k]-a[k] for k in range(3)]
            for it in range(3):
                m=[(a[k]+b[k]+c[k]+d[k])/4 for k in range(3)]
                du=[((b[k]-a[k])+(d[k]-c[k]))/(2*hu) for k in range(3)]
                dv=[((c[k]-a[k])+(d[k]-b[k]))/(2*hv) for k in range(3)]
                f=F(m[0],m[1],m[2],du[0],dv[0],du[1],dv[1])
                d=[b[k]+c[k]-a[k]+hu*hv*f[k] for k in range(3)]
            if d[0]<=1e-3 or d[1]<=0 or not np.isfinite(d[0]) or abs(d[2])>50: 
                if stop is None: stop=(u[i+1],v[j+1])
                continue
            r[i+1,j+1],Om[i+1,j+1],W[i+1,j+1]=d
    return u,v,r,Om,W,hu,hv
if __name__=="__main__":
    N=int(sys.argv[1]); umax=float(sys.argv[2]); vmax=float(sys.argv[3])
    u,v,r,Om,W,hu,hv=run(N,umax,vmax)
    np.savez('wedge_%d.npz'%N,u=u,v=v,r=r,Om=Om,W=W)
    # constraints C_u = r_uu - (Om_u/Om) r_u + 2 W_u^2/r  (sigma_u = Om_u/(2 Om))
    ruu=(r[2:,:]-2*r[1:-1,:]+r[:-2,:])/hu**2; ru=(r[2:,:]-r[:-2,:])/(2*hu); Ou=(Om[2:,:]-Om[:-2,:])/(2*hu); Wu=(W[2:,:]-W[:-2,:])/(2*hu)
    Cu=ruu-Ou/Om[1:-1,:]*ru+2*Wu**2/r[1:-1,:]
    rvv=(r[:,2:]-2*r[:,1:-1]+r[:,:-2])/hv**2; rv=(r[:,2:]-r[:,:-2])/(2*hv); Ov=(Om[:,2:]-Om[:,:-2])/(2*hv); Wv=(W[:,2:]-W[:,:-2])/(2*hv)
    Cv=rvv-Ov/Om[:,1:-1]*rv+2*Wv**2/r[:,1:-1]
    fin=np.isfinite(r); print('filled frac',fin.mean())
    print('max|Cu|,|Cv| (finite region):',np.nanmax(abs(Cu)),np.nanmax(abs(Cv)))
    # W_u on the front u=0+ along v (one-sided) : should stay 1/sqrt2
    Wu0=(-3*W[0,:]+4*W[1,:]-W[2,:])/(2*hu); print('W_u at u=0+: v=0,mid,end',Wu0[0],Wu0[N//2],Wu0[-1],' expected',1/np.sqrt(2))
    Wv0=(-3*W[:,0]+4*W[:,1]-W[:,2])/(2*hv); print('W_v at v=0+ (cap side interior value 0 expected for exact cap?):',Wv0[0],Wv0[N//2])
    for (i,j) in [(N//4,N//4),(N//2,N//2),(3*N//4,3*N//4),(N,N),(N,N//2),(N//2,N)]:
        print('u=%.3f v=%.3f r=%.5f Om=%.5f W=%.5f'%(u[i],v[j],r[i,j],Om[i,j],W[i,j]))
