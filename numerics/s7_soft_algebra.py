"""Interlude B, additional computations (numerical checks of statements proved in the text).
(1) S^3 = unit quaternions: right-invariant frame X_a(x) = x e_a has constant structure functions.
(2) S^7 = unit octonions: X_a(x) = x e_a has x-dependent structure functions
    f_ab^c(x) = <[R_a,R_b] x, x e_c> = <[e_b,e_a], e_c> + 2 <[x,e_b,e_a], x e_c>.
(3) Associator orthogonality <[x,y,z], x> = 0, and tangency of [R_a,R_b]x.
(4) Hagedorn: x^3-3x^2-3x+1 = (x+1)(x^2-4x+1), root 2-sqrt3 of z_V(x)=1.
"""
import numpy as np, sys
sys.path.insert(0, __file__.rsplit('/',1)[0])
from octonion_spin10 import omul, qmul, Rmat, E
rng = np.random.default_rng(1)
def assoc(x,y,z): return omul(omul(x,y),z) - omul(x,omul(y,z))
def R4(a): return np.array([qmul(np.eye(4)[j],a) for j in range(4)]).T
ok = True
# (1) quaternions
fq=[]
for _ in range(20):
    x = rng.normal(size=4); x/=np.linalg.norm(x)
    F = np.array([[[ (R4(np.eye(4)[a])@R4(np.eye(4)[b])-R4(np.eye(4)[b])@R4(np.eye(4)[a]))@x @ qmul(x,np.eye(4)[c]) for c in range(1,4)] for b in range(1,4)] for a in range(1,4)])
    fq.append(F)
fq=np.array(fq); print('S3 structure functions: max variation', np.abs(fq-fq[0]).max())
ok &= np.abs(fq-fq[0]).max()<1e-12
# (2),(3) octonions
fo=[]; maxerr=0; maxorth=0; maxtan=0; maxanti=0
for _ in range(50):
    x = rng.normal(size=8); x/=np.linalg.norm(x)
    F=np.zeros((7,7,7))
    for a in range(1,8):
        for b in range(1,8):
            C = Rmat(E[a])@Rmat(E[b]) - Rmat(E[b])@Rmat(E[a])
            v = C@x
            maxtan=max(maxtan,abs(v@x))
            for c in range(1,8):
                F[a-1,b-1,c-1] = v @ omul(x,E[c])
                pred = (omul(E[b],E[a])-omul(E[a],E[b]))@E[c] + 2*assoc(x,E[b],E[a])@omul(x,E[c])
                maxerr=max(maxerr,abs(F[a-1,b-1,c-1]-pred))
    maxanti=max(maxanti,np.abs(F+F.transpose(1,0,2)).max(), np.abs(F+F.transpose(0,2,1)).max())
    fo.append(F)
    y,z=rng.normal(size=8),rng.normal(size=8); A=assoc(x,y,z)
    maxorth=max(maxorth,abs(A@x),abs(A@y),abs(A@z))
fo=np.array(fo)
print('S7: formula error', maxerr, '| tangency', maxtan, '| assoc orthogonality', maxorth)
print('S7: total antisymmetry error', maxanti)
print('S7 structure functions: max variation over x', np.abs(fo-fo[0]).max())
f1 = np.zeros((7,7,7))
for a in range(1,8):
    for b in range(1,8):
        for c in range(1,8): f1[a-1,b-1,c-1]=(omul(E[b],E[a])-omul(E[a],E[b]))@E[c]
print('S7 at x=1 equals 2x octonion structure constants:', np.abs(f1).max(), sorted(set(np.round(f1.flatten(),9))))
ok &= maxerr<1e-12 and maxtan<1e-12 and maxorth<1e-12 and maxanti<1e-12 and np.abs(fo-fo[0]).max()>0.1
# (4) Hagedorn
x=2-np.sqrt(3); z=(6*x**2-2*x**3)/(1-x)**3
print('Hagedorn z_V(2-sqrt3)=',z,' T_H*R = 1/ln(2+sqrt3) =',1/np.log(2+np.sqrt(3)))
P=np.poly1d([1,-3,-3,1]); print('roots of x^3-3x^2-3x+1:',np.sort(P.r), ' (x+1)(x^2-4x+1) coeffs', np.polymul([1,1],[1,-4,1]))
ok &= abs(z-1)<1e-12
print('ALL CHECKS PASS' if ok else 'FAILURE')
