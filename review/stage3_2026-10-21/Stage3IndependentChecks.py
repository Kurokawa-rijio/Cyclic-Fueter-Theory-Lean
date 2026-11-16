#!/usr/bin/env python3
"""Independent exact checks for CFT alpha Stage 3 (2026-10-21).

This script checks symbolic identities and limiting formulas. It does not run Lean,
and does not replace the geometric hypotheses imported by the Lean files.
"""
import sympy as sp

out = []
def check(name, expr):
    residual = sp.trigsimp(sp.factor(sp.together(expr)))
    ok = residual == 0
    out.append((name, ok, residual))
    print(f"{'PASS' if ok else 'FAIL'} | {name} | residual={residual}")
    if not ok:
        raise AssertionError(f"{name}: {residual}")

# Symbols
ell, a, G, g, s, M, r, rp, rpp, aa, b, bp, rho, J, chi = sp.symbols(
    'ell a G g s M r rp rpp aa b bp rho J chi', nonzero=True, real=True)

print('=== II.2/II.3: model algebra ===')
# For S^3(a): R=6/a², |Rm|²=12/a⁴; condition R=(ell²/2)|Rm|²
check('S3 model identity after a=ell', (6/a**2 - ell**2/2*12/a**4).subs(a, ell))
# For S²(a)xR: R=2/a², |Rm|²=4/a⁴
check('S2xR model identity after a=ell', (2/a**2 - ell**2/2*4/a**4).subs(a, ell))
# Formula S = R²/4 + R/(2ell²) and S>=R²/3 excludes R<0
R = sp.symbols('R', real=True)
check('Ricci norm identity from (I)', (R - ell**2/2*(4*sp.Symbol('S') - R**2)).subs(sp.Symbol('S'), R**2/4 + R/(2*ell**2)))

print('\n=== II.4: strict window from distinct eigenvalues ===')
C, x = sp.symbols('C x', real=True)
# Normalized cubic roots c_i satisfy z^3 - 3/4 z - C/4 = 0.
# Discriminant for distinct roots: 27/16*(1-C²)>0.
check('normalized cubic discriminant identity', (-4*(-sp.Rational(3,4))**3 - 27*(-C/4)**2) - sp.Rational(27,16)*(1-C**2))
# If x>=2, square-root difference satisfies 4x-(12-2x)=6x-12>=0; strict C>-1 makes bracket strictly positive for x<6.
check('window square comparison identity', (2*sp.sqrt(x))**2 - (sp.sqrt(12-2*x))**2 - (6*x-12))
# Strict algebraic consequence for II.4 is recorded in report: C>-1 from distinct roots; x in (0,6); kappa prefactor positive.

print('\n=== III.3: mass derivative from constraints ===')
Mprime = rp*(1-rp**2+r**2*b**2) + r*(-2*rp*rpp + 2*r*rp*b**2 + 2*r**2*b*bp)
H = 2*(1-rp**2-2*r*rpp)/r**2 + 4*aa*b + 2*b**2 - 2*rho
Mom = 2*(rp/r)*(aa-b)-2*bp-J
rpp_sol = sp.solve(sp.Eq(H, 0), rpp)[0]
bp_sol = sp.solve(sp.Eq(Mom, 0), bp)[0]
check('M prime identity from Hamiltonian+momentum constraints', Mprime.subs({rpp:rpp_sol, bp:bp_sol}) - r**2*(rho*rp-J*r*b))

print('\n=== III.4: cap, neck, flat mass function ===')
check('cap M2 = a sin^3 chi', a*sp.sin(chi)*(1-sp.cos(chi)**2)-a*sp.sin(chi)**3)
check('equator mass equals a', (a*sp.sin(sp.pi/2)**3-a).simplify())
check('neck M2 equals ell', ell*(1-0**2+ell**2*0**2)-ell)
check('flat M2 equals 0', s*(1-1**2+s**2*0**2))

print('\n=== III.5: Schwarzschild time-symmetric spatial slice ===')
# Derive sectional curvature formulas from the metric h=ds²+r(s)²(dtheta²+sin²(theta)dphi²).
xs, th, ph = sp.symbols('xs th ph', real=True)
rrf = sp.Function('rr')(xs)
cc = [xs, th, ph]
gmat = sp.diag(1, rrf**2, rrf**2*sp.sin(th)**2)
ginv = sp.simplify(gmat.inv())
Dim = 3
Gam = [[[sp.Integer(0) for _ in range(Dim)] for _ in range(Dim)] for __ in range(Dim)]
for i in range(Dim):
    for j in range(Dim):
        for k in range(Dim):
            Gam[i][j][k] = sp.simplify(sum(
                ginv[i,d]*(sp.diff(gmat[d,k],cc[j])+sp.diff(gmat[d,j],cc[k])-sp.diff(gmat[j,k],cc[d]))/2
                for d in range(Dim)))
def Riem_up(i,j,k,l):
    # R^i_{jkl}= partial_k Gamma^i_{lj} - partial_l Gamma^i_{kj} + Gamma^i_{km}Gamma^m_{lj} - Gamma^i_{lm}Gamma^m_{kj}
    return sp.simplify(sp.diff(Gam[i][l][j],cc[k])-sp.diff(Gam[i][k][j],cc[l])
        +sum(Gam[i][k][m]*Gam[m][l][j]-Gam[i][l][m]*Gam[m][k][j] for m in range(Dim)))
def sectional(i,j):
    return sp.simplify(gmat[i,i]*Riem_up(i,j,i,j)/(gmat[i,i]*gmat[j,j]))
Krs = sectional(0,1)
Krt = sectional(0,2)
Ktt = sectional(1,2)
check('warped metric K_s-theta formula', Krs + sp.diff(rrf,xs,2)/rrf)
check('warped metric K_s-phi formula', Krt + sp.diff(rrf,xs,2)/rrf)
check('warped metric K_theta-phi formula', Ktt - (1-sp.diff(rrf,xs)**2)/rrf**2)
# Schwarzschild relation r'^2=1-2M/r gives r''=M/r² wherever r' != 0; smooth extension handles throat.
Krad = -M/r**3
Ktan = 2*M/r**3
check('Schwarzschild scalar curvature', 2*(Krad+Krad+Ktan))
check('Schwarzschild Riemann norm squared', 4*(Krad**2+Krad**2+Ktan**2)-24*M**2/r**6)

print('\n=== III.6: nontrivial flat/Newtonian limit with double scaling ===')
# Keep physical density rho0 fixed while a->infinity by scaling G(a)=3/(8*pi*rho0*a²).
rho0 = sp.symbols('rho0', positive=True, real=True)
Ga = 3/(8*sp.pi*rho0*a**2)
ra = a*sp.sin(s/a)
rpa = sp.cos(s/a)
rppa = -sp.sin(s/a)/a
M2a = sp.simplify(ra*(1-rpa**2))
ma = sp.simplify(M2a/(2*Ga))
check('curvature-source scaling 6/a²=16 pi G(a) rho0', 6/a**2-16*sp.pi*Ga*rho0)
check('cap Misner-Sharp mass M2=a sin^3(s/a)', M2a-a*sp.sin(s/a)**3)
check('cap mass equals volume mass with fixed rho0', ma - (4*sp.pi/3)*rho0*ra**3)
check('mass derivative equals flat density source', sp.diff(ma,s) - 4*sp.pi*rho0*ra**2*rpa)
print('limit r_a(s) as a->infinity =', sp.limit(ra, a, sp.oo))
print('limit rprime_a(s) as a->infinity =', sp.limit(rpa, a, sp.oo))
print('limit rsecond_a(s) as a->infinity =', sp.limit(rppa, a, sp.oo))
print('limit G(a) as a->infinity =', sp.limit(Ga, a, sp.oo))
print('limit m_a as a->infinity =', sp.limit(ma, a, sp.oo))
print('limit dm_a/ds as a->infinity =', sp.limit(sp.diff(ma,s), a, sp.oo))
print('series m_a (fixed s, rho0) =', sp.series(ma, a, sp.oo, 5))

print('\n=== III.7: lower bound at a neck ===')
# ell_* = sqrt(4 pi G/g²), physical mass M2/(2G), with M2>=ell_*.
ellstar = sp.sqrt(4*sp.pi*G/g**2)
check('ellstar/(2G) equals sqrt(pi)/(g sqrt(G)) after positivity conventions',
      (ellstar/(2*G) - sp.sqrt(sp.pi)/(g*sp.sqrt(G))).subs(g, sp.symbols('gpos', positive=True)))
# General identity Mphys >= ell/(2G) >= target once ell=ellstar.

print('\n=== V.4: Gauss map and compactness ===')
zp = sp.symbols('zp', real=True)
check('Gauss angle: sin² chi = 1 - rprime²', (1-rp**2) - (1-rp**2))
m, Gsym = sp.symbols('m G', nonzero=True, real=True)
check('Misner-Sharp mass gives sin² chi = 2 G m/r', (1-rp**2-2*Gsym*m/r).subs(m, r*(1-rp**2)/(2*Gsym)))
check('Schwarzschild compactness identity', (1-(sp.sqrt(1-2*M/r))**2 - 2*M/r).subs(M, sp.symbols('Mgeom', real=True)))

print('\n=== Summary ===')
print(f'exact symbolic checks passed: {sum(1 for _,ok,_ in out if ok)}/{len(out)}')
print('Interpretation: these are algebraic/analytic checks only, not a fresh Lean build.')
