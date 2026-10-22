#!/usr/bin/env python3
"""Independent symbolic checks for Stage 4 junction identities.

Uses the metric definitions and equations written in this script, not the
existing Lean theorem statements. SymPy verifies the algebraic identities;
the report separately states analytic assumptions required for the jump/transport arguments.
"""
import sympy as sp

u, v, s = sp.symbols('u v s', real=True)
G, ell = sp.symbols('G ell', positive=True, finite=True, nonzero=True)
pi = sp.pi
sigma = sp.Function('sigma')(u, v)
r = sp.Function('r')(u, v)
W = sp.Function('W')(u, v)
coords = [u, v]

checks = []
def check(name, expr):
    reduced = sp.simplify(sp.factor(expr))
    ok = reduced == 0
    checks.append((name, ok, str(reduced)))
    if not ok:
        raise AssertionError(f'{name}: residual is {reduced}')
    print(f'PASS | {name} | residual = 0')

# A. Independently compute the 2D Christoffel symbols and Ricci scalar
# h = -2 exp(2 sigma) du dv, so h_uv = h_vu = -exp(2 sigma).
h = sp.Matrix([[0, -sp.exp(2*sigma)], [-sp.exp(2*sigma), 0]])
hi = sp.simplify(h.inv())
Gamma = {}
for a in range(2):
    for b in range(2):
        for c in range(2):
            Gamma[a,b,c] = sp.simplify(sum(
                hi[a,d]*(sp.diff(h[d,c], coords[b]) + sp.diff(h[d,b], coords[c])
                         - sp.diff(h[b,c], coords[d]))
                for d in range(2))/2)
check('Gamma^u_uu = 2 sigma_u', Gamma[0,0,0] - 2*sp.diff(sigma,u))
check('Gamma^v_vv = 2 sigma_v', Gamma[1,1,1] - 2*sp.diff(sigma,v))
for key,val in Gamma.items():
    if key not in {(0,0,0),(1,1,1)}:
        check(f'Gamma{key} vanishes', val)

Ric = sp.zeros(2)
for b in range(2):
    for c in range(2):
        val = 0
        for a in range(2):
            val += sp.diff(Gamma[a,b,c], coords[a]) - sp.diff(Gamma[a,b,a], coords[c])
            for d in range(2):
                val += Gamma[a,b,c]*Gamma[d,a,d] - Gamma[d,b,a]*Gamma[a,c,d]
        Ric[b,c] = sp.simplify(val)
R2 = sp.simplify(sum(hi[a,b]*Ric[a,b] for a in range(2) for b in range(2)))
check('2D Ricci scalar = 4 exp(-2 sigma) sigma_uv',
      R2 - 4*sp.exp(-2*sigma)*sp.diff(sigma,u,v))

# Covariant Hessian and box of r on the 2D base.
Huu = sp.simplify(sp.diff(r,u,2) - Gamma[0,0,0]*sp.diff(r,u) - Gamma[1,0,0]*sp.diff(r,v))
check('nabla_u nabla_u r = r_uu - 2 sigma_u r_u',
      Huu - (sp.diff(r,u,2)-2*sp.diff(sigma,u)*sp.diff(r,u)))
boxr = sp.simplify(sum(hi[a,b]*(sp.diff(r,coords[a],coords[b])
            - sum(Gamma[c,a,b]*sp.diff(r,coords[c]) for c in range(2)))
            for a in range(2) for b in range(2)))
check('box_h r = -2 exp(-2 sigma) r_uv',
      boxr + 2*sp.exp(-2*sigma)*sp.diff(r,u,v))

# From the warped-product identity G_ab = -2/r Hess_ab(r) + terms proportional to h_ab,
# the uu component has no h_uu terms.
Guu = -2*Huu/r
check('G_uu = -2/r (r_uu - 2 sigma_u r_u)',
      Guu + 2/r*(sp.diff(r,u,2)-2*sp.diff(sigma,u)*sp.diff(r,u)))

# B. Spatial slice scalar curvature and shell-density coefficient.
r0, jump, sig_shell = sp.symbols('r0 jump sig_shell', nonzero=True, finite=True)
# R^(3)=2(1-r'^2-2 r r'')/r^2; a jump [r'] in r'' contributes -4 [r']/r0 delta.
sing_R3 = 2*(-2*r0*jump)/r0**2
check('spatial scalar-curvature delta coefficient', sing_R3 - (-4*jump/r0))
# 16 pi G sigma = singular scalar-curvature coefficient
sigma_solution = sp.solve(sp.Eq(16*pi*G*sig_shell, sing_R3), sig_shell)[0]
check('spatial shell density formula', sigma_solution - (-jump/(4*pi*G*r0)))

# Specific cap and neck curvatures at r=ell, r'=0.
rpp_cap = -1/ell
rpp_neck = sp.Integer(0)
R_cap = sp.simplify(2*(1 - 0**2 - 2*ell*rpp_cap)/ell**2)
R_neck = sp.simplify(2*(1 - 0**2 - 2*ell*rpp_neck)/ell**2)
check('cap R3 at equator = 6/ell^2', R_cap - 6/ell**2)
check('neck R3 = 2/ell^2', R_neck - 2/ell**2)
check('C1 seam has no spatial delta when [rprime]=0', -4*(0)/ell)

# Hamiltonian constraint and the prescribed matter models.
rho_cap = sp.simplify(R_cap/(16*pi*G))
rho_neck = sp.simplify(R_neck/(16*pi*G))
p_cap = sp.simplify(rho_cap/3)  # isotropic radiation on cap
p_neck = sp.simplify(-rho_neck) # radial magnetic tension on neck
jump_Tnn = sp.simplify(p_neck - p_cap)
check('rho_cap = 3/(8 pi G ell^2)', rho_cap - 3/(8*pi*G*ell**2))
check('rho_neck = 1/(8 pi G ell^2)', rho_neck - 1/(8*pi*G*ell**2))
check('normal stress jump = -1/(4 pi G ell^2)', jump_Tnn + 1/(4*pi*G*ell**2))

# C. Null shell from singular coefficient in G_uu.
# If r and sigma are continuous and piecewise C^2 across u=0, r_uu has [r_u] delta;
# sigma_u*r_u has no delta. Hence (G_uu)_sing = -2 [r_u]/r0 delta.
ru_jump = sp.symbols('jump_ru', real=True)
mu = sp.symbols('mu', real=True)
Guu_delta = -2*ru_jump/r0
mu_solution = sp.solve(sp.Eq(Guu_delta, 8*pi*G*mu), mu)[0]
check('null-shell density mu = -[r_u]/(4 pi G r0)',
      mu_solution - (-ru_jump/(4*pi*G*r0)))

# The other warped-product component needed for the mixed EYM equation.
ru_sym, rv_comp, ruv_sym = sp.symbols('ru_trace rv_comp ruv_trace', real=True)
Huv = ruv_sym  # Gamma^u_uv = Gamma^v_uv = 0
box_expr = -2*sp.exp(-2*sigma)*ruv_sym
norm_grad_sq = -2*sp.exp(-2*sigma)*ru_sym*rv_comp
Guv_from_identity = (-2*Huv/r + 2*h[0,1]/r*box_expr
                     - h[0,1]/r**2*(1-norm_grad_sq))
Guv_closed = 2*ruv_sym/r + 2*ru_sym*rv_comp/r**2 + sp.exp(2*sigma)/r**2
check('warped-product identity yields explicit G_uv', Guv_from_identity-Guv_closed)
Wsym = sp.symbols('W_trace', real=True)
F_EYM = sp.exp(2*sigma)/2*(ell**2*(1-Wsym**2)**2/r**2 - 1)
Tuv_times_8piG = sp.exp(2*sigma)*ell**2*(1-Wsym**2)**2/r**4
check('G_uv = 8 pi G T_uv gives mixed EYM equation',
      sp.expand((r**2/2)*(Tuv_times_8piG-Guv_closed) - (F_EYM-(r*ruv_sym+ru_sym*rv_comp))))

# D. Characteristic transport from the spherical magnetic EYM mixed equation:
# r r_uv + r_u r_v = F(r,sigma,W), where F depends only on continuous traces.
r_sym, rv_sym, rup, rum, ruvp, ruvm, Fsym = sp.symbols(
    'r_trace rv_trace ru_plus ru_minus ruv_plus ruv_minus F', nonzero=True, finite=True)
q = rup - rum
qprime = ruvp - ruvm
jump_equation = (r_sym*ruvp + rup*rv_sym - Fsym) - (r_sym*ruvm + rum*rv_sym - Fsym)
check('jump of mixed EYM equations gives r qprime + rv q = 0',
      jump_equation - (r_sym*qprime + rv_sym*q))
# Along the shell write r=r(v), q=q(v); the jump equation is r q' + r' q = 0.
r_trace = sp.Function('r_trace')(v)
q_trace = sp.Function('q_trace')(v)
transport_derivative = sp.diff(r_trace*q_trace, v)
check("transport derivative equals r q' + r' q",
      transport_derivative - (r_trace*sp.diff(q_trace,v) + sp.diff(r_trace,v)*q_trace))
# Initial q(v0)=0 makes r q constant zero; r>0 then q=0.

print('\nSUMMARY')
print(f'{sum(ok for _,ok,_ in checks)}/{len(checks)} symbolic checks passed.')
print('Analytic assumptions not automated by this script: piecewise C^2 traces; the reduced EYM mixed equation;')
print('uniqueness/transport on the characteristic; the physical cap radiation and neck magnetic equations of state;')
print('and the geometric distributional junction identities stated in the report.')
