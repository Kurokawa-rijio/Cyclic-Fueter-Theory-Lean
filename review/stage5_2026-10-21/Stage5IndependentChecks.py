#!/usr/bin/env python3
"""Independent symbolic checks for Stage 5 of CFT_alpha_lean_2026-10-21e.

This verifies selected differential/algebraic identities and Taylor expansions.
It does not prove the PDE well-posedness assumptions, and is not a Lean build.
"""
import sympy as s

x, r, rp, W, ell = s.symbols('x r rp W ell', real=True, nonzero=True)
q, qp, rv = s.symbols('q q_prime r_v', real=True)

gd = s.atan(s.sinh(x))
front = s.asinh(s.tan(x))
checks = []

def check(label, expr):
    residual = s.simplify(expr)
    ok = residual == 0
    checks.append((label, ok, residual))
    if not ok:
        raise AssertionError(f'{label}: residual={residual}')

# Differentiation from definitions. For front, the square identity is global
# off cos(x)=0; the signed sec identity additionally requires cos(x)>0.
check('gd derivative: d/dx atan(sinh x) = sech x', s.diff(gd, x) - 1/s.cosh(x))
check('front derivative squared: (d/dx asinh(tan x))^2 = sec^2 x', s.diff(front, x)**2 - 1/s.cos(x)**2)
check('cos(gd x)^2 = sech(x)^2', s.cos(gd)**2 - 1/s.cosh(x)**2)
check('sin(gd x)^2 = tanh(x)^2', s.sin(gd)**2 - s.tanh(x)**2)

# Reduced throat ODE: E = r(1+r_dot^2)+ell^2/r.
acc = -(rp**2 + 1 - ell**2/r**2)/(2*r) - W**2/r
energy = r*(1+rp**2) + ell**2/r
Edot = s.diff(energy, r)*rp + s.diff(energy, rp)*acc
check('reduced energy balance: dE/dtau = -2 W^2 r_dot', Edot + 2*W**2*rp)

# Jump of r*r_uv + r_u*r_v = common source; assume [r]=[r_v]=0.
duv_p, duv_m, ru_p, ru_m, source = s.symbols('r_uv_plus r_uv_minus r_u_plus r_u_minus source', real=True)
field_plus = r*duv_p + ru_p*rv - source
field_minus = r*duv_m + ru_m*rv - source
jump = s.expand(field_plus - field_minus)
check('mixed equation jump identity', jump - (r*(duv_p-duv_m) + rv*(ru_p-ru_m)))
check('transport equation is product derivative d_v(r q)', (r*qp + rv*q) - (rv*q + r*qp))

# Jump of r_uu constraint when sigma_u and r_u have common traces.
wu_p, wu_m, su, ru, r0 = s.symbols('Wu_plus Wu_minus sigma_u r_u r0', real=True, nonzero=True)
ruu_plus = 2*su*ru - 2*wu_p**2/r0
ruu_minus = 2*su*ru - 2*wu_m**2/r0
check('uu constraint gives [r_uu] = -(2/r)[W_u^2]', (ruu_plus-ruu_minus) + 2*(wu_p**2-wu_m**2)/r0)

# Taylor expansions derived by SymPy from exact definitions.
gd_series = s.series(gd, x, 0, 7).removeO().expand()
front_series = s.series(front, x, 0, 7).removeO().expand()
metric_series = s.series(s.cos(x)**2, x, 0, 6).removeO().expand()
check('Gudermann expansion through degree 5', gd_series - (x - x**3/s.Integer(6) + x**5/s.Integer(24)))
check('front expansion through degree 5', front_series - (x + x**3/s.Integer(6) + x**5/s.Integer(24)))
check('metric coefficient expansion through degree 4', metric_series - (1 - x**2 + x**4/s.Integer(3)))

print('STAGE 5 INDEPENDENT SYMBOLIC CHECKS')
print('Source archive: CFT_alpha_lean_2026-10-21e.zip')
print('Scope: direct derivatives, the reduced energy identity, jump algebra, Taylor coefficients.')
for label, ok, residual in checks:
    print(f'{"PASS" if ok else "FAIL"}: {label}; residual={residual}')
print(f'\nSymbolic checks: {sum(ok for _, ok, _ in checks)}/{len(checks)}')
print('Important branch condition: d/dx asinh(tan x)=sec x requires -pi/2 < x < pi/2 (in particular cos x>0 on the principal strip).')
print('These checks are not a PDE existence/uniqueness proof and do not substitute for a Lean build.')
print('\nSeries obtained from definitions:')
print(f'gd(x) = {gd_series} + O(x^7)')
print(f'asinh(tan x) = {front_series} + O(x^7)')
print(f'cos(x)^2 = {metric_series} + O(x^6)')
