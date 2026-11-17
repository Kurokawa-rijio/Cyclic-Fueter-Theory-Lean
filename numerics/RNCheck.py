# RN tortoise field against the vacuum equations (cf. SchwarzschildVacuumSolution).
# 2*Om = f(r) = 1 - 2M/r + Q^2/r^2, r_u = -Om, r_v = +Om, M/Q constant.
# Checks: du/dv Om, vacuum r/Om-equation residuals, constraints C_u/C_v,
# Misner-Sharp mass m.  Q=0 must reproduce the Schwarzschild module.
import sympy as sp

r, M, Q = sp.symbols('r M Q')
Om = (1 - 2*M/r + Q**2/r**2)/2
dOm_dr = sp.diff(Om, r)
duOm = dOm_dr * (-Om)
dvOm = dOm_dr * (Om)
r_uv = duOm  # du(dv r) = du Om
r_rhs = -Om/(2*r) - (-Om)*(Om)/r  # vacuum r-eq RHS
d2Om_dr2 = sp.diff(dOm_dr, r)
Om_uv = d2Om_dr2 * (-Om) * Om + dOm_dr * duOm
Om_rhs = duOm*dvOm/Om - 2*Om*r_uv/r  # vacuum Om-eq RHS
Cu = (-duOm) - (duOm/Om)*(-Om)
Cv = (dvOm) - (dvOm/Om)*(Om)
m = r/2 + r*(-Om)*(Om)/Om

print("duOm =", sp.factor(duOm))
print("dvOm =", sp.factor(dvOm))
print("r-eq residual  =", sp.factor(sp.simplify(r_uv - r_rhs)), " = Q^2*Om/(2*r^3) ?",
      sp.simplify((r_uv - r_rhs) - Q**2*Om/(2*r**3)) == 0)
print("Om-eq residual =", sp.factor(sp.simplify(Om_uv - Om_rhs)), " = -Q^2*Om^2/r^4 ?",
      sp.simplify((Om_uv - Om_rhs) + Q**2*Om**2/r**4) == 0)
print("C_u =", sp.simplify(Cu), " C_v =", sp.simplify(Cv))
print("m =", sp.factor(sp.simplify(m)))
print("Q=0: r-resid", sp.simplify((r_uv - r_rhs).subs(Q, 0)),
      "Om-resid", sp.simplify((Om_uv - Om_rhs).subs(Q, 0)),
      "m", sp.simplify(m.subs(Q, 0)))
