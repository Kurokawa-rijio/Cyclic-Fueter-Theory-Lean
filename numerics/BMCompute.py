"""BM (Bartnik–McKinnon) shooting computation for gap propositions 11-11 / 12-7.7 / 12-7.8.

Recomputes b_n (n=1..8) by bisection on the node-count classification,
compares with the literature values recorded in the ledger
(b_1..b_5 = 0.4537, 0.6517, 0.6970, 0.7048, 0.7062), and measures the
asymptotic laws: mass defect 1 - M_n, b-gap ratios (both expected to
scale like e^{pi/sqrt3} per node) and the node spacing in proper
distance s near the throat (expected 2*pi/sqrt3).

Status: NUMERICAL DIAGNOSTIC (double precision floats). This is not an
interval-arithmetic certification; the Lean-side certification of b_n
remains open (11-11 remainder).
"""
import numpy as np
from scipy.optimize import brentq
from StaticEYMProperDistance import constraint
from BartnikMcKinnonShooting import run, cls, bis

known = {1: 0.453716257503256, 2: 0.651725501081946, 3: 0.697040022536808,
         4: 0.704878467049758, 5: 0.7061686556741109}
extra_brackets = {6: (0.706378, 0.70638), 7: (0.706412, 0.706414), 8: (0.706418, 0.70642)}

results = {}
for n, b0 in known.items():
    lo, hi = b0 - 1e-6, b0 + 1e-6
    clo, chi = cls(lo)[0], cls(hi)[0]
    print(f"n={n} bracket classes {clo} -> {chi}", flush=True)
    assert clo != chi
    b = bis(lo, hi, tol=1e-14)
    results[n] = b
    print(f"b_{n} = {b:.15f}  (previous value {b0:.15f}, diff {b - b0:+.2e})", flush=True)

for n, (lo, hi) in extra_brackets.items():
    clo, chi = cls(lo)[0], cls(hi)[0]
    print(f"n={n} bracket classes {clo} -> {chi}", flush=True)
    assert clo != chi
    b = bis(lo, hi, tol=1e-14)
    results[n] = b
    print(f"b_{n} = {b:.15f}", flush=True)

bs = [results[n] for n in sorted(results)]
print("b gaps:", [f"{bs[i+1]-bs[i]:.4e}" for i in range(len(bs) - 1)], flush=True)
print("b gap ratios:", [f"{(bs[i+1]-bs[i])/(bs[i+2]-bs[i+1]):.4f}" for i in range(len(bs) - 2)], flush=True)
print("e^{pi/sqrt3} =", np.exp(np.pi / np.sqrt(3)), " 2pi/sqrt3 =", 2 * np.pi / np.sqrt(3),
      " pi/sqrt3 =", np.pi / np.sqrt(3), flush=True)

print("\n n   b_n            1-M_n      max|constr|  nodes  throat gaps in s", flush=True)
masses = {}
for n, b in sorted(results.items()):
    sol = run(b)
    send = sol.t[-1]
    if send < 2e3:
        s = np.linspace(sol.t[0], send, 400000)
    else:
        s = np.concatenate([np.linspace(sol.t[0], 200, 400000), np.geomspace(200, send, 20000)])
    r, rp, W, Wp, nup = sol.sol(s)
    m = r * (1 - rp ** 2) / 2
    idx = np.where(r > 5)[0]
    i = idx[np.argmin(np.abs(np.abs(W[idx]) - 1))] if len(idx) else len(s) - 1
    M = m[i]
    masses[n] = 1 - M
    cons = np.array([constraint(sol.sol(si), 0.0) for si in s[::997]])
    zc = np.where(np.sign(W[1:]) != np.sign(W[:-1]))[0]
    sk = np.array([brentq(lambda ss: sol.sol(ss)[2], s[j], s[j + 1]) for j in zc])
    rk = np.array([sol.sol(sv)[0] for sv in sk])
    thr = (rk > 0.85) & (rk < 1.15)
    gaps_thr = np.diff(sk[thr]) if thr.sum() > 1 else np.array([])
    print(f"{n} {b:.12f} {1-M:.4e}  {np.max(np.abs(cons)):.2e}    {len(sk)}   "
          f"{np.round(gaps_thr, 3)}", flush=True)
    print(f"    node s: {np.round(sk, 3)}", flush=True)
    print(f"    node r: {np.round(rk, 4)}", flush=True)

print("\nmass defect ratios (1-M_n)/(1-M_{n+1}):",
      [f"{masses[n]/masses[n+1]:.4f}" for n in range(1, 8)], flush=True)
np.save('bn_computed.npy', np.array(bs))
print("saved bn_computed.npy", flush=True)
