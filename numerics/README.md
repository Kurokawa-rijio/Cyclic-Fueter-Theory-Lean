# Numerical checks (not verified by Lean)

Python 3 with numpy and scipy. Units: the neck radius ℓ = 1 (the Bartnik–McKinnon / Volkov et al. units).
These scripts support ledger rows that are marked 完(外) or 部; Lean does not check them.

| Script | Ledger | What it does |
|---|---|---|
| `closed.py` | XIV.3, XIV.4 | Static EYM + Λ in proper-distance gauge, ds² = −e^{2ν}dt² + ds² + r(s)²dΩ²; regular-pole series; test on the Einstein static universe (a = √2, Λ = 3/4). |
| `family.py` | XIV.4 | Closed (S³) solutions n = 1..10 by shooting to a reflection point (W = 0 for odd n, W′ = 0 for even n); writes `family.pkl`. Compare Volkov et al., hep-th/9605089, Table 1. |
| `shape.py` | XIV.4 | Shape of the closed solutions (cylinder fraction, node spacing). Needs `family.pkl`. |
| `bmS3.py`, `bm6.py` | XIII.5, XIV.6 | Bartnik–McKinnon shooting values b_n (Λ = 0) by bisection with far integration; `bm6.py` writes `bn.npy` (brackets for n ≥ 6 were located by a scan). |
| `bm7.py` | XIV.6 | Masses 1 − M_n, node spacing in the throat, throat length. Needs `bn.npy`. |
| `omega2.py` | XIV.8 | Superposition Ω = A cos η + B/sin u: null–null and +− components; realisability by a Yang–Mills field. |
| `static_cf.py` | XIII.4 | Static conformally flat interpolation Ω = Bu/sin u: constraint residual. |
