# FieldEquations

Lean 4 / Mathlib formalization of

1. **Characteristic (Goursat) problems for semilinear second-order systems** `w_{uv} = F(w, w_u, w_v)` on a rectangle:
   a characteristic Grönwall inequality, uniqueness, existence for globally Lipschitz `F` via the Banach fixed-point theorem
   in a weighted sup norm, continuous dependence on the characteristic data, and a stability estimate for linear systems
   (`FieldEquations/Characteristic`).
2. **Local well-posedness of the characteristic initial-value problem for the spherically symmetric Einstein–Yang–Mills
   equations in double-null form** (SU(2) magnetic ansatz): uniqueness, local existence for `C¹` data with `r, Ω > 0`
   at the corner, and Lipschitz dependence on the data (`FieldEquations/SphericalEYM`).
3. **Einstein equations from the first-order Cartan–Palatini action** at a point, torsion-freeness from the connection
   variation, Lorentz signature, gauge covariance of curvature, the correspondence between frame and coordinate Einstein
   tensors, the second and contracted Bianchi identities, linearized gravity and the Newtonian limit
   (`FieldEquations/Gravity`).

   equations as a single biquaternionic equation, Kustaanheimo–Stiefel identities, the Cayley 4-form on 2-forms of ℝ⁸,
   self-dual 2-forms, null fields, the BPS monopole and the Langevin function, Killing fields of AdS₂
   (`FieldEquations/Quaternionic`).

Each file begins with a header stating exactly what is proved and what is assumed or not formalized.

## Scope notes

- "C²" in Part 1–2 means continuous first partial derivatives and continuous mixed derivative `∂_u∂_v`
  (structure `C2Data`); pure second derivatives are not required. Derivatives at edge points are two-sided.
- The Einstein–Yang–Mills results concern the three evolution equations; the constraint equations are not proved to
  propagate. The corner of the characteristic rectangle is at `(0,0)`.
- The Cartan–Palatini variation is pointwise and finite dimensional; integration by parts is not formalized.

## Build

```bash
lake update
lake exe cache get
lake build
lake env lean Audit.lean   # #print axioms for every theorem
```

Lean 4.15.0, Mathlib v4.15.0. No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
