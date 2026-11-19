# FieldEquations

Lean 4 / Mathlib formalization of a chain from the first-order variational principle of general relativity to the local
well-posedness of a characteristic initial-value problem:

1. **Einstein equations from the Cartan–Palatini action** (`FieldEquations/Gravity`): at a point, in an orthonormal frame,
   the first variation of the density is −8 Σ k G, so stationarity ⇔ G = 0 (8G = T with a source); torsion-freeness from
   the connection variation; Lorentz signature; gauge covariance of curvature; frame ⇔ coordinate Einstein equations;
   the second and contracted Bianchi identities, linearized gravity and the Newtonian limit.
2. **Spherical reduction** (`FieldEquations/SphericalEYM/Reduction.lean`): for −2Ω du dv + r² dΩ² the Einstein tensor
   is computed from the Levi-Civita connection, and the Einstein equations with the magnetic SU(2) Yang–Mills source are
   equivalent to the constraint and evolution equations of part 3 (the Yang–Mills stress tensor is taken as given).
3. **Characteristic (Goursat) problems** (`FieldEquations/Characteristic`, `FieldEquations/SphericalEYM`): for
   w_uv = F(w, w_u, w_v), a characteristic Grönwall inequality, uniqueness, existence for globally Lipschitz F (Banach
   fixed point in a weighted sup norm), continuous dependence and linear stability; for the spherically symmetric
   Einstein–Yang–Mills system, local existence and uniqueness for C¹ data with r, Ω > 0 at the corner and Lipschitz
   dependence on the data.

Each file begins with a header stating exactly what is proved and what is assumed or not formalized.

## Scope notes

- "C²" in part 3 means continuous first partial derivatives and continuous mixed derivative `∂_u∂_v`
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
