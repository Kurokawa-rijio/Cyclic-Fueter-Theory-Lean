Overview

Cyclic Fueter Theory develops a geometric construction beginning with cyclic quaternionic Fueter-type operators and their complex matrix and spinor representations. This Lean 4 archive formalizes selected calculations that connect a momentum-space quantum sphere and Dirac-type operators to relativistic mass-shell geometry, then studies a spherical Einstein–Yang–Mills (EYM) dumbbell whose gauge profile is tied to its spatial shape. The purpose is to make the algebraic identities, geometric correspondences, and field-equation calculations auditable—not to present a completed physical unification.

Version 1.2.0 contains 2743 declarations (2740 theorems and 3 private lemmas) in 261 modules (a count of declarations, not of independent claims), plus 556 aliases in an index module that restate existing theorems under ledger names. All of them build without sorry or project-specific axioms. The descriptions of versions 1.1.1 and earlier (docs/ZENODO_DESCRIPTION_v1.1.1.md and before) remain valid for the content they describe; this text lists what is new.

New in version 1.2.0

1. Local well-posedness of the wedge evolution problem (foundation items 4-7, 4-8, 4-9, 4-12, 4-15, 4-17).

The wedge between the null fronts of the dumbbell is a characteristic initial-value (Goursat) problem for the spherically symmetric EYM system in double-null form, with unknowns (r, Ω, W). Version 1.1.1 cited local existence and uniqueness as classical theorems; version 1.2.0 proves them in Lean.

- Uniqueness (4-7). Two C² solutions on a rectangle [0,a]×[0,b] with the same characteristic data on its two edges, both with r > 0 and Ω > 0 on the rectangle, coincide there. The proof uses a characteristic Grönwall inequality; the bounds it needs are obtained from continuity and compactness. Equations and data are imposed only on the rectangle, but the regularity hypothesis asks for two-sided derivatives at edge points, so the solutions are assumed to extend slightly beyond the rectangle as C¹ functions.
- Continuous dependence (4-8). If two solutions satisfy fixed bounds B, m on the rectangle and their C¹ traces on the edges differ by at most E, then |δr| + |δΩ| + |δW| ≤ C·E, where C depends on B, m, a and b.
- Existence (4-9, 4-17). A Goursat existence theorem for semilinear systems with a globally Lipschitz right-hand side is proved by the Banach fixed-point theorem in a weighted sup norm. Truncating the right-hand side then gives local existence for the wedge system. For characteristic data that are C¹ on all of ℝ, agree at the corner and have r > 0 and Ω > 0 there, there is a square [0,ε]² (ε is not given explicitly) on which a C² solution exists with r, Ω ≥ r₀ > 0, and it is the only C² solution there with r > 0 and Ω > 0. The case of the dumbbell's cap and neck data is a separate theorem.
- Also proved: a local stability estimate for the linearised system (4-12), of Grönwall type growing from the corner; and, for every rectangle and box of bounds, the existence of a C² field with the cap and neck data that satisfies the evolution equations wherever its values stay inside the box (4-15).
- A second, independent line of work reduces the PDE to an integral equation, defines the frozen-coefficient iteration map, and proves a contraction estimate for it in the C¹ norm on small rectangles; the fixed-point step is not carried out on that route, so the existence result above is the one to cite.

Scope: "C²" in this section means that the function, ∂_u, ∂_v and ∂_u∂_v are continuous (with ∂_u∂_v = ∂_v∂_u); ∂_u² and ∂_v² are not included, and for C¹ data they need not exist. These are statements about the three evolution equations. That the solutions also satisfy the constraint equations C_u = C_v = 0 is not proved here. The corner is placed at (0,0). The version including the cap centre (r = 0) remains open (4-16). The reading of 4-15 as "the only obstruction to continuation is leaving the box" is an interpretation; no continuation theorem of that form is proved.

2. Classical physics written from the author's geometry (new chapter 13 of the proposition set).

- Curvature from metric jets. Christoffel symbols and the Riemann tensor are built from the values of the metric derivatives; metric compatibility and the first Bianchi identity are proved.
- Second Bianchi identity. It is proved in gauge form for an arbitrary noncommutative ring and in coordinate components. The contracted Bianchi identity ∇^μ G_μν = 0 is proved in normal coordinates.
- Linearised gravity. Gauge invariance, the linearised Bianchi identity, matter conservation, the harmonic (Lorenz) gauge, vacuum gravitational waves, and the Newtonian limit (G₀₀ ↔ Poisson equation, Christoffel symbols ↔ Newtonian force).
- The geodesic equation as the Euler–Lagrange equation of ½ g v v.
- Mechanics. Kepler problem: angular momentum, energy, the Laplace–Runge–Lenz vector and the identity A·x = L² − kr. Harmonic oscillator, and rigid-body conservation laws (2T = Σ I_i ω_i² and |L|²).
- Continuum laws. Navier–Stokes in conservation form, Bernoulli, Navier–Cauchy, the acoustic wave equation, and Coulomb's law (harmonicity and field).
- Special relativity. Mass shell, invariance of the interval under boosts, velocity addition, and the electromagnetic invariants.
- Bridges to the Fueter operator.
  - Maxwell's equations imply one biquaternionic Fueter equation D F = −(Iρ + j) (one direction; the converse is not formalised).
  - The electromagnetic invariants as the scalar part of F², and the mass shell as the biquaternionic norm.
  - Bernoulli, viscous Navier–Stokes and Coulomb in terms of the spatial Fueter operator Vec = i∂₁ + j∂₂ + k∂₃ (Vec u = −div u + curl u for a vector field u, and Vec² = −Δ). The two Coulomb theorems state their hypotheses ∂_j x_j = 1 and ∂_j(1/r) = −x_j/r³ also for the time index j = 0; for a static potential these are incompatible, so as stated they do not apply to the static Coulomb field (see docs/REVIEW_2026-11-18_JA.md, item 8).
  - The Lorenz gauge, and the quaternionic gauge Bianchi identity.
- Quaternionic mechanics.
  - Kustaanheimo–Stiefel map x = q i q̄, with |x| = |q|² and the speed identity. The Kepler energy relation is rewritten in the form of a four-dimensional oscillator energy; the equation of motion is not derived.
  - Euler's rigid-body equation as a quaternionic commutator, conservation of |q| for the attitude equation 2q̇ = qω, and constant speed for the frame geodesic equation V̇ = −(PV − VQ) with P, Q in Λ²₊ ⊕ Λ²₋.

3. Nonlinear Einstein equations from the Cartan–Palatini action (first-order form, orthonormal frame).

- At a point, the first variation of the Cartan–Palatini density ε ε R e e in the frame e, around e = δ, equals −8 Σ k G. The stationarity condition is therefore G = 0, and with matter 8G = T. The identity εεR = −4G uses only the two antisymmetries of R.
- Variation of the connection. The Euler–Lagrange expression for the connection is entered in its standard integrated-by-parts form; integration by parts itself is not formalized. That expression vanishes if and only if the torsion vanishes. The torsion-free connection compatible with the metric is uniquely given by the Koszul formula.
- Lorentz signature η = diag(−1, 1, 1, 1). Raising the four indices of ε gives −ε, and stationarity ⇔ G^L = 0.
- Gauge covariance of the curvature. F(g⁻¹Ag + g⁻¹∂g) = g⁻¹F(A)g holds in an arbitrary noncommutative ring.
- Frame–coordinate correspondence. For the frame components of a coordinate Riemann tensor with the two antisymmetries, the frame Ricci tensor, scalar curvature and Einstein tensor are the coordinate ones transported by the frame, and g^{μν} = Σ η_a E_a^μ E_a^ν is the inverse of g_{μν} = Σ η_a e^a_μ e^a_ν. Hence stationarity of the Lorentzian Cartan action ⇔ the coordinate Einstein equations G_{νσ} = 0.
- Not formalized: that the Riemann tensor built from the Christoffel symbols of a metric has the two antisymmetries, and that the frame connection obtained from the Christoffel symbols is the Levi-Civita ω.

4. Other additions since version 1.1.1.

- Wheeler–DeWitt operator.
  - The physical inner product as an explicit integral, with strict positivity.
  - The scale factor as an internal clock: the exact branches satisfy a first-order Schrödinger equation.
  - The semiclassical limit to the Hamilton–Jacobi function S = aσ(b), and the correspondence of the branches with classical outgoing motion.
  - The closed sin/cos form of the branch combinations for all a.
- Known solutions. Reissner–Nordström in double-null coordinates, as an explicit residual form and in analytic deriv form. The Schwarzschild solution and the flat limit in analytic deriv form.
- The extremal RN horizon. The double zero of f and T = 0; near the horizon, the metric has the AdS₂ × S² form.
- Wedge classification by the order of the zeros of Ω (12-8). Light parts are proved:
  - double-null gauge fixing by characteristic data and corner conditions;
  - the divergence of the coupling A = Ω/(2r²) in Kruskal-type coordinates and for general fields;
  - Ω → ∞ on the singular side.
- Light results from the proposition set's chapter 14:
  - self-dual 2-forms in four dimensions and their relation to the quaternions;
  - the octonions and the Cayley 4-form T = *(Φ∧·) with eigenvalues 3 and −1 (the dimensions 7 and 21 are not counted);
  - null fields ⇔ nilpotent 2×2 matrices;
  - the BPS monopole profile expressed through the Langevin paramagnet partition function (for x ≠ 0);
  - the three conformal Killing fields of the rigidity theorem as isometries of the throat.

Wording and audit

The headers and the review summary docs/REVIEW_2026-11-18_JA.md say what each theorem proves and what is only an interpretation. The wording was revised after an author-side audit, which checked the quantifier structure of the headline theorems against their prose and found no errors. Theorem statements and proofs were not changed by that revision. The additions in this version were not audited by an independent reviewer.

Build

The project targets Lean 4.15.0 and Mathlib v4.15.0. To reproduce the build, install Elan and run `lake update`, `lake exe cache get`, and `lake build` from the repository root. `lake env lean Audit.lean` prints the axioms used by each audited theorem.
