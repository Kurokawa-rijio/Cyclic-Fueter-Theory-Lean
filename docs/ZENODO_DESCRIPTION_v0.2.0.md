## Overview

Cyclic Fueter Theory develops a geometric construction beginning with cyclic quaternionic Fueter-type operators and their complex matrix and spinor representations. This Lean 4 archive formalizes selected calculations that connect a momentum-space quantum sphere and Dirac-type operators to relativistic mass-shell geometry, then studies a spherical Einstein–Yang–Mills (EYM) dumbbell whose gauge profile is tied to its spatial shape. The purpose is to make the algebraic identities, geometric correspondences, and field-equation calculations auditable—not to present a completed physical unification.

Version 0.2.0 contains 1074 theorem declarations in 101 modules (a count of declarations, not of independent claims). All of them build without `sorry` or project-specific axioms; 1061 depend only on Lean's standard axioms [propext, Classical.choice, Quot.sound], and the remaining 13 on subsets of these.

## Quantum sphere and relativistic geometry

For mass m > 0, define E = √(m² + |p|²) and Q(p) = (m/E, p/E). The formalization verifies that Q is a bijection from momentum space to the open upper hemisphere of the unit three-sphere and computes its pullback metric, ∂ᵢQ·∂ⱼQ = δᵢⱼ/E² − pᵢpⱼ/E⁴.

For the Dirac Hamiltonian H = mβ + α·p, the Clifford relations yield H² = E²; the positive-energy projector P₊ = (1 + H/E)/2 is shown to be idempotent. Its quantum metric equals one half of the metric induced by Q, corresponding in these conventions to a sphere of radius 1/√2. The code also checks quaternion-to-complex-matrix identities and the determinant/Lorentz structure of the SL(2,ℂ) action.

The same momentum variables parameterize the relativistic mass-shell hyperboloid (E/m, p/m). The code verifies reciprocal-coordinate and Gudermann-angle identities, as well as conformal-metric, slope, normal, and area relations between the hyperbolic mass shell and the quantum hemisphere. These are precise geometric correspondences under the stated definitions, not by themselves proof of physical equivalence between relativity and quantum theory.

## Fueter, Berry, and Wigner connections

For U(p) = (m − iσ·p)/E, the code computes U⁻¹dU, verifies its Maurer–Cartan identity, and checks the induced frame metric. It compares the Fueter/frame connection A_F = ½U⁻¹dU, the Berry connection A_B, and the Wigner connection A_W. With the sign and normalization conventions in the source,

A_B = −(m/E) A_W,  𝒢_F = 𝒢_B = (m/E)⁴ 𝒢_W,

where 𝒢 is the encoded trace-Gram invariant of the curvature. For E > m > 0, these invariant values distinguish the Fueter/frame and Berry connections from the Wigner connection; the source includes an explicit proof that the Berry and Wigner connections cannot be gauge-equivalent in this regime. Other modules formalize selected Foldy–Wouthuysen identities, an SU(2)-coupled Dirac operator on S³, a heat-kernel coefficient, and monopole Dirac zero-mode formulas; some spectral results use stated external theorems.

## The Einstein–Yang–Mills dumbbell

The second construction is a time-symmetric, spherically symmetric spatial geometry ds² + r(s)² dΩ², with spherical caps r(s) = ℓ sin(s/ℓ) joined to a cylindrical neck r(s) = ℓ, locally modeled on S² × ℝ. In the magnetic spherical SU(2) Yang–Mills ansatz, W = r′ ties the gauge profile to the geometry, and the Hamiltonian constraint fixes the common scale ℓ² = 4πG/g².

Field equations from the action. The first variation of the reduced Einstein–Hilbert + Gibbons–Hawking–York + Yang–Mills action reproduces the reduced field equations. In version 0.2.0, all 16 components of the four-dimensional Einstein tensor (computed from the Levi-Civita formula) and all 12 components of the Yang–Mills equations (with F = dA + A∧A) are computed for the spherical ansatz in synchronous gauge and shown to be equivalent to the same equations, so Palais' principle of symmetric criticality is not needed for this ansatz.

Junctions. Junction conditions are derived from the field equations read as distributions, using a δ-coefficient lemma proved by integration by parts and assuming each side is C² up to the surface with matching traces. For the dumbbell, a timelike junction surface requires both a gravitational shell and a colour surface current; a spacelike slice has shell density σ = −[r′]/(4πG r₀); a null front carries neither a shell nor a colour current, but carries a weak discontinuity [W_u] that is constant along the front.

Evolution. Outside the fronts the solution is exact: each cap is a closed radiation FRW universe and the neck is AdS₂ × S². The wedge between the fronts is a characteristic initial-value (Goursat) problem; the constraints are proved to propagate, while local existence and uniqueness are cited as classical theorems. Along the cap centre, a(η) = ℓ cos η and the Kretschmann scalar K = 24ℓ⁴/a⁸ diverges at central proper time ℓ < πℓ/2. The neck does not collapse; its synchronous time πℓ/2 marks the edge of the domain of dependence, not a curvature singularity. The minimal mass m ≥ √π M_Pl/g is derived from the constraints, an untrapped exterior, the dominant energy condition, and the neck's field equation.

The archive does not claim a global continuation of the solution in the wedge, and W = r′ is a condition on initial data, not an established dynamically invariant sector of the full EYM system.

## Scope and reproducibility

Lean checks each theorem from its declared hypotheses and imported results. This archive provides machine-checked algebraic, differential, metric, curvature, distributional, spectral-formula, and constraint calculations; it is not a numerical PDE solver and does not claim a completed unification of general relativity and quantum theory. An author-maintained ledger classifies 51 items as 35 complete (including items that use a named external theorem), 9 partial, 3 conditional, and 4 not formalized as stated; 10 of 35 further items on consequences of the action principle are complete. `DepCheck.lean` records which lemmas each final theorem's proof uses.

The project targets Lean 4.15.0 and Mathlib v4.15.0. To reproduce the build, install Elan and Git, then run `lake update`, `lake exe cache get`, and `lake build` from the repository root; `lake env lean Audit.lean` reproduces the axiom audit. The English README and the Japanese status ledger (docs/CLAIM_STATUS_JA.md) describe each module and claim.
