# Cyclic Fueter Theory: Lean 4 Formalization of Selected Results

**Author:** Ryojiro Kurokawa  
**Version:** v0.3.0 (2026-11-02)  
**Lean toolchain:** `leanprover/lean4:v4.15.0`  
**Mathlib dependency:** `v4.15.0`

日本語の研究状況は [`docs/CLAIM_STATUS_JA.md`](docs/CLAIM_STATUS_JA.md)、作者の作業用の詳しい記録(全項目の定理名と注意)は [`docs/README_JA_full.md`](docs/README_JA_full.md) を参照してください。

## Overview

This repository contains Lean 4 formalizations associated with the research program *Cyclic Fueter Theory* (CFT) and the author's claim ledger α-I–α-IX. The code covers quaternionic algebra, matrix and spinor constructions, quantum-geometric identities, Cartan-frame calculations, the reduced Einstein–Yang–Mills (EYM) action and its field equations, curvature and stress tensors computed from metric and connection data, distributional junction conditions, characteristic evolution and constraint propagation, zero-mode calculations, and selected links to WZW and related geometric formulas.

The current snapshot contains **1216 theorem declarations** in 118 Lean modules (v0.2.0: 1074 in 101). This count includes 109 auxiliary polynomial identities used in the α-II.5 calculations and many component-by-component tensor identities; it is a count of declarations, **not** of independent research claims.

## What changed in v0.3.0

Seventeen new or extended modules (142 theorems) close ten items of α-I–α-VIII at the scopes stated in `docs/CLAIM_STATUS_JA.md`:

- **Static S³ (α-VI.3).** R = 6/ℓ² for the ultrastatic metric is computed from the Levi-Civita formula, the four-dimensional Yang–Mills stress is shown to be traceless for any field strength, and the static EYM configuration is shown to be impossible without a cosmological constant (`CFT.VIStatic.static_S3_YM_impossible`).
- **Hypercharge obstruction (α-VII.3).** The commutant of L(su(2)) in so(4) is exactly R(su(2)) (`CFT.VIIComm.commutant_so4`).
- **Minisuperspace and Wheeler–DeWitt (α-IV.12, α-VI.4, α-VI.6, α-VI.8).** The reduced Lagrangian is derived from the 4D action; the total derivative is cancelled exactly by the GHY term; the normalisation c = L_x/(2G) and the regularity of the Legendre map are proved. The WKB series terminates at order ħ, so Ψ = e^{iaσ/ħ}/σ is an exact solution on Q > 0, for both momentum branches and for both the "momenta to the right" and the Laplace–Beltrami orderings. The physical inner product is fixed, up to unitary equivalence, by the affine-group (canonical group) quantisation of the reduced phase space (explicit representation, group law, unitarity, commutator; uniqueness by Gel'fand–Naimark). The semiclassical limit checks all hypotheses of the stationary-phase theorem (support C > C_min(b), existence, non-degeneracy and uniqueness of the stationary point).
- **Dirac levels on S³ (α-V.2).** The left-invariant frame, the vector-field bracket, the Koszul coefficients and the spin term (3i/2)·1 give D = 3/2 + λΣσ⊗σ on the 4-dimensional invariant subspace, with the full spectrum 3/2 + λ (triplet) and 3/2 − 3λ (singlet).
- **Maxwell from the action and the tangent bundle (α-VII.1).** Bianchi identity and equations of motion are separated; the charged-W bundle of the hedgehog is identified with T^{1,0}S² as a complex line bundle (topological isomorphism, c₁ = χ(S²) = 2).
- **Quantum stress on the cap (α-V.7).** For conformal spectator fields in the conformal vacuum (renormalisation with b = 0), the energy density on closed FRW is derived from the trace anomaly and conservation: ρ = κ₁/a⁴ + (3ħa_E/8π²)X², unique up to κ/a⁴ (`CFT.Anomaly.rho_unique`).
- **Charges (α-VII.8).** The lowest Dirac eigenspace on S⁹ (16-dimensional, Camporesi–Higuchi) and the existing charge assignment are counted as complete; masslessness/chirality is a separate open item VII.8-C.

**Correction (RealLine).** The six "final" theorems that use `RealLine` (`timelike_final`, `color_final`, `slice_final`, `null_final`, `wave_jump_final`, `cap_crunch_final`) combine a field `S` with ring-homomorphism evaluations and continuity. In that setting every element is constant on the interval, so these theorems apply only to constant fields, and some have inconsistent hypotheses. The underlying algebraic identities and the real-function theorems are unaffected. Items α-III.1, III.2, III.9 and IV.2 are therefore reclassified as partial until the bridge is rebuilt on a commutative ring with point evaluations (planned as the last task).

**New open items.** α-VII.8-C (massless chiral modes from an internal Dirac operator) and α-V.7′ (back-reaction of the SU(2) quantum fluctuations, where a β-function term ∝ F² enters the trace).

## What changed in v0.2.0

- **Field equations from the action, without symmetric criticality.** The first variation of the reduced EH + GHY + YM action reproduces the five reduced field equations (`el_iff_alpha`). New in this version, all 16 components of the four-dimensional Einstein tensor (computed from the Levi-Civita formula) and all 12 components of the Yang–Mills equations (with F = dA + A∧A) are computed for the spherically symmetric ansatz in synchronous gauge and shown to be equivalent to the same five equations (`CFT.S2M.full_4d_iff_alpha`, `CFT.S2M.palais_free`). Palais' principle of symmetric criticality is therefore not needed for this ansatz.
- **Junctions as distributional EYM equations.** A δ-coefficient lemma proved by integration by parts (`delta_coeff_weighted`) turns the second-derivative terms of the curvature into surface terms. For the dumbbell, a timelike junction surface needs both a gravitational shell and a colour surface current (`timelike_final`, `color_final`); a null front carries no shell and no colour current (`null_final`), while the dumbbell's front carries a weak discontinuity [W_u] ≠ 0 (`dumbbell_front`); a spacelike slice has shell density σ = −[R_x]/(4πG R₀) (`slice_final`). *(v0.3.0: these final theorems are affected by the RealLine correction above; the real-function lemmas they call remain valid.)*
- **Evolution.** Outside the fronts the solution is exact: the caps are closed radiation FRW universes and the neck is AdS₂ × S². The wedge between the fronts is posed as a characteristic (Goursat) problem whose constraints are proved to propagate (`constraint_prop_from_eqs`); [W_u] is constant along a front (`wave_jump_final`). Along the cap centre a(η) = ℓ cos η and the Kretschmann scalar K = 24ℓ⁴/a⁸ diverges as η → π/2 (`cap_crunch_final`; affected by the RealLine correction, while the real-function result `cap_unique`/`kret_blowup` stands), at central proper time ℓ < πℓ/2 (`cap_proper_time`, `t_sing_lt`). The neck does not collapse: its synchronous time πℓ/2 is the edge of the domain of dependence, not a curvature singularity.
- **Shape and mass.** The minimal mass m ≥ √π M_Pl/g is derived from the constraints, an untrapped exterior, the dominant energy condition, and the neck's EYM constraint, with ℓ² = 4πG/g² derived rather than assumed (`min_mass_from_constraints`). The Gauss map of the embedded slice is defined from an explicit profile immersion (`AlphaV_GaussMap`).
- **Dependency checks.** `DepCheck.lean` reports separately which constants a theorem's *proof* uses and which appear in its *statement*, so that final theorems can be checked to call the intended lemmas rather than assume their conclusions (`review/depcheck.txt`).

## Important scope statement

Lean checks that each theorem follows from its formalized assumptions. It does not automatically validate whether those assumptions correctly model a physical system, whether an imported theorem applies to the research setting, or whether a numerical result is an exact solution of the field equations.

The author-maintained status ledger (2026-11-02) classifies the 53 items of α-I–α-VIII as:

| Status | Count (v0.3.0, 53 items) | Count (v0.2.0, 51 items) | Meaning |
|---|---:|---:|---|
| Complete, including items that rely on a stated external theorem | 41 | 35 | The ledger considers the formalized statement complete at the stated scope |
| Partial | 7 | 9 | The Lean statement is weaker than the full claim |
| Conditional | 2 | 3 | A key hypothesis that is not a known theorem remains assumed |
| Not formalized as stated | 3 | 4 | The formalized object differs from, or does not yet cover, the ledger claim |

The 35 items of α-IX (consequences of the action principle): 10 complete, 25 not yet started. In total, α has 88 items: 51 complete, 7 partial, 2 conditional, 3 not formalized, 25 not started. These are **author-maintained research classifications**, not peer-review results. Using a named, established theorem with its hypotheses checked is counted as complete. The v0.2.0 count of 35 included α-III.1, III.2, III.9 and IV.2, which are now partial (see the RealLine correction above).

Specific limits of the present formalization:

- Junction results assume that each side is C² up to the surface, with matching traces on the surface; jumps of normal derivatives are kept as independent data.
- Local well-posedness of the characteristic initial-value problem (Goursat problem) and uniqueness of smooth EYM solutions in their domain of dependence (Choquet-Bruhat) are cited classical theorems. Global continuation of the solution in the wedge between the fronts is **not** claimed.
- The 4D component match is carried out in synchronous gauge (lapse 1, zero shift). The lapse and shift variations (the constraints) are retained on the reduced-action side.
- `W = r'` is a condition on time-symmetric initial data; it is not established as a dynamically invariant sector of the full EYM system.
- Open problems that are deliberately left open (for example chirality on S⁹, the general local classification without the cited CIS theorem) are listed in `docs/README_JA_full.md`.

## Build

Install [Elan](https://github.com/leanprover/elan) and Git. From the repository root:

```bash
lake update
lake exe cache get
lake build
```

The `lean-toolchain` file pins Lean 4.15.0 and `lakefile.lean` uses Mathlib tag `v4.15.0`. The author's build used a local Mathlib checkout at the same tag (commit `9837ca9d65d9de6fad1ef4381750ca688774e608`); its log is `docs/archive/build_2026-10-21k.log`. Some modules (`CFT/Cartan/SS*`) need several GB of memory each; on a small machine build them one at a time.

To run the axiom audit and the dependency checks after building:

```bash
lake env lean Audit.lean      # #print axioms for every theorem; output recorded in audit.txt
lake env lean DepCheck.lean   # proof and statement dependencies; output recorded in review/depcheck.txt
```

Recorded audit result for v0.3.0: 1216 theorems, of which 1202 depend only on Lean's standard axioms [propext, Classical.choice, Quot.sound], 7 on [propext, Quot.sound], 4 on [propext], and 3 on no axioms. `audit.txt` holds the v0.2.0 output for the 1074 unchanged theorems followed by the CI output (run 41331208469) for the 142 new ones; the full `lake build` and the complete audit of `Audit.lean` were also run together in CI (run 41374173874, success, no `sorryAx`). There is no `sorry` and no project-specific `axiom`. The GitHub Actions workflow runs the same audit after the build and reports the counts in the job summary.

A GitHub Actions workflow under `.github/workflows/lean.yml` builds the project on pushes and pull requests.

## Repository layout

- `CFT/` — Lean modules grouped by the α claim families and supporting calculations. Modules named `AlphaS1_*`–`AlphaS5_*` and `AlphaS2_4DMatch` are the staged rebuild of 2026-10-21 (action, equations, shapes, junctions, evolution).
- `CFT.lean` — umbrella module importing every module.
- `Audit.lean`, `audit.txt`, `audit_raw.txt` — axiom audit source and output.
- `DepCheck.lean` — dependency checks for the final theorems.
- `review/` — claim ledgers, the 2026-10-21 per-item audit table (`audit_table_2026-10-21.md`), stage audits, patch notes, and dependency-check output. Older files in this folder are kept as history and contain older counts.
- `docs/CLAIM_STATUS_JA.md` — current 53-item status ledger plus α-IX (88 items in total).
- `docs/README_JA_full.md` — the author's full working record in Japanese (theorem names and notes for every item).
- `docs/archive/` — historical README and build logs.
- `scripts/` — SymPy scripts that generated the large component identities (see `scripts/README.md`). They are not needed to build the project.

## Reproducibility and external results

Some claims explicitly rely on external mathematical input, such as cited classification theorems or the local well-posedness theorem above. Such dependencies are stated in the relevant Lean modules, in `docs/README_JA_full.md`, and in `review/audit_table_2026-10-21.md`. The formal code should be read together with those assumptions and the per-claim status ledger.

## License

MIT License, matching the license declared on the project's Zenodo records. See `LICENSE`.
