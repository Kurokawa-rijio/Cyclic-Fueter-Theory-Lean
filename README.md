# Cyclic Fueter Theory: Lean 4 Formalization of Selected Results

**Author:** Ryojiro Kurokawa  
**Version:** v0.2.0 (source snapshot `CFT_alpha_lean_2026-10-21k`)  
**Lean toolchain:** `leanprover/lean4:v4.15.0`  
**Mathlib dependency:** `v4.15.0`

日本語の研究状況は [`docs/CLAIM_STATUS_JA.md`](docs/CLAIM_STATUS_JA.md)、作者の作業用の詳しい記録(全項目の定理名と注意)は [`docs/README_JA_full.md`](docs/README_JA_full.md) を参照してください。

## Overview

This repository contains Lean 4 formalizations associated with the research program *Cyclic Fueter Theory* (CFT) and the author's claim ledger α-I–α-IX. The code covers quaternionic algebra, matrix and spinor constructions, quantum-geometric identities, Cartan-frame calculations, the reduced Einstein–Yang–Mills (EYM) action and its field equations, curvature and stress tensors computed from metric and connection data, distributional junction conditions, characteristic evolution and constraint propagation, zero-mode calculations, and selected links to WZW and related geometric formulas.

The current snapshot contains **1074 theorem declarations** in 101 Lean modules. This count includes 109 auxiliary polynomial identities used in the α-II.5 calculations and many component-by-component tensor identities; it is a count of declarations, **not** of independent research claims.

## What changed in v0.2.0

- **Field equations from the action, without symmetric criticality.** The first variation of the reduced EH + GHY + YM action reproduces the five reduced field equations (`el_iff_alpha`). New in this version, all 16 components of the four-dimensional Einstein tensor (computed from the Levi-Civita formula) and all 12 components of the Yang–Mills equations (with F = dA + A∧A) are computed for the spherically symmetric ansatz in synchronous gauge and shown to be equivalent to the same five equations (`CFT.S2M.full_4d_iff_alpha`, `CFT.S2M.palais_free`). Palais' principle of symmetric criticality is therefore not needed for this ansatz.
- **Junctions as distributional EYM equations.** A δ-coefficient lemma proved by integration by parts (`delta_coeff_weighted`) turns the second-derivative terms of the curvature into surface terms. For the dumbbell, a timelike junction surface needs both a gravitational shell and a colour surface current (`timelike_final`, `color_final`); a null front carries no shell and no colour current (`null_final`), while the dumbbell's front carries a weak discontinuity [W_u] ≠ 0 (`dumbbell_front`); a spacelike slice has shell density σ = −[R_x]/(4πG R₀) (`slice_final`).
- **Evolution.** Outside the fronts the solution is exact: the caps are closed radiation FRW universes and the neck is AdS₂ × S². The wedge between the fronts is posed as a characteristic (Goursat) problem whose constraints are proved to propagate (`constraint_prop_from_eqs`); [W_u] is constant along a front (`wave_jump_final`). Along the cap centre a(η) = ℓ cos η and the Kretschmann scalar K = 24ℓ⁴/a⁸ diverges as η → π/2 (`cap_crunch_final`), at central proper time ℓ < πℓ/2 (`cap_proper_time`, `t_sing_lt`). The neck does not collapse: its synchronous time πℓ/2 is the edge of the domain of dependence, not a curvature singularity.
- **Shape and mass.** The minimal mass m ≥ √π M_Pl/g is derived from the constraints, an untrapped exterior, the dominant energy condition, and the neck's EYM constraint, with ℓ² = 4πG/g² derived rather than assumed (`min_mass_from_constraints`). The Gauss map of the embedded slice is defined from an explicit profile immersion (`AlphaV_GaussMap`).
- **Dependency checks.** `DepCheck.lean` reports separately which constants a theorem's *proof* uses and which appear in its *statement*, so that final theorems can be checked to call the intended lemmas rather than assume their conclusions (`review/depcheck.txt`).

## Important scope statement

Lean checks that each theorem follows from its formalized assumptions. It does not automatically validate whether those assumptions correctly model a physical system, whether an imported theorem applies to the research setting, or whether a numerical result is an exact solution of the field equations.

The author-maintained status ledger (2026-10-21) classifies the 51 items of α-I–α-VIII as:

| Status | Count (v0.2.0) | Count (v0.1.0) | Meaning |
|---|---:|---:|---|
| Complete, including items that rely on a stated external theorem | 35 | 25 | The ledger considers the formalized statement complete at the stated scope |
| Partial | 9 | 17 | The Lean statement is weaker than the full claim |
| Conditional | 3 | 5 | A key hypothesis that is not a known theorem remains assumed |
| Not formalized as stated | 4 | 4 | The formalized object differs from, or does not yet cover, the ledger claim |

The 35 items of α-IX (consequences of the action principle) are tracked separately: 10 complete, 25 not yet started. These are **author-maintained research classifications**, not peer-review results. Using a named, established theorem with its hypotheses checked is counted as complete.

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

Recorded audit result for v0.2.0: 1074 theorems, of which 1061 depend only on Lean's standard axioms [propext, Classical.choice, Quot.sound], 6 on [propext, Quot.sound], 4 on [propext], and 3 on no axioms. There is no `sorry` and no project-specific `axiom`.

A GitHub Actions workflow under `.github/workflows/lean.yml` builds the project on pushes and pull requests.

## Repository layout

- `CFT/` — Lean modules grouped by the α claim families and supporting calculations. Modules named `AlphaS1_*`–`AlphaS5_*` and `AlphaS2_4DMatch` are the staged rebuild of 2026-10-21 (action, equations, shapes, junctions, evolution).
- `CFT.lean` — umbrella module importing every module.
- `Audit.lean`, `audit.txt`, `audit_raw.txt` — axiom audit source and output.
- `DepCheck.lean` — dependency checks for the final theorems.
- `review/` — claim ledgers, the 2026-10-21 per-item audit table (`audit_table_2026-10-21.md`), stage audits, patch notes, and dependency-check output. Older files in this folder are kept as history and contain older counts.
- `docs/CLAIM_STATUS_JA.md` — current 51-item status ledger plus α-IX.
- `docs/README_JA_full.md` — the author's full working record in Japanese (theorem names and notes for every item).
- `docs/archive/` — historical README and build logs.
- `scripts/` — SymPy scripts that generated the large component identities (see `scripts/README.md`). They are not needed to build the project.

## Reproducibility and external results

Some claims explicitly rely on external mathematical input, such as cited classification theorems or the local well-posedness theorem above. Such dependencies are stated in the relevant Lean modules, in `docs/README_JA_full.md`, and in `review/audit_table_2026-10-21.md`. The formal code should be read together with those assumptions and the per-claim status ledger.

## License

MIT License, matching the license declared on the project's Zenodo records. See `LICENSE`.
