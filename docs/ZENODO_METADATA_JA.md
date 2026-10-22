# Zenodo metadata recommendation / Zenodoメタデータ案

## Recommended title

Cyclic Fueter Theory: Lean 4 Formalization of Selected Results

## Description (.zenodo.json, short form)

This software repository contains Lean 4 source files developed in connection with the Cyclic Fueter Theory (CFT) research program. It formalizes selected algebraic and geometric statements involving quaternionic algebra, Fueter-type operators, matrix and spinor constructions, quantum-geometric identities, Cartan-frame calculations, the reduced Einstein–Yang–Mills action and its four-dimensional field equations, distributional junction conditions, characteristic evolution and constraint propagation, zero-mode calculations, and selected Wess–Zumino–Witten (WZW)-related formulas.

Version 0.2.0 contains 1074 theorem declarations in 101 modules, with no sorry and no project-specific axioms. The repository includes an author-maintained status ledger for 51 items grouped into α-I–α-VIII (35 complete including items that use a named external theorem, 9 partial, 3 conditional, 4 not formalized as stated) and 35 items in α-IX (10 complete). These labels describe the current scope of this formalization; they are not independent certification or peer review of the corresponding research claims. Lean verifies each theorem from its declared assumptions and imported results. Formalization does not by itself establish that a physical model, external theorem, or interpretation is appropriate.

The project targets Lean 4.15.0 and Mathlib v4.15.0. To reproduce the build, install Elan and run `lake update`, `lake exe cache get`, and `lake build` from the repository root.

The full description used on the Zenodo record is `docs/ZENODO_DESCRIPTION_v0.2.0.md`.

## Keywords

Lean 4, Mathlib, formalization, formal verification, interactive theorem proving, quaternionic analysis, Fueter equations, Clifford algebra, differential geometry, mathematical physics, Einstein–Yang–Mills theory, constraint propagation, Wess–Zumino–Witten model

## Suggested subjects to add in Zenodo's metadata editor

Use a controlled-vocabulary match where one is available; otherwise add these as custom keyword/subject entries:

- Mathematical logic
- Differential geometry
- Mathematical physics
- Formal methods / formal verification
- Quaternionic analysis

Zenodo supports controlled terms from EuroSciVoc, MeSH, and GEMET as well as custom keyword/subject entries. Do not invent vocabulary identifiers for custom subjects. The `.zenodo.json` file therefore uses the `keywords` field and leaves controlled-vocabulary `subjects` unset; add suitable subject entries in the Zenodo UI if desired.

## Zenodo/GitHub update behavior

- The repository should have a release tag (for example `v0.1.0`) when you intend Zenodo to archive a snapshot.
- Once GitHub-to-Zenodo integration is enabled, new GitHub releases are automatically ingested and archived.
- Metadata on a published Zenodo record can be edited without issuing a new DOI. The published files of that version are immutable; for code/file changes, create a new version/release. Zenodo assigns a version-specific DOI and maintains a concept DOI for the evolving project.
- When both `.zenodo.json` and `CITATION.cff` exist, Zenodo uses `.zenodo.json` for GitHub release archiving, so keep their title and description in sync.

## Not yet specified

- License: MIT (declared on the Zenodo record and in `LICENSE`).
- ORCID and affiliation: omitted rather than guessed.
- Version: v0.2.0 (Git tag `v0.2.0`). The full Zenodo description for this version is `docs/ZENODO_DESCRIPTION_v0.2.0.md`.
