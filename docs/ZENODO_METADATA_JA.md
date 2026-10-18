# Zenodo metadata recommendation / Zenodoメタデータ案

## Recommended title

Cyclic Fueter Theory: Lean 4 Formalization of Selected Results

## Description (Zenodo record)

This software repository contains Lean 4 source files developed in connection with the Cyclic Fueter Theory (CFT) research program. It formalizes selected algebraic and geometric statements involving quaternionic algebra, Fueter-type operators, matrix and spinor constructions, quantum-geometric identities, Cartan-frame calculations, spherically symmetric Einstein–Yang–Mills reductions, junction calculations, constraint-propagation identities, zero-mode calculations, and selected Wess–Zumino–Witten (WZW)-related formulas.

The repository includes an author-maintained status ledger for 51 items grouped into α-I–α-VIII. The labels complete, partial, conditional, and not formalized as stated describe the current scope of this formalization; they are not independent certification or peer review of the corresponding research claims. Lean verifies each theorem from its declared assumptions and imported results. Formalization does not by itself establish that a physical model, external theorem, or interpretation is appropriate. Some statements rely on standard formulas or external results, while some broader claims remain partial or conditional.

The project targets Lean 4.15.0 and Mathlib v4.15.0. To attempt a reproducible build, install Elan and run `lake update`, `lake exe cache get`, and `lake build` from the repository root. Build status should be checked for the specific release using its CI results.

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

- License: not set by this metadata change. Choose a license deliberately and add the matching license file/metadata before public release.
- ORCID and affiliation: omitted rather than guessed.
- Version: omitted here; use the actual Git tag/release version.
