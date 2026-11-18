# Source snapshot provenance

Counting method: see `README.md`, "How the declaration count is produced".
Figures before v1.1.1 use the earlier pattern (the six `private theorem`
lines included, modules = files under `CFT/` only); each section below
states which pattern its figures use and whether they were re-measured
from a tree on hand or quoted from the release notes.

## v1.6.1

- Lean module files in `CFT/`: 169 (1857 theorem declarations on the
  earlier pattern: 1848 `theorem` + 3 `private lemma` + 6 `private
  theorem`; on the canonical pattern 1851 declarations in 170 modules).
  Index aliases: 556.
- **Re-measured 2026-11-19** from `Cyclic-Fueter-Theory-Lean-v1.6.1.zip`
  (the counts above reproduce exactly).
- Cleanup and renaming only; no mathematical content changed. The
  tautological `cyclic_momentum` was deleted, the two vacuous RealLine
  final files (14 theorems) and the superseded `z44_full` were deleted,
  all modules were renamed to content-revealing names and grouped into
  topic folders, and ledger item α-XV.11 was regraded to 完(外).
  See `README.md`, "What changed in v1.6.1".

## v0.6.0

- Lean module files in `CFT/`: 171 (1873 theorem declarations on the
  earlier pattern: 1864 `theorem` + 3 `private lemma` + 6 `private
  theorem`; on the canonical pattern 1867 declarations in 172 modules).
  Index aliases: 556 (index module `CFT/AlphaIndex.lean`, renamed to
  `CFT/Index.lean` in v1.6.1).
- **Re-measured 2026-11-19** from the v0.6.0 tree on hand
  (`Cyclic-Fueter-Theory-Lean-v0.6.0/`; the counts above reproduce
  exactly).
- Real-function versions (α-III, α-IV, α-X); Ω and its quantum geometry
  (α-XV); shape of the dumbbell; one action for the spherically symmetric
  sector; weak gravity conjecture. The ledger has 182 items in α-I–α-XV
  (103 complete, 67 complete using a named external theorem or
  literature, 9 complete in a differential field pending a bridge to
  real functions, 0 partial, 3 not started). See `README.md`,
  "What changed in v0.6.0", and `docs/ZENODO_DESCRIPTION_v0.6.0.md`.

## v0.5.0

- Lean module files in `CFT/`: 150 (1641 theorem declarations).
  Index aliases: 340.
- **Quoted** from `README.md` and `docs/ZENODO_DESCRIPTION_v0.5.0.md`
  (no v0.5.0 tree on hand to re-measure; figures are on the earlier
  pattern — see the note at the top of this file).
- Bridges (α-X.9, X.12, X.13); root review (α-X.14, I.8); new pillar
  α-XII (polar decomposition and the self-dual connection); conformal
  frame (α-XIII); smoothness map (α-XIV). The ledger has 134 items
  (62 complete, 46 complete using a named external theorem or
  literature, 9 complete (bridge), 10 partial, 7 not started).
  See `README.md`, "What changed in v0.5.0".

## v0.4.0

- Lean module files in `CFT/`: 141 (1544 theorem declarations).
  Index aliases: 244 (the index module is first recorded in this version).
- **Quoted** from `README.md` and `docs/ZENODO_DESCRIPTION_v0.4.0.md`
  (no v0.4.0 tree on hand to re-measure; figures are on the earlier
  pattern — see the note at the top of this file).
- Ledger restructured: kinematics → action → dynamics. The ledger has
  107 items in α-I–α-XI, each recording kinematics, action and dynamics.
  Independent audit (2026-11-04/05): all recomputed Lean algebra
  correct, 11 classifications lowered. See `README.md`,
  "What changed in v0.4.0".

## v0.3.0

- Lean module files in `CFT/`: 118 (1216 theorem declarations).
  Index aliases: none recorded for this version (the index module is
  first recorded in v0.4.0, with 244 aliases).
- **Quoted** from `README.md` and `docs/ZENODO_DESCRIPTION_v0.3.0.md`
  (no v0.3.0 tree on hand to re-measure; figures are on the earlier
  pattern — see the note at the top of this file).
- Seventeen new or extended modules (142 theorems) close ten items of
  α-I–α-VIII: static S³, hypercharge obstruction, minisuperspace and
  Wheeler–DeWitt, Dirac levels on S³, Maxwell from the action, quantum
  stress on the cap, charges. The six `RealLine` "final" theorems were
  reclassified as partial (they apply only to constant fields).
  See `README.md`, "What changed in v0.3.0".

## v1.1.1 (pointer)

Version numbering was reset by the author: v1.6.1 was renamed v1.1.1.
The release snapshot is 2151 declarations (2148 theorems and
3 private lemmas) in 205 modules, plus 556 aliases — see
`docs/ZENODO_DESCRIPTION_v1.1.1.md` (the figures are on the canonical
pattern: 204 files under `CFT/` + the root `CFT.lean`). Note that the
hourly zip dated 2026-11-16 14:58 still shows the earlier 1991/187
state, so the 2151/205 release state was reached later that day.
The current working snapshot is in `README.md`.

## v0.2.0

- Imported source archive: `CFT_alpha_lean_2026-10-21k.zip`
- SHA-256: `90aba0ba4a46959ba3dc84dcb7ffc58a4409207a3a2ada410b311dbf9ce4497b`
- Imported at: 2026-10-22
- Lean module files in `CFT/`: 101 (1074 theorem declarations)
- Built by the author with Lean 4.15.0 and a local Mathlib checkout at tag `v4.15.0` (commit `9837ca9d65d9de6fad1ef4381750ca688774e608`); build log `docs/archive/build_2026-10-21k.log`. The repository's `lakefile.lean` requires the same public Mathlib tag.
- The archive's generator scripts are included under `scripts/` without their pickled certificate files, which the scripts regenerate.

## v0.1.0

- Imported source archive: `CFT_alpha_lean_2026-10-17b.zip`
- SHA-256: `63ea084fbd64c18863bbd773413383a27840377f1acdf3e01e3be6b0299ea888`
- Imported at: 2026-10-18
- Original archive file count: 283
- Lean module files in `CFT/`: 77

The original archive's Lake manifest used a path dependency on `../mathlib4`. That environment-specific manifest was removed and `lakefile.lean` was changed to use the public Mathlib tag `v4.15.0`.
