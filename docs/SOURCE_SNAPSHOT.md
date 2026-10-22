# Source snapshot provenance

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
