# Source snapshot provenance

- Imported source archive: `CFT_alpha_lean_2026-10-17b.zip`
- SHA-256: `63ea084fbd64c18863bbd773413383a27840377f1acdf3e01e3be6b0299ea888`
- Imported at: 2026-10-18
- Original archive file count: 283
- Lean module files in `CFT/`: 77

The original archive's Lake manifest used a path dependency on `../mathlib4`. That environment-specific manifest was removed and `lakefile.lean` was changed to use the public Mathlib tag `v4.15.0`. Because Lean/Lake is not installed in the preparation environment, dependency resolution and a fresh build have not been run here; the GitHub Actions workflow is included to test the published repository.
