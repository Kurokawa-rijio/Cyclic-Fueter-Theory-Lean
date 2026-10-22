# Generator scripts

These SymPy scripts generated the large component identities in the Lean sources and the `linear_combination` certificates used in their proofs. They are provided for transparency; the Lean files are self-contained and building the project does not need them.

- `S1/` — scalar curvature and GHY boundary term of the spherical reduction, YM field-strength formulas (stage 1).
- `S2/` — reduced action, first variation, and the match with the reduced field equations (stage 2, `AlphaS2_Action`, `AlphaS2_Match`).
- `S4/` — Christoffel symbols, Ricci, Einstein, Riemann and Kretschmann tensors, YM stress tensor and YM equations for the diagonal and double-null spherical metrics, and the 16 + 12 component four-dimensional match (`AlphaS4_Curv`, `AlphaS5_Curvature`, `AlphaS2_4DMatch`).
- `gen_audit.py` — regenerates `Audit.lean` and `CFT.lean` from the module list.

The scripts were written for the author's working directory layout (paths under `/home/claude/lean`), and the certificate files (`*.pkl`) they write are not included; adjust the paths before rerunning. Python 3 with SymPy is required.
