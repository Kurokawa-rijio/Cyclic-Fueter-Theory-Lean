# Requirements for the textbook (re-read before every chapter)

## User's instructions, verbatim (2026-11-12 23:42 JST)

> 全部書き直して欲しい。1冊にします。ただし、出力するときは1章ずつ終わったらpdfで出力していってください。1章終わったら出力...みたいに。最後にできたのをくっつけるだけでいいです。僕たちの会話で出てきたワードは全て使わない。けど、僕の幾何学の理論は絶対に使うこと。比喩でダンベルみたいというくらいにとどめておきましょう。あと物理で本来使われている文字に寄せてください。僕たちにしか分からない文字は使わないこと。全て先行研究を参考にしてどのような書き方をしているかを把握して書いてください。CIは別で確立されているのでleanのコードは要りません。学部生にも理解できる内容にして欲しいのですが、あまり基礎的なところから説明するとキリがないので、学部2-4生や院生向けで、なおかつ専門家にも凄さがわかるようにお願いします。6についてはそこまでいったら追加で計算して証明できそうなものはしてください。あと、番外編にはnullity paravector理論が八元数を行列の左右積や複素関数の形で表現できる可能性を示し、spin(10)との関連性がないかを検証してください。これを定期的に読み直して忘れないようにお願いします。

Earlier instructions still in force:
- Cover ALL Lean theorems (1873), understandable for undergraduates, novelty clear to experts.
- No terminology from the user's own theory; everything through prior literature.
- One single logical line (dependency order, not development history).
- Title: "Dynamics, the Action Principle, and the Kinematics That Supports Them". English only. LaTeX PDF. Monochrome figures. Human (non-mechanical) prose.
- Exercises only within what Lean has checked.
- Standard Model and string theory as interludes at the right places.

## Rules derived from these

1. ONE volume. Rewrite everything (old draft in book/ is not reused except macros/figure ideas).
2. After each chapter is finished: build, extract that chapter's pages, send the PDF to the user. The final book is just the concatenation (whole-book build).
3. Forbidden in the text: every coined word from our conversations — dumbbell (except ONE metaphor "shaped somewhat like a dumbbell"), cap, neck (as a term), quantum sphere, cyclic Fueter (family/theory), ledger labels (alpha-, Z-, U21', pillar, stage, bridge, fix, phase), "Kurokawa", "Omega" as a name, AW/AF/FW pair names, etc. The lint script enforces this.
4. The user's geometry MUST be used (it is the spine): quadratic forms that factorise (q q̄ = |q|², D̄D = Δ, X X^# = det X, det(t + x·σ) = t² − |x|²); M₂(ℂ) with two real structures (quaternions/SU(2) and Hermitian matrices/Minkowski space); rank one = null = pure state; slice sphere = Bloch sphere = celestial sphere; with mass, the hemisphere of states over the mass shell (height m/E), circular and hyperbolic polar forms linked by the Gudermannian; the state metric = mass-shell metric/(2E²); then the closed Tolman universe glued to a Bertotti–Robinson throat. Present it in standard language.
5. Symbols: those used in the physics literature (signature −+++, G, g, Λ, m(r), w(r) for the YM potential, N lapse, a(t) scale factor, ℓ only after a standard-looking definition, etc.). No private symbols.
6. Style: follow how prior literature writes (Wald, Carroll, Poisson's Toolkit, Volkov–Gal'tsov review, Baez "The Octonions", Lounesto, Penrose–Rindler, Sudbery). Check conventions against them.
7. No Lean code in the book. Lean appears only as theorem identifiers in a correspondence appendix.
8. Audience: undergrad years 2–4 and graduate students; do not start from absolute basics; experts must see what is new (Statement of Results + Relation to the Literature).
9. Interludes ("6"): when reached, compute and prove additional things that can be proved.
10. Interlude on octonions: show that paravector-nullity methods can represent octonions via left/right multiplication matrices and complex (slice) functions; check the relation to Spin(10). Honest status tags.
11. Status tags: proved / external input / numerical / negative / open. Never overclaim. α (fine-structure constant) is NOT derived.
12. Only backward references (a chapter uses only earlier chapters).
</content>
</invoke>

## Structure (fixed 2026-11-12; 31 chapters + 2 interludes)
Part I Algebra of 2×2 matrices: 1 Quaternions and SU(2); 2 SL(2,C), Minkowski space and the Dirac algebra; 3 Fueter operators.
Part II Geometry of relativistic states: 4 Mass shell as hyperbolic space / hemisphere model; 5 Positive energy and Foldy–Wouthuysen; 6 Berry and Wigner connections; 7 Monopoles, bundles, index.
Part III Curvature, gauge fields, action: 8 Moving frames; 9 Spherically symmetric metrics; 10 Maxwell and Yang–Mills; 11 Action principle; 12 Spherical reduction and the 4D check.
Interlude A: internal symmetry, octonions and Spin(10) (+ new computations).
Part IV Spherical EYM: 13 Constraints and mass; 14 Homogeneous 3-geometries; 15 Tolman and Bertotti–Robinson; 16 Static solutions; 17 Junction conditions; 18 Throat as envelope, uniqueness.
Part V Evolution and stability: 19 Constraint propagation/evolution; 20 Collapse, clock, trapped surfaces; 21 Conformal frame; 22 Linear rigidity, BF; 23 Higgs, sphalerons, BPS.
Part VI Thermodynamics and quantum: 24 BH thermodynamics; 25 JT gravity; Interlude B strings (+ new computations); 26 Canonical/WDW; 27 QFT on the glued spacetime; 28 Fermions.
Part VII: 29 Shape degrees of freedom; 30 WGC; 31 Open problems.
Plan map: map/plan_src.txt (module -> chapter; theorem-level moves are allowed, coverage.py tracks).

## Notation sheet (keep consistent)
Signature (−,+,+,+); c = ħ = k_B = 1; G explicit. Quaternions ℍ, units i,j,k, conjugate q̄. Pauli σ_i, X = t·1 + x·σ, det X = t² − |x|².
ρ: ℍ → M₂(ℂ). SL(2,ℂ) acts X ↦ A X A†. Rapidity ζ (not η); Gudermannian χ = gd ζ. Hemisphere point (m/E, p/E).
Dirac Hamiltonian H = α·p + βm. Fueter operator D = ∂₀ + i∂₁ + j∂₂ + k∂₃ (Sudbery), D̄D = Δ.
YM: action S = ∫√−g [R/(16πG) − F^a_{μν}F^{aμν}/(4g²)]; magnetic ansatz with w(t,r); ℓ ≡ √(4πG)/g (natural EYM length).
Spherical metric: ds² = h_ab dx^a dx^b + r² dΩ²; Misner–Sharp mass m. Tolman: closed radiation FRW a(η) (η conformal time).
Bertotti–Robinson AdS₂×S² radius ℓ. Junction (Poisson): [K_ab] − h_ab[K] = −8πG S_ab. Berry connection 𝒜, Wigner rotation W. Λ only cosmological constant.
