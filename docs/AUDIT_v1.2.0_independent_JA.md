# v1.2.0 独立点検の報告(2026-11-18)

> **点検後の対応(2026-11-19、Claude)**:
> - 1-1(Coulomb、major)は、定理の文を空間の添字 j ≠ 0 に制限して直しました(`coulomb_harmonic`、`coulomb_field`、`coulomb_fueter`)。
> - 2-6・4-1 は、直した `scripts/GenerateAuditIndex.py` で `Audit.lean` を作り直して対応しました(3297 行、未掲載 0)。
> - どちらも CI で確かめます。ほかの指摘への対応は、このファイルの本文のとおりです。


対象:ブランチ `release-v1.2.0`(HEAD f1167e7「v1.2.0 audit follow-up」)。`origin/main` に対して追加された
CFT 以下の 30 モジュール、`README.md`(What changed in v1.2.0)、`docs/REVIEW_2026-11-18_JA.md`、
`docs/ZENODO_DESCRIPTION_v1.2.0.md`、`CITATION.cff`、`.zenodo.json`、命題集 `LEAN_GAP_TREES_merged.md`
(第 4・13・14 章と 13-A の表。読むだけで変更していない)、`CFT.lean`・`Audit.lean`・`scripts/`。

やり方:Lean の処理系は手元に無いので、すべて読んで点検した。数式の係数・符号は、numpy による数値計算と、
有理数係数の多項式での厳密な計算(sympy は入っていないので自前の小さな多項式演算)で別に確かめた。
Lean の証明が通るかどうかは確かめていない(CI の記録に頼っている)。定理の文・定義・証明は一切変えていない。

## 結論

- major(主張が偽、または定理が空虚):**1 件**
- correction(文章が言い過ぎ、または規約の食い違い):**7 件**
- minor(言い回し・整理):**18 件**

一番大きいのは Coulomb の 2 定理です。仮定が時間の添字 j = 0 まで含むので、ふつうの静的なモデルでは
仮定が矛盾し、物理の Coulomb ポテンシャルには当てはめられません(1-1)。

くさび(4-7、4-8、4-9、4-12、4-15、4-17)の定理には、空虚な仮定や文章とのずれは見つかりませんでした。
∀/∃ の順、定数の決まり方、方向も文章どおりです。気をつける点は、「C² 解」の C² が混合 C²
(∂_u²、∂_v² を含まない)の意味だということです(2-1)。

Cartan–Palatini・枠と座標・線形化重力・Bianchi の係数(−4、−8、捩れの 2、Lorentz の +4η、G₀₀ = 2ΔΦ、
Γⁱ₀₀ = ∂ᵢΦ、縮約 Bianchi)は、すべて数値でも合いました。符号や係数の誤りはありませんでした(第 3 節)。

## (1) 仮定の破綻・空虚な定理

### 1-1 [major] Coulomb の仮定が j = 0 を含み、静的なモデルでは矛盾する

- 場所:`CFT/Foundations/ContinuumFieldLaws.lean` の `coulomb_harmonic`(99–102 行)、
  `CFT/Foundations/FueterFamousEquations.lean` の `coulomb_fueter`(171–175 行)。
- 何が問題か:仮定 `hx : ∀ j, D j (x j) = 1` と `hri : ∀ j, D j ri = -(x j * (ri * ri * ri))` が、
  時間の添字 j = 0 を含む `Fin 4` 全体で置かれている。
- なぜ問題か:静的なポテンシャル(∂₀ = ∂_t で、ri = 1/r は t によらない、つまり D 0 ri = 0)では、
  j = 0 の `hri` から x₀ ri³ = 0 が出る。S は体で ri ≠ 0(`hnorm` から)なので x₀ = 0。すると j = 0 の
  `hx` は D 0 0 = 1、つまり 0 = 1 になって矛盾する。したがって、意図したモデルではこの 2 定理は空虚で、
  「q/r は r ≠ 0 で調和」を物理の場について示したことになっていない。
  - D₀ を不自然な導分に取れば仮定をみたすモデルは作れる(`coulomb_harmonic` は形式的には空虚でない)。
    それでも、物理の読みでは使えない。
  - 証明が使うのは j = 1, 2, 3 の場合だけ。
  - REVIEW の 8 番は「∂_j x_j = 1(対角だけ)」と書いていて、この点を見落としている。
  - 同じ形の `bernoulli` では、j = 0 の余分な仮定をすでに外してある。
- 直し方(提案、定理の文の変更なので未実施):`hx`、`hri` を `∀ j, j ≠ 0 → …` にする。証明の
  `simp only [..., hx, hri, ...]` は `hx 1 (by decide)`、`hri 1 (by decide)` などの具体的な形に置き換える。
  `coulomb_fueter` も同じように直す。
- 実施した直し:両モジュールのヘッダー、REVIEW の 8 番、Zenodo の説明に、この制限を書き足した。

### 1-2 そのほか

- 仮定が矛盾する定理、結論を含む仮定、自明に成り立つ ∃ は、ほかには見つからなかった。
- 確かめたもの:
  - 一意性:`char_uniqueness`、`wedge_uniqueness*`。
  - 存在:`goursat_exists`、`wedge_local_existence(_gen)`。
  - 依存性と安定性:`char_dependence`、`wedge_dependence`、`linear_stability`。
  - Einstein 方程式:`cartan_einstein`、`einstein_*`、`torsion_*`、`einstein_lorentz_coord`。
  - 線形化重力と縮約 Bianchi:`lin_bianchi`、`newton_*`、`contracted_bianchi_normal`。
  - Fueter の橋:`maxwell_*`、`bernoulli_fueter` など。
  - 力学・八元数・単極子・喉:`ks_*`、`kepler_*`、Oct8・SelfDual4・NullField・MonopoleLangevin・ThroatSymmetry の各定理。
- `wedge_continuation`(4-15)は「∃ F」の弱い形で、箱が角の値を含まないときは中身が無い。
  それでも空虚ではない。角の値(r = Ω = 1 など)を含む箱では、データの辺の上で方程式が効く。
  弱さはヘッダーに書いてある。
- [minor] `sound_wave` の `hmom : ∀ i, …` も i = 0 を含む(ContinuumFieldLaws 86 行)。こちらは u 0 を
  u₀ := −c²ρ₁/ρ₀ と取ればみたせるので、矛盾はない。ただし不要な仮定。

## (2) 飛躍(文章と定理の食い違い)

### 2-1 [correction] 「C² 解」の C² は混合 C² で、C¹ のデータからは通常の C² 解は出ない

- 場所:
  - 構造:`CharacteristicUniqueness.C2Data`(30 行)、`GoursatExistence.GlobalC2`(183 行)、`WedgeUniq.C2On`(244 行)。
  - 文章:README(24 行)、Zenodo の 13・15 行、命題集の 4-7・4-9・4-17、REVIEW の 11c。
- 何が問題か:これらの構造が要求するのは、値・∂_u・∂_v・∂_u∂_v の連続性と、∂_u∂_v = ∂_v∂_u だけ。
  ∂_u²、∂_v² は含まない。一方 4-17 のデータは C¹ しか仮定しないので、解の ∂_u² r は(v = 0 の辺では φ₀″)
  一般には存在しない。通常の意味の「C² 解が存在する」は、C¹ データに対しては偽になる。
- 影響:発展方程式に出るのは ∂_u∂_v だけなので、定理そのものは正しく、意味もある。ただし拘束 C_u、C_v
  (`WedgeConstraints` は `Duu`、`Dvv` を含む)は、この正則性の解については意味を持たない。
- 実施した直し:各構造の docstring とヘッダー、WedgeLocalExistenceGeneral のヘッダー、README、Zenodo の Scope、
  REVIEW の 11c に、「混合 C²(∂_u²、∂_v² は含まない)」と書いた。

### 2-2 [correction] CharacteristicUniqueness のヘッダーが自分の注意と食い違っていた

- 場所:`CFT/Foundations/CharacteristicUniqueness.lean` の 9 行(release-v1.2.0 の行番号)。
- 何が問題か:「仮定はすべて R の上だけで置く(R の外での値や方程式は使わない)」とあった。ところが同じヘッダーの
  13 行と REVIEW の 1 番は、辺の点での両側 `HasDerivAt` が R の外の値に依存することを認めている。
- 実施した直し:「方程式とデータの仮定は R の上だけ。ただし辺の両側微分を通して R のすぐ外の値には依存する」に直した。

### 2-3 [correction] 「Maxwell 方程式を 1 本の双四元数の Fueter 方程式として」は片方向だけ

- 場所:README(33 行)、Zenodo の 31 行、`.zenodo.json`。
- 何が問題か:`maxwell_single_equation` が示すのは「Maxwell ⇒ D F = −(Iρ + j)」だけ。
  一般の可換環 R では逆向きは成り立たない(E、B 自身が I を含みうるので、スカラー部・ベクトル部を「実部」と
  「I 部」に分けられない)。REVIEW の 12 番には片方向と書いてあるが、公開用の文には書いていなかった。
- 実施した直し:3 か所とも「imply … (one direction; the converse is not formalised)」にした。
- 次の打ち手:R = R₀ ⊕ I R₀ の分解(E、B ∈ R₀)を仮定に足せば、⇔ の形にできる。

### 2-4 [correction] 流体と Coulomb の橋は D̄D ではなく空間の Fueter 作用素 Vec を使っている

- 場所:Zenodo の 33 行(旧文は「in terms of D̄D = Δ / □」)。
- 何が問題か:`bernoulli_fueter`、`ns_viscous_fueter`、`coulomb_fueter` が使うのは、Vec = i∂₁ + j∂₂ + k∂₃ と
  `vec_vec`(Vec² = −Δ₃)。4 次元の D̄D(`conj_product`、`biquaternion_box`)は使っていない。
  命題集の 13-A の前置き(「Fueter 型の幾何学(D̄D = Δ…)から」)も同じ言い方なので、合わせて直すのがよい
  (命題集は読むだけなので未変更)。
- 実施した直し:Zenodo を「in terms of the spatial Fueter operator Vec … (Vec² = −Δ)」に直した。

### 2-5 [correction] `MetricJet` は計量の jet になっておらず、FrameCoordinateEinstein の残りの段はこのままでは示せない

- 場所:`CFT/Foundations/CurvatureJetAlgebra.lean` の `MetricJet`(67 行)と `riem`。
  `FrameCoordinateEinstein` のヘッダー(20–22 行)、Zenodo の 23 行、命題集の 13-1。
- 何が問題か:「計量から作った Riemann テンソル」とあるが、`MetricJet` は計量 g_ab そのものを持たない。
  ginv と dg の関係(g g⁻¹ = 1)、dginv と dg の関係(∂g⁻¹ = −g⁻¹(∂g)g⁻¹)、ddg の微分の添字の対称性
  (∂_e∂_c = ∂_c∂_e)も仮定していない。示されている定理(第 1 Bianchi、反対称性、Christoffel の対称性)は、
  どれもこれらを使わない「対称な接続」一般の性質なので、正しい。ただし Zenodo とヘッダーが「未形式化」と
  している「Christoffel から作った Riemann の添字を下げたものの 2 組の反対称性」は、今の `MetricJet` からは
  原理的に出ない。
- 直し方(提案):`MetricJet` に次を足す。それで R_abcd = −R_bacd が示せるようになる。
  - `g`、`g_symm`。
  - `inv : ∀ a b, Σ_c g a c * ginv c b = δ_ab`。
  - `dginv_eq : dginv c a b = −Σ_{e,f} ginv a e * dg c e f * ginv f b`。
  - `ddg_comm : ddg e c a b = ddg c e a b`。
- 実施した直し:両モジュールのヘッダーに、この範囲の注意を書いた。

### 2-6 [correction] 「Audit.lean はすべての定理の公理を出す」は事実でない

- 場所:README(190 行)、CI のステップ名「Axiom audit (every theorem)」(`.github/workflows/lean.yml` 42 行)。
- 何が問題か:`CFT.lean` が取り込むのに `Audit.lean` が取り込まないモジュールが 56 本あった。
  - 1 本は Basic で、定理は 0 件。
  - 残りは主に v1.1.1 の light closures(WDW、RN、Schwarzschild、4-13 の角条件、Muse 側の
    WedgeIterationMap・WedgeRhsLipschitz・WedgeC1Norm・WedgeDerivContraction など)と、
    今回の WedgeC1Contraction。
  - 合計 537 件の公開定理に `#print axioms` の行が無かった。
- 影響:CI の sorry 検査は `audit.txt` の `sorryAx` を数えるだけなので、これらのモジュールに sorry が入っても
  CI は通ってしまう。ソースを grep した範囲では、`sorry`・`admit`・`axiom`・`native_decide` はどこにも無い。
  したがって「sorry なし」の主張自体は事実。
- 実施した直し:
  - WedgeC1Contraction は今回の追加分なので、import と 7 行を `Audit.lean` に足した(4-1 を参照)。
  - README を「Audit.lean に載っている定理について。v1.2.0 では 55 モジュール・530 件が未掲載」に直した。
  - CI のステップ名は変えていない。
- 次の打ち手:直した `scripts/GenerateAuditIndex.py`(4-2)で `Audit.lean` を作り直して CI に通す。
  載っていない行の名前の誤りは CI がすぐ見つけるので、手で足すより安全。

### 2-7 [correction] 縮約 Bianchi は「正規座標の 1 点で」だけ

- 場所:README(30 行)、`.zenodo.json`、Zenodo の 24 行。
- 何が問題か:`contracted_bianchi_normal` は、Γ(p) = 0、∂g(p) = 0 の点での式。テンソル性の段は未形式化。
  README と `.zenodo.json` は、この限定なしに「the contracted Bianchi identity」と書いていた。
- 実施した直し:3 か所に「at a point in normal coordinates」を足した。
- 定義の点検:REVIEW の 5 番が点検を求めていた `dRic`・`divG` の定義は、p での正しい式になっている。
  - ∂_b Ric_ad = Σ_c(∂_b∂_c Γ^c_da − ∂_b∂_d Γ^c_ca)。
  - ∇^a G_ad = g^ab ∂_b Ric_ad − ½ ∂_d R。
  - 乱数の H(x,y で対称、u,v,w で完全対称)で divG = 0 になることも数値で確かめた。

### 2-8 [minor] 文章と定理の小さなずれ

1. `SpecialRelativityLaws.velocity_addition`(27 行)
   - ずれ:示しているのは合成の時間成分 t″ だけ。ヘッダーは「ブーストの合成は…のブースト」と言っていた。
   - 直した:ヘッダーに範囲を書いた。
   - 次の打ち手:x 成分を 1 本足す。
2. `GeodesicEquation`(ヘッダー 10 行、`EL` 28 行)
   - ずれ:「計量の対称性は使わない」とあるが、`EL` の定義で ∂L/∂v^λ = Σ_μ g_λμ v^μ と書いた所に対称性が
     入っている(一般には ½Σ(g_λμ + g_μλ)v^μ)。
   - 直した:ヘッダーに注記した。
3. `ThroatIsometrySL2`
   - ずれ:`Killing` と `comm_*` は、偏微分の値を引数として代入した代数の式。その値が実際の偏微分であることは
     `xi1_*`、`xi2_*` が別に示していて、1 本の定理にはまとまっていない。
     「つまり、Tolman 宇宙の…と同じである」は形式化していない読み。
   - 直した:ヘッダーに注記した。
4. FueterFamousEquations の `coulomb_fueter`
   - ずれ:ヘッダーの「電場 ∇φ」。電場は E = −∇φ。
   - 直した:符号を書いた(3-2 も参照)。
5. `torsion_free_of_stationary`
   - ずれ:ヘッダーと Zenodo は「停留 ⇔ 捩れ 0」だが、定理は K = 0 ⇒ T = 0 の向きだけ。
     逆向きは `torsion_contraction`(K は T について線形)から直ちに出るので、実害はない。
   - 未変更。
6. `einstein_lorentz_coord`
   - ずれ:左辺は e = δ のまわりの第一変分に枠の成分の曲率を入れたもの。実際の枠 e のまわりで
     δe = k e と動かしたときの停留と同じであることは形式化していない。ヘッダーは「(`einstein_lorentz_iff` の形)」と
     断っているが、README・Zenodo の「stationarity ⇔ G = 0」はそこまで書いていない。
   - 未変更。
7. 命題集の 13-A「✓ … 4-15 障害の同定」
   - ずれ:定理は切り落とした系の解の ∃ まで。✓ は言い過ぎ。4-15 の本文には「解釈」と書いてある。
   - 命題集は読むだけなので未変更。
8. 命題集 4-17 の最後の「一般データに対する連続依存(4-8 の一般版)も未」
   - ずれ:`wedge_dependence` はデータを問わず、評価 `Good B m` をみたす任意の 2 解に効く。
     「定数がデータだけで決まる版は未」という意味なら、そう書くのがよい。
9. 命題集 13-2 の「残り:縮約した形 ∇^a G_ab = 0」
   - ずれ:13-A ではこれが ✓(1 点で)になっていて、命題集の中で食い違っている。
   - 同じく 13-A の「✓ Coulomb(q/r は調和…)」は、1-1 により ◐ が妥当。

## (3) 記号・符号・係数の誤り

### 3-1 数値・厳密計算で確かめたもの(誤りなし)

1. Levi-Civita 記号:`eps`(Vandermonde 積 /12)は 4 次元の置換の符号と一致する。
2. `cartan_einstein`:R の 2 組の反対称性だけ(対の対称性も第 1 Bianchi も無し)を仮定した乱数の R で、
   Σ ε_{μνρσ} ε_{aνcd} R_{cdρσ} = −4 G_{μa} が成り立つ。
   - 手計算でも E = 2δ R_s − 4 Ric になり、−4G に一致する。
3. `first_variation`:V(k) = −8 Σ k_{aμ} G_{μa}。差分で求めた d/dt L(δ + tk)|₀ とも一致する。
4. `torsion_contraction`:K = 2(T − δ t + δ t)。
5. Lorentz:
   - `eps_raise`:ε の 4 添字を上げると −ε。
   - `cartan_einstein_lorentz`:EL = 4 η_μ G^L。
   - ε^{μνρσ}(η で上げたもの)を使った Lorentz の密度の第一変分は −V(R̃) になる。
     `einstein_lorentz_iff` の読み替えが正しいことの数値の裏づけ。
6. `FrameCoordinateEinstein`:
   - `metric_inverse` と `einstein_frame` が成り立つ(乱数の枠 e と、2 組の反対称性をもつ乱数の Rc)。
   - 縮約は、CartanEinstein(Σ_d R_{μdad})、CartanTorsionLorentz(Σ_d η_d R_{μdad})、FrameCoord(2 番目と 4 番目)、
     CurvatureJetAlgebra・ContractedBianchi(R_bd = R^a_bad)でみな同じ規約。
     2 組の反対称性のもとで互いに一致する。
   - `BianchiSecond.curv_apply` の (a,b) 成分 = R^a_bcd も、CurvatureJetAlgebra の `riemann` と同じ規約。
7. 線形化重力(有理数係数の 4 変数多項式で厳密に計算):
   - `lin_bianchi`、`G_harmonic`、`ric_gauge` が成り立つ。
   - `newton_G00`:G₀₀ = 2ΔΦ。
   - Lean の線形化 Ricci は、CurvatureJetAlgebra の規約 R^a_bcd = ∂_cΓ^a_db − … の線形化
     Ric_bd = ∂_aΓ^a_db − ∂_dΓ^a_ab と一致する。
8. Maxwell(複素係数の四元数で計算):`maxwell_biquaternion` の各成分が合う。
   Ampère・Faraday・Gauss の符号(c = 1)も標準どおり。
9. 電磁場:x 方向のブーストでの E′、B′ の式は標準どおり。E·B と |E|² − |B|² が不変になることも確かめた。
10. Kustaanheimo–Stiefel:`ks_velocity`、`ks_norm` が成り立つ。Re ẋ = 0 も確かめた。
11. Kepler:LRL ベクトル A = (v_y L − kx/r, −v_x L − ky/r) と、A·x = L² − kr。
12. 八元数:
    - ノルムの乗法性と交代律。
    - `cayley_link` の Φ は完全反対称で、標準の Cayley 形式(三重交叉積)の符号を逆にしたもの。
      ヘッダーの「向きを選んだ」と一致する。
    - Lean に書いた T の 28×28 行列は、この Φ から作ったものと一致する。
      固有値は 3 が 7 重、−1 が 21 重(Lean では次元を数えていないが、数値では正しい)。
13. 喉の Killing 方程式と sl(2,ℝ) の交換関係:手計算で合う。Killing 形式の符号は (−,+,+) で so(2,1) ≅ sl(2,ℝ)。
14. Prasad–Sommerfield:W = x/sinh x、h = coth x − 1/x が Bogomolny 方程式 W′ = −hW、h′ = (1 − W²)/x² をみたす。

### 3-2 [minor] 規約の注意(誤りではない)

- `coulomb_fueter` のヘッダーの「電場 ∇φ」は、E = −∇φ の符号を落としていた(直した)。
- Lorentz の Cartan 密度の ε^{μνρσ}:
  - η で上げたテンソル(`EL`)と読むと、全体の符号は −V(R̃)。
  - 微分形式から来る記号(密度)と読むと V(R̃)。
  - 真空の方程式には効かない。物質つきの Lorentz 版を作るときは、どちらの読みかを決めておく必要がある。
- □ の符号:LinGrav は mostly-plus(□ = −∂₀² + Δ)、Fueter 側の `Box` は ∂₀² − Δ で、逆。
  `mass_shell` は −u₀² + |u|² = −1、`mass_shell_biquaternion` は P P̄ = p₀² − |p|²。
  どれも REVIEW の 3 節に書いてあり、`box_bridge` で橋渡しされている。食い違いはない。

## (4) コード・ファイルの整理

### 4-1 [minor] `Audit.lean` に WedgeC1Contraction が無かった(直した)

- 何が問題か:`CFT.lean` には入っていたが、`Audit.lean` には import も 7 件の `#print axioms` も無かった。
- 実施した直し:import と 7 行を足した。
  - 名前空間 `CFT.WedgeC1Contract` の 7 定理名は、ソースで確かめた。
  - 全モジュールの宣言名を集めて、修飾名の重複が無いことも確かめた(import を足しても名前の衝突は起きない)。
- そのほかの照合:
  - `Audit.lean` の `#print` 行 2767 本は、すべて実在の定理か別名を指している。
  - 重複行は無い。`CFT.lean`・`Audit.lean` の import にも重複は無い。
  - 今回の 30 モジュールのうち、ほかの 29 本の定理はすべて `#print` 行がある(この 30 本に private の定理は無い)。

### 4-2 [minor] `scripts/GenerateAuditIndex.py` が古いパスを書いていた(直した)

- 何が問題か:19 行が `import CFT.Basic` を書き出していた。v1.1.1 の改名で `CFT/Foundations/Basic.lean` に移った
  モジュールで、除外の条件は新しいパスに直っていたのに、この行だけ古いままだった。作り直した `CFT.lean` は
  build できなかった。
- 実施した直し:`import CFT.Foundations.Basic` に直した。スクリプトは CI では使わない。

### 4-3 [minor] `audit.txt` が古い

- 2402 件で、v1.2.0 の追加分を含まない。既に分かっていることなので、CI で作り直すのを待つ。

### 4-4 [minor] 証明の重複

1. `CharacteristicDependence.char_gronwall_inhom`(21 行)と `CharacteristicGronwall.char_gronwall_on`(50 行):
   約 100 行がほぼ同じ。後者は D = 0 の系として出せる(結論 f ≤ 0 と非負性から)。
2. `CharacteristicDependence.char_dependence` の評価 `hK` と `char_uniqueness` の `hK`:E = 0 の場合として共通化できる。
3. `WedgeExistence.wedge_local_existence`(174 行)と `WedgeExistGen.wedge_local_existence_gen`(53 行):
   約 150 行がほぼ同じ。前者は後者を `phiW`、`psiW` に当てはめた系にできる
   (`WedgeDataOn` と `GenDataOn phiW psiW` の言い換えの補題を 1 本足す)。
   `WedgeContinuation` の `eDu`・`eDv`・`eDuv`・`hp` の組み立ても同じ形の繰り返し。
4. `WedgeDependence` の `hC`・`hpd`・`lift` は `wedge_uniqueness_same` と同じ。
5. `sameDataOn_of_gen`(WedgeLocalExistenceGeneral 40 行)と `sameDataOn_of_dataOn`(WedgeUniqueness 265 行):証明が同じ。
6. d(½) = 0 の補題が 3 か所にある。`LinGrav.d_half`(38 行)、`Continuum.d_half'`(32 行)、
   `kepler_energy` の中の `h12`(ClassicalMechanicsLaws 44 行)。
7. 第 1 種 Christoffel の式が 3 か所にある。`Geodesic.chr1`、`MetricJet.chr1`、`ContractedBianchi.ddchr1`。
   どれも同じ規約で、食い違いはない。

### 4-5 [minor] 名前の不揃い

モジュール名と名前空間が対応していないものがある。

| モジュール | 名前空間 |
|---|---|
| CartanTorsionLorentz | `CFT.CartanEinstein` と `CFT.Classical` |
| BianchiSecond・CurvatureJetAlgebra | `CFT.Classical` |
| ContractedBianchiNormal | `CFT.ContractedBianchi` |
| ThroatIsometrySL2 | `CFT.ThroatSymmetry` |
| FueterFamousEquations | `CFT.FueterBridge` |
| ClassicalMechanicsLaws | `CFT.Mechanics` |

ほかに、次の 2 点がある。

- `WedgeDependence.wedge_dependence` には docstring が無い。
- 第 14 章のモジュール(Octonion・SelfDual・NullField・Monopole・Throat)のヘッダーの日付は 2026-11-14 で、
  命題集の「2026-11-18 追加」と違う。

### 4-6 [minor] 文書の数の食い違い(直した)

- REVIEW の表:WedgeUniqueness を 27 件としていたが、実際は 30 件(`SameDataOn` 版の 3 件が増えた)。直した。
  命題集の 4-7 の「定理 27 件」も同じ(読むだけなので未変更)。
- README の「Thirty modules were added」:同じ段落の基準(v1.1.1 の 232 モジュール)から数えると 261 − 232 = 29。
  30 は `main` から見た数(`main` には WedgeC1Contraction が無い)。基準を書き足した。
- 宣言数 2743(= 定理 2740 + private lemma 3)は、ソースの数え方と一致する。
  `FueterOperatorSquares` の private theorem 6 件は、以前の版から数えていない。
- モジュール数 261(CFT 以下 260 + 1)も、以前の版の数え方と一致する。

### 4-7 そのほか

- `scripts/check_*.lean` のような試験用の残りファイルは、追跡されているファイルの中には無い。
- `numerics/bm_compute_out.txt`、`numerics/bn_computed.npy` は `numerics/BMCompute.py` の出力。
  `numerics/README.md` には載っていない(minor)。
- 新しいモジュールのヘッダー・docstring で backtick に入れた識別子は、すべて実在する(スクリプトで照合)。
  無いものは Mathlib の名前とタクティク名だけ。
- REVIEW 0 節の「選択公理を使わない定理(`FueterBridge` の 9 件など)」は、Lean が無いので確かめられなかった。

## ここからどう詰めるか(提案)

1. Coulomb の仮定を j ≠ 0 に制限する(1-1)。証明の変更は `simp` の引数を具体的な形にするだけで済む見込み。
2. 拘束 C_u、C_v に進むには、まず正則性の段が要る:データが C²(F が C¹)なら Goursat 解の ∂_u²、∂_v² が
   存在して連続であること。
   - 不動点の式 w = F(U[w], …) を u で差分商にする。
   - 差分商の系に 4-12 の `linear_stability` を当てる。
   これは今ある道具で届く形だと思う。その後に拘束の伝播(4-2、4-10)を当てる。
3. `MetricJet` に g と 4 つの関係を足し、添字を下げた R の前の 2 添字の反対称性を示す(2-5)。
   これで FrameCoordinateEinstein の仮定 h1、h2 が計量から出せるようになる。
4. 直した生成スクリプトで `Audit.lean` を作り直し、CI で 530 件を監査に入れる(2-6)。
5. Maxwell の逆向き(2-3)、ブーストの x 成分(2-8 の 1)、Killing と偏微分を 1 本にまとめた定理(2-8 の 3)は、
   どれも小さな追加で閉じる。
6. 重複の整理(4-4)は、定理の文を変えずに証明を系に置き換えるだけ。CI で確かめながら進められる。

## このブランチで行ったコミット

| ハッシュ | 内容 |
|---|---|
| e4f24e5 | Audit.lean:WedgeC1Contraction の import と 7 件の `#print axioms` を追加 |
| 6276d24 | ヘッダー:C2Data・GlobalC2・C2On は混合 C² と明記。CharacteristicUniqueness の「R の外の値は使わない」を訂正 |
| d14c0cd | Coulomb の仮定が j = 0 を含む点をヘッダーと REVIEW に記載 |
| 5934fe3 | 公開文書:Maxwell は片方向、流体・Coulomb の橋は D̄D ではなく Vec |
| e2c3455 | README:モジュール数の基準、縮約 Bianchi の範囲、監査の範囲 |
| 0535bbd | ヘッダー:速度の合成、測地線の EL、MetricJet、喉の Killing 場の範囲の注記 |
| df595bb | REVIEW:WedgeUniqueness は 30 件。4-17 の C² は混合 C² |
| ad832c0 | Zenodo 説明:くさびの結果の C² の定義 |
| c7559c9 | GenerateAuditIndex.py:`import CFT.Basic` → `import CFT.Foundations.Basic` |
| 628b272 | Zenodo の 2 文書:縮約 Bianchi は 1 点で |
| 41f7b00 | README:4-17 は角で r, Ω > 0 を仮定し、解は混合 C² |
| (この報告書) | docs/AUDIT_v1.2.0_independent_JA.md を追加 |

どれもコメント・文書・スクリプトの変更だけです。定理の文・定義・証明は変えていません。
push・PR・CI の起動・main への取り込み・ブランチの削除はしていません。

- worktree:`/home/claude/cyclic-fueter-theory-lean/.claude/worktrees/agent-a9af225393a08b909`
- ブランチ:`audit-v1.2.0`(`release-v1.2.0` の f1167e7 から分岐)
