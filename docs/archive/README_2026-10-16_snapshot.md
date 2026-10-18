# 命題群 α の Lean 4 形式化(α-I〜α-VIII の ◎・◎(既存定理の適用)・⊘)

検証日:2026-10-16
環境:Lean 4.15.0、Mathlib(タグ v4.15.0)

## 結果の要約

- 定理 706 個が、すべてエラーなしでコンパイルを通る(2026-10-16、全体を作り直して確認)(うち 109 個は α-II.5 の証明を小さく分けた補助恒等式 `cf…_k…`)。
- `sorry`(証明の穴)はゼロ。独自の `axiom` もゼロ。
- `#print axioms`(audit.txt)では、697 個が Lean 標準の公理 [propext, Classical.choice, Quot.sound] だけに、4 個(fw_generator、d_inv、curvature_covariant、inversion_swaps)が propext だけに、2 個(yukawa_weight、deriv_ofNat)が propext と Quot.sound だけに依存し、3 個(witten_even、spinor16_count、higgs_bidoublet)は公理を使わない。
- **独立監査(review/audit_table.md)の結果、51 項目のうち台帳の命題どおりに完全なのは 12 項目だった。B(ダンベルの基礎、2026-10-16)と作用原理で 4 項目、2026-10-17 に 6 項目を閉じ、いまは 22 項目。** 下の「集計」と各行の判定は監査後のもの。
- 形式化の途中で、式の誤り二つ、規約の問題一つ、質量の定義の取り違え一つが見つかった(下の「見つかった誤り」)。どれも結論は変わらない。

## 判定の意味

Lean が保証するのは「書かれた仮定から、書かれた結論が論理的に従う」ことだけである。

- **完全**:命題の数学的な核心を Lean で証明した。物理の入力(場の方程式、計量、連鎖律で得た導関数の形)は、定義または定理の仮定として明示している。
- **完全(外部定理を仮定)**:Lean で証明した部分に、論文などの既知の定理を一つ足すと命題全体になる。足す定理の名前を明記する。足すものが既知の定理でない例外:α-II.5 は sympy の厳密な記号計算(係数行列の階数 12)、α-VIII.2 は台帳どおりの作用の切り詰め(条件つきの障害)。
- **外部定理の引用**:命題そのものが既知の定理の引用で、Lean で付け加えることがない。
- **部分**:核心の一部だけを証明した。
- **未**:今回は形式化していない(理由つき)。

α-II.4〜II.6 の幾何の入力は、Cartan の動標構の公理だけである:R を開集合 U 上の滑らかな関数の環、e₀, e₁, e₂ を正規直交枠(R の導分)とし、Levi-Civita 接続の係数 Γ が「Γ i j k = −Γ j i k(計量との両立)」と「[e_k, e_m] = Σ(Γ x m k − Γ x k m)e_x(捩れゼロ)」を満たす。曲率と Ricci はそこから定義し、3 次元で Ricci が曲率を決めることも Lean で証明した。U 上で消えない関数が R の単元であることは仮定 IsUnit として入れる。

## 集計(α-I〜α-VIII の ◎・◎既存・⊘、全 51 項目)

| 判定(独立監査後、2026-10-16) | 項目数 |
|---|---|
| 完全 | 22 |
| 部分(形式化が主張より弱い) | 17 |
| 条件つき(核心を仮定に置く) | 8 |
| 未(台帳と別の対象を形式化) | 4 |

監査直後は 完全 12 / 部分 19 / 条件つき 16 / 未 4。B(2026-10-16)で α-I.5(部分 → 完全)、α-III.3、α-IV.5(条件つき → 完全)を、作用原理(2026-10-16)で α-II.1(部分 → 完全(外部定理を仮定))を、2026-10-17 に α-I.7、α-III.4、α-V.4、α-VIII.7、α-VII.6、α-VIII.5(条件つき → 完全、うち I.7、VIII.7、VII.6、VIII.5 は外部定理を仮定)を更新した。α-VIII.7 は仮定が一つ減ったが、外部定理の仮定が残るので条件つきのまま。

独立した監査(review/audit_table.md)で、各項目の Lean の定理の仮定と結論を、台帳 Z・Y の命題と一つずつ照合した結果。監査前は 49 項目を「完全」としていたが、それは過大評価だった。

## 見つかった誤り

1. 旧スクリプト awaf.py に記録されていた A_W と A_B の閉じた形は、どちらも全体の符号が逆だった。正しくは A_W = −iσ·(p×dp)/(2m(E+m))、A_B = +iσ·(p×dp)/(2E(E+m))。関係 A_B = −(m/E)A_W と、ゲージ非同値の結論には影響しない。
2. Z5(α-II.9)の再証明は、最後の一歩が「多項式 P(x,u) が正」を格子点で数値的に確かめただけだった。P は境界 u = 0 上で (x,u) = (1,0) と (√3−1, 0) に零点を持ち、後者では P の二次の部分が退化している(P ≈ 0.86(ξ + 2u)² + 113u³)。**解決済み**:P > 0 を経由しない証明に差し替えた。W ≠ 0, W² ≠ 1 の開集合上でハミルトン拘束を流れに沿って 3 回微分すると、代数的に矛盾する(証明書 ℓ²(rW(W²−1))⁴ = Σ kᵢEᵢ)。結論は変わらない。

3. α-VIII.5(Z38)の ℓ*² = α′/8 の係数は規約に依存する。ℓ*² = 4πG/g² とヘテロティック弦の G_N = c·α_GUT·α′ から ℓ*² = c·α′ で、台帳の 1/8 は g² = 4κ²/α′ の規約(c = 1/8)に当たる。Witten(hep-th/9602070)の木の近似の縮約 G_N = α_GUT α′/4 では ℓ*² = α′/4。本文では ℓ*² = α′/4(Witten の規約)を採用する(2026-10-16 決定)。Z42 の障害(k が正の整数にならない)はどちらの規約でも成立する。

4. Z9-b・Z9-c で E = r(1 + ṙ²) + ℓ²/r を「Misner–Sharp 質量の 2G 倍」と呼んでいたのは誤り(台帳 e3f51db2 の注意を Lean で確認)。喉(∂_s r = 0)では 2Gm_MS = r(1 + ṙ²)(ms_general)で、E = 2Gm_MS + ℓ²/r は Reissner–Nordström の質量母数 2GM(rn_param)。首の値 E = 2ℓ は極限 RN(rn_extremal)。崩壊中の増え方は、E は常に(dE/dτ = −2W²ṙ ≥ 0)、MS 質量は 2(rW)² ≥ ℓ² のとき(ms_deriv、ms_increases)で、後者は崩壊の条件と同じ式。結論は変わらない。

## B:ダンベルの基礎(2026-10-16 追加)

台帳の項目ではなく、ダンベルの形そのものを確かめた結果(AlphaB_QH、AlphaIII_Shape、AlphaIV_Z9、AlphaI_QBij)。

- 量子球面 Q と質量殻 H は同じ空間:Q の北半球は H³ の半球模型。同じ固有速度 u = p/m の上で Q の高さ m/E と H の高さ E/m は逆数(qh_reciprocal)。Q の極角はラピディティの Gudermann 関数 χ = gd η(gudermann、台帳 Z10 と同じ関数)。計量は ds_Q² = ds_H²/E²(conformal)。
- 傾き:H の傾き dE/dp = v(速度)、Q の傾き −p/m(固有速度)(slope_H、slope_Q、slope_Q_value)。
- 法線:H の法線は 4 元速度、Q の法線は状態 U そのもの。接点 p = 0 で二つは (1, 0) に一致し、運動量は m 倍の法線(normal_H、normal_Q、contact)。
- 混在する面:Σ_κ:X₀ = √(1 − κX²) は接点を共有し、2 階微分は −κ(κ = 1 が Q、−1 が H、0 が Newton の平面)(cayley_klein、curv_H_Q、curv_Q_over_u)。
- 面積:H の円板 2πm(E₀ − m)(運動エネルギーに比例)、Q の帽子 2π(1 − m/E₀)、比は mE₀、半球全体 2π、H の円板の Gauss–Bonnet(area_H、area_Q、area_ratio、hemisphere_area、gauss_bonnet_H)。任意の領域は Area_Q = ∫ dA_H/E²。
- 時空の切り口:帽子の傾き r′ = cos(s/ℓ)(頂点で 1、接合で 0)、帯の面積、帽子の体積 π²ℓ³、断面の Gauss–Bonnet 4π(cap_slope、cap_slope_ends、band_cap、band_neck、cap_volume、gauss_bonnet_dumbbell)。
- 接合部:周縁的捕捉面(null 膨張 0)、自分の Schwarzschild 半径にある(2Gm = r)、法線方向の応力は放射の圧力 +1/(8πGℓ²) から磁場の張力 −1/(8πGℓ²) に跳ぶ(junction_mots、junction_schwarzschild、junction_entropy、normal_stress)。

## 項目ごとの対応

### α-I 代数的な起点

| 項目 | 判定 | Lean の定理(ファイル) | 内容と残り |
|---|---|---|---|
| α-I.1 (Y1) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `i_sq` `j_sq` `k_sq` `ijk` `normSq_mul'`(AlphaI) | 四元数の規約とノルムの乗法性 |
| α-I.2 (Y2) ◎ | **部分(形式化が主張より弱い)**(監査前:完全(C は台帳の記述から再構成)) | `right_kernel` `left_kernel` `rank_three` `singular` `gam_i` `gam_mk` `ker_eq_range` `real_rank_twelve`(AlphaI_C) | 巡回 Fueter 係数 C_{ra} = e_{r+a}(e = (1,i,j,k)、係数は左から作用)。ker_R C = γ(−k)ℍ、ker_L C = ℍγ(i) を両方向で証明し、列 0, 1, 2 の右一次独立と列 3 = 列0·k + 列1 − 列2·k から rank_ℍ C = 3。C の成分は台帳の記述(巡回 Fueter、左右の核)から再構成したもので、二つの核が台帳の主張と一致することが検算。実数化した ℝ 線形写像 Cmap : ℍ⁴ → ℍ⁴ の階数は 12(real_rank_twelve:核 = γ(−k)ℍ が 4 次元、16 − 4)。「階数 3」は右 ℍ 加群としての階数で、実数の階数 12 に対応 |
| α-I.3 (Y1, Y2) ◎既存 | **完全**(監査前:完全) | `det_rho` `rho_mul` `det_lorentz`(AlphaI)、`rho_injective` `rho_star` `rho_one` `rho_SU2` `lorentz_action`(AlphaCompleteB) | ρ は単射な代数準同型で ρ(q̄) = ρ(q)†、単位四元数は SU(2) に写る。SL(2,ℂ) は X ↦ AXA† でエルミート性と det X = t² − \|x\|² を保つ |
| α-I.4 (Y3) ◎ | **完全**(監査前:完全) | `dirac_sq` `proj_idem`(AlphaI)、`quantum_metric`(AlphaCompleteB) | H² = E²、P = ½(1 + H/E) は冪等、量子計量 ½tr(∂P∂P) = ½(δ/E² − pp/E⁴) |
| α-I.5 (Y4) ◎ | **完全**(監査前:完全、監査後:部分 → B で更新) | `qD_unit` `qD_upper` `Qm_unit` `Qm_rest` `radial_metric` `chi_deriv`(AlphaI)、`pullback_metric` `dQ0_deriv`(AlphaCompleteB) | 単位性、上半球、引き戻し計量 δ/E² − pp/E⁴。g^Q = ½(単位 S³)なので半径 1/√2。B(2026-10-16):監査で欠けていた全単射を証明した:Q(p) = (m/E, p/E) は R³ から開いた上半球への全単射で、逆写像は p = m x/w(qmap_bij、qinv_left、qinv_right、AlphaI_QBij)。局所的な等長と合わせて開半球との等長同型 |
| α-I.6 (Y5) ◎ | **完全**(監査前:完全) | `curv_formula` `gram_trace` `gram_gauge` `*_coeffs` `trG_*` `ratio` `trG_B_lt` `wigner_deriv` `berry_deriv` `berry_not_gauge_wigner`(AlphaI_AW)、`d_inv` `curvature_covariant`(GaugeCovariance) | trG_B = (m/E)⁴ trG_W、p ≠ 0 で F_B = gF_Wg⁻¹ となる g は存在しない。「ゲージ同値なら曲率は共役(F′ = gFg⁻¹)」も任意の非可換環で証明した |
| α-I.7 (Y6) ◎ | **完全(外部定理を仮定)**(監査前:完全(外部定理を仮定)、監査後:条件つき → 2026-10-17 更新) | `hopf_norm` `hopf_re` `bps_k` `bps_f`(AlphaI)、`F_eps` `starF_closed`(AlphaCompleteC)、`bps_closed` `bps` `aB_eq` `apB_eq`(AlphaCompleteC2) | Berry 接続と Φ = (p/E)·T は、曲率 −1 の H³ 上で BPS 方程式 D_AΦ = −*F を厳密に満たす。単極子から S¹ 不変インスタントンへの対応は Atiyah(1984)の定理。2026-10-17:監査で欠けていた「h の曲率が −1」を証明した(AlphaI_H3):h = dP²/E² + (P²/m²)dΩ²(h_radial、h_tangential)、P = m sinh η で h = dη² + sinh²η dΩ²(h_rapidity)、Cartan の第二構造式で ds² + f²dΩ² の曲率 2 形式を全成分計算(warped_curvature、sectional)、f = sinh で断面曲率はすべて −1(h3_curvature)、検算として帽子は +1/ℓ²(cap_curvature)。外部定理は Atiyah(1984)だけ |

### α-II 統一方程式 U21′ と三つの相

| 項目 | 判定 | Lean の定理 | 内容と残り |
|---|---|---|---|
| α-II.1 (Z2) ◎ | **完全(外部定理を仮定)**(監査前:完全、監査後:部分 → 2026-10-16 作用原理で更新) | `coeff_I` `rm2_3d` `ric2_of_I` `trace_II`(AlphaII)、`II_iff_cotton`(AlphaCompleteB)、`ym_stress` `cap_stress` `neck_stress` `ell_cap` `ell_neck` `flux_cap` `riem_identity` `geometric_constraint` `Rtt_deriv` `sector_delta` `sector_geodesic` `phase_neck` `phase_form` `no_hyperbolic` `neck_any_lapse` `frw_exact`(AlphaII_EYM)、`spin_torsion_free` `spin_antisymmetric` `spin_is_witten` `s3_spin_connection` `lambda_zero`(AlphaII_Action) | 作用は SU(2) の Einstein–Yang–Mills S = ∫√−g[R/(16πG) − (1/2g²)trF²] + GHY 項。ゲージ群は量子球面 Q = SU(2)、U21′ の W = r′ は「YM 場 = 空間のスピン接続」と同値(spin_is_witten)。ダンベルはこの理論の時間対称な初期データ:帽子は放射 ρ = 3/(2g²ℓ⁴)、首は Bertotti–Robinson、ハミルトン拘束は両方の領域で ℓ² = 4πG/g²、Λ = 0 は貼り合わせで決まる。拘束は幾何の式 ³R = (ℓ²/2)|Riem₃|²。W = r′ は作用に代入せず初期データの条件として課し、時間対称な瞬間の 2 階の時間微分で保たれるのは(測地的な時間で)平坦・S³(ℓ)・S²×ℝ(ℓ) の三つの相だけ(phase_neck、phase_form、no_hyperbolic)。帽子(FRW)と首では厳密に全時間で保たれる。外部定理:Lovelock の定理と YM の一意性(作用の一意性)、球対称な YM の場の強さと応力の公式、ADM の発展式。数値計算(2026-10-16、aux/EYM/evolve.py、同期ゲージ、帽子と首の厳密解を境界条件、解像度 201〜1601 で収束):接合部から出る光円錐の外では W = r′ が保たれ、内側では破れる(|W − r′| の最大は t = 0.2, 0.4, 0.6, 0.8 で 1.0×10⁻³, 9.3×10⁻³, 3.9×10⁻², 0.13、解像度によらない、およそ t³ で育つ。時間対称な瞬間の 2 階の微分が 0 という解析と整合)。ハミルトン拘束の残差は解像度とともに 0 に収束。したがって U21′ は EYM の閉じたセクターではなく、初期データの条件(三つの相の内部でだけ厳密に保たれる)。場の強さの公式(B_r = (1 − W²)/r²、B_t = W′/r)は接続から sympy で確認(aux/EYM/fcheck.py) |
| α-II.2 (Z3) ◎既存 | **条件つき(核心を仮定に置く)**(監査前:完全(外部定理を仮定)) | `satI_*` `not_satI_*` `three_phases`(AlphaII) | CIS 1999 Theorem A の候補のうち (I) を満たすのは平坦、S³(ℓ)、S²(ℓ)×ℝ だけ。2026-10-16:球対称・時間対称・W = r′ の範囲では、CIS を使わずに三つの相が力学の両立性とハミルトン拘束から出る(AlphaII_EYM の phase_neck、phase_form、no_hyperbolic)。2026-10-17 の整理:CIS の定理の適用条件のうち「スカラー曲率一定」は (II) と縮約 Bianchi から出る。縮約 Bianchi を動標構の公理から証明しようとしたが、枠の Jacobi 恒等式(可積分条件)が公理にないため閉じなかった(次の課題)。大域的な分類(完備性)は CIS の外部定理のまま |
| α-II.3 (Z3) ⊘ | **条件つき(核心を仮定に置く)**(監査前:外部定理の引用) | — | CIS 1999 Theorem B。2026-10-17 の整理:内容は大域的な分類(完備性から全体の形)で、de Rham の分解などの外部定理が必要。Lean の数学ライブラリにまだない |
| α-II.4 (Z4-1, Z4-2) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `Riem_anti_left` `Riem_anti_right` `riem_of_diag_ricci`(Cartan/Frame)、`riem` `cod*` `D*` `G*` `pD*` `pG*` `S*` `T*` `bochner`(Cartan/C2)、`kappa_eq_neg_grad` `kappa_nonpos`(Cartan/BochnerSign)、`kappa_sym` `kappa_closed` `window` `window_cos`(AlphaII) | Cartan の動標構(Levi-Civita 枠の公理 2 つ)から、Codazzi の一般解(e_kλ_i と Γ が (λ, α, β, γ, η) の多項式)、曲率の構造式 18 本を導き、1 段目の両立条件が Bochner 恒等式 \|∇Ric\|² + Σ_{i<j}K_ij(λ_i−λ_j)² = 0 であることを示した(= −(λ₀−λ₁)²S0101 − (λ₀−λ₂)²S0202 − (λ₁−λ₂)²S1212)。各点で κ = −\|∇Ric\|² ≤ 0、窓定理と合わせて C2 の必要条件 |
| α-II.5 (Z4-3) ◎ | **条件つき(核心を仮定に置く)**(監査前:完全(外部の計算を仮定:2 段目の係数行列の階数 12 は sympy の厳密計算)) | `fs*`(SSFirst)、`row0`〜`row11`(SSRows*)、`K0`〜`K3`(SSK)、`Bj_frame`(SecondStage)、補助 `cf…_k…`(SSCoef*) | 2 段目の未知数 E_kj = e_k e₂v に対する 21 本の一次方程式のうち、捩れの 12 本の分子 n0〜n11 を定義し、任意の C2 枠で n_r = 0(row*)、Bochner 多項式 Bj = 0(Bj_frame:2(λ₀−λ₁)²(λ₀−λ₂)²Bj が構造式 S1212 と 1 段目の解の一次結合)を証明。捩れの行だけの左核 4 本は多項式の恒等式として K₀ ≡ 0、K₁ = m₁·B、K₂ = m₂·B、K₃ = a₀·e₀B + m₃·B(E の項は消える)。残り 3 本(Hessian の捩れ)は捩れの公理そのもの。左核が 9 次元(係数行列の階数 12)であることだけは aux/cartan/stage2r.py の厳密な記号計算で、Lean では未証明。これを認めると独立な条件は高々 2 本:rank C ≤ 2。B ≠ 0 の点では rank C = 3(対照実験、sympy) |
| α-II.6 (Z4-D, E) ⊘ | **完全**(監査前:完全) | `codazzi_to_flow` `flow_s1` `flow_s2` `flow_e1`〜`flow_e3` `cert` `diagonal_class_degenerate` `scalar_conserved`(AlphaII_Diagonal)、`aligned_impossible`(Cartan/Aligned) | 対角型(Z4-D):Codazzi と σ₂ 一定から 4 回微分で Δ² = Σcₖeₖ、α ≠ 0 かつ固有値が相異なる解はない。整列型(Z4-E):固有値の勾配が e₀ 方向で消えないとき、構造式から β = γ = η = 0、固有値だけの関係 g(λ) = 0 が出て、e₀ で 2 回微分すると ((λ₀−λ₁)(λ₀−λ₂)(λ₁−λ₂))³ = 0 の矛盾 |
| α-II.9 (Z5) ⊘ | **完全**(監査前:完全) | `br_lapse_d1` `br_lapse_d2`(AlphaII)、`dV_from_bd` `E0_eq` `flow_E0`〜`flow_E2` `cert` `static_W_trichotomy` `const_of_discrete` `static_classification`(AlphaII_Z5) | 静的方程式 (a)(b)(d) の解は区間上で W ≡ 0(r² = ℓ²、BR の首)か W ≡ ±1(V = 0、ρ = 0、平坦)。(c) は不要。「見つかった誤り」2 を解決 |

### α-III 接合とダンベルの必然性

| 項目 | 判定 | Lean の定理 | 内容 |
|---|---|---|---|
| α-III.1 (Z6) ⊘ | **部分(形式化が主張より弱い)**(監査前:完全) | `israel_jump` `israel_impossible` | [T_nn] = −1/(4πGℓ²) ≠ 0 |
| α-III.2 (Z7) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `null_front`(AlphaIII_P1) | k^μ[T_μν] = 0 |
| α-III.3 (Z0) ◎ | **完全**(監査前:完全、監査後:条件つき → B で更新) | `integrand_nonneg` `penrose_spherical` `no_flat_exterior`(AlphaIII)、`ms_from_constraints` `penrose_from_constraints`(AlphaIII_Shape) | M₂ ≥ r₀。監査で指摘された仮定 hD(質量の恒等式 M′ = r²(ρr′ − J rK_T))を、ハミルトン拘束と運動量拘束(AlphaIII_Codazzi の codazzi_s の形)から導いた。残る入力は拘束方程式そのもの(場の方程式)と ³R = 2(1 − r′² − 2rr″)/r² の公式 |
| α-III.4 (Z0′) ◎ | **完全**(監査前:完全、監査後:条件つき → 2026-10-17 更新) | `M2_cap` `M2_equator` `M2_neck` `neck_marginal` `M2_flat` `a_eq_l` | a = ℓ、首は平坦へ開けない。2026-10-17:仮定を結論にしない二つの独立な導出(AlphaIII_Glue):C¹ の貼り合わせ [r] = [r′] = 0 から a = ℓ(glue_C1)、EYM のハミルトン拘束が帽子と首でそれぞれ半径² = 4πG/g² を要求することから a = ℓ(glue_EYM)。首が平坦へ開けないことは拘束方程式からの Penrose 型定理で(no_flat_from_constraints) |
| α-III.5 (Z0′) ⊘ | **完全**(監査前:完全) | `schw_*` | Schwarzschild は (I) を満たさない |
| α-III.6 (Z0-f) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `cap_newton` `flat_mass_rate` | 平坦極限との整合 |
| α-III.7 (Z0-m) ◎ | **完全**(監査前:完全) | `min_mass` | ℓ*/(2G) = √π M_Pl/g |
| α-III.9 (Z23) ◎ | **条件つき(核心を仮定に置く)**(監査前:完全) | `classify` `scalR` `constraint_form` `weak_second_derivative` `shell_density` `no_shell_iff`(AlphaIII_Junction)、`israel_jump`(AlphaIII)、`null_front`(AlphaIII_P1)、`israel_trace` `israel_inverse` `israel_inverse_three` `israel_no_shell`(AlphaIII_Israel)、`codazzi_s` `codazzi_theta` `codazzi_phi` `hamiltonian_K`(AlphaIII_Codazzi) | 面の型を法線の長さで分類。空間的な切り口の中では Gauss の式 ³R = 2(1−r′²−2rr″)/r²、両側の部分積分で r″ = r″_正則 + [r′]δ、表面密度 σ = −[r′]/(4πG r₀)、殻なし ⇔ [r′] = 0(Z1 の接合は殻なし)。時間的な面は Israel(III.1)、ヌルな面は k^μ[T_μν] = 0(III.2)。非球対称な接合は未。非球対称の非ヌル面(2026-10-16 追加):任意の枠の誘導計量 h(可逆)で Israel の条件 S = −([K] − h tr_h[K])/(8πG) を逆に解き [K_ab] = −8πG(S_ab − h_ab tr_h S/(n−1))(n = 3 で ½)、殻なし ⇔ [K_ab] = 0。残り:ヌル面(Barrabès–Israel)、分布としての Einstein 方程式から条件自体を導くこと。球面の外曲率 K = (r′/r)h で σ = −[H]/(8πG) が σ = −[r′]/(4πG r₀) と一致(sphere_consistency)。台帳の Z23(ダンベルの首と半球の切り口の Gauss–Codazzi と各領域の拘束、時間的・空間的・ヌルの接合の区別)を閉じた(2026-10-16 第 3 弾):Christoffel 記号を計量の公式から計算し、球対称の運動量拘束 2(r′/r)(a−b) − 2b′ = 8πG j_s、角度成分 0、ハミルトン拘束の外曲率部分 K² − K·K = 4ab + 2b²。Gauss の式と表面密度(Junction)、一般の Israel 条件(Israel)、ヌル面(null_front)、型の区別(classify)と合わせて完全。球対称でない接合は台帳の命題に含まれない |

### α-IV 時間発展

| 項目 | 判定 | Lean の定理 | 内容と残り |
|---|---|---|---|
| α-IV.1 (Z1) ◎既存 | **条件つき(核心を仮定に置く)**(監査前:完全(外部定理を仮定)) | `cap_constraint` `neck_constraint` `cap_r_deriv` `cap_rp_deriv` `junction_jumps` `cap_energy` `neck_energy`(AlphaIntegrals) | 初期データは拘束を満たし C^{1,1}、エネルギー有限。弱解の存在と一意性は Rauch–Reed(1981/1985)。2026-10-17:幾何の部分を証明した(AlphaIV_Propagation):球対称な EYM の同期ゲージで、拘束は ∂_t H = 2K H − 4(DR/R)M − 2DM、∂_t M = 2(K_x + K_T)M − ½DH を満たす(hamiltonian_propagation、momentum_propagation、微分体の導分で証明)。右辺は (H, M) について線形・斉次なので、拘束は時間発展で保たれる(縮約 Bianchi の球対称での形)。残る外部:非線形 EYM の解の存在・一意性(Choquet-Bruhat、折れ目のある C^{1,1} データでは低い正則性の理論)と、線形の系の一意性のエネルギー評価 |
| α-IV.2 (Z8) ◎ | **完全**(監査前:完全) | `jump_const` `ruu_jump`(AlphaIV) | [W_u] は一定、[r_uu] = −(2/r)[W_u²] |
| α-IV.3 (Z9-a) ◎ | **完全**(監査前:完全) | `center_ode`(AlphaCompleteA) | 二重 null 方程式から中心の式を導出(σ の時間微分が打ち消し合う) |
| α-IV.4 ◎ | **完全**(監査前:完全) | `energy_deriv` `energy_nondecreasing`(AlphaIV) | dE/dτ = −2W²r′ |
| α-IV.5 (Z9-c) ◎ | **完全**(監査前:完全、監査後:条件つき → B で更新) | `acc_le` `rp_nonpos` `r_le` `rp_bound` `r_lt` `energy_lower` `psi_deriv` `psi_lt` `z9_collapse` `z9_before_half_period` `z9_reaches_zero` `static_iff` `static_dichotomy` `neck_frequency`(AlphaIV_Z9)、`energy_inequality` ほか(AlphaCompleteA) | 監査で指摘された仮定(ṙ ≤ 0 と微分不等式を全時間で仮定)を外した:転回点から、(rW_l)² ≥ κ、2κ ≥ ℓ² の類では ṙ ≤ 0 と r < r₁ を方程式から導き、正の解は固有時 π r₁/2 より長く続かない(z9_collapse、鋭い:κ = ℓ²/2 で等号に近づく)。r₁ ≤ ℓ* なら t_sing < πℓ*/2(Z9-b の目標)。閾値 2κ = ℓ² は静止した喉が消える点(static_dichotomy)。残り:源 W 自身の発展方程式との連立(W は与えられた関数として扱う)と、特性初期値問題の適切性 |
| α-IV.7 (Z10) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `tan_gd` `gd_deriv` `sqrt_one_add_tan_sq` `front_deriv`(AlphaIV) | gd と波面 |
| α-IV.8 (Z10′) ◎ | **完全**(監査前:完全) | `fronts_meet_before` `arrival_bound` `cap_lifetime`(AlphaIV)、`arrival_time`(AlphaCompleteA) | τ(z) = ∫₀^z sech(t/ℓ)dt = ℓ gd(z/ℓ) < πℓ/2、キャップの寿命 ℓ |
| α-IV.9 (Z0-f) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `gd_deriv_zero` `gd_zero`(AlphaIV) | 平坦極限 |
| α-IV.12 (Z13) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `wdw_exact`(AlphaIV)、`hj_exact`(AlphaCompleteA) | Hamilton–Jacobi の厳密解 S = aσ(b) と、WKB 波動関数 e^{iaσ}/σ が WDW を厳密に満たすこと |

### α-V 量子論

| 項目 | 判定 | Lean の定理 | 内容と残り |
|---|---|---|---|
| α-V.1 (Z14〜Z17) ◎ | **未(台帳と別の対象を形式化)**(監査前:完全) | `cos_gd` `sin_gd` `conformal_consistent` `mode_identity` `fw_generator`(AlphaV)、`fw_exact`(AlphaV_FW)、`frame_eq` `maurer_cartan` `inv_deriv` `frame_metric`(AlphaCompleteB) | Z14 共形対応、Z15 FW 生成子、Z16 A_F = ½U⁻¹dU は計量 g^Q の Levi-Civita スピン接続(捩れゼロ・su(2) 値・枠の計量が g^Q と一致)、Z17 FW 変換 |
| α-V.2 (Z18-a) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `SS_singlet` `SS_upup` `level_shift` `level_triplet`(AlphaV) | 3/2 − 3λ と 3/2 + λ |
| α-V.4 (Z19) ◎ | **完全**(監査前:完全、監査後:条件つき → 2026-10-17 更新) | `gauss_compactness` `gauss_interior` `gauss_vacuum`(AlphaV) | Gauss 写像。2026-10-17:Gauss 写像を定義して導出した(AlphaV_Gauss):時間対称・球対称で R⁴ に埋め込める切り口(|r′| ≤ 1)の単位法線 N ∈ S³ について cos χ = r′(gauss_normal、gauss_angle)、Misner–Sharp 質量で sin²χ = 2Gm/r(gauss_mass)、Schwarzschild で 2m/r、赤道 χ = π/2 ⇔ r′ = 0 ⇔ 2Gm = r(地平面・周縁的捕捉面、gauss_marginal)。ダンベルでは帽子が χ = s/ℓ、首全体と接合の球面が赤道(gauss_cap、gauss_neck)。量子球面 Q との対応は同じ S³ の極角という形の対応にとどめる |
| α-V.5 (Z29) ◎ | **条件つき(核心を仮定に置く)**(監査前:完全(外部定理を仮定)) | `endpoint_F` `endpoint_G` `not_L2_half` `not_L2_gt`(AlphaIntegrals) | 局所解と、κ ≥ 1/2 で L² でないこと。limit-point の結論は Weyl の判定法 |
| α-V.7 (Z31) ◎ | **未(台帳と別の対象を形式化)**(監査前:完全(外部定理を仮定)) | `log_coeff_meron` `a4_meron` `a4_vacua`(AlphaV)、`curvature_formula` `curvature_traceless` `EF_eq` `trace_Msum_sq` `trace_EF_sq` `trace_Omega_sq` `integrand` `a4_value` `four_pi_three_halves`(AlphaV_A4) | F_ab = 4iλ(1−λ)ε_abc s_c、tr E_F² = 48λ²(1−λ)²、Σtr Ω_F² = −96λ²(1−λ)²、(4π)^{−3/2}(1/360)·2π²·(180·48 − 30·96) = 4√π。よって a₄(λ) − a₄(0) = 4√π λ²(1−λ)² を閉じた形で導出(数値フィットと一致)。外部定理は Gilkey の a₄ 公式と Lichnerowicz の公式 |

### α-VI 重力と量子重力

| 項目 | 判定 | Lean の定理 | 内容 |
|---|---|---|---|
| α-VI.3 (U21′ 監査) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `s3_not_ultrastatic` | S³ 相は宇宙定数なしでは静的でない |
| α-VI.4 (Z33) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `wdw_exact` | WDW の厳密解 |
| α-VI.6 (Z35) ◎ | **未(台帳と別の対象を形式化)**(監査前:完全) | `bracket_TK` `bracket_KH` `K_*_deriv` `T_*_deriv`(AlphaVI)、`H_a` `H_b` `H_pa` `H_pb`(AlphaCompleteA) | {T, K} = 1、{K, H} = 0。偏微分もすべて Lean で検算 |
| α-VI.8 (Z37) ◎ | **未(台帳と別の対象を形式化)**(監査前:完全) | `constraint_conserved` `instanton_action` | 拘束の保存、8π² |

### α-VII 電磁気と標準模型

| 項目 | 判定 | Lean の定理 | 内容と残り |
|---|---|---|---|
| α-VII.1 (Z24〜Z26) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `dirac_difference` `dirac_quantization` `curvature_N` `curvature_S` `chern_number` `chern_eq_two_q` `gauss_bonnet_round` `ym_formula` `ym_roots`(AlphaVII_Bundle)、`decomposition` `cross_zero_parallel` `abelian_projection`(AlphaVII_Abelian)、`ricci` `n_dot_dn` `connection_decomp` `thooft_identity`(AlphaVII_Thooft)、`stabilizer_iff` `stabilizer_abelian`(AlphaVII_Abelian) | Z24:2 枚の座標の接続 a_N, a_S、遷移関数 e^{iNφ} の一価性 ⇔ N ∈ ℤ、c₁ = N = 2q、球面の Gauss–Bonnet。Z25:S³ 上の一様な場の YM 方程式 = 8iλ(1−λ)(2λ−1)s_b、解は λ = 0, 1/2, 1。Z26 は以下(原典の n の定義は台帳になく、標準形で定式化)。Z26(2026-10-16 追加、標準形での定式化):単位の方向場 n で F = (F·n)n + n×(F×n)、D n = 0 と Ricci の恒等式 [D_μ,D_ν]n = F_μν×n から F_μν = (n·F_μν)n(Abelian 射影)。原典の n の定義は台帳になく、標準形を採用。微分まで含めた形(2026-10-16 第 2 弾):可換な導分 ∂_μ と定数 g で、[D_μ,D_ν]n = gF_μν×n を定義から証明、n·n = 1 ⇒ n·∂n = 0、D n = 0 ⇒ gA_μ = g(A_μ·n)n − n×∂_μn(第二項は一般のゲージで残る)、't Hooft の恒等式 g(n·F) − n·(Dn×Dn) = g(∂_μ(n·A_ν) − ∂_ν(n·A_μ)) − n·(∂n×∂n)。残り:'t Hooft テンソルのゲージ不変性、Z26 の n の定義。Z26 を閉じた(第 3 弾):n の安定化部分代数は n が張る一次元の可換代数 u(1)、D n = 0 の上で SU(2) は U(1) に還元され F = (n·F)n、接続の分解、't Hooft の恒等式。台帳の Z26 の命題(還元の条件、安定化群、接続と曲率の対応)をすべて含む |
| α-VII.3 (Z28) ⊘ | **部分(形式化が主張より弱い)**(監査前:完全(N1 の定義は台帳による)) | `center_pure_trivial` `no_mixing`(AlphaVII_N1) | 障害 N1 の正確な形:電弱混合には SU(2)_L の生成子すべてと可換な超電荷 Y(U(1)_Y の生成子)が必要。単位四元数の片側の作用の SU(2) 一つでは、Lie 代数 Im ℍ の中でそのような元は 0 だけ(i と j に可換な純虚四元数は 0)。SU(2) に U(1) 部分群(最大トーラス)はあるが SU(2) と可換ではないので、Y にはなれない。Y = 0 なら Q = T₃ で sin²θ_W = 1(no_mixing):混合角は生じない |
| α-VII.4 (Z28-d) ◎ | **条件つき(核心を仮定に置く)**(監査前:完全(外部定理を仮定:S⁹ の Killing スピノルと球面調和関数の関係式、楕円体族と共形族の二次係数の一致)) | `beta23` `beta23_m1` `beta23_m2` `z28d_coefficient`(AlphaIntegrals)、`rs_coefficients` `rs_single_level` `z28d_from_rs` `z28d_values`(AlphaVII_Perturb)、`rs_first` `rs_second`(AlphaVII_RSGeneral)、`resolvent_formula` `z28d_first` `z28d_second` `vol_root_deriv` `vol_coefficient` `z28d_normalized` `z28d_values`(AlphaVII_Z28d) | 二次の摂動公式(Rayleigh–Schrödinger、単純固有値と励起準位一つ)を内積空間で証明し、λ₂ = ⟨W⟩ − ‖u‖²/L の形を導いた。L = 20 と ‖u‖² ∝ Var X = 1/25 の構造はこれで説明される。残りは係数 ‖u‖² = (n²(n−1)/4)A、⟨W⟩ = −(n/4)A の出所(元の作用素 H(ε))。一般の多準位(2026-10-16 追加):H₀ の固有基底で e₁ = V₀₀、(ψ₁)_m = V_m0/(E₀−E_m)、e₂ = W₀₀ + Σ_{m≠0} V_0m V_m0/(E₀−E_m) を任意の体の上で証明。残り:Z28-d の H(ε) そのもの。エルミートな V で e₂ = W₀₀ + Σ|V_m0|²/(E₀−E_m)(rs_second_hermitian)。台帳の H(ε) を特定して閉じた(第 3 弾):S⁹ の共形変形 e^{2tf}g₀(f = |y_H|² − 2/5)の Dirac 作用素 D₀φ = λe^{tf}φ。D(fψ) = (n/2)fψ + df·ψ、D(df·ψ) = L fψ − ((n−2)/2)df·ψ を入力に、(D−a)⁻¹(fψ) = ((n−1)/L)fψ + (1/L)df·ψ、λ₁ = 0、λ₂ = −(n²(n−1)/(4L))A − (n/4)A(縮退した固有空間の任意性を含めて)、体積の正規化 Vol^{1/9} の係数 (9/2)A、合わせて n(n−1)/4·(1−n/L)A = 99/250。ρ = 1 は楕円体族に沿った局所最小で、大域的な最小という主張は撤回済み |
| α-VII.6 (Z28-f) ⊘ | **完全(外部定理を仮定)**(監査前:外部定理の引用) | — | 奇数次元の指数は 0(Atiyah–Singer)。2026-10-17:Atiyah–Singer を使わずに証明した(AlphaVII_Lichnerowicz):対称な作用素では余核 = 核なので指数は 0(index_zero)。Lichnerowicz の公式の代数の核心を一般の次元 n で証明(clifford_three:Σ_bcd R_abcd γ_bγ_cγ_d = 2Σ_c Ric_ac γ_c、clifford_four:Σ R_abcd γ_aγ_bγ_cγ_d = −2(ΣRic_aa))、正のスカラー曲率なら零モードなし(no_zero_mode)、丸い S⁹ で scal = 72(s9_scalar)。残る外部:スピノルの曲率の公式と閉多様体上の部分積分(D の対称性) |
| α-VII.7 (Z28-f) ◎既存 | **完全**(監査前:完全) | `monopole_zero_modes` `monopole_gap`(AlphaVII)、`zero_mode` `zero_mode_other` `count_integer_charge` `admissible_half` `count_half_charge` `other_chirality_empty` `exponent_condition`(AlphaCompleteD)、`tan_half_bounds` `sin_bounds` `u_sq_bounds` `integrable_iff_of_bounds` `zero_side` `pi_side` `zero_mode_L2`(ZeroModeL2) | ゼロモードを厳密解 tan(θ/2)^m sin(θ)^q として構成し、許される m が 2\|q\| 個、カイラリティは sign(q)。L² ⇔ \|m\| < q + 1/2 もべきとの比較で証明した |
| α-VII.8 (Z28-f) ◎ | **条件つき(核心を仮定に置く)**(監査前:完全(外部定理を仮定:S⁹ の最低 Dirac 固有空間が 16 次元のスピノル表現であること、SO(10) 不変な Yukawa の縮約の存在)) | `M_parity` `U_parity` `U_det` `inversion_swaps` `left_right_commute` `charges_leptons` `charges_quarks` `hypercharges` `weinberg_full` `weinberg_leptons` `anomaly_*` `witten_even`(AlphaVII_N1)、`bl_commute_color` `bl_direction` `bl_normalization` `bl_charges` `bl_anomaly_linear` `bl_anomaly_cubic` `bl_anomaly_needs_nuR`(AlphaVII_BL)、`ellipsoid_breaks` `spinor16_count` `spinor16_charges` `higgs_bidoublet` `yukawa_weight`(AlphaVII_SO10)、`jr_unique` `kink_plus` `kink_minus` `norm_plus` `norm_plus_lt` `norm_minus` `shell_unit` `shell_sign` `shell_equator` `shell_celestial` `helicity_chern` `chiral_protected` `conjugate_branch`(AlphaVII_Chirality) | N1-break:U(p) ∈ SU(2)、U(−p) = U(p)⁻¹、反転は左右の作用を交換、左右の乗法は可換で SU(2)_L × SU(2)_R。Q = T₃L + T₃R + (B−L)/2 で一世代の電荷が標準模型と一致、sin²θ_W = 3/8(レプトンだけなら 1/4)、anomaly 相殺。B−L の値は入力(Spin(10) の 16 からの導出は数値のみ)、Higgs と Yukawa の作用は未。B−L の導出(2026-10-16 追加):SU(4)_C ⊃ SU(3)_C で、色の入れ替えと可換な跡ゼロの対角生成子は a·diag(1,1,1,−3) に限られ、ν_L が中性という一つの入力でレプトン −1、クォーク 1/3、電荷 0, −1, 2/3, −1/3。U(1)_{B−L} の anomaly は ν_R を含む 16 成分で相殺し、ν_R なしでは相殺しない。残り:四元数の幾何からこの埋め込みを導く写像、Higgs と Yukawa。ν_R なしでは一世代あたり Σ(B−L) = Σ(B−L)³ = −1、三世代で −3(bl_anomaly_without_nuR、bl_anomaly_three_generations)。幾何から群への写像(第 3 弾、台帳 40022e17 の経路):S⁹ の等長群 SO(10) を、Z28-d と同じ楕円体変形 R⁴ ⊕ R⁶ が SO(4) × SO(6) ≅ SU(2)_L × SU(2)_R × SU(4)_C(Pati–Salam)に破る。16 の重みに B−L = −(2/3)(w₀+w₁+w₂)、T₃L = (w₃+w₄)/2、T₃R = (w₃−w₄)/2 を当てると、電荷の表は ν^c を含む一世代と並べ替えを除いて一致。R⁴ 側のベクトル表現は Higgs の二重項(中性成分の Y = ∓1/2)、16·16·10 の重みの釣り合いもある。注意:最低モードが質量ゼロのカイラルな場になることは未証明のまま(丸い S⁹ では Dirac の固有値が正)。カイラリティの調査(2026-10-16):(A)Jackiw–Rebbi の一般論:ゼロモードは一次元、符号の跳び一つにつき規格化できるカイラルなモードがちょうど一つ(f₊ = 1/cosh は ∫ < 2、f₋ = cosh は ∫ ≥ 2R)。局在したモードは壁の座標以外の関数なので、ダンベルの首(壁の座標 s が時空の中)では 2+1 次元の場になり、4 次元の物質場にならない。(B)Q の赤道を壁とすると、壁を横切る座標 cos χ = m/E は質量殻の座標で時空の外。赤道は質量ゼロ、質量殻の無限遠(光的な方向)で、ヘリシティの線束の Chern 数 ±1 がカイラリティを位相的に守る(単独のカイラルな束は可縮な半球に延びない:可縮な空間の上の束が自明なことは外部定理)。S⁹ の固有値 ±9/2 の二つの枝は 16 と 16̄(電荷が反転、Bär の対応は外部定理)で、北半球と南半球に分かれる。残る問題:S⁹ の最低モードは質量 9/2(1/R の単位)が 0 でないので赤道に乗らず、質量ゼロ自体はこの幾何からは導かれない(Witten の no-go と整合) |
| α-VII.9 (Z28-f) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `one_generation`(AlphaVII)、`one_generation_from_twist`(AlphaCompleteD)、`zero_mode_L2`(ZeroModeL2) | ひねりの電荷 q = χ/4 = 1/2 でゼロモード 1 個 |

### α-VIII 弦理論

| 項目 | 判定 | 内容と残り |
|---|---|---|
| α-VIII.2 (Z39, Z40) ⊘ | **部分(形式化が主張より弱い)**(監査前:完全(条件つきの障害として:台帳どおり、切り詰めた有効作用と標準埋め込みを仮定)) | `sqDensity` `z40_alpha_term_vanishes`(AlphaVIII_Embedding)、原命題には Bergshoeff–de Roo の結果と有効作用の明示式が必要。代数的な部分(2026-10-16):`curvature_embed` `trace_embed` `pontryagin_match` `gs_rhs_vanishes`(AlphaVIII_Embedding)。行列値の接続で、標準埋め込み ι(X) = X ⊕ 0 について F(ιΩ) = ι(F(Ω))、tr(ιX ιY) = tr(XY)、したがって Green–Schwarz の Bianchi 恒等式の右辺 Tr F∧F − tr R∧R の各成分が 0。これは Bianchi の相殺だけで、場の方程式や SUSY 条件、Z39–Z40 の「障害」の主張(元の作用が必要)ではない。台帳の Z40 の障害を閉じた(第 3 弾):切り詰めた作用の α′ 項 −(α′/4)(Tr F² − tr R²) は A = ι(Ω) の上で恒等的に 0 で、U21′ に必要な Yang–Mills の源が残らない。台帳の注意どおり、これはこの切り詰め・この埋め込みでの障害で、非標準埋め込みや H 場・ディラトンを含む縮約は別の経路(H 場とディラトンの運動方程式は、障害の主張には不要なので計算していない) |
| α-VIII.3 (Z41) ◎ | **部分(形式化が主張より弱い)**(監査前:完全) | `entropy_from_action` `z41_deriv_v1` `z41_deriv_v2` `z41_critical` `z41_entropy` `z41_neck`(AlphaVIII_Z41)、`exp_derivs` `char_root` `real_roots_iff` `bf_ads2` `oscillating_solution`(AlphaVIII_BF)、`f_deriv_e` `f_deriv_v1` `f_deriv_v2` `attractor_unique` `attractor_entropy`(AlphaVIII_Attractor): 線形のゆらぎ φ'' − dφ' − μφ = 0 の指数解 ⇔ α² − dα − μ = 0、実根 ⇔ μ ≥ −d²/4(BF 境界、AdS₂ で −1/4)、境界の下の振動解。非線形アトラクターの存在・安定性はアトラクター関数が手元になく未。比較模型(2026-10-16 追加):Einstein–Maxwell の AdS₂×S² に Sen のエントロピー関数を当てはめ、臨界点は v₁ = v₂ = q²+p²、e = q の一つだけ(アトラクター機構)、値 π(q²+p²) = 面積/4。Z41 の作用での計算は元の作用が必要。台帳の式で閉じた(第 3 弾):作用 R/(16πG) − F²/(4g²) に AdS₂ × S² と磁荷 p を入れると、Sen のエントロピー関数は台帳の ℰ = (π/G)(v₂−v₁) + (4π²p²/g²)(v₁/v₂) に一致し、臨界点は v₁ = v₂ = p²ℓ*²(ℓ*² = 4πG/g²)だけ、臨界値 4π²p²/g² = 面積/(4G)、p = 1 で近地平線の半径が首の半径 ℓ*(Z27)と一致 |
| α-VIII.5 (Z38, Z42) ⊘ | **完全(外部定理を仮定)**(監査前:完全(外部定理を仮定:A-VIII.5a、A-VIII.5b)) | `ell_sq_eq` `ell_witten` `ell_ledger` `kaplunovsky` `wzw_level` `wzw_obstruction` `wzw_obstruction_values`(AlphaVIII_Z38)、`z42_adopted` `one_quarter_not_integer`(AlphaVIII_BF)。比較用:`z42_conditional` `one_eighth_not_integer` | **採用する規約:ℓ*² = α′/4。** 理論の ℓ*² = 4πG/g² と弦の G_N = c·α_GUT·α′ から ℓ*² = c·α′(ell_sq_eq)。Witten の木の近似の縮約(c = 1/4)で ℓ*² = α′/4(ell_witten)。このとき α′/ℓ*² = 4、α′R(S³) = 24、α′R(S⁴) = 48(z42_adopted)。Z42:S³ の SU(2)_k WZW の R² = kα′ と R = ℓ* から k = c = 1/4 で、正の整数にならない(wzw_level、wzw_obstruction、one_quarter_not_integer)。旧台帳の α′/8 は c = 1/8 の規約(g² = 4κ²/α′)に当たり、比較のため残す(ell_ledger、kaplunovsky、z42_conditional)。α′R > 1 なので、低次の α′ 展開の制御は別の課題。2026-10-17:幾何の部分を証明した(AlphaVIII_WZW):S³ = SU(2) の構造定数は四元数の交換子 [i, j] = 2k(quat_bracket)、平行化の捩れ H = (2/R)ε で 1 ループの条件 Ric = ¼H² が恒等式として成り立つ(eps_contract、s3_ricci、parallelizing_torsion)、Vol(S³(R)) = 2π²R³(s3_volume)、流束 4π²R²(flux)、∫H/(4π²α′) = k ⇔ R² = kα′(level)。残る外部:H の規格化(世界面の作用、Witten 1984)と G_N = c α_GUT α′(Witten 1996) |
| α-VIII.7 (Z44) ⊘ | **完全(外部定理を仮定)**(監査前:完全(外部定理を仮定:Killing スピノルの双線形は Killing ベクトル、球対称の等長変換は面積半径を保つ)) | `killing_time_pos` `causal_time_ne_zero` `throat_static` `no_killing_spinor`(AlphaVIII_Z44)、`real_roots_iff` `oscillating_solution`(AlphaVIII_BF)、`susy_posSemidef` `energy_split` `bps_iff` `susy_energy_nonneg` `no_bf_violating_mode`(AlphaVIII_BPS): BF 違反の線形モードの存在まで。BPS の no-go 本体は作用・SUSY 変換則が手元になく未。no-go の代数的な核心(2026-10-16 追加):H = Q†Q + QQ† は半正定値、⟨ψ,Hψ⟩ = ‖Qψ‖² + ‖Q†ψ‖²、BPS ⇔ Qψ = Q†ψ = 0、負のエネルギーの固有状態(BF 違反のモード)はない。残り:Z44 の作用と変換則から揺らぎの演算子がこの形になること。合意した再構成で閉じた(第 3 弾):Killing ベクトル K^μ = ε̄γ^με の時間成分は ε†ε > 0、喉では ∂_s r = 0 なので K(r) = 0 から ∂_t r = 0、半径が一定になり Z9 の有限時間の崩壊と矛盾。よって崩壊するダンベルは BPS でない。B(2026-10-16):仮定 hcollapse は Z9 から供給した(z44_from_z9、AlphaIV_Z9)。残る仮定は外部定理(Killing スピノルの双線形は Killing ベクトル、等長変換は面積半径を保つ)の hiso だけ。超対称なら揺らぎに負のモードがないこと(AlphaVIII_BPS)と合わせて BPS の no-go 2026-10-17:仮定 hiso を分けた(AlphaVIII_Z44b):喉で ∂_s r = 0 は鏡映対称性から証明(throat_ds_zero)、崩壊は Z9 から(z44_full)。残る外部の事実は「Killing スピノルの双線形は Killing ベクトルで、球対称な等長変換は r を保つ」一つ(hKill) |

## ファイル

- `CFT/Basic.lean`:共通の import
- `CFT/AlphaI.lean` 〜 `CFT/AlphaVII.lean`、`AlphaIII_P1`、`AlphaV_FW`、`AlphaIntegrals`、`AlphaI_AW`:各群の本体
- `CFT/AlphaCompleteA.lean` 〜 `AlphaCompleteD.lean`、`AlphaCompleteC2.lean`:前回の完全化
- `CFT/Cartan/`:Cartan の動標構の代数的な形式化(Frame:公理と曲率、C2:Codazzi の解・構造式・Bochner 恒等式、Aligned:整列型の非存在、BochnerSign:各点での符号)
- `CFT/AlphaI_C.lean`(巡回 Fueter 行列)、`AlphaIII_Junction.lean`(接合)、`AlphaVII_N1.lean`(N1 と左右の作用)、`AlphaVII_Bundle.lean`(単極子の束・一様な YM 場)、`AlphaVII_Perturb.lean`(二次の摂動公式)、`AlphaVIII_BF.lean`(BF 境界・条件つきの算術)
- `CFT/GaugeCovariance.lean`、`ZeroModeL2.lean`、`AlphaII_Diagonal.lean`、`AlphaII_Z5.lean`、`AlphaV_A4.lean`:今回の追加(ゲージ共変性、L² 判定、対角型の非存在、Z5 の完全な証明、a₄ の導出)
- `Audit.lean`、`audit.txt`:公理の監査
- α-II.5 の Lean ファイル(CFT/Cartan/SS*.lean、SecondStage.lean)は aux/cartan/gen_ss.py、gen_split.py、run_split.py、assemble_split.py、bj_cert.py が生成し、fastsyntax.py が書式を整える。大きな多項式の恒等式は、Λ = (λ, α, β, γ, η) 以外の原子の単項式 κ ごとに係数を比べる形に分けた(係数は def、κ ごとの恒等式は補助定理 `cf…_k…`)。意味は一つの大きな ring と同じで、メモリ 8GB に収めるための分割である。ビルドは全体で 1 時間ほどかかる(SSJet が約 2 分半、SSCoefR3/R6 が各 8 分、SSK が約 9 分)。
- `aux/`:Lean に渡す係数を求めた sympy スクリプト(`aux/diag/`:対角型の証明書、`aux/z5/`:Z5 の証明書、`aux/cartan/`:動標構の計算と Lean の生成、α-II.5 の厳密な点ごとの確認、`gen_audit.py`:Audit.lean の生成)

## 検証の手順

```
lake build                 # 全ファイルのコンパイル(BPS の証明は 2 コアで 20 分ほどかかる)
lake env lean Audit.lean   # 各定理が依存する公理の一覧
```

lakefile.lean は `require mathlib from "../mathlib4"`(ローカルの Mathlib)になっている。
自分の環境では `require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"` に書き換え、`lake exe cache get` を使うと速い。
