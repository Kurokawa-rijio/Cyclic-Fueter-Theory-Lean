# 命題群 α 段階 1〜5 の再監査(2026-10-21、最新ソースに対して)

旧 `review/audit_table.md`(2026-10-16)は古いソースへの監査なので、この表で置き換える。評価軸は外部の評価基準(2026-10-21)の A〜F:

- A 命題の一致
- B 仮定の妥当性
- C 数学的導出
- D 依存関係(最終定理が補題を実際に使うか。`DepCheck.lean` が推移的な依存を機械的に確かめる)
- E 適用範囲
- F 再現性(ゼロからの全体ビルドのログ `build_all.log`、公理の監査 `audit.txt`)

判定の記号:

- **完全**:台帳と一致し、仮定が明示され、証明が通り、外部定理の適用条件も一致
- **完全・条件付き**:明示した正則性や外部の古典定理のもとで完全
- **部分**:核心の含意か最終定理への接続が欠ける

## 段階 1:作用原理(α-II.1)

| 項目 | Lean の定理 | 入力・外部 | A | B | C | D | E | 判定 |
|---|---|---|---|---|---|---|---|---|
| 1-A ゲージ群 | `gauge_group`、`unit_left_mul`、`su_two_bracket` | なし | ✓ | ✓ | ✓ | ✓ | 右 ℍ 線形でノルムを保つ ℝ 線形写像の類 | 完全 |
| 1-B Maxwell 項 | `maxwell_symbol`、`maxwell_is_F2`、`maxwell_mass` | Lorentz 不変なテンソルが η と k で書けること(標準) | ✓ | ✓ | ✓ | ✓ | Lorentz 不変な二階の二次形式の類 | 完全・条件付き |
| 1-C 非可換項 | `ym_covariance`、`ym_invariance`、`ym_coupling_forced`(c = 1) | Utiyama 1956(非可換な延長の一意性) | ✓ | ✓ | ✓ | ✓ | F = dA + A∧A の係数は Jacobi から強制 | 完全・条件付き |
| 1-D 重力項 | `fierz_pauli`(線形化の一意性) | Lovelock 1971(4 次元、局所、微分同相不変、二階の EL 方程式) | ✓ | ✓ | ✓(線形) | ✓ | 一意性は Lovelock の類に限る | 完全・条件付き |
| 1-E 境界項 | `ghy_frw`、`ghy_spherical` | なし | ✓ | ✓ | ✓ | ✓ | 球対称の一般の計量 | 完全 |
| 1-F 定数 | `lambda_zero`、`ell_cap`、`ell_neck`、`glue_EYM` | なし | ✓ | ✓ | ✓ | ✓ | Λ = 0 と ℓ² = 4πG/g² は作用だけでなく相の場の方程式と貼り合わせから出る(区別を明記) | 完全 |

## 段階 2:作用から場の方程式へ(α-IV.3、IX.0〜IX.9)

| 項目 | Lean の定理 | 入力・外部 | 判定と注意 |
|---|---|---|---|
| 2-A 第一変分 | `first_variation`(AlphaS2_Action)。δL = Σ δφ E_φ + 全微分を恒等式で示す。E_φ は生成した定義だが、恒等式がそれを Euler–Lagrange の式だと証明する(手入力の係数を一致させただけではない) | なし | 完全 |
| 2-B α の方程式 | `el_iff_abstract`、`el_iff_alpha`、`match_*` | なし | 完全 |
| 2-C 拘束と発展 | E_N = AR²H、E_β = −2A²R²M(拘束)、E_W、E_A、E_R(発展) | なし | 完全 |
| 2-D Maxwell | `gauss`、`ampere`(変分から)、`bianchi_div`、`faraday`(恒等式から、別に) | なし | 完全 |
| 2-E YM | `ym_first_variation`、`u1_projection` | なし | 完全 |
| 2-F 保存則 | `stress_divergence`、`charge_conservation`、`dust_lorentz` | なし | 完全 |
| 2-G 解析力学 | `particle_el`、`hamilton`、`mass_shell` | 世界線に沿う連鎖律(入力) | 完全・条件付き |
| 縮約の正当性 | **`full_4d_iff_alpha`、`palais_free`(AlphaS2_4DMatch、2026-10-21 第 10 弾)**:同期ゲージ N = 1 の球対称 ansatz で、4 次元の Einstein テンソル(Levi-Civita の公式から)と YM 方程式(F = dA + A∧A から)の全成分を直接計算し、E₀₀ = H/2、E₀₁ = E₁₀ = −AM、E₁₁ = A²(2T + H/2)、E₂₂ = R²(X + T + H/2)、E₃₃ = s²E₂₂、他の 10 成分 0(`sync_ij`)、YM の (1,θ) = −s eP、s·(2,φ) = (1,θ)、他の 10 成分 0(`ym_sync_02`、`ym_sync_13`、`ymA_an`)。したがって 4 次元の EYM 方程式の全成分(16 + 12)⇔ α の五つの方程式 ⇔ 縮約した作用の Euler–Lagrange 方程式 | なし(Palais の対称臨界性は使わない。使っても誤りではないが、重力理論では成立条件の確認が必要なので直接照合にした) | 完全。注意:照合は同期ゲージ(N = 1、β = 0)で行った。ラプスとシフトの変分(拘束)は縮約した作用の側で E_N、E_β として残る(2-C) |

## 段階 3:解の分類とダンベルの幾何

| 項目 | Lean の最終定理 | 入力・外部 | 判定と注意 |
|---|---|---|---|
| II.2、II.3 三つの相 | `three_phases`、`satI_*`、`not_satI_*`、球対称では `phase_neck`、`phase_form`、`no_hyperbolic` | CIS 1999 Theorem A、B | 完全・条件付き。分類は商空間と位相の違いを除いて(文字どおり S³、S²×ℝ には単連結性が要る) |
| II.4 厳密な窓 | `c2_window`(`kappa_nonpos` と `strict_window` を合成)、`disc_identity`、`C_strict` | なし | 完全。κ ≤ 0 だけから固有値の相異と (I) で 0 < Rℓ² < 2 |
| II.5 階数 | `rank12_star`、`Bj_frame`、`K0`〜`K3` | 階数の下半連続性(標準) | 完全・条件付き。x* を含む B = 0 の既約成分の稠密な開集合の上で |
| II.6 対角型・整列型 | `diagonal_class_degenerate`、`aligned_impossible` | なし | 完全(多項式の証明書。数値検算に頼らない) |
| II.9 静的分類 | `static_classification`、`static_W_trichotomy` | なし | 完全(W ≡ 0、W ≡ ±1 の分岐を含む) |
| III.3 Penrose 型 | `penrose_from_constraints`、`ms_from_constraints` | 拘束方程式(場の方程式)、未捕捉、優勢エネルギー条件 | 完全 |
| III.4 形と質量 | `glue_C1`、`glue_EYM`、`no_flat_from_constraints` | なし | 完全 |
| III.5 Schwarzschild | `schw_*` | なし | 完全 |
| III.6 平坦極限 | `flat_r`、`flat_mass`、`flat_mass_rate_limit`、`cap_mass_exact` | なし | 完全 |
| III.7 最小質量 | **`min_mass_from_constraints`(AlphaS3_Mass)**:`penrose_from_constraints` と `min_mass` を合成。2026-10-21 第 10 弾で首半径の入力を `r(s₀)=ℓ` と首の EYM ハミルトン拘束に置換し、`ell_neck` から半径²を導出 | 拘束、未捕捉、DEC、周縁的捕捉面、首の EYM ハミルトン拘束 | 条件付きで完全。首の喉の EYM 拘束と `r(s₀)=ℓ` は明示した入力。旧 `min_mass` は数の恒等式だけで、評価基準 3-G に反していた |
| V.4 Gauss 写像 | `embed_exists`、`embed_metric`、`normal_unit`、`normal_orth`、`normal_unique`、`gauss_cos`、`gauss_sin_mass`、`gauss_equator`。2026-10-21 第 10 弾で `profile_immersion_data`・`profileMap_injective` を追加 | 時間対称・球対称、\|r′\| ≤ 1。大域単射には `StrictMono (zProfile r1)` と `r(s) ≠ 0` も必要 | 幾何データ・接ベクトル・誘導計量を `profile_immersion_data` で一つの定理に接続。`profileMap_injective` は単調性等を追加仮定として単射性を示す。一般仮定だけで大域的な位相的埋め込みが得られるとは主張しない |

## 段階 4:接合

最終定理は AlphaS4_Final にある。分布としての方程式(弱解の定義そのもの)と、各側の場の方程式(微分体 S の恒等式)だけを入力にとる。横断線の実現 `RealLine`(S の元 → 線の上の関数、導分 → 微分)で両者をつなぐ。

| 項目 | 最終定理 | 呼んでいる補題(DepCheck で確認) | 入力 | 判定 |
|---|---|---|---|---|
| III.1 重力 | `timelike_final` | `delta_coeff_weighted`、`shell_coeff`、`tt_side`、`ang_side`(`tube_tt_form`、`tube_ang_form` ← `einD_*` ← `ricD_*`)、`tube_israel`、`nn_eq_eval`(`gauss_tube`、`tnn_tube`)、`timelike_no_go`、`fymD` | 両側の EYM 方程式、接合点での計量と W の連続性、時間対称、帽子 w = −1/ℓ、首 w = 0、tt・角度成分の分布としての方程式 | 完全・条件付き(両側が面まで C²) |
| III.1 ゲージ場 | `color_final` | `shell_coeff`、`ym_side`(`ymD_split` ← `ymD_02`)、`fymD` | 両側の YM 方程式(F = dA + A∧A)、分布としての YM 方程式 | 完全・条件付き |
| III.9 | `slice_final` | `shell_coeff`、`tt_side`(`tube_tt_form`) | ハミルトン拘束の分布としての式、A = 1 | 完全・条件付き。σ = −[R_x]/(4πG R₀) |
| III.2 | `null_final` | `shell_coeff`、`uu_side`(`uu_form`)、`mixed_eq`、`trace_deriv_eq`、`null_front_from_mixed`(`jump_transport`)、`fymN` | 両側の EYM 方程式(二重ヌル)、波面に沿う実現と各 v での横断線の実現、波面の上で r, Ω, W, ℓ が連続、角で [r_u] = 0(`initial_jump`) | 完全・条件付き。μ ≡ 0、YM の表面流 [−sW_v] ≡ 0 |

補助定理 `timelike_dumbbell`、`null_front_weak`、`dumbbell_no_shellfree_timelike`(AlphaS4_Distrib、AlphaS4_Junction)は δ の係数の関係式を入力にとる版で、DepCheck では `delta_coeff_weighted` を使わない。最終定理ではない。`[r_uu]` の公式は一般に 2[σ_u r_u] の項を含み、`ruu_jump`、`null_ruu_jump` は σ_u が共通という仮定つき(README に明記)。

## 段階 5:時間発展

| 項目 | 最終定理 | 入力・外部 | 判定 |
|---|---|---|---|
| IV.1 適切性 | `constraint_prop_from_eqs`(Einstein と YM の方程式 → `goursat_r`、`goursat_Om`、`goursat_W` → `constraint_prop_u`、`constraint_prop_v`)、`constraint_transport`、外側の厳密解 `cap_*`、`neck_*` | 2 変数の半線形双曲系の Goursat 問題の局所的な存在と一意性(古典定理。F は r > 0、Ω > 0 でなめらか、データは外側の厳密解のトレース、角で一致)、なめらかなデータの依存領域での一意性(Choquet-Bruhat) | 完全・条件付き。主張は局所的な適切性で、楔全体への長時間の延長は主張しない |
| IV.2 波面 | **`wave_jump_final`(新規、AlphaS5_Final)**:YM 方程式(F = dA + A∧A)→ `goursat_W` → [W_u] は波面に沿って一定 | 両側が波面まで C²、波面の上で Ω, W, r が連続 | 完全・条件付き |
| IV.4 エネルギー | `energy_deriv`、`energy_nondecreasing` | 中心の ODE(IV.3 の `center_ode`) | 完全 |
| IV.5 崩壊 | **`cap_crunch_final`(新規)**:帽子の EYM 方程式 → `cap_00`、`cap_22` → a″ = −a → 一意性 a = ℓ cos η → `kret_cap`(K = 24ℓ⁴/a⁸)→ `kret_blowup`(K → ∞)。補助:`front_inward`(波面 χ = π/2 − η)、`front_hits_center`、`center_limit`、`cap_proper_time`、`t_sing_lt`。比較定理の正しい形 `z9_maximal` | 中心の世界線に沿う実現(C²)、時間対称な初期値 | 完全・条件付き。首(W = 0)は崩壊しない(AdS₂ の t = πℓ/2 は依存領域の端) |
| IV.7 Gudermann | `front_gd_inv`、`gd_front_inv`、`mercator`、`neck_mercator`、`null_curve_unique` | なし | 完全(主値の帯を明記、座標の対応と力学の同値を区別) |
| IV.8 時計 | `fronts_meet_iff`(等式)、`arrival_time`、`cap_unique`、`cap_proper_time` | なし | 完全 |
| IV.9 平坦極限 | `flat_clock`、`flat_front`、`flat_metric` | なし | 完全(点ごとの極限。一様収束は主張しない。G を固定すれば g → 0 で、固定した結合定数の極限ではない) |

## F:再現性

- `build_all.log`:2026-10-21 にコピーした作業ディレクトリで .lake/build を空にして全体を作り直した記録。2 コアと 8 GB では大きな SS* ファイルが並列で OOM(code 137)になるので、それらを順に作り直し、最後に全体をもう一度ビルドした
- 結果:ビルド成功(最後の全体ビルド 18 分、エラー 0)。定理 990 個(977 個が標準の 3 公理だけ、6 個が propext と Quot.sound、4 個が propext、3 個は公理なし)、sorryAx 0
- `audit.txt`:すべての定理の `#print axioms`(sorryAx なし)
- `DepCheck.lean`:最終定理の推移的な依存の機械的な確認。結果 `review/depcheck.txt`:最終定理が呼ぶべき補題はすべて true(57 件)、false は入力版の補助定理 3 件と、Goursat の形を仮定にとる `constraint_prop_u`(合成は `constraint_prop_from_eqs`)だけ

### 2026-10-21 第 10 弾(外部パッチ j の検証と段階 2 の 4 次元照合)

- 外部パッチ j(`null_final` の両側の色流束と共通トレース `cs`、`min_mass_from_constraints` の `ell_neck` からの首の半径の導出、`profile_immersion_data`・`profileMap_injective`、DepCheck の証明本体と型の依存の分離)を Lean でコンパイルし、内容が正しいことを確認した。パッチの「未コンパイル」の注記はこの版で解消。
- 段階 2 の「縮約の正当性」を AlphaS2_4DMatch で閉じた(上の表)。外部の検算(4 成分 + YM 1 成分、SymPy)と一致し、残りの全成分も Lean で検証した。
- 全体ビルド成功(build_k.log、エラー 0、sorry 0)。定理 1074 個(1061 個が標準の 3 公理だけ、6 個が propext と Quot.sound、4 個が propext、3 個は公理なし)、sorryAx 0、独自の axiom 0(audit.txt)。DepCheck(review/depcheck.txt)で `full_4d_iff_alpha` が `sync_*`・`ym_sync_*`・`fym_eq` を、`palais_free` が `el_iff_alpha` を、`min_mass_from_constraints` が `ell_neck` を証明の中で使うことを確認。false の 4 件(timelike_dumbbell、null_front_weak、constraint_prop_u)は δ の係数や Goursat の形を入力にとる補助版で、第 9 弾と同じ。
- `wave_jump_final` の使っていない仮定 v0 ≤ v1 を外した(仮定が減るだけで結論は同じ)。

