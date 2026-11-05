# 命題群 α — 現行判定(運動学・作用・力学の台帳、103 項目)

**基準日:2026-11-05**(alpha-phase1。公開版 v0.3.0 は 88 項目、2026-11-02 時点)

この一覧は研究の進捗管理用であり、第三者による査読済み判定ではない。Lean で形式化された定理の仮定・結論と、物理的な主張全体の強さは区別する。

## 読み方

理論を表す言葉:**ダンベルは運動学で、作用を入れると力学が生まれる。** 各項目に次の三つを書く。

- **運動学**:ダンベルのどの部品(量子半球・帽子、双曲的な首、接合・波面、内部空間)の、どの量(計量、接続、磁荷、a(η) など)を使うか
- **作用**:入れる作用(EYM + GHY、JT、Dirac、弦の有効作用など)。幾何そのものの項目は「—」
- **力学**:作用から導いた式・結論

**区分**

- **運動学**:幾何そのもの(作用なし)
- **ダンベル**:ダンベルの量に作用を入れて力学を出したもの
- **一般**:一般の物理(平坦時空・一般の RN・有限系など)を Lean で確かめたもの。正しいが、ダンベルに固有の結果ではない

**判定**

- **完**:Lean の定理が命題どおりのことを示す
- **完(外)**:明示した確立済みの外部定理を、その条件を確かめたうえで使う範囲で完全
- **部**:形式化が主張より弱い
- **条**:核心の仮定または外部入力が残る(新しい原理・計算が要る)
- **未**:未形式化
- **未着手**:まだ計算していない

Lean の索引 `CFT/AlphaIndex.lean` は、各項目の代表の定理に別名を置き、運動学・作用・力学を docstring に書いたもの(主張は元の定理と同じ)。

## 集計

**完 94(完(外)を含む)/ 部 5 / 条 0 / 未 0 / 未着手 4 = 103**

| 区分 | 完 | 部 | 条 | 未着手 | 計 |
|---|---:|---:|---:|---:|---:|
| 運動学 | 11 | 0 | 0 | 0 | 11 |
| ダンベル | 54 | 4 | 0 | 4 | 62 |
| 一般 | 29 | 0 | 0 | 0 | 29 |
| —(X.6 非空性) | 0 | 1 | 0 | 0 | 1 |

残り:部 5 は RealLine の橋渡し(III.1、III.2、III.9、IV.2)と、その橋渡しを含む X.6 の非空性(最後の課題、質量ギャップの前)。未着手 4 は X.7(数値)と、首を支える作用の拡張の XI.5〜XI.7。条件つきは 0。

## 2026-11-05 の変更(その 2):首を支える作用の拡張(XI.4〜XI.7 を追加、99 → 103)

命題の文言を範囲で絞った IX.13(ディラトン)、IX.14 と XI.1(長い首は Schwarzian が使えるが不安定)、IX.33(宇宙定数がない)は、ダンベルの形ではなく、首を磁場だけで支えている作用の弱さから来る。そこで作用を足す項目を加えた。
- XI.4(完(外)):随伴 Higgs を足す(AlphaXI_HiggsNeck)。首(W = 0、H = v)は厳密な解のままで、首の半径 ℓ² = 4πG/g² も変わらない。W のモードの質量は m²ℓ² = −1 + m_W²ℓ²(m_W = gv、v = 0 で IX.15 に戻る)。BF 限界から安定 ⇔ m_W²ℓ² ≥ 3/4 ⇔ v ≥ √(3/16π) M_Pl ≈ 0.244 M_Pl。このときは Hardy 型の不等式 ∫(f′² − ¼f²/sin²u) = ∫ sin u(h′² + ¼h²) ≥ 0(f = √(sin u) h)から、どの長さの首でも成長するモードはない(min–max は外部)。XI.1 の不安定性と IX.14 の「長い首」の衝突が解ける。外部:'t Hooft–Polyakov の ansatz の縮約の無矛盾性、min–max。Lee–Nair–Weinberg(1992)の「磁荷の RN は地平線が小さいと不安定」と定性的に一致。
- XI.5(未着手):dyon の首(VIII.3 で p, q > 0 ならアトラクターがある)。IX.13 のディラトンの問題の解決の候補。
- XI.6(未着手):V.7-N の実効的な負の宇宙定数で Hawking–Page 型の比較。IX.33 の候補。
- XI.7(未着手):Higgs を入れると帽子の解 W = cos χ が変わる(勾配のエネルギー)。帽子と接合を計算し直す。

## 2026-11-05 の変更(独立監査とその修正)

独立した監査(作業を見ていない別の担当、懐疑的な理論物理学者の立場)で、2026-11-04 に完とした 40 項目を点検した。Lean の代数は計算し直した範囲ですべて正しかったが、判定は 完 36 / 部 4 から 完 25 / 部 12 / 条 3 に下がった(上げた項目はない)。指摘を一つずつ直し、次の項目を閉じた(モジュール AlphaFix_Thermo、AlphaFix_Neck、AlphaFix_Unify、AlphaFix_Gauge、AlphaFix_FW、AlphaFix_Z28)。

- **物理の誤りの修正**
  - IX.24:首は磁荷なのに電荷の作用 I = β(M − ΦQ)/2 を仮定していた。磁荷の場の Maxwell の項を実際に積分し(∫F²r²dr、F² = 2Q²/r⁴)、I = β(M + ΦQ)/2 = β(M − TS)(磁荷を固定した正準集団、Hawking–Ross 1995)。S = A/4 は同じ。
  - IX.13:S₀ = 4π²/g² はディラトンのない EYM での値と明記(弦理論の作用では VIII.3 のとおりディラトンが逃げる)。
- **前提を確かめた・定めた項目**
  - VIII.2:埋め込む接続を Euclid の断面のスピン接続 Ω ∈ so(4) に定めた(ι は反対称性を保ち so(4 + m) に入る、コンパクト)。H の Chern–Simons から来る H·F の項を含めても埋め込みと可換。
  - IX.14:首の座標 −dt² + cos²(t/ℓ)dz² で JT の dilaton の方程式を解いた。静的な解は 0 だけ。対称な解 B cos(t/ℓ)cosh(z/ℓ) は首の中心を分岐面とする JT の永遠のブラックホールの形で、t = πℓ/2(帽子の崩壊と同じ cos)で 0。接合は u_c ≤ πe^{−L/ℓ} で漸近境界に近づく(長い首で Schwarzian の前提が成り立つ)。C = φ_r/(2G)、S₀ = πℓ²/G。
  - V.1:2 回目の FW 変換で 1/m² までの偶の部分が変わらないことを定理にした。[π_k, φ] = −i∂_kφ などの交換子を作用素として示し、Darwin 項とスピン軌道項の形を出した。適用範囲は静的な外場。
- **トートロジー・算術だけの定理の差し替え**
  - X.1:有限自由度の一般の Noether の定理(EL 方程式と対称性 ⇒ Σp_iK_i の保存)。循環座標はその特別な場合。
  - X.5:Witten の ansatz で F_tr の交換子が消えることを計算(F_tr = (∂_ta₁ − ∂_ra₀)T)。
  - IX.34:写像の次数 (1/4π)∫n·(∂_θn × ∂_φn) = 1 を積分で計算。
  - VII.9:S² のスピン接続 −cos θ dφ の曲率を計算し、½ ひねりの電荷 q = 1/2 を積分で出し、L² のゼロモードがちょうど 1 個(m = 0)であることを示した。
- **弱かった項目の強化**
  - IX.27:Jüttner → Maxwell の各点の極限(p² = mq² の尺度)と、優関数の単調性。
  - IX.30:KMS の成分の式 g = e^{−βω}h から揺動散逸の関係を導いた(KMS を実際に使う)。
  - IX.33:Hawking–Page(宇宙定数が要る)をやめ、磁荷の正準集団で同じ温度の二つの枝を比べた。首につながる小さい枝の自由エネルギーが低い(r₁r₂ > 3Q²)。小さい枝は比熱が正。
- **部分から完にした項目**
  - XI.1:Liouville の変換と 1/sin²u ≥ 1/u² の比較を Lean で証明し(外部から外した)、本当の二次形式が負であることを示した。成長率の下限 λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²(min–max は外部)。L/ℓ ≥ 7 なら帽子の崩壊の時間 ℓ のうちに少なくとも 1 回 e 倍。前提:静的な首、接合で Dirichlet 条件、時計は接合でそろえる(解釈)。
  - XI.3:波面の上の球は θ₊ = 0、θ₋ < 0(周辺的に捕捉された球)で、0 < η < π/2 のすべての時刻、つまり崩壊の前にある。首の球は θ± = 0。厳密に捕捉された球は r² − ℓ² の 2 次による(範囲外)。
  - X.4:閉じたダンベルには ADM 質量がない(命題の文言を変更)。帽子の Misner–Sharp 質量 m = (4π/3)ρR³ と第一法則 dm = −p dV、首で m = ℓ/2。
  - X.2:2 次元の WKB の展開の (ik)² の係数がアイコナール方程式で、IV.7 の首の波面がそれをみたす。
  - VII.4(条 → 完(外)):核心の仮定「楕円体族の 2 次の係数 = 共形族の 2 次の係数」を導いた。(1) 1 次では楕円体 = 微分同相 φ_ε(x) = Ax/|Ax| + 共形変形 e^{2εu₁}(u₁ = ⟨x, Bx⟩、差は ε² の次数を多項式の恒等式で示す)、(2) Killing スピノルのエネルギー運動量は計量に比例し、規格化した固有値 λVol^{1/9} の第一変分は丸い S⁹ ですべての方向に 0、(3) 2 次の係数は 1 次の方向だけで決まる。外部:Bourguignon–Gauduchon の第一変分、Kato の摂動展開、スペクトルの微分同相不変性(AlphaFix_Z28)。
  - VII.8-C(未 → 完(外)、否定的な結果):楕円体は凸なのでスカラー曲率が正、Lichnerowicz から内部の Dirac の核は 0。質量ゼロのカイラルなモードは内部の核からは出ない(接合の壁とひねりから来る)。
- **命題の文言を変えた項目**:X.4(ADM → Misner–Sharp)、IX.33(Hawking–Page → 磁荷の正準集団での比較)、IX.13(EYM に限る)、IX.14(長い首に限る)、V.1(静的な外場に限る)、VIII.2(Euclid の断面)、XI.3(周辺的な捕捉面まで)。
- 区分:監査のとおり、ダンベルの量を使わない項目を「一般」として分けた(29 項目)。

## これまでの変更(要約)

- 2026-11-04:α-IX〜XI の段階 1〜5 を計算(完 87 / 部 9 / 条 1 / 未 1 / 未着手 1)。α-XII(巡回 Fueter 構造)を解くべき項目から削除(104 → 99、理由:Fueter の接続 A_F は Berry 接続とゲージ同値で、ゲージ不変な新しい情報を持たない)。V.1(Wigner 回転のホロノミー、FW)、VIII.2・VIII.3・VIII.7 を閉じた。
- 2026-11-02:III.1、III.2、III.9、IV.2 を部分に戻した(RealLine の定式化の欠陥、最後の課題)。VII.8-C、V.7′ を新しい項目として分けた。α-X、α-XI、V.7-N を未着手として追加。
- 2026-10-21 以前:v0.1.0(完 25 / 部 17 / 条 5 / 未 4)、v0.2.0(完 35 / 部 9 / 条 3 / 未 4)。詳細は `review/` と `docs/README_JA_full.md`(古い記述を含む)。

| 版 | 基準日 | 項目数 | 完(完(外)を含む) | 部 | 条 | 未 | 未着手 |
|---|---|---:|---:|---:|---:|---:|---:|
| v0.1.0 | 2026-10-18 | 51 | 25 | 17 | 5 | 4 | — |
| v0.2.0 | 2026-10-21 | 51 | 35 | 9 | 3 | 4 | — |
| v0.3.0 | 2026-11-02 | 88 | 41(I〜VIII)+ IX | 7 | 2 | 3 | — |
| alpha-phase1 | 2026-11-04 | 99 | 87 | 9 | 1 | 1 | 1 |
| alpha-phase1(監査後) | 2026-11-05 | 99 | 93 | 5 | 0 | 0 | 1 |
| alpha-phase1(XI.4〜XI.7 を追加) | 2026-11-05 | 103 | 94 | 5 | 0 | 0 | 4 |

## WGC との関係(各項目で確かめる)

WGC に関わる項目:XI.4(首の安定の条件 m_W ≳ 0.24 g M_Pl は磁気的な WGC の切断 g M_Pl と同じ尺度、解釈)、XI.5(dyon、電気的な WGC)、XI.2(F⁴ 補正で極限の M/Q < 1)、IX.24(磁荷の首は正準集団。極限 T = 0 での F = M = Q)、IX.33(首につながる枝が選ばれる)、IX.23(極限で T = 0)、IX.15・XI.1(首の不安定性と崩壊の時間)、III.7(ℓ = √(4π)ℓ_P/g)、V.7′(走る結合)、IX.13(S₀ = 4π²/g²)。それ以外の今回の修正(X.1、X.2、X.5、V.1、VIII.2、VII.9 など)は WGC と関係ない。

## α-I — 四元数と量子球面 Q(7 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| I.1 (Y1) | 四元数の規約とノルムの乗法性 | 四元数 ℍ、ノルム |pq| = |p||q| | — | — | 運動学 | 完 | `i_sq` `ijk` `conj_product` |
| I.2 (Y2) | 巡回 Fueter 係数とその核 | 係数行列 C(階数 3)、核 (1, −k, −1, k) | — | — | 運動学 | 完 | `right_kernel` `rank_three` `singular` |
| I.3 (Y1, Y2) | ρ: ℍ → SU(2)、SL(2,ℂ) の Lorentz 不変量 | ℍ_ℂ = M₂(ℂ) の二つの実構造 | — | — | 運動学 | 完 | `det_rho` `rho_mul` `det_lorentz` |
| I.4 (Y3) | H² = E²、射影 P、量子計量 | 質量殻、正エネルギーの射影 | — | — | 運動学 | 完 | `dirac_sq` `proj_idem` `quantum_metric` |
| I.5 (Y4) | Q(p) の開いた上半球への全単射、半径 1/√2 | 量子半球(帽子のもと) | — | — | 運動学 | 完 | `qD_unit` `qD_upper` `Qm_unit` |
| I.6 (Y5) | Berry 曲率と Wigner 曲率の非ゲージ同値性 | 半球と H³ の二つの接続 | — | — | 運動学 | 完 | `curv_formula` `ratio` |
| I.7 (Y6) | H³ 上の Berry 接続と BPS 単極子 | 双曲面 H³ と単極子 | — | BPS 方程式 | 運動学 | 完(外) | `bps_k` `bps_f` `starF_closed` |

## α-II — 作用・相の分類・Cartan 幾何(7 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| II.1 (Z2) | EYM + GHY 作用、W = r′ とスピン接続の関係 | 初期データ(W = r′) | EYM + GHY | W = r′ が保たれるのは三つの相だけ | ダンベル | 完(外) | `ym_stress` `sector_geodesic` `phase_form` |
| II.2 (Z3) | 平坦・S³(ℓ)・S²×ℝ 相の分類(CIS Theorem A) | 球対称な空間の相 | ハミルトン拘束 | 三つの相と半径 ℓ | ダンベル | 完(外) | `three_phases` `phase_neck` |
| II.3 (Z3) | 大域的分類(CIS Theorem B) | 完備な空間の大域的な形 | ハミルトン拘束 | 大域的な分類 | ダンベル | 完(外) | — |
| II.4 (Z4-1, 2) | Codazzi 一般解、構造式、第一段階の両立条件 | Cartan 幾何 | — | — | 運動学 | 完 | `codazzi_to_flow` |
| II.5 (Z4-3) | 第二段階の両立条件、階数 12 | Cartan 幾何 | — | — | 運動学 | 完(外) | — |
| II.6 (Z4-D, E) | 対角型・整列型の非存在 | Cartan 幾何 | — | — | 運動学 | 完 | `flow_s1` |
| II.9 (Z5) | 静的解は首(W ≡ 0)か平坦(W ≡ ±1)のみ | 静的な球対称 | EYM | 静的解の分類 | ダンベル | 完 | `br_lapse_d1` `flow_E0` `E0_eq` |

## α-III — ダンベルの形と接合(8 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| III.1 (Z6) | Israel 接合と法線応力の跳び | 接合面 | EYM の Einstein 方程式 | 法線応力の跳び | ダンベル | 部 | `israel_jump` `gauss_tube` |
| III.2 (Z7) | 波面での k^μ[T_μν] = 0 | ヌルの波面 | EYM | 応力の跳びの条件 | ダンベル | 部 | `null_front` `jump_mixed` |
| III.3 (Z0) | 質量の下限 M₂ ≥ r₀ | 帽子と首の形 | 拘束方程式 | 質量の下限 | ダンベル | 完 | `penrose_from_constraints` `integrand_nonneg` |
| III.4 (Z0′) | a = ℓ、首は平坦に開けない | 帽子・赤道・首 | 拘束方程式 | a = ℓ | ダンベル | 完 | `a_eq_l` `M2_neck` |
| III.5 (Z0′) | Schwarzschild は条件 (I) を満たさない | 外部の候補 | Einstein 方程式 | 条件 (I) の否定 | ダンベル | 完 | `schw_not_I` |
| III.6 (Z0-f) | 平坦極限との整合 | 平坦極限 | Einstein 方程式 | Newton 極限の質量 | ダンベル | 完 | `cap_newton` `flat_mass_rate` |
| III.7 (Z0-m) | ℓ*/(2G) = √π M_Pl/g | 首の半径 ℓ | ハミルトン拘束 | ℓ² = 4πG/g² | ダンベル | 完 | `min_mass` `ell_cap` |
| III.9 (Z23) | Gauss–Codazzi、時間的・空間的・ヌルの接合 | 接合面 | Einstein 方程式 | 接合条件の分類 | ダンベル | 部 | `no_shell_iff` `constraint_form` |

## α-IV — 時間発展と崩壊(9 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| IV.1 (Z1) | 初期データと適切性 | 帽子・首の初期データ | EYM | 拘束と適切性 | ダンベル | 完(外) | `cap_constraint` `neck_constraint` `junction_jumps` |
| IV.2 (Z8) | 波面での跳びの輸送 [W_u]、[r_uu] | 波面 | EYM(二重ヌル) | 跳びの輸送 | ダンベル | 部 | `jump_const` `ruu_jump` `goursat_W` |
| IV.3 (Z9-a) | 二重ヌル方程式から中心の式を導出 | 帽子の中心 | EYM | 中心の ODE | ダンベル | 完 | `center_ode` |
| IV.4 | 中心の質量 dE/dτ = −2W²r′ | 帽子の中心 | EYM | 質量の変化 | ダンベル | 完 | `energy_deriv` `energy_nondecreasing` |
| IV.5 (Z9-c) | 有限時間崩壊、t < πr₁/2 | 帽子 a(η) | EYM | 有限時間の崩壊 | ダンベル | 完 | `acc_le` `r_lt` |
| IV.7 (Z10) | gd と首のヌル波面 | 首 −dt² + cos²(t/ℓ)dz²、Gudermann 関数 | EYM(首は厳密解) | ヌルの波面 | ダンベル | 完 | `front_deriv` `front_gd_inv` `neck_mercator` |
| IV.8 (Z10′) | 波面到着時間、キャップ寿命 | 波面と帽子 | EYM | 到着時間と寿命 | ダンベル | 完 | `fronts_meet_before` `cap_lifetime` |
| IV.9 (Z0-f) | 平坦極限 | 平坦極限 | EYM | 平坦極限の時計と波面 | ダンベル | 完 | `flat_clock` `flat_front` |
| IV.12 (Z13) | HJ 厳密解と WKB 波動関数の WDW 解 | ミニ超空間 | EH の縮約 | HJ と WKB | ダンベル | 完(外) | `hj_exact` `wdw_exact` |

## α-V — 量子力学とスピン(7 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| V.1 (Z14〜17) | 共形対応、FW 生成子、スピン接続、FW 変換(静的な外場) | 質量殻 H³ と運動量の半球(Z14) | Dirac の作用 | Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 | 一般 | 完(外) | `metric_pullback` `transport` `berry_fueter_gauge` `fw_order2` `second_fw` `double_comm_pi` |
| V.2 (Z18-a) | 準位 3/2 − 3λ、3/2 + λ(左不変な 4 次元の部分空間) | 帽子 S³ | Dirac の作用 | 準位 | ダンベル | 完(外) | `SS_singlet` `level_shift` `level_triplet` |
| V.4 (Z19) | Gauss 写像から sin²χ = 2Gm/r | 帽子 | Einstein 方程式 | sin²χ = 2Gm/r | ダンベル | 完 | `gauss_compactness` `gauss_vacuum` |
| V.5 (Z29) | 端点 Dirac 方程式の limit-point 性 | 帽子の端点 | Dirac の作用 | limit-point 性 | ダンベル | 完(外) | `endpoint_F` `xy_system` |
| V.7 (Z31) | 量子応力と反作用(共形場、共形真空、背景 SU(2) に結合しない場) | 帽子 | 共形場の有効作用(アノマリー) | 反作用 | ダンベル | 完(外) | `a4_meron` `curvature_traceless` |
| V.7′ (Z31) | 背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²) | 帽子 a(t) | 1 ループの YM の有効作用 | 結合定数が帽子の尺度で走る | ダンベル | 完(外) | `rho_beta_unique` `running_coupling` |
| V.7-N (Z31) | 首 AdS₂ × S² の上の共形場の量子応力 | 首 | 共形場の有効作用(アノマリー) | 負の宇宙定数の働き、半径が縮む | ダンベル | 完(外) | `neck_ricci` `neck_H3` `neck_backreaction` |

## α-VI — 量子重力(4 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| VI.3 (U21′) | S³ 相は宇宙定数なしでは静的でない | S³ 相 | EH | 静的でない | ダンベル | 完 | `s3_not_ultrastatic` |
| VI.4 (Z33) | WDW 方程式の厳密解(二つの順序、二つの枝) | ミニ超空間 | EH の縮約 | WDW の解 | ダンベル | 完 | `wdw_exact_LB` |
| VI.6 (Z35) | 物理的内積(P1〜P3 のもとで一意) | ミニ超空間 | EH の縮約 | 内積 | ダンベル | 完(外) | `bracket_TK` `H_a` |
| VI.8 (Z37) | 半古典極限 | ミニ超空間 | EH の縮約 | 半古典極限 | ダンベル | 完(外) | `constraint_conserved` `instanton_action` |

## α-VII — ゲージ場・物質・指数(8 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| VII.1 (Z24〜26) | 磁荷の量子化、YM 一様場、'tHooft 分解 | 帽子・首の S² と単極子 | YM | 磁荷の量子化 | ダンベル | 完(外) | `dirac_quantization` `chern_eq_two_q` |
| VII.3 (Z28) | SU(2) 単独で独立な超電荷 Y を作れない障害 | 四元数の左の作用 | — | — | 運動学 | 完 | `center_pure_trivial` `no_mixing` |
| VII.4 (Z28-d) | S⁹ 楕円体変形、99/250、ρ = 1 の局所最小 | 内部空間 S⁹ と楕円体の族(1 次では微分同相 + 共形) | 内部の Dirac の作用 | 規格化した最低固有値の 2 次の係数 99/250 > 0 | ダンベル | 完(外) | `ellipsoid_first_order` `killing_stress` `normalized_first_variation` `z28d_values` `ellipsoid_local_min` |
| VII.6 (Z28-f) | 奇数次元の指数は 0 | 奇数次元の内部空間 | Dirac | 指数 0 | 一般 | 完(外) | `index_zero` |
| VII.7 (Z28-f) | ゼロモード厳密解、2|q| 個、カイラリティ sign(q) | S² の単極子 | Dirac | ゼロモード | ダンベル | 完 | `zero_mode` `monopole_zero_modes` `zero_mode_L2` |
| VII.8 (Z28-f) | SO(10) → Pati–Salam、一世代の電荷 | S⁹ の等長群と楕円体の破れ | — | 電荷の表 | ダンベル | 完(外) | `ellipsoid_breaks` `spinor16_charges` `charges_leptons` |
| VII.8-C (Z28-f) | 質量ゼロのカイラルなモード(内部 Dirac 作用素の核) | 楕円体 S⁹(凸) | 内部の Dirac の作用 | 核は 0:内部の核からは出ない(否定的) | ダンベル | 完(外) | `scal_pos_of_convex` `ellipsoid_II_pos` `no_massless_internal` |
| VII.9 (Z28-f) | ひねりの電荷 q = 1/2 でゼロモード 1 個 | 単位 S² の枠とスピン接続 | Dirac(U(1)_F = ½ω でひねる) | q = 1/2、ゼロモードはちょうど 1 個 | ダンベル | 完 | `spin_curvature` `twist_charge` `twist_zero_mode` |

## α-VIII — 弦理論との接点(4 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| VIII.2 (Z39, 40) | 標準埋め込み、α′ 項の消失(Euclid の断面、Ω ∈ so(4)) | Euclid 化したダンベルのスピン接続 | ヘテロティックの O(α′) の作用 | 4 つの場の方程式で α′ 項が消える | 一般 | 完(外) | `all_alpha_terms_vanish` `ymH_embed_iff` `iota_antisymm` |
| VIII.3 (Z41) | アトラクターとエントロピー | 首(磁荷) | Einstein–ディラトン–Maxwell(a = 1) | 磁荷だけではディラトンが逃げる | ダンベル | 完(外) | `string_attractor` `no_attractor_magnetic` `veff_min` |
| VIII.5 (Z38, 42) | ℓ*² = α′/4、WZW 準位 k = 1/4 | 首の半径 | 弦の有効作用 | ℓ*² = α′/4 | ダンベル | 完(外) | `ell_witten` `wzw_level` |
| VIII.7 (Z44) | Killing スピノル不存在(超対称性の障害) | 帽子 a = ℓ cos η | EYM | Killing スピノルはない | ダンベル | 完(外) | `cap_unique` `no_killing_spinor_cap` |

## α-IX — 作用原理からの帰結(35 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| IX.0 | 縮約した作用の第一変分 ⇔ α の五つの方程式(4 次元の全成分と照合) | ダンベルの ansatz | EYM + GHY(縮約) | α の方程式 | ダンベル | 完 | `el_iff_alpha` `full_4d_iff_alpha` `palais_free` |
| IX.1 | 電磁気学の第一変分 | Minkowski | Maxwell | Maxwell の方程式 | 一般 | 完 | `first_variation` |
| IX.2 | ∇·E = ρ、∇×B = J + ∂_tE | Minkowski | Maxwell | Gauss・Ampère | 一般 | 完 | `gauss` `ampere` |
| IX.3 | Bianchi、Faraday、電荷の保存 | Minkowski | Maxwell | Faraday | 一般 | 完 | `bianchi_div` `faraday` |
| IX.4 | SU(2) = Q の Yang–Mills の第一変分 | SU(2) | YM | YM 方程式 | 一般 | 完 | `ym_first_variation` `u1_projection` |
| IX.5 | 電荷と磁荷の区別 | Minkowski | Maxwell | Gauss の積分 | 一般 | 完 | `gauss_integral` |
| IX.6 | 応力テンソルの保存 | Minkowski | Maxwell | ∂T = −FJ | 一般 | 完 | `stress_divergence` |
| IX.7 | 荷電した塵の Lorentz 力 | Minkowski | Maxwell + 塵 | Lorentz 力 | 一般 | 完 | `dust_lorentz` |
| IX.8 | 粒子の Euler–Lagrange 方程式 | Minkowski | 粒子の作用 | 運動方程式 | 一般 | 完 | `particle_el` |
| IX.9 | Hamilton 形式と質量殻 | 質量殻 | 粒子の作用 | Hamilton の式 | 一般 | 完 | `hamilton` `mass_shell` |
| IX.10 | 球対称の縮約 S₂、U = 2 − 2ℓ²/Φ | 首(球対称) | EYM | 2 次元のディラトン重力 | ダンベル | 完(外) | `reduction_identity` `potential_from_YM` |
| IX.11 | 首 Φ = ℓ² は厳密な解(AdS₂) | 首 | IX.10 の作用 | U = 0、R = −2/ℓ² | ダンベル | 完 | `neck_exact` `neck_metric_curvature` |
| IX.12 | JT への展開(余りまで厳密) | 首 | IX.10 の作用 | JT | ダンベル | 完 | `jt_expansion` `jt_kinetic` |
| IX.13 | 基底のエントロピー S₀ = πℓ²/G = 4π²/g²(ディラトンのない EYM) | 首 | EYM | S₀ | ダンベル | 完(外) | `ground_entropy` |
| IX.14 | Schwarzian の熱力学(長い首、L/ℓ ≫ 1) | 首の JT dilaton と接合 | JT | 対称な dilaton = 永遠のブラックホール、E(β)、S(T) | ダンベル | 完(外) | `jt_neck_solution` `no_static_dilaton` `junction_near_boundary` `schwarzian_energy` |
| IX.15 | 1 ループ:m²ℓ² = −1 < −1/4、Δ = ½ ± i√3/2 | 首 | W の 2 次の作用 | BF 限界を下回る | ダンベル | 完(外) | `delta_roots` `neck_mode_below_BF` |
| IX.16 | 完全流体:連続の式と相対論的 Euler | Minkowski | 流体 | Euler 方程式 | 一般 | 完(外) | `fluid_euler` |
| IX.17 | 帽子は輻射の宇宙(p = ρ/3) | 帽子 | YM | 閉じた輻射 FRW | ダンベル | 完 | `cap_radiation` `cap_stress` |
| IX.18 | Kelvin の循環定理の局所形 | 流体 | 流体 | L_uω = 0 | 一般 | 完(外) | `kelvin` |
| IX.19 | 理想 MHD の磁束凍結 | 流体 | MHD | L_uF = 0 | 一般 | 完(外) | `flux_freezing` |
| IX.20 | ヘリシティの釣り合い | Minkowski | Maxwell | ヘリシティの式 | 一般 | 完 | `helicity_balance` |
| IX.21 | Hawking 温度、RN の T | 地平線 | Euclid の EH | T = κ/2π | 一般 | 完(外) | `conical_period` `rn_slope` |
| IX.22 | Euclid の首は H²(曲率 −1/ℓ²) | 首 | — | — | ダンベル | 完 | `euclid_neck_curvature` |
| IX.23 | 第一法則と Smarr、極限で T = 0 | 磁荷の RN | EYM | 第一法則 | 一般 | 完 | `first_law` `smarr` |
| IX.24 | Euclid 作用(磁荷):I = β(M − TS)(正準集団)、S = A/4 | 首の磁荷 | Euclid の EH + GHY + Maxwell | 磁荷を固定した正準集団 | ダンベル | 完(外) | `maxwell_magnetic` `magnetic_action` |
| IX.25 | Tolman–Ehrenfest | 静的な時空 | 輻射 | TN が一定 | 一般 | 完(外) | `tolman` `tolman_const` |
| IX.26 | KMS 条件(有限次元) | 有限系 | — | KMS | 一般 | 完 | `kms` |
| IX.27 | Jüttner 分布の非相対論の極限、Q の座標 m/E | 質量殻 | — | Jüttner → Maxwell | 一般 | 完(外) | `juttner_to_maxwell` `nr_monotone` `q_coordinate` |
| IX.28 | Planck の積分 π⁴/15、Stefan–Boltzmann | 輻射 | — | π⁴/15 | 一般 | 完 | `bose_integral` `stefan_boltzmann` |
| IX.29 | Schwarzian の状態密度と熱力学の整合 | 首の JT | JT | dS/dE = 1/T | 一般 | 完(外) | `laplace_exponent` `micro_temperature` |
| IX.30 | 揺動散逸の関係(有限系、KMS から) | 有限系 | — | S(ω) = coth(βω/2)χ″(ω) | 一般 | 完 | `kms_weights` `fdt_spectral` |
| IX.31 | 焦点を結ぶ定理 | ヌルの測地線 | Einstein(NEC) | θ → −∞ | 一般 | 完(外) | `focusing` |
| IX.32 | Euclid の首 H²/Γ の面積、測地流のエルゴード性 | Euclid の首 | — | 面積 4π(g − 1)ℓ² | 一般 | 完(外) | `hyperbolic_area` |
| IX.33 | 相の比較(磁荷の正準集団)と W の凝縮 | 首につながる RN の枝 | IX.24 の Euclid 作用 | 首につながる小さい枝が選ばれる | ダンベル | 完 | `small_branch_preferred` `heat_capacity_sign` `landau` |
| IX.34 | はりねずみの次数 = 1、π₂(S²) = ℤ | 帽子の単極子 n̂ = x̂ | YM | 次数 = 磁荷 | ダンベル | 完(外) | `hedgehog_jacobian` `hedgehog_degree` |

## α-X — 統一と整合性(7 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| X.1 | Noether の定理を作用から一般に | 有限自由度 | L(q, q̇) | Σ p_iK_i の保存 | 一般 | 完 | `noether` `cyclic_from_noether` `charge_conservation` |
| X.2 | 幾何光学 = HJ = WKB(首の波面) | 首 −dt² + cos²(t/ℓ)dz² | 波動の作用 | アイコナール = 質量ゼロの HJ | ダンベル | 完 | `wkb_2d` `neck_eikonal` |
| X.3 | ゲージ場 = 接続、力 = 曲率 | U(1)、SU(2)、重力 | — | — | 一般 | 完 | `abelian_gauge_invariance` |
| X.4 | 質量(閉じたダンベルでは Misner–Sharp、ADM は定義されない) | 帽子・首 | EYM(Friedmann) | m = (4π/3)ρR³、dm = −p dV | ダンベル | 完 | `cap_ms_mass` `cap_first_law` `weak_discontinuity_no_mass` |
| X.5 | 色電荷 Q^a の接合面での保存 | Witten の ansatz | YM | F_tr の交換子が消え Q = 0 | ダンベル | 完(外) | `witten_Ftr` `color_charge_vanishes` |
| X.6 | すべての最終定理に非空性 | — | — | — | — | 部 | `nonempty_cap` `nonempty_magnetic` `nonempty_window` |
| X.7 | 数値:くさびの特性発展と大域的な継続 | 帽子・首・接合 | EYM | — | ダンベル | 未着手 | — |

## α-XI — 弱い重力予想と首の安定性(7 項目)

| 項目 | 内容 | 運動学(部品・量) | 作用 | 力学(導いたもの) | 区分 | 判定 | 代表の Lean 定理 |
|---|---|---|---|---|---|---|---|
| XI.1 | 首の不安定性の時間スケール | 首(大域 AdS₂)と接合 u_c | W の 2 次の作用 | λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 | ダンベル | 完(外) | `liouville_actual` `actual_form_neg` `growth_rate_bound` `one_efold_before_collapse` |
| XI.2 | 高階補正(F⁴)の符号と穏やかな WGC | 磁荷の RN | L = −F²/4 + α(F²)² | 極限の M/Q < 1 | 一般 | 完(外) | `mass_function` `lighter_extremal` |
| XI.3 | 宇宙検閲:帽子の崩壊の前に捕捉面ができるか | 帽子の波面、首 | EYM | 崩壊の前に波面の上に周辺的な捕捉面 | ダンベル | 完 | `no_trapped_in_cap` `front_marginally_trapped` `neck_marginal` |
| XI.4 | 首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件 | 首(そのまま) | EYM + 随伴 Higgs | m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 | ダンベル | 完(外) | `neck_rho` `force_W_zero` `force_H_zero` `quad_expansion` `w_mass_neck` `planck_condition` `hardy_neck` `no_growing_mode` |
| XI.5 | dyon の首:電荷 q を加えたアトラクター(2pq = ℓ²)と W の安定性 | 首(磁荷 p と電荷 q) | EYM(+ ディラトン) | — | ダンベル | 未着手 | — |
| XI.6 | 実効的な負の宇宙定数(V.7-N)での Hawking–Page 型の相転移 | 首 | 量子応力を含む有効作用 | — | ダンベル | 未着手 | — |
| XI.7 | Higgs を入れたときの帽子と接合(W = cos χ の解の変化) | 帽子・接合 | EYM + 随伴 Higgs | — | ダンベル | 未着手 | — |
