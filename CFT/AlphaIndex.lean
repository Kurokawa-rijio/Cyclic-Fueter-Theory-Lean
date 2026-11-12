/-
  命題群 α の索引:各項目を「運動学(ダンベルの部品と量)・作用・力学」の形で並べ、代表の Lean 定理への
  別名(alias)を置く。区分:運動学 = 幾何そのもの(作用なし)、ダンベル = ダンベルの量に作用を入れて
  力学を出したもの、一般 = 一般の物理を Lean で確かめたもの。判定は docs/CLAIM_STATUS_JA.md と同じ。
  別名は元の定理とまったく同じ主張をもつ(新しい仮定は加えない)。
-/
import CFT.AlphaBridge_Clock
import CFT.AlphaBridge_Thermal
import CFT.AlphaBridge_Twist
import CFT.AlphaCompleteA
import CFT.AlphaCompleteB
import CFT.AlphaCompleteC
import CFT.AlphaCompleteD
import CFT.AlphaDumbbell_Bogomolny
import CFT.AlphaDumbbell_Shape
import CFT.AlphaFix_Dyn
import CFT.AlphaFix_FW
import CFT.AlphaFix_Gauge
import CFT.AlphaFix_Geo
import CFT.AlphaFix_Neck
import CFT.AlphaFix_Thermo
import CFT.AlphaFix_Unify
import CFT.AlphaFix_Z28
import CFT.AlphaI
import CFT.AlphaII
import CFT.AlphaIII
import CFT.AlphaIII_Junction
import CFT.AlphaIII_P1
import CFT.AlphaIII_Shape
import CFT.AlphaII_Action
import CFT.AlphaII_Diagonal
import CFT.AlphaII_EYM
import CFT.AlphaII_Z5
import CFT.AlphaIV
import CFT.AlphaIV_WKB2
import CFT.AlphaIV_Z9
import CFT.AlphaIX_Classical
import CFT.AlphaIX_Fluid
import CFT.AlphaIX_JT
import CFT.AlphaIX_Second
import CFT.AlphaIX_Stat
import CFT.AlphaIX_Thermo
import CFT.AlphaIX_YM
import CFT.AlphaI_AW
import CFT.AlphaI_C
import CFT.AlphaI_Operators
import CFT.AlphaIntegrals
import CFT.AlphaJunction_Unique
import CFT.AlphaKS_WDW
import CFT.AlphaOmega_Close
import CFT.AlphaOmega_Last
import CFT.AlphaOmega_Quantum
import CFT.AlphaOpen_Split
import CFT.AlphaPillar_Conformal
import CFT.AlphaPillar_Polar
import CFT.AlphaPillar_SelfDual
import CFT.AlphaPillar_Smooth
import CFT.AlphaReal_Junction
import CFT.AlphaReal_Rest
import CFT.AlphaRoot_Duality
import CFT.AlphaRoot_Junction
import CFT.AlphaS2_4DMatch
import CFT.AlphaS2_Match
import CFT.AlphaS4_Junction
import CFT.AlphaS5_Evolution
import CFT.AlphaV
import CFT.AlphaVI
import CFT.AlphaVII
import CFT.AlphaVIII_EOM
import CFT.AlphaVIII_StringAttractor
import CFT.AlphaVIII_Z38
import CFT.AlphaVIII_Z44Cap
import CFT.AlphaVII_Bundle
import CFT.AlphaVII_Lichnerowicz
import CFT.AlphaVII_N1
import CFT.AlphaVII_SO10
import CFT.AlphaVII_Z28d
import CFT.AlphaV_A4
import CFT.AlphaV_Endpoint
import CFT.AlphaV_FWOrder
import CFT.AlphaV_NeckQuantum
import CFT.AlphaV_Wigner
import CFT.AlphaXI_HiggsNeck
import CFT.AlphaX_Unify
import CFT.Cartan.SSRank
import CFT.Cartan.SecondStage
import CFT.ZeroModeL2
import Batteries.Tactic.Alias

namespace CFT.Index

/-! ## α-I 四元数と量子球面 Q -/

/-- I.1(運動学、完):四元数の規約とノルムの乗法性。運動学:四元数 ℍ、ノルム |pq| = |p||q|。作用:—。力学:— -/
alias I_1_i_sq := CFT.AlphaI.i_sq

/-- I.1(運動学、完):四元数の規約とノルムの乗法性。運動学:四元数 ℍ、ノルム |pq| = |p||q|。作用:—。力学:— -/
alias I_1_ijk := CFT.AlphaI.ijk

/-- I.1(運動学、完):四元数の規約とノルムの乗法性。運動学:四元数 ℍ、ノルム |pq| = |p||q|。作用:—。力学:— -/
alias I_1_conj_product := CFT.Operators.conj_product

/-- I.2(運動学、完):巡回 Fueter 係数とその核。運動学:係数行列 C(階数 3)、核 (1, −k, −1, k)。作用:—。力学:— -/
alias I_2_right_kernel := CFT.FueterC.right_kernel

/-- I.2(運動学、完):巡回 Fueter 係数とその核。運動学:係数行列 C(階数 3)、核 (1, −k, −1, k)。作用:—。力学:— -/
alias I_2_rank_three := CFT.FueterC.rank_three

/-- I.2(運動学、完):巡回 Fueter 係数とその核。運動学:係数行列 C(階数 3)、核 (1, −k, −1, k)。作用:—。力学:— -/
alias I_2_singular := CFT.FueterC.singular

/-- I.3(運動学、完):ρ: ℍ → SU(2)、SL(2,ℂ) の Lorentz 不変量。運動学:ℍ_ℂ = M₂(ℂ) の二つの実構造。作用:—。力学:— -/
alias I_3_det_rho := CFT.AlphaI.det_rho

/-- I.3(運動学、完):ρ: ℍ → SU(2)、SL(2,ℂ) の Lorentz 不変量。運動学:ℍ_ℂ = M₂(ℂ) の二つの実構造。作用:—。力学:— -/
alias I_3_rho_mul := CFT.AlphaI.rho_mul

/-- I.3(運動学、完):ρ: ℍ → SU(2)、SL(2,ℂ) の Lorentz 不変量。運動学:ℍ_ℂ = M₂(ℂ) の二つの実構造。作用:—。力学:— -/
alias I_3_det_lorentz := CFT.AlphaI.det_lorentz

/-- I.4(運動学、完):H² = E²、射影 P、量子計量。運動学:質量殻、正エネルギーの射影。作用:—。力学:— -/
alias I_4_dirac_sq := CFT.AlphaI.dirac_sq

/-- I.4(運動学、完):H² = E²、射影 P、量子計量。運動学:質量殻、正エネルギーの射影。作用:—。力学:— -/
alias I_4_proj_idem := CFT.AlphaI.proj_idem

/-- I.4(運動学、完):H² = E²、射影 P、量子計量。運動学:質量殻、正エネルギーの射影。作用:—。力学:— -/
alias I_4_quantum_metric := CFT.AlphaCompleteB.quantum_metric

/-- I.5(運動学、完):Q(p) の開いた上半球への全単射、半径 1/√2。運動学:量子半球(帽子のもと)。作用:—。力学:— -/
alias I_5_qD_unit := CFT.AlphaI.qD_unit

/-- I.5(運動学、完):Q(p) の開いた上半球への全単射、半径 1/√2。運動学:量子半球(帽子のもと)。作用:—。力学:— -/
alias I_5_qD_upper := CFT.AlphaI.qD_upper

/-- I.5(運動学、完):Q(p) の開いた上半球への全単射、半径 1/√2。運動学:量子半球(帽子のもと)。作用:—。力学:— -/
alias I_5_Qm_unit := CFT.AlphaI.Qm_unit

/-- I.6(運動学、完):Berry 曲率と Wigner 曲率の非ゲージ同値性。運動学:半球と H³ の二つの接続。作用:—。力学:— -/
alias I_6_curv_formula := CFT.AlphaI_AW.curv_formula

/-- I.6(運動学、完):Berry 曲率と Wigner 曲率の非ゲージ同値性。運動学:半球と H³ の二つの接続。作用:—。力学:— -/
alias I_6_ratio := CFT.AlphaI_AW.ratio

/-- I.7(運動学、完(外)):H³ 上の Berry 接続と BPS 単極子。運動学:双曲面 H³ と単極子。作用:—。力学:BPS 方程式 -/
alias I_7_bps_k := CFT.AlphaI.bps_k

/-- I.7(運動学、完(外)):H³ 上の Berry 接続と BPS 単極子。運動学:双曲面 H³ と単極子。作用:—。力学:BPS 方程式 -/
alias I_7_bps_f := CFT.AlphaI.bps_f

/-- I.7(運動学、完(外)):H³ 上の Berry 接続と BPS 単極子。運動学:双曲面 H³ と単極子。作用:—。力学:BPS 方程式 -/
alias I_7_starF_closed := CFT.AlphaCompleteC.starF_closed

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_det_M := CFT.RootDuality.det_M

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_real_slice_unitary := CFT.RootDuality.real_slice_unitary

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_imag_slice_hermitian := CFT.RootDuality.imag_slice_hermitian

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_wick_path := CFT.RootDuality.wick_path

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_curvature_flip := CFT.RootDuality.curvature_flip

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_hemisphere_on_sphere := CFT.RootDuality.hemisphere_on_sphere

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_hemisphere_deriv := CFT.RootDuality.hemisphere_deriv

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_hemisphere_conformal := CFT.RootDuality.hemisphere_conformal

/-- I.8(運動学、完):量子半球と相対双曲面は一つのものの二つの顔:M(z) = z₀ + i z·σ の行列式 z₀² + z·z の実の切り口(SU(2)、S³)と虚の切り口(Hermite、Minkowski、H³)、回転 c = e^{−iθ} で滑らかにつながる(Cartan の双対)。量子半球は双曲面の半球模型で、赤道は双曲面の無限遠。運動学:ℍ_ℂ = M₂(ℂ)、量子半球 Q = (m/E, p/E)、質量殻 H³。作用:—。力学:— -/
alias I_8_equator_at_infinity := CFT.RootDuality.equator_at_infinity


/-! ## α-II 作用・相の分類・Cartan 幾何 -/

/-- II.1(ダンベル、完(外)):EYM + GHY 作用、W = r′ とスピン接続の関係。運動学:初期データ(W = r′)。作用:EYM + GHY。力学:W = r′ が保たれるのは三つの相だけ -/
alias II_1_ym_stress := CFT.EYM.ym_stress

/-- II.1(ダンベル、完(外)):EYM + GHY 作用、W = r′ とスピン接続の関係。運動学:初期データ(W = r′)。作用:EYM + GHY。力学:W = r′ が保たれるのは三つの相だけ -/
alias II_1_sector_geodesic := CFT.EYM.sector_geodesic

/-- II.1(ダンベル、完(外)):EYM + GHY 作用、W = r′ とスピン接続の関係。運動学:初期データ(W = r′)。作用:EYM + GHY。力学:W = r′ が保たれるのは三つの相だけ -/
alias II_1_phase_form := CFT.EYM.phase_form

/-- II.2(ダンベル、完(外)):平坦・S³(ℓ)・S²×ℝ 相の分類(CIS Theorem A)。運動学:球対称な空間の相。作用:ハミルトン拘束。力学:三つの相と半径 ℓ -/
alias II_2_three_phases := CFT.AlphaII.three_phases

/-- II.2(ダンベル、完(外)):平坦・S³(ℓ)・S²×ℝ 相の分類(CIS Theorem A)。運動学:球対称な空間の相。作用:ハミルトン拘束。力学:三つの相と半径 ℓ -/
alias II_2_phase_neck := CFT.EYM.phase_neck

/-- II.3(ダンベル、完):大域的分類:球対称な断面は S³(ℓ) の一部・平坦・首(半径 ℓ)の三つだけ(一般の場合は CIS Theorem B)。運動学:球対称な空間の断面 ds² + r(s)²dΩ²。作用:ハミルトン拘束(II.2 の三つの相)。力学:S³ 相は r = r(0)cos(s/ℓ) + ℓr′(0)sin(s/ℓ)(振幅 ℓ、極で滑らか)、平坦相は直線、首は r = ℓ -/
alias II_3_s3_global := CFT.FixGeo.s3_global

/-- II.3(ダンベル、完):大域的分類:球対称な断面は S³(ℓ) の一部・平坦・首(半径 ℓ)の三つだけ(一般の場合は CIS Theorem B)。運動学:球対称な空間の断面 ds² + r(s)²dΩ²。作用:ハミルトン拘束(II.2 の三つの相)。力学:S³ 相は r = r(0)cos(s/ℓ) + ℓr′(0)sin(s/ℓ)(振幅 ℓ、極で滑らか)、平坦相は直線、首は r = ℓ -/
alias II_3_s3_amplitude := CFT.FixGeo.s3_amplitude

/-- II.3(ダンベル、完):大域的分類:球対称な断面は S³(ℓ) の一部・平坦・首(半径 ℓ)の三つだけ(一般の場合は CIS Theorem B)。運動学:球対称な空間の断面 ds² + r(s)²dΩ²。作用:ハミルトン拘束(II.2 の三つの相)。力学:S³ 相は r = r(0)cos(s/ℓ) + ℓr′(0)sin(s/ℓ)(振幅 ℓ、極で滑らか)、平坦相は直線、首は r = ℓ -/
alias II_3_s3_pole_regular := CFT.FixGeo.s3_pole_regular

/-- II.3(ダンベル、完):大域的分類:球対称な断面は S³(ℓ) の一部・平坦・首(半径 ℓ)の三つだけ(一般の場合は CIS Theorem B)。運動学:球対称な空間の断面 ds² + r(s)²dΩ²。作用:ハミルトン拘束(II.2 の三つの相)。力学:S³ 相は r = r(0)cos(s/ℓ) + ℓr′(0)sin(s/ℓ)(振幅 ℓ、極で滑らか)、平坦相は直線、首は r = ℓ -/
alias II_3_flat_global := CFT.FixGeo.flat_global

/-- II.3(ダンベル、完):大域的分類:球対称な断面は S³(ℓ) の一部・平坦・首(半径 ℓ)の三つだけ(一般の場合は CIS Theorem B)。運動学:球対称な空間の断面 ds² + r(s)²dΩ²。作用:ハミルトン拘束(II.2 の三つの相)。力学:S³ 相は r = r(0)cos(s/ℓ) + ℓr′(0)sin(s/ℓ)(振幅 ℓ、極で滑らか)、平坦相は直線、首は r = ℓ -/
alias II_3_phase_neck := CFT.EYM.phase_neck

/-- II.4(運動学、完):Codazzi 一般解、構造式、第一段階の両立条件。運動学:Cartan 幾何。作用:—。力学:— -/
alias II_4_codazzi_to_flow := CFT.Diagonal.codazzi_to_flow

/-- II.5(運動学、完(外)):第二段階の両立条件、階数 12。運動学:Cartan 幾何(C2 枠)。作用:—。力学:— -/
alias II_5_Bj_frame := CFT.Cartan.C2.Bj_frame

/-- II.5(運動学、完(外)):第二段階の両立条件、階数 12。運動学:Cartan 幾何(C2 枠)。作用:—。力学:— -/
alias II_5_Bj_star := CFT.Cartan.Bj_star

/-- II.5(運動学、完(外)):第二段階の両立条件、階数 12。運動学:Cartan 幾何(C2 枠)。作用:—。力学:— -/
alias II_5_rank12_star := CFT.Cartan.rank12_star

/-- II.6(運動学、完):対角型・整列型の非存在。運動学:Cartan 幾何。作用:—。力学:— -/
alias II_6_flow_s1 := CFT.Diagonal.flow_s1

/-- II.9(ダンベル、完):静的解は首(W ≡ 0)か平坦(W ≡ ±1)のみ。運動学:静的な球対称。作用:EYM。力学:静的解の分類 -/
alias II_9_br_lapse_d1 := CFT.AlphaII.br_lapse_d1

/-- II.9(ダンベル、完):静的解は首(W ≡ 0)か平坦(W ≡ ±1)のみ。運動学:静的な球対称。作用:EYM。力学:静的解の分類 -/
alias II_9_flow_E0 := CFT.Z5.flow_E0

/-- II.9(ダンベル、完):静的解は首(W ≡ 0)か平坦(W ≡ ±1)のみ。運動学:静的な球対称。作用:EYM。力学:静的解の分類 -/
alias II_9_E0_eq := CFT.Z5.E0_eq


/-! ## α-III ダンベルの形と接合 -/

/-- III.1(ダンベル、完):Israel 接合と法線応力の跳び:瞬間での [T_nn] = −1/(4πGℓ²) ≠ 0、時間的な管は面積半径が帽子 √(ℓ² − τ²)・首 ℓ で τ ≠ 0 で一致せず接合面になれない、表面の色の流れ j = s/ℓ ≠ 0(実関数と弱い形で、RealLine なし)。運動学:接合面。作用:EYM の Einstein 方程式と YM 方程式(弱い形)。力学:時間的な接合は不可能、接合はヌルの波面へ -/
alias III_1_israel_jump := CFT.AlphaIII.israel_jump

/-- III.1(ダンベル、完):Israel 接合と法線応力の跳び:瞬間での [T_nn] = −1/(4πGℓ²) ≠ 0、時間的な管は面積半径が帽子 √(ℓ² − τ²)・首 ℓ で τ ≠ 0 で一致せず接合面になれない、表面の色の流れ j = s/ℓ ≠ 0(実関数と弱い形で、RealLine なし)。運動学:接合面。作用:EYM の Einstein 方程式と YM 方程式(弱い形)。力学:時間的な接合は不可能、接合はヌルの波面へ -/
alias III_1_gauss_tube := CFT.S4J.gauss_tube

/-- III.1(ダンベル、完):Israel 接合と法線応力の跳び:瞬間での [T_nn] = −1/(4πGℓ²) ≠ 0、時間的な管は面積半径が帽子 √(ℓ² − τ²)・首 ℓ で τ ≠ 0 で一致せず接合面になれない、表面の色の流れ j = s/ℓ ≠ 0(実関数と弱い形で、RealLine なし)。運動学:接合面。作用:EYM の Einstein 方程式と YM 方程式(弱い形)。力学:時間的な接合は不可能、接合はヌルの波面へ -/
alias III_1_rj_tube_mismatch := CFT.RJ.rj_tube_mismatch

/-- III.1(ダンベル、完):Israel 接合と法線応力の跳び:瞬間での [T_nn] = −1/(4πGℓ²) ≠ 0、時間的な管は面積半径が帽子 √(ℓ² − τ²)・首 ℓ で τ ≠ 0 で一致せず接合面になれない、表面の色の流れ j = s/ℓ ≠ 0(実関数と弱い形で、RealLine なし)。運動学:接合面。作用:EYM の Einstein 方程式と YM 方程式(弱い形)。力学:時間的な接合は不可能、接合はヌルの波面へ -/
alias III_1_rj_color_dumbbell := CFT.RJ.rj_color_dumbbell

/-- III.2(ダンベル、完):波面での k^μ[T_μν] = 0:各 v の弱い形の uu 方程式と混合成分の式、角での [r_u] = 0 から面密度 μ = 0。W の連続から [T_vv] = 0、YM の表面流 0(実関数、RealLine なし)。運動学:ヌルの波面。作用:EYM(二重ヌル、弱い形)。力学:殻も表面流もない -/
alias III_2_null_front := CFT.AlphaIII.null_front

/-- III.2(ダンベル、完):波面での k^μ[T_μν] = 0:各 v の弱い形の uu 方程式と混合成分の式、角での [r_u] = 0 から面密度 μ = 0。W の連続から [T_vv] = 0、YM の表面流 0(実関数、RealLine なし)。運動学:ヌルの波面。作用:EYM(二重ヌル、弱い形)。力学:殻も表面流もない -/
alias III_2_jump_mixed := CFT.S4J.jump_mixed

/-- III.2(ダンベル、完):波面での k^μ[T_μν] = 0:各 v の弱い形の uu 方程式と混合成分の式、角での [r_u] = 0 から面密度 μ = 0。W の連続から [T_vv] = 0、YM の表面流 0(実関数、RealLine なし)。運動学:ヌルの波面。作用:EYM(二重ヌル、弱い形)。力学:殻も表面流もない -/
alias III_2_rj_null_real := CFT.RJ.rj_null_real

/-- III.2(ダンベル、完):波面での k^μ[T_μν] = 0:各 v の弱い形の uu 方程式と混合成分の式、角での [r_u] = 0 から面密度 μ = 0。W の連続から [T_vv] = 0、YM の表面流 0(実関数、RealLine なし)。運動学:ヌルの波面。作用:EYM(二重ヌル、弱い形)。力学:殻も表面流もない -/
alias III_2_rj_front_tangential := CFT.RJ.rj_front_tangential

/-- III.3(ダンベル、完):質量の下限 M₂ ≥ r₀。運動学:帽子と首の形。作用:拘束方程式。力学:質量の下限 -/
alias III_3_penrose_from_constraints := CFT.Shape.penrose_from_constraints

/-- III.3(ダンベル、完):質量の下限 M₂ ≥ r₀。運動学:帽子と首の形。作用:拘束方程式。力学:質量の下限 -/
alias III_3_integrand_nonneg := CFT.AlphaIII.integrand_nonneg

/-- III.4(ダンベル、完):a = ℓ、首は平坦に開けない。運動学:帽子・赤道・首。作用:拘束方程式。力学:a = ℓ -/
alias III_4_a_eq_l := CFT.AlphaIII.a_eq_l

/-- III.4(ダンベル、完):a = ℓ、首は平坦に開けない。運動学:帽子・赤道・首。作用:拘束方程式。力学:a = ℓ -/
alias III_4_M2_neck := CFT.AlphaIII.M2_neck

/-- III.5(ダンベル、完):Schwarzschild は条件 (I) を満たさない。運動学:外部の候補。作用:Einstein 方程式。力学:条件 (I) の否定 -/
alias III_5_schw_not_I := CFT.AlphaIII.schw_not_I

/-- III.6(ダンベル、完):平坦極限との整合。運動学:平坦極限。作用:Einstein 方程式。力学:Newton 極限の質量 -/
alias III_6_cap_newton := CFT.AlphaIII.cap_newton

/-- III.6(ダンベル、完):平坦極限との整合。運動学:平坦極限。作用:Einstein 方程式。力学:Newton 極限の質量 -/
alias III_6_flat_mass_rate := CFT.AlphaIII.flat_mass_rate

/-- III.7(ダンベル、完):ℓ*/(2G) = √π M_Pl/g。運動学:首の半径 ℓ。作用:ハミルトン拘束。力学:ℓ² = 4πG/g² -/
alias III_7_min_mass := CFT.AlphaIII.min_mass

/-- III.7(ダンベル、完):ℓ*/(2G) = √π M_Pl/g。運動学:首の半径 ℓ。作用:ハミルトン拘束。力学:ℓ² = 4πG/g² -/
alias III_7_ell_cap := CFT.EYM.ell_cap

/-- III.9(ダンベル、完):Gauss–Codazzi、時間的・空間的・ヌルの接合:空間的(時間対称な切り口)は [R′] = 0 で殻なし、³R は 6/ℓ² → 2/ℓ² と跳ぶ。時間的は不可能(III.1)、ヌルは殻なしの弱い不連続(III.2、IV.2)。運動学:接合面。作用:Einstein 方程式(弱い形)。力学:接合条件の分類 -/
alias III_9_no_shell_iff := CFT.Junction.no_shell_iff

/-- III.9(ダンベル、完):Gauss–Codazzi、時間的・空間的・ヌルの接合:空間的(時間対称な切り口)は [R′] = 0 で殻なし、³R は 6/ℓ² → 2/ℓ² と跳ぶ。時間的は不可能(III.1)、ヌルは殻なしの弱い不連続(III.2、IV.2)。運動学:接合面。作用:Einstein 方程式(弱い形)。力学:接合条件の分類 -/
alias III_9_constraint_form := CFT.Junction.constraint_form

/-- III.9(ダンベル、完):Gauss–Codazzi、時間的・空間的・ヌルの接合:空間的(時間対称な切り口)は [R′] = 0 で殻なし、³R は 6/ℓ² → 2/ℓ² と跳ぶ。時間的は不可能(III.1)、ヌルは殻なしの弱い不連続(III.2、IV.2)。運動学:接合面。作用:Einstein 方程式(弱い形)。力学:接合条件の分類 -/
alias III_9_rj_slice_dumbbell := CFT.RJ.rj_slice_dumbbell


/-! ## α-IV 時間発展と崩壊 -/

/-- IV.1(ダンベル、完(外)):初期データと適切性。運動学:帽子・首の初期データ。作用:EYM。力学:拘束と適切性 -/
alias IV_1_cap_constraint := CFT.AlphaIntegrals.cap_constraint

/-- IV.1(ダンベル、完(外)):初期データと適切性。運動学:帽子・首の初期データ。作用:EYM。力学:拘束と適切性 -/
alias IV_1_neck_constraint := CFT.AlphaIntegrals.neck_constraint

/-- IV.1(ダンベル、完(外)):初期データと適切性。運動学:帽子・首の初期データ。作用:EYM。力学:拘束と適切性 -/
alias IV_1_junction_jumps := CFT.AlphaIntegrals.junction_jumps

/-- IV.2(ダンベル、完):波面での跳びの輸送:W_uv が両側で共通の値なら [W_u] は波面に沿って一定(角の値 1/(√2ℓ))、[r_u] = 0、角での [r_uu] = −1/ℓ(帽子の r = ℓcos²(u/(√2ℓ)) と一致)。運動学:波面。作用:EYM(二重ヌル)。力学:跳びは減衰も増幅もせず光速で運ばれる -/
alias IV_2_jump_const := CFT.AlphaIV.jump_const

/-- IV.2(ダンベル、完):波面での跳びの輸送:W_uv が両側で共通の値なら [W_u] は波面に沿って一定(角の値 1/(√2ℓ))、[r_u] = 0、角での [r_uu] = −1/ℓ(帽子の r = ℓcos²(u/(√2ℓ)) と一致)。運動学:波面。作用:EYM(二重ヌル)。力学:跳びは減衰も増幅もせず光速で運ばれる -/
alias IV_2_ruu_jump := CFT.AlphaIV.ruu_jump

/-- IV.2(ダンベル、完):波面での跳びの輸送:W_uv が両側で共通の値なら [W_u] は波面に沿って一定(角の値 1/(√2ℓ))、[r_u] = 0、角での [r_uu] = −1/ℓ(帽子の r = ℓcos²(u/(√2ℓ)) と一致)。運動学:波面。作用:EYM(二重ヌル)。力学:跳びは減衰も増幅もせず光速で運ばれる -/
alias IV_2_goursat_W := CFT.S5.goursat_W

/-- IV.2(ダンベル、完):波面での跳びの輸送:W_uv が両側で共通の値なら [W_u] は波面に沿って一定(角の値 1/(√2ℓ))、[r_u] = 0、角での [r_uu] = −1/ℓ(帽子の r = ℓcos²(u/(√2ℓ)) と一致)。運動学:波面。作用:EYM(二重ヌル)。力学:跳びは減衰も増幅もせず光速で運ばれる -/
alias IV_2_rj_Wu_transport := CFT.RJ.rj_Wu_transport

/-- IV.2(ダンベル、完):波面での跳びの輸送:W_uv が両側で共通の値なら [W_u] は波面に沿って一定(角の値 1/(√2ℓ))、[r_u] = 0、角での [r_uu] = −1/ℓ(帽子の r = ℓcos²(u/(√2ℓ)) と一致)。運動学:波面。作用:EYM(二重ヌル)。力学:跳びは減衰も増幅もせず光速で運ばれる -/
alias IV_2_rj_ruu_corner := CFT.RJ.rj_ruu_corner

/-- IV.3(ダンベル、完):二重ヌル方程式から中心の式を導出。運動学:帽子の中心。作用:EYM。力学:中心の ODE -/
alias IV_3_center_ode := CFT.AlphaCompleteA.center_ode

/-- IV.4(ダンベル、完):中心の質量 dE/dτ = −2W²r′。運動学:帽子の中心。作用:EYM。力学:質量の変化 -/
alias IV_4_energy_deriv := CFT.AlphaIV.energy_deriv

/-- IV.4(ダンベル、完):中心の質量 dE/dτ = −2W²r′。運動学:帽子の中心。作用:EYM。力学:質量の変化 -/
alias IV_4_energy_nondecreasing := CFT.AlphaIV.energy_nondecreasing

/-- IV.5(ダンベル、完):有限時間崩壊、t < πr₁/2。運動学:帽子 a(η)。作用:EYM。力学:有限時間の崩壊 -/
alias IV_5_acc_le := CFT.Z9.acc_le

/-- IV.5(ダンベル、完):有限時間崩壊、t < πr₁/2。運動学:帽子 a(η)。作用:EYM。力学:有限時間の崩壊 -/
alias IV_5_r_lt := CFT.Z9.r_lt

/-- IV.7(ダンベル、完):gd と首のヌル波面。運動学:首 −dt² + cos²(t/ℓ)dz²、Gudermann 関数。作用:EYM(首は厳密解)。力学:ヌルの波面 -/
alias IV_7_front_deriv := CFT.AlphaIV.front_deriv

/-- IV.7(ダンベル、完):gd と首のヌル波面。運動学:首 −dt² + cos²(t/ℓ)dz²、Gudermann 関数。作用:EYM(首は厳密解)。力学:ヌルの波面 -/
alias IV_7_front_gd_inv := CFT.S5.front_gd_inv

/-- IV.7(ダンベル、完):gd と首のヌル波面。運動学:首 −dt² + cos²(t/ℓ)dz²、Gudermann 関数。作用:EYM(首は厳密解)。力学:ヌルの波面 -/
alias IV_7_neck_mercator := CFT.S5.neck_mercator

/-- IV.8(ダンベル、完):波面到着時間、キャップ寿命。運動学:波面と帽子。作用:EYM。力学:到着時間と寿命 -/
alias IV_8_fronts_meet_before := CFT.AlphaIV.fronts_meet_before

/-- IV.8(ダンベル、完):波面到着時間、キャップ寿命。運動学:波面と帽子。作用:EYM。力学:到着時間と寿命 -/
alias IV_8_cap_lifetime := CFT.AlphaIV.cap_lifetime

/-- IV.9(ダンベル、完):平坦極限。運動学:平坦極限。作用:EYM。力学:平坦極限の時計と波面 -/
alias IV_9_flat_clock := CFT.S5.flat_clock

/-- IV.9(ダンベル、完):平坦極限。運動学:平坦極限。作用:EYM。力学:平坦極限の時計と波面 -/
alias IV_9_flat_front := CFT.S5.flat_front

/-- IV.12(ダンベル、完(外)):HJ 厳密解と WKB 波動関数の WDW 解。運動学:ミニ超空間。作用:EH の縮約。力学:HJ と WKB -/
alias IV_12_hj_exact := CFT.AlphaCompleteA.hj_exact

/-- IV.12(ダンベル、完(外)):HJ 厳密解と WKB 波動関数の WDW 解。運動学:ミニ超空間。作用:EH の縮約。力学:HJ と WKB -/
alias IV_12_wdw_exact := CFT.AlphaIV.wdw_exact


/-! ## α-V 量子力学とスピン -/

/-- V.1(一般、完(外)):共形対応、FW 生成子、スピン接続、FW 変換(静的な外場)。運動学:質量殻 H³ と運動量の半球(Z14)。作用:Dirac の作用。力学:Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 -/
alias V_1_metric_pullback := CFT.Wigner.metric_pullback

/-- V.1(一般、完(外)):共形対応、FW 生成子、スピン接続、FW 変換(静的な外場)。運動学:質量殻 H³ と運動量の半球(Z14)。作用:Dirac の作用。力学:Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 -/
alias V_1_transport := CFT.Wigner.transport

/-- V.1(一般、完(外)):共形対応、FW 生成子、スピン接続、FW 変換(静的な外場)。運動学:質量殻 H³ と運動量の半球(Z14)。作用:Dirac の作用。力学:Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 -/
alias V_1_berry_fueter_gauge := CFT.Wigner.berry_fueter_gauge

/-- V.1(一般、完(外)):共形対応、FW 生成子、スピン接続、FW 変換(静的な外場)。運動学:質量殻 H³ と運動量の半球(Z14)。作用:Dirac の作用。力学:Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 -/
alias V_1_fw_order2 := CFT.FWOrder.fw_order2

/-- V.1(一般、完(外)):共形対応、FW 生成子、スピン接続、FW 変換(静的な外場)。運動学:質量殻 H³ と運動量の半球(Z14)。作用:Dirac の作用。力学:Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 -/
alias V_1_second_fw := CFT.FixFW.second_fw

/-- V.1(一般、完(外)):共形対応、FW 生成子、スピン接続、FW 変換(静的な外場)。運動学:質量殻 H³ と運動量の半球(Z14)。作用:Dirac の作用。力学:Wigner 回転の輸送、FW の 1/m² まで、Darwin とスピン軌道の形 -/
alias V_1_double_comm_pi := CFT.FixFW.double_comm_pi

/-- V.2(ダンベル、完(外)):準位 3/2 − 3λ、3/2 + λ(左不変な 4 次元の部分空間)。運動学:帽子 S³。作用:Dirac の作用。力学:準位 -/
alias V_2_SS_singlet := CFT.AlphaV.SS_singlet

/-- V.2(ダンベル、完(外)):準位 3/2 − 3λ、3/2 + λ(左不変な 4 次元の部分空間)。運動学:帽子 S³。作用:Dirac の作用。力学:準位 -/
alias V_2_level_shift := CFT.AlphaV.level_shift

/-- V.2(ダンベル、完(外)):準位 3/2 − 3λ、3/2 + λ(左不変な 4 次元の部分空間)。運動学:帽子 S³。作用:Dirac の作用。力学:準位 -/
alias V_2_level_triplet := CFT.AlphaV.level_triplet

/-- V.4(ダンベル、完):Gauss 写像から sin²χ = 2Gm/r。運動学:帽子。作用:Einstein 方程式。力学:sin²χ = 2Gm/r -/
alias V_4_gauss_compactness := CFT.AlphaV.gauss_compactness

/-- V.4(ダンベル、完):Gauss 写像から sin²χ = 2Gm/r。運動学:帽子。作用:Einstein 方程式。力学:sin²χ = 2Gm/r -/
alias V_4_gauss_vacuum := CFT.AlphaV.gauss_vacuum

/-- V.5(ダンベル、完(外)):端点 Dirac 方程式の limit-point 性。運動学:帽子の端点。作用:Dirac の作用。力学:limit-point 性 -/
alias V_5_endpoint_F := CFT.AlphaIntegrals.endpoint_F

/-- V.5(ダンベル、完(外)):端点 Dirac 方程式の limit-point 性。運動学:帽子の端点。作用:Dirac の作用。力学:limit-point 性 -/
alias V_5_xy_system := CFT.Endpoint.xy_system

/-- V.7(ダンベル、完(外)):量子応力と反作用(共形場、共形真空、背景 SU(2) に結合しない場)。運動学:帽子。作用:共形場の有効作用(アノマリー)。力学:反作用 -/
alias V_7_a4_meron := CFT.AlphaV.a4_meron

/-- V.7(ダンベル、完(外)):量子応力と反作用(共形場、共形真空、背景 SU(2) に結合しない場)。運動学:帽子。作用:共形場の有効作用(アノマリー)。力学:反作用 -/
alias V_7_curvature_traceless := CFT.A4.curvature_traceless

/-- V.7′(ダンベル、完(外)):背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²)。運動学:帽子 a(t)、X = ℓ²/a⁴。作用:1 ループの YM の有効作用。力学:結合定数が帽子の尺度で走る、反作用全体が保存、古典との比 −2g²β_gℓ⁴/a⁴ -/
alias V_7p_rho_beta_unique := CFT.NeckQuantum.rho_beta_unique

/-- V.7′(ダンベル、完(外)):背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²)。運動学:帽子 a(t)、X = ℓ²/a⁴。作用:1 ループの YM の有効作用。力学:結合定数が帽子の尺度で走る、反作用全体が保存、古典との比 −2g²β_gℓ⁴/a⁴ -/
alias V_7p_running_coupling := CFT.NeckQuantum.running_coupling

/-- V.7′(ダンベル、完(外)):背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²)。運動学:帽子 a(t)、X = ℓ²/a⁴。作用:1 ループの YM の有効作用。力学:結合定数が帽子の尺度で走る、反作用全体が保存、古典との比 −2g²β_gℓ⁴/a⁴ -/
alias V_7p_total_conserved := CFT.FixDyn.total_conserved

/-- V.7′(ダンベル、完(外)):背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²)。運動学:帽子 a(t)、X = ℓ²/a⁴。作用:1 ループの YM の有効作用。力学:結合定数が帽子の尺度で走る、反作用全体が保存、古典との比 −2g²β_gℓ⁴/a⁴ -/
alias V_7p_cap_X := CFT.FixDyn.cap_X

/-- V.7′(ダンベル、完(外)):背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²)。運動学:帽子 a(t)、X = ℓ²/a⁴。作用:1 ループの YM の有効作用。力学:結合定数が帽子の尺度で走る、反作用全体が保存、古典との比 −2g²β_gℓ⁴/a⁴ -/
alias V_7p_cap_backreaction_ratio := CFT.FixDyn.cap_backreaction_ratio

/-- V.7′(ダンベル、完(外)):背景 SU(2) 場の量子揺らぎと反作用(β 関数の項 ∝ F²)。運動学:帽子 a(t)、X = ℓ²/a⁴。作用:1 ループの YM の有効作用。力学:結合定数が帽子の尺度で走る、反作用全体が保存、古典との比 −2g²β_gℓ⁴/a⁴ -/
alias V_7p_backreaction_grows := CFT.FixDyn.backreaction_grows

/-- V.7-N(ダンベル、完(橋)):首 AdS₂ × S² の上の共形場の量子応力。運動学:首。作用:共形場の有効作用(アノマリー)。力学:負の宇宙定数の働き、半径が縮む -/
alias V_7N_neck_ricci := CFT.NeckQuantum.neck_ricci

/-- V.7-N(ダンベル、完(橋)):首 AdS₂ × S² の上の共形場の量子応力。運動学:首。作用:共形場の有効作用(アノマリー)。力学:負の宇宙定数の働き、半径が縮む -/
alias V_7N_neck_H3 := CFT.NeckQuantum.neck_H3

/-- V.7-N(ダンベル、完(橋)):首 AdS₂ × S² の上の共形場の量子応力。運動学:首。作用:共形場の有効作用(アノマリー)。力学:負の宇宙定数の働き、半径が縮む -/
alias V_7N_neck_backreaction := CFT.NeckQuantum.neck_backreaction


/-! ## α-VI 量子重力 -/

/-- VI.3(ダンベル、完):S³ 相は宇宙定数なしでは静的でない。運動学:S³ 相。作用:EH。力学:静的でない -/
alias VI_3_s3_not_ultrastatic := CFT.AlphaVI.s3_not_ultrastatic

/-- VI.4(ダンベル、完):WDW 方程式の厳密解(二つの順序、二つの枝)。運動学:ミニ超空間。作用:EH の縮約。力学:WDW の解 -/
alias VI_4_wdw_exact_LB := CFT.WKB2.wdw_exact_LB

/-- VI.6(ダンベル、完(外)):物理的内積(P1〜P3 のもとで一意)。運動学:ミニ超空間。作用:EH の縮約。力学:内積 -/
alias VI_6_bracket_TK := CFT.AlphaVI.bracket_TK

/-- VI.6(ダンベル、完(外)):物理的内積(P1〜P3 のもとで一意)。運動学:ミニ超空間。作用:EH の縮約。力学:内積 -/
alias VI_6_H_a := CFT.AlphaCompleteA.H_a

/-- VI.8(ダンベル、完(外)):半古典極限。運動学:ミニ超空間。作用:EH の縮約。力学:半古典極限 -/
alias VI_8_constraint_conserved := CFT.AlphaVI.constraint_conserved

/-- VI.8(ダンベル、完(外)):半古典極限。運動学:ミニ超空間。作用:EH の縮約。力学:半古典極限 -/
alias VI_8_instanton_action := CFT.AlphaVI.instanton_action


/-! ## α-VII ゲージ場・物質・指数 -/

/-- VII.1(ダンベル、完(外)):磁荷の量子化、YM 一様場、'tHooft 分解。運動学:帽子・首の S² と単極子。作用:YM。力学:磁荷の量子化 -/
alias VII_1_dirac_quantization := CFT.Bundle.dirac_quantization

/-- VII.1(ダンベル、完(外)):磁荷の量子化、YM 一様場、'tHooft 分解。運動学:帽子・首の S² と単極子。作用:YM。力学:磁荷の量子化 -/
alias VII_1_chern_eq_two_q := CFT.Bundle.chern_eq_two_q

/-- VII.3(運動学、完):SU(2) 単独で独立な超電荷 Y を作れない障害。運動学:四元数の左の作用。作用:—。力学:— -/
alias VII_3_center_pure_trivial := CFT.N1.center_pure_trivial

/-- VII.3(運動学、完):SU(2) 単独で独立な超電荷 Y を作れない障害。運動学:四元数の左の作用。作用:—。力学:— -/
alias VII_3_no_mixing := CFT.N1.no_mixing

/-- VII.4(ダンベル、完(外)):S⁹ 楕円体変形、99/250、ρ = 1 の局所最小。運動学:内部空間 S⁹ と楕円体の族(1 次では微分同相 + 共形)。作用:内部の Dirac の作用。力学:規格化した最低固有値の 2 次の係数 99/250 > 0 -/
alias VII_4_ellipsoid_first_order := CFT.FixZ28.ellipsoid_first_order

/-- VII.4(ダンベル、完(外)):S⁹ 楕円体変形、99/250、ρ = 1 の局所最小。運動学:内部空間 S⁹ と楕円体の族(1 次では微分同相 + 共形)。作用:内部の Dirac の作用。力学:規格化した最低固有値の 2 次の係数 99/250 > 0 -/
alias VII_4_killing_stress := CFT.FixZ28.killing_stress

/-- VII.4(ダンベル、完(外)):S⁹ 楕円体変形、99/250、ρ = 1 の局所最小。運動学:内部空間 S⁹ と楕円体の族(1 次では微分同相 + 共形)。作用:内部の Dirac の作用。力学:規格化した最低固有値の 2 次の係数 99/250 > 0 -/
alias VII_4_normalized_first_variation := CFT.FixZ28.normalized_first_variation

/-- VII.4(ダンベル、完(外)):S⁹ 楕円体変形、99/250、ρ = 1 の局所最小。運動学:内部空間 S⁹ と楕円体の族(1 次では微分同相 + 共形)。作用:内部の Dirac の作用。力学:規格化した最低固有値の 2 次の係数 99/250 > 0 -/
alias VII_4_z28d_values := CFT.Z28d.z28d_values

/-- VII.4(ダンベル、完(外)):S⁹ 楕円体変形、99/250、ρ = 1 の局所最小。運動学:内部空間 S⁹ と楕円体の族(1 次では微分同相 + 共形)。作用:内部の Dirac の作用。力学:規格化した最低固有値の 2 次の係数 99/250 > 0 -/
alias VII_4_ellipsoid_local_min := CFT.FixZ28.ellipsoid_local_min

/-- VII.6(一般、完(外)):奇数次元の指数は 0。運動学:奇数次元の内部空間。作用:Dirac。力学:指数 0 -/
alias VII_6_index_zero := CFT.Lichnerowicz.index_zero

/-- VII.7(ダンベル、完):ゼロモード厳密解、2|q| 個、カイラリティ sign(q)。運動学:S² の単極子。作用:Dirac。力学:ゼロモード -/
alias VII_7_zero_mode := CFT.AlphaCompleteD.zero_mode

/-- VII.7(ダンベル、完):ゼロモード厳密解、2|q| 個、カイラリティ sign(q)。運動学:S² の単極子。作用:Dirac。力学:ゼロモード -/
alias VII_7_monopole_zero_modes := CFT.AlphaVII.monopole_zero_modes

/-- VII.7(ダンベル、完):ゼロモード厳密解、2|q| 個、カイラリティ sign(q)。運動学:S² の単極子。作用:Dirac。力学:ゼロモード -/
alias VII_7_zero_mode_L2 := CFT.ZeroModeL2.zero_mode_L2

/-- VII.8(ダンベル、完(外)):SO(10) → Pati–Salam、一世代の電荷。運動学:S⁹ の等長群と楕円体の破れ。作用:—。力学:電荷の表 -/
alias VII_8_ellipsoid_breaks := CFT.SO10.ellipsoid_breaks

/-- VII.8(ダンベル、完(外)):SO(10) → Pati–Salam、一世代の電荷。運動学:S⁹ の等長群と楕円体の破れ。作用:—。力学:電荷の表 -/
alias VII_8_spinor16_charges := CFT.SO10.spinor16_charges

/-- VII.8(ダンベル、完(外)):SO(10) → Pati–Salam、一世代の電荷。運動学:S⁹ の等長群と楕円体の破れ。作用:—。力学:電荷の表 -/
alias VII_8_charges_leptons := CFT.N1.charges_leptons

/-- VII.8-C(ダンベル、完(外)):質量ゼロのカイラルなモード(内部 Dirac 作用素の核)。運動学:楕円体 S⁹(凸)。作用:内部の Dirac の作用。力学:核は 0:内部の核からは出ない(否定的) -/
alias VII_8C_scal_pos_of_convex := CFT.FixGauge.scal_pos_of_convex

/-- VII.8-C(ダンベル、完(外)):質量ゼロのカイラルなモード(内部 Dirac 作用素の核)。運動学:楕円体 S⁹(凸)。作用:内部の Dirac の作用。力学:核は 0:内部の核からは出ない(否定的) -/
alias VII_8C_ellipsoid_II_pos := CFT.FixGauge.ellipsoid_II_pos

/-- VII.8-C(ダンベル、完(外)):質量ゼロのカイラルなモード(内部 Dirac 作用素の核)。運動学:楕円体 S⁹(凸)。作用:内部の Dirac の作用。力学:核は 0:内部の核からは出ない(否定的) -/
alias VII_8C_no_massless_internal := CFT.FixGauge.no_massless_internal

/-- VII.9(ダンベル、完):ひねりの電荷 q = 1/2 でゼロモード 1 個。運動学:単位 S² の枠とスピン接続。作用:Dirac(U(1)_F = ½ω でひねる)。力学:q = 1/2、ゼロモードはちょうど 1 個 -/
alias VII_9_spin_curvature := CFT.FixGauge.spin_curvature

/-- VII.9(ダンベル、完):ひねりの電荷 q = 1/2 でゼロモード 1 個。運動学:単位 S² の枠とスピン接続。作用:Dirac(U(1)_F = ½ω でひねる)。力学:q = 1/2、ゼロモードはちょうど 1 個 -/
alias VII_9_twist_charge := CFT.FixGauge.twist_charge

/-- VII.9(ダンベル、完):ひねりの電荷 q = 1/2 でゼロモード 1 個。運動学:単位 S² の枠とスピン接続。作用:Dirac(U(1)_F = ½ω でひねる)。力学:q = 1/2、ゼロモードはちょうど 1 個 -/
alias VII_9_twist_zero_mode := CFT.FixGauge.twist_zero_mode


/-! ## α-VIII 弦理論との接点 -/

/-- VIII.2(一般、完(外)):標準埋め込み、α′ 項の消失(Euclid の断面、Ω ∈ so(4))。運動学:Euclid 化したダンベルのスピン接続。作用:ヘテロティックの O(α′) の作用。力学:4 つの場の方程式で α′ 項が消える -/
alias VIII_2_all_alpha_terms_vanish := CFT.EmbeddingEOM.all_alpha_terms_vanish

/-- VIII.2(一般、完(外)):標準埋め込み、α′ 項の消失(Euclid の断面、Ω ∈ so(4))。運動学:Euclid 化したダンベルのスピン接続。作用:ヘテロティックの O(α′) の作用。力学:4 つの場の方程式で α′ 項が消える -/
alias VIII_2_ymH_embed_iff := CFT.FixGauge.ymH_embed_iff

/-- VIII.2(一般、完(外)):標準埋め込み、α′ 項の消失(Euclid の断面、Ω ∈ so(4))。運動学:Euclid 化したダンベルのスピン接続。作用:ヘテロティックの O(α′) の作用。力学:4 つの場の方程式で α′ 項が消える -/
alias VIII_2_iota_antisymm := CFT.FixGauge.iota_antisymm

/-- VIII.3(ダンベル、完(外)):アトラクターとエントロピー。運動学:首(磁荷)。作用:Einstein–ディラトン–Maxwell(a = 1)。力学:磁荷だけではディラトンが逃げる -/
alias VIII_3_string_attractor := CFT.StringAttractor.string_attractor

/-- VIII.3(ダンベル、完(外)):アトラクターとエントロピー。運動学:首(磁荷)。作用:Einstein–ディラトン–Maxwell(a = 1)。力学:磁荷だけではディラトンが逃げる -/
alias VIII_3_no_attractor_magnetic := CFT.StringAttractor.no_attractor_magnetic

/-- VIII.3(ダンベル、完(外)):アトラクターとエントロピー。運動学:首(磁荷)。作用:Einstein–ディラトン–Maxwell(a = 1)。力学:磁荷だけではディラトンが逃げる -/
alias VIII_3_veff_min := CFT.StringAttractor.veff_min

/-- VIII.5(ダンベル、完(外)):ℓ*² = α′/4、WZW 準位 k = 1/4。運動学:首の半径。作用:弦の有効作用。力学:ℓ*² = α′/4 -/
alias VIII_5_ell_witten := CFT.Z38.ell_witten

/-- VIII.5(ダンベル、完(外)):ℓ*² = α′/4、WZW 準位 k = 1/4。運動学:首の半径。作用:弦の有効作用。力学:ℓ*² = α′/4 -/
alias VIII_5_wzw_level := CFT.Z38.wzw_level

/-- VIII.7(ダンベル、完(外)):Killing スピノル不存在(超対称性の障害)、帽子の領域だけの仮定で。運動学:帽子 a = ℓ cos η(0 ≤ η < π/2)。作用:EYM。力学:Killing スピノルはない -/
alias VIII_7_cap_unique := CFT.Z44Cap.cap_unique

/-- VIII.7(ダンベル、完(外)):Killing スピノル不存在(超対称性の障害)、帽子の領域だけの仮定で。運動学:帽子 a = ℓ cos η(0 ≤ η < π/2)。作用:EYM。力学:Killing スピノルはない -/
alias VIII_7_no_killing_spinor_cap := CFT.Z44Cap.no_killing_spinor_cap

/-- VIII.7(ダンベル、完(外)):Killing スピノル不存在(超対称性の障害)、帽子の領域だけの仮定で。運動学:帽子 a = ℓ cos η(0 ≤ η < π/2)。作用:EYM。力学:Killing スピノルはない -/
alias VIII_7_cap_unique_local := CFT.FixGeo.cap_unique_local

/-- VIII.7(ダンベル、完(外)):Killing スピノル不存在(超対称性の障害)、帽子の領域だけの仮定で。運動学:帽子 a = ℓ cos η(0 ≤ η < π/2)。作用:EYM。力学:Killing スピノルはない -/
alias VIII_7_no_killing_spinor_local := CFT.FixGeo.no_killing_spinor_local


/-! ## α-IX 作用原理からの帰結 -/

/-- IX.0(ダンベル、完):縮約した作用の第一変分 ⇔ α の五つの方程式(4 次元の全成分と照合)。運動学:ダンベルの ansatz。作用:EYM + GHY(縮約)。力学:α の方程式 -/
alias IX_0_el_iff_alpha := CFT.S2.el_iff_alpha

/-- IX.0(ダンベル、完):縮約した作用の第一変分 ⇔ α の五つの方程式(4 次元の全成分と照合)。運動学:ダンベルの ansatz。作用:EYM + GHY(縮約)。力学:α の方程式 -/
alias IX_0_full_4d_iff_alpha := CFT.S2M.full_4d_iff_alpha

/-- IX.0(ダンベル、完):縮約した作用の第一変分 ⇔ α の五つの方程式(4 次元の全成分と照合)。運動学:ダンベルの ansatz。作用:EYM + GHY(縮約)。力学:α の方程式 -/
alias IX_0_palais_free := CFT.S2M.palais_free

/-- IX.1(一般、完):電磁気学の第一変分。運動学:Minkowski。作用:Maxwell。力学:Maxwell の方程式 -/
alias IX_1_first_variation := CFT.Classical.first_variation

/-- IX.2(一般、完):∇·E = ρ、∇×B = J + ∂_tE。運動学:Minkowski。作用:Maxwell。力学:Gauss・Ampère -/
alias IX_2_gauss := CFT.Classical.gauss

/-- IX.2(一般、完):∇·E = ρ、∇×B = J + ∂_tE。運動学:Minkowski。作用:Maxwell。力学:Gauss・Ampère -/
alias IX_2_ampere := CFT.Classical.ampere

/-- IX.3(一般、完):Bianchi、Faraday、電荷の保存。運動学:Minkowski。作用:Maxwell。力学:Faraday -/
alias IX_3_bianchi_div := CFT.Classical.bianchi_div

/-- IX.3(一般、完):Bianchi、Faraday、電荷の保存。運動学:Minkowski。作用:Maxwell。力学:Faraday -/
alias IX_3_faraday := CFT.Classical.faraday

/-- IX.4(一般、完):SU(2) = Q の Yang–Mills の第一変分。運動学:SU(2)。作用:YM。力学:YM 方程式 -/
alias IX_4_ym_first_variation := CFT.IXYM.ym_first_variation

/-- IX.4(一般、完):SU(2) = Q の Yang–Mills の第一変分。運動学:SU(2)。作用:YM。力学:YM 方程式 -/
alias IX_4_u1_projection := CFT.IXYM.u1_projection

/-- IX.5(一般、完):電荷と磁荷の区別。運動学:Minkowski。作用:Maxwell。力学:Gauss の積分 -/
alias IX_5_gauss_integral := CFT.Classical.gauss_integral

/-- IX.6(一般、完):応力テンソルの保存。運動学:Minkowski。作用:Maxwell。力学:∂T = −FJ -/
alias IX_6_stress_divergence := CFT.Classical.stress_divergence

/-- IX.7(一般、完):荷電した塵の Lorentz 力。運動学:Minkowski。作用:Maxwell + 塵。力学:Lorentz 力 -/
alias IX_7_dust_lorentz := CFT.Classical.dust_lorentz

/-- IX.8(一般、完):粒子の Euler–Lagrange 方程式。運動学:Minkowski。作用:粒子の作用。力学:運動方程式 -/
alias IX_8_particle_el := CFT.Classical.particle_el

/-- IX.9(一般、完):Hamilton 形式と質量殻。運動学:質量殻。作用:粒子の作用。力学:Hamilton の式 -/
alias IX_9_hamilton := CFT.Classical.hamilton

/-- IX.9(一般、完):Hamilton 形式と質量殻。運動学:質量殻。作用:粒子の作用。力学:Hamilton の式 -/
alias IX_9_mass_shell := CFT.Classical.mass_shell

/-- IX.10(ダンベル、完(橋)):球対称の縮約 S₂、U = 2 − 2ℓ²/Φ。運動学:首(球対称)。作用:EYM。力学:2 次元のディラトン重力 -/
alias IX_10_reduction_identity := CFT.JT.reduction_identity

/-- IX.10(ダンベル、完(橋)):球対称の縮約 S₂、U = 2 − 2ℓ²/Φ。運動学:首(球対称)。作用:EYM。力学:2 次元のディラトン重力 -/
alias IX_10_potential_from_YM := CFT.JT.potential_from_YM

/-- IX.11(ダンベル、完):首 Φ = ℓ² は厳密な解(AdS₂)、4 次元の Einstein 方程式でも。運動学:首 AdS₂ × S²(Ricci の固有値 (−1, −1, 1, 1)/ℓ²)。作用:IX.10 の作用、EYM。力学:U = 0、R = −2/ℓ²、G = 8πG T の 4 成分 ⇔ ℓ² = 4πG/g² -/
alias IX_11_neck_exact := CFT.JT.neck_exact

/-- IX.11(ダンベル、完):首 Φ = ℓ² は厳密な解(AdS₂)、4 次元の Einstein 方程式でも。運動学:首 AdS₂ × S²(Ricci の固有値 (−1, −1, 1, 1)/ℓ²)。作用:IX.10 の作用、EYM。力学:U = 0、R = −2/ℓ²、G = 8πG T の 4 成分 ⇔ ℓ² = 4πG/g² -/
alias IX_11_neck_metric_curvature := CFT.JT.neck_metric_curvature

/-- IX.11(ダンベル、完):首 Φ = ℓ² は厳密な解(AdS₂)、4 次元の Einstein 方程式でも。運動学:首 AdS₂ × S²(Ricci の固有値 (−1, −1, 1, 1)/ℓ²)。作用:IX.10 の作用、EYM。力学:U = 0、R = −2/ℓ²、G = 8πG T の 4 成分 ⇔ ℓ² = 4πG/g² -/
alias IX_11_neck_einstein := CFT.FixGeo.neck_einstein

/-- IX.12(ダンベル、完):JT への展開(余りまで厳密)。運動学:首。作用:IX.10 の作用。力学:JT -/
alias IX_12_jt_expansion := CFT.JT.jt_expansion

/-- IX.12(ダンベル、完):JT への展開(余りまで厳密)。運動学:首。作用:IX.10 の作用。力学:JT -/
alias IX_12_jt_kinetic := CFT.JT.jt_kinetic

/-- IX.13(ダンベル、完(外)):基底のエントロピー S₀ = πℓ²/G = 4π²/g²(ディラトンのない EYM)。運動学:首。作用:EYM。力学:S₀ -/
alias IX_13_ground_entropy := CFT.JT.ground_entropy

/-- IX.14(ダンベル、完(外)):Schwarzian の熱力学(長い首、L/ℓ ≫ 1)。運動学:首の JT dilaton と接合。作用:JT。力学:対称な dilaton = 永遠のブラックホール、E(β)、S(T) -/
alias IX_14_jt_neck_solution := CFT.FixNeck.jt_neck_solution

/-- IX.14(ダンベル、完(外)):Schwarzian の熱力学(長い首、L/ℓ ≫ 1)。運動学:首の JT dilaton と接合。作用:JT。力学:対称な dilaton = 永遠のブラックホール、E(β)、S(T) -/
alias IX_14_no_static_dilaton := CFT.FixNeck.no_static_dilaton

/-- IX.14(ダンベル、完(外)):Schwarzian の熱力学(長い首、L/ℓ ≫ 1)。運動学:首の JT dilaton と接合。作用:JT。力学:対称な dilaton = 永遠のブラックホール、E(β)、S(T) -/
alias IX_14_junction_near_boundary := CFT.FixNeck.junction_near_boundary

/-- IX.14(ダンベル、完(外)):Schwarzian の熱力学(長い首、L/ℓ ≫ 1)。運動学:首の JT dilaton と接合。作用:JT。力学:対称な dilaton = 永遠のブラックホール、E(β)、S(T) -/
alias IX_14_schwarzian_energy := CFT.JT.schwarzian_energy

/-- IX.15(ダンベル、完(外)):1 ループ:m²ℓ² = −1 < −1/4、Δ = ½ ± i√3/2。運動学:首。作用:W の 2 次の作用。力学:BF 限界を下回る -/
alias IX_15_delta_roots := CFT.JT.delta_roots

/-- IX.15(ダンベル、完(外)):1 ループ:m²ℓ² = −1 < −1/4、Δ = ½ ± i√3/2。運動学:首。作用:W の 2 次の作用。力学:BF 限界を下回る -/
alias IX_15_neck_mode_below_BF := CFT.JT.neck_mode_below_BF

/-- IX.16(一般、完(橋)):完全流体:連続の式と相対論的 Euler。運動学:Minkowski。作用:流体。力学:Euler 方程式 -/
alias IX_16_fluid_euler := CFT.Fluid.fluid_euler

/-- IX.17(ダンベル、完):帽子は輻射の宇宙(p = ρ/3)、最大の半径は首の半径 ℓ。運動学:帽子 a = ℓ cos η。作用:YM(Friedmann)。力学:閉じた輻射 FRW、a′² + a² = (8πG/3)ρa⁴ = ℓ² -/
alias IX_17_cap_radiation := CFT.Fluid.cap_radiation

/-- IX.17(ダンベル、完):帽子は輻射の宇宙(p = ρ/3)、最大の半径は首の半径 ℓ。運動学:帽子 a = ℓ cos η。作用:YM(Friedmann)。力学:閉じた輻射 FRW、a′² + a² = (8πG/3)ρa⁴ = ℓ² -/
alias IX_17_cap_stress := CFT.EYM.cap_stress

/-- IX.17(ダンベル、完):帽子は輻射の宇宙(p = ρ/3)、最大の半径は首の半径 ℓ。運動学:帽子 a = ℓ cos η。作用:YM(Friedmann)。力学:閉じた輻射 FRW、a′² + a² = (8πG/3)ρa⁴ = ℓ² -/
alias IX_17_cap_rho := CFT.FixGeo.cap_rho

/-- IX.17(ダンベル、完):帽子は輻射の宇宙(p = ρ/3)、最大の半径は首の半径 ℓ。運動学:帽子 a = ℓ cos η。作用:YM(Friedmann)。力学:閉じた輻射 FRW、a′² + a² = (8πG/3)ρa⁴ = ℓ² -/
alias IX_17_cap_friedmann_l := CFT.FixGeo.cap_friedmann_l

/-- IX.18(一般、完(橋)):Kelvin の循環定理の局所形。運動学:流体。作用:流体。力学:L_uω = 0 -/
alias IX_18_kelvin := CFT.Fluid.kelvin

/-- IX.19(一般、完(橋)):理想 MHD の磁束凍結。運動学:流体。作用:MHD。力学:L_uF = 0 -/
alias IX_19_flux_freezing := CFT.Fluid.flux_freezing

/-- IX.20(一般、完(橋)):ヘリシティの釣り合い。運動学:Minkowski。作用:Maxwell。力学:ヘリシティの式 -/
alias IX_20_helicity_balance := CFT.Fluid.helicity_balance

/-- IX.21(一般、完(外)):Hawking 温度、RN の T。運動学:地平線。作用:Euclid の EH。力学:T = κ/2π -/
alias IX_21_conical_period := CFT.Thermo.conical_period

/-- IX.21(一般、完(外)):Hawking 温度、RN の T。運動学:地平線。作用:Euclid の EH。力学:T = κ/2π -/
alias IX_21_rn_slope := CFT.Thermo.rn_slope

/-- IX.22(ダンベル、完):Euclid の首は H²(曲率 −1/ℓ²)。運動学:首。作用:—。力学:— -/
alias IX_22_euclid_neck_curvature := CFT.Thermo.euclid_neck_curvature

/-- IX.23(一般、完):第一法則と Smarr、極限で T = 0。運動学:磁荷の RN。作用:EYM。力学:第一法則 -/
alias IX_23_first_law := CFT.Thermo.first_law

/-- IX.23(一般、完):第一法則と Smarr、極限で T = 0。運動学:磁荷の RN。作用:EYM。力学:第一法則 -/
alias IX_23_smarr := CFT.Thermo.smarr

/-- IX.24(ダンベル、完(外)):Euclid 作用(磁荷):I = β(M − TS)(正準集団)、S = A/4。運動学:首の磁荷。作用:Euclid の EH + GHY + Maxwell。力学:磁荷を固定した正準集団 -/
alias IX_24_maxwell_magnetic := CFT.FixThermo.maxwell_magnetic

/-- IX.24(ダンベル、完(外)):Euclid 作用(磁荷):I = β(M − TS)(正準集団)、S = A/4。運動学:首の磁荷。作用:Euclid の EH + GHY + Maxwell。力学:磁荷を固定した正準集団 -/
alias IX_24_magnetic_action := CFT.FixThermo.magnetic_action

/-- IX.25(ダンベル、完):Tolman–Ehrenfest:∇_μT^μ_x = 0 から、首では T = T₀/cosh(x/ℓ)。運動学:首の静的な計量 −cosh²(x/ℓ)dt² + dx² + ℓ²dΩ²。作用:輻射。力学:p′ = −(ρ + p)N′/N、TN が一定 -/
alias IX_25_christoffel_static := CFT.FixGeo.christoffel_static

/-- IX.25(ダンベル、完):Tolman–Ehrenfest:∇_μT^μ_x = 0 から、首では T = T₀/cosh(x/ℓ)。運動学:首の静的な計量 −cosh²(x/ℓ)dt² + dx² + ℓ²dΩ²。作用:輻射。力学:p′ = −(ρ + p)N′/N、TN が一定 -/
alias IX_25_static_euler := CFT.FixGeo.static_euler

/-- IX.25(ダンベル、完):Tolman–Ehrenfest:∇_μT^μ_x = 0 から、首では T = T₀/cosh(x/ℓ)。運動学:首の静的な計量 −cosh²(x/ℓ)dt² + dx² + ℓ²dΩ²。作用:輻射。力学:p′ = −(ρ + p)N′/N、TN が一定 -/
alias IX_25_tolman := CFT.Thermo.tolman

/-- IX.25(ダンベル、完):Tolman–Ehrenfest:∇_μT^μ_x = 0 から、首では T = T₀/cosh(x/ℓ)。運動学:首の静的な計量 −cosh²(x/ℓ)dt² + dx² + ℓ²dΩ²。作用:輻射。力学:p′ = −(ρ + p)N′/N、TN が一定 -/
alias IX_25_neck_tolman := CFT.FixGeo.neck_tolman

/-- IX.26(一般、完):KMS 条件(有限次元)。運動学:有限系。作用:—。力学:KMS -/
alias IX_26_kms := CFT.Stat.kms

/-- IX.27(一般、完(外)):Jüttner 分布の非相対論の極限、Q の座標 m/E。運動学:質量殻。作用:—。力学:Jüttner → Maxwell -/
alias IX_27_juttner_to_maxwell := CFT.FixThermo.juttner_to_maxwell

/-- IX.27(一般、完(外)):Jüttner 分布の非相対論の極限、Q の座標 m/E。運動学:質量殻。作用:—。力学:Jüttner → Maxwell -/
alias IX_27_nr_monotone := CFT.FixThermo.nr_monotone

/-- IX.27(一般、完(外)):Jüttner 分布の非相対論の極限、Q の座標 m/E。運動学:質量殻。作用:—。力学:Jüttner → Maxwell -/
alias IX_27_q_coordinate := CFT.Thermo.q_coordinate

/-- IX.28(一般、完):Planck の積分 π⁴/15、Stefan–Boltzmann。運動学:輻射。作用:—。力学:π⁴/15 -/
alias IX_28_bose_integral := CFT.Stat.bose_integral

/-- IX.28(一般、完):Planck の積分 π⁴/15、Stefan–Boltzmann。運動学:輻射。作用:—。力学:π⁴/15 -/
alias IX_28_stefan_boltzmann := CFT.Stat.stefan_boltzmann

/-- IX.29(ダンベル、完(外)):Schwarzian の状態密度と熱力学の整合(厳密な ρ ∝ sinh(2π√(2CE)))。運動学:首の JT。作用:JT。力学:1/T = 4π²C coth x/x、主要項との差は指数関数的に小さい、正準集団との差 3/(4π²CT) -/
alias IX_29_laplace_exponent := CFT.Thermo.laplace_exponent

/-- IX.29(ダンベル、完(外)):Schwarzian の状態密度と熱力学の整合(厳密な ρ ∝ sinh(2π√(2CE)))。運動学:首の JT。作用:JT。力学:1/T = 4π²C coth x/x、主要項との差は指数関数的に小さい、正準集団との差 3/(4π²CT) -/
alias IX_29_micro_temperature := CFT.Thermo.micro_temperature

/-- IX.29(ダンベル、完(外)):Schwarzian の状態密度と熱力学の整合(厳密な ρ ∝ sinh(2π√(2CE)))。運動学:首の JT。作用:JT。力学:1/T = 4π²C coth x/x、主要項との差は指数関数的に小さい、正準集団との差 3/(4π²CT) -/
alias IX_29_micro_exact_deriv := CFT.FixDyn.micro_exact_deriv

/-- IX.29(ダンベル、完(外)):Schwarzian の状態密度と熱力学の整合(厳密な ρ ∝ sinh(2π√(2CE)))。運動学:首の JT。作用:JT。力学:1/T = 4π²C coth x/x、主要項との差は指数関数的に小さい、正準集団との差 3/(4π²CT) -/
alias IX_29_coth_eq := CFT.FixDyn.coth_eq

/-- IX.29(ダンベル、完(外)):Schwarzian の状態密度と熱力学の整合(厳密な ρ ∝ sinh(2π√(2CE)))。運動学:首の JT。作用:JT。力学:1/T = 4π²C coth x/x、主要項との差は指数関数的に小さい、正準集団との差 3/(4π²CT) -/
alias IX_29_micro_exact_bound := CFT.FixDyn.micro_exact_bound

/-- IX.29(ダンベル、完(外)):Schwarzian の状態密度と熱力学の整合(厳密な ρ ∝ sinh(2π√(2CE)))。運動学:首の JT。作用:JT。力学:1/T = 4π²C coth x/x、主要項との差は指数関数的に小さい、正準集団との差 3/(4π²CT) -/
alias IX_29_canonical_vs_micro := CFT.FixDyn.canonical_vs_micro

/-- IX.30(一般、完):揺動散逸の関係(有限系、KMS から)。運動学:有限系。作用:—。力学:S(ω) = coth(βω/2)χ″(ω) -/
alias IX_30_kms_weights := CFT.FixThermo.kms_weights

/-- IX.30(一般、完):揺動散逸の関係(有限系、KMS から)。運動学:有限系。作用:—。力学:S(ω) = coth(βω/2)χ″(ω) -/
alias IX_30_fdt_spectral := CFT.FixThermo.fdt_spectral

/-- IX.31(一般、完(外)):焦点を結ぶ定理。運動学:ヌルの測地線。作用:Einstein(NEC)。力学:θ → −∞ -/
alias IX_31_focusing := CFT.Second.focusing

/-- IX.32(運動学、完):Euclid の首の測地線の偏差:Lyapunov 指数 1/ℓ(コンパクトな H²/Γ ではないのでエルゴード性は主張しない)。運動学:Euclid の首(曲率 −1/ℓ²、IX.22)。作用:—。力学:J = cosh(s/ℓ) ≥ e^{s/ℓ}/2 -/
alias IX_32_jacobi_neck := CFT.FixGeo.jacobi_neck

/-- IX.32(運動学、完):Euclid の首の測地線の偏差:Lyapunov 指数 1/ℓ(コンパクトな H²/Γ ではないのでエルゴード性は主張しない)。運動学:Euclid の首(曲率 −1/ℓ²、IX.22)。作用:—。力学:J = cosh(s/ℓ) ≥ e^{s/ℓ}/2 -/
alias IX_32_lyapunov_neck := CFT.FixGeo.lyapunov_neck

/-- IX.33(ダンベル、完):相の比較(磁荷の正準集団)と W の凝縮。運動学:首につながる RN の枝。作用:IX.24 の Euclid 作用。力学:首につながる小さい枝が選ばれる -/
alias IX_33_small_branch_preferred := CFT.FixThermo.small_branch_preferred

/-- IX.33(ダンベル、完):相の比較(磁荷の正準集団)と W の凝縮。運動学:首につながる RN の枝。作用:IX.24 の Euclid 作用。力学:首につながる小さい枝が選ばれる -/
alias IX_33_heat_capacity_sign := CFT.FixThermo.heat_capacity_sign

/-- IX.33(ダンベル、完):相の比較(磁荷の正準集団)と W の凝縮。運動学:首につながる RN の枝。作用:IX.24 の Euclid 作用。力学:首につながる小さい枝が選ばれる -/
alias IX_33_landau := CFT.Second.landau

/-- IX.34(ダンベル、完(外)):はりねずみの次数 = 1、π₂(S²) = ℤ。運動学:帽子の単極子 n̂ = x̂。作用:YM。力学:次数 = 磁荷 -/
alias IX_34_hedgehog_jacobian := CFT.FixThermo.hedgehog_jacobian

/-- IX.34(ダンベル、完(外)):はりねずみの次数 = 1、π₂(S²) = ℤ。運動学:帽子の単極子 n̂ = x̂。作用:YM。力学:次数 = 磁荷 -/
alias IX_34_hedgehog_degree := CFT.FixThermo.hedgehog_degree


/-! ## α-X 統一と整合性 -/

/-- X.1(一般、完(橋)):Noether の定理を作用から一般に。運動学:有限自由度。作用:L(q, q̇)。力学:Σ p_iK_i の保存 -/
alias X_1_noether := CFT.FixUnify.noether

/-- X.1(一般、完(橋)):Noether の定理を作用から一般に。運動学:有限自由度。作用:L(q, q̇)。力学:Σ p_iK_i の保存 -/
alias X_1_cyclic_from_noether := CFT.FixUnify.cyclic_from_noether

/-- X.1(一般、完(橋)):Noether の定理を作用から一般に。運動学:有限自由度。作用:L(q, q̇)。力学:Σ p_iK_i の保存 -/
alias X_1_charge_conservation := CFT.Unify.charge_conservation

/-- X.2(ダンベル、完(橋)):幾何光学 = HJ = WKB(首の波面)。運動学:首 −dt² + cos²(t/ℓ)dz²。作用:波動の作用。力学:アイコナール = 質量ゼロの HJ -/
alias X_2_wkb_2d := CFT.FixUnify.wkb_2d

/-- X.2(ダンベル、完(橋)):幾何光学 = HJ = WKB(首の波面)。運動学:首 −dt² + cos²(t/ℓ)dz²。作用:波動の作用。力学:アイコナール = 質量ゼロの HJ -/
alias X_2_neck_eikonal := CFT.FixUnify.neck_eikonal

/-- X.3(一般、完(橋)):ゲージ場 = 接続、力 = 曲率。運動学:U(1)、SU(2)、重力。作用:—。力学:— -/
alias X_3_abelian_gauge_invariance := CFT.Unify.abelian_gauge_invariance

/-- X.4(ダンベル、完):質量(閉じたダンベルでは Misner–Sharp、ADM は定義されない)。運動学:帽子・首。作用:EYM(Friedmann)。力学:m = (4π/3)ρR³、dm = −p dV -/
alias X_4_cap_ms_mass := CFT.FixUnify.cap_ms_mass

/-- X.4(ダンベル、完):質量(閉じたダンベルでは Misner–Sharp、ADM は定義されない)。運動学:帽子・首。作用:EYM(Friedmann)。力学:m = (4π/3)ρR³、dm = −p dV -/
alias X_4_cap_first_law := CFT.FixUnify.cap_first_law

/-- X.4(ダンベル、完):質量(閉じたダンベルでは Misner–Sharp、ADM は定義されない)。運動学:帽子・首。作用:EYM(Friedmann)。力学:m = (4π/3)ρR³、dm = −p dV -/
alias X_4_weak_discontinuity_no_mass := CFT.Unify.weak_discontinuity_no_mass

/-- X.5(ダンベル、完(外)):色電荷 Q^a の接合面での保存。運動学:Witten の ansatz。作用:YM。力学:F_tr の交換子が消え Q = 0 -/
alias X_5_witten_Ftr := CFT.FixUnify.witten_Ftr

/-- X.5(ダンベル、完(外)):色電荷 Q^a の接合面での保存。運動学:Witten の ansatz。作用:YM。力学:F_tr の交換子が消え Q = 0 -/
alias X_5_color_charge_vanishes := CFT.FixUnify.color_charge_vanishes

/-- X.6(—、完):すべての最終定理に非空性(実関数版の最終定理は部分積分で仮定が満たせることを示す。RealLine 版は仮定が満たせないので置き換えた)。運動学:—。作用:—。力学:— -/
alias X_6_nonempty_cap := CFT.Unify.nonempty_cap

/-- X.6(—、完):すべての最終定理に非空性(実関数版の最終定理は部分積分で仮定が満たせることを示す。RealLine 版は仮定が満たせないので置き換えた)。運動学:—。作用:—。力学:— -/
alias X_6_nonempty_magnetic := CFT.FixThermo.nonempty_magnetic

/-- X.6(—、完):すべての最終定理に非空性(実関数版の最終定理は部分積分で仮定が満たせることを示す。RealLine 版は仮定が満たせないので置き換えた)。運動学:—。作用:—。力学:— -/
alias X_6_nonempty_window := CFT.FixNeck.nonempty_window

/-- X.6(—、完):すべての最終定理に非空性(実関数版の最終定理は部分積分で仮定が満たせることを示す。RealLine 版は仮定が満たせないので置き換えた)。運動学:—。作用:—。力学:— -/
alias X_6_rj_color_nonempty := CFT.RJ.rj_color_nonempty

/-- X.6(—、完):すべての最終定理に非空性(実関数版の最終定理は部分積分で仮定が満たせることを示す。RealLine 版は仮定が満たせないので置き換えた)。運動学:—。作用:—。力学:— -/
alias X_6_rj_slice_nonempty := CFT.RJ.rj_slice_nonempty

/-- X.6(—、完):すべての最終定理に非空性(実関数版の最終定理は部分積分で仮定が満たせることを示す。RealLine 版は仮定が満たせないので置き換えた)。運動学:—。作用:—。力学:— -/
alias X_6_rj_null_witness := CFT.RJ.rj_null_witness

/-- X.7(ダンベル、完):くさび(二つの波面のあいだ)の大域的な発展:拘束から (r_u/Ω)_u = −2W_u²/(rΩ) ≤ 0、波面では r_u = 0(首)、r_v = 0(帽子)なので、くさび全体で r_u ≤ 0、r_v ≤ 0(捕捉領域、定理)。数値(numerics/wedge_evolution.py、2 次収束):[W_u] = 1/√2 は一定、r → 0 に崩壊、特異面は空間的、接合球の寿命は固有時間で約 1.271ℓ、W は 1 を越えて約 1.05。運動学:帽子・首・接合。作用:EYM(二重ヌル)。力学:くさびは捕捉領域で、首は帽子の崩壊に飲み込まれる -/
alias X_7_oc_raychaudhuri := CFT.OC.oc_raychaudhuri

/-- X.7(ダンベル、完):くさび(二つの波面のあいだ)の大域的な発展:拘束から (r_u/Ω)_u = −2W_u²/(rΩ) ≤ 0、波面では r_u = 0(首)、r_v = 0(帽子)なので、くさび全体で r_u ≤ 0、r_v ≤ 0(捕捉領域、定理)。数値(numerics/wedge_evolution.py、2 次収束):[W_u] = 1/√2 は一定、r → 0 に崩壊、特異面は空間的、接合球の寿命は固有時間で約 1.271ℓ、W は 1 を越えて約 1.05。運動学:帽子・首・接合。作用:EYM(二重ヌル)。力学:くさびは捕捉領域で、首は帽子の崩壊に飲み込まれる -/
alias X_7_oc_raychaudhuri_sign := CFT.OC.oc_raychaudhuri_sign

/-- X.7(ダンベル、完):くさび(二つの波面のあいだ)の大域的な発展:拘束から (r_u/Ω)_u = −2W_u²/(rΩ) ≤ 0、波面では r_u = 0(首)、r_v = 0(帽子)なので、くさび全体で r_u ≤ 0、r_v ≤ 0(捕捉領域、定理)。数値(numerics/wedge_evolution.py、2 次収束):[W_u] = 1/√2 は一定、r → 0 に崩壊、特異面は空間的、接合球の寿命は固有時間で約 1.271ℓ、W は 1 を越えて約 1.05。運動学:帽子・首・接合。作用:EYM(二重ヌル)。力学:くさびは捕捉領域で、首は帽子の崩壊に飲み込まれる -/
alias X_7_oc_trapped := CFT.OC.oc_trapped

/-- X.8(ダンベル、完):閉じたダンベルの全エネルギーは 0:Misner–Sharp 質量 m = R(1 − R′²)/(2G) は m′ = 4πR²ρR′、両端の極で m = 0 なので ∫m′ = 0。帽子の m = ℓ sin³y/(2G) は赤道で首の ℓ/(2G) と一致。運動学:ダンベル全体(閉じた空間)。作用:EYM(ハミルトン拘束)。力学:全エネルギー 0 -/
alias X_8_rr_ms_constraint := CFT.RR.rr_ms_constraint

/-- X.8(ダンベル、完):閉じたダンベルの全エネルギーは 0:Misner–Sharp 質量 m = R(1 − R′²)/(2G) は m′ = 4πR²ρR′、両端の極で m = 0 なので ∫m′ = 0。帽子の m = ℓ sin³y/(2G) は赤道で首の ℓ/(2G) と一致。運動学:ダンベル全体(閉じた空間)。作用:EYM(ハミルトン拘束)。力学:全エネルギー 0 -/
alias X_8_rr_closed_total_zero := CFT.RR.rr_closed_total_zero

/-- X.8(ダンベル、完):閉じたダンベルの全エネルギーは 0:Misner–Sharp 質量 m = R(1 − R′²)/(2G) は m′ = 4πR²ρR′、両端の極で m = 0 なので ∫m′ = 0。帽子の m = ℓ sin³y/(2G) は赤道で首の ℓ/(2G) と一致。運動学:ダンベル全体(閉じた空間)。作用:EYM(ハミルトン拘束)。力学:全エネルギー 0 -/
alias X_8_rr_cap_mass := CFT.RR.rr_cap_mass

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_on_hyperboloid := CFT.BridgeClock.on_hyperboloid

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_neck_gaussian := CFT.BridgeClock.neck_gaussian

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_cap_gaussian := CFT.BridgeClock.cap_gaussian

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_two_events := CFT.BridgeClock.two_events

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_same_point := CFT.BridgeClock.same_point

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_static_clock := CFT.BridgeClock.static_clock

/-- X.9(ダンベル、完):共通の時計:初期の断面からのガウス正規時間(帽子 τ_c = ℓ sin η、首 t)。帽子の崩壊 ℓ と首の焦点 πℓ/2 は別の出来事。運動学:首の AdS₂ の埋め込み(同期・静的の座標)、帽子 a = ℓ cos η。作用:EYM(帽子と首の解)。力学:g_tt = −1、sin τ = sin(t/ℓ) sin u、首の中心の静的な時計 = ガウス時間 -/
alias X_9_neck_centre_clock := CFT.BridgeClock.neck_centre_clock

/-- X.10(ダンベル、完(外)):随伴 Higgs の出どころ(候補の同定):S⁹ の楕円体の変形は SO(10) の対称トレースレス表現 54 にあたり、Pati–Salam の部分群のもとで 54 = (1,1) + (3,3) + (1,20′) + (4,6)。(3,3) = 1 + 3 + 5 は対角の SU(2) の随伴 3 を含む。随伴 Higgs は内部空間の形の揺らぎの中にある(表現の分解は外部、Lean は次元の数え方)。運動学:内部空間 S⁹ の形の揺らぎ。作用:—。力学:随伴 3 は 54 の中にある -/
alias X_10_ol_rep_count := CFT.OL.ol_rep_count

/-- X.10-B(ダンベル、完(外)):形の揺らぎの二次の項:球面 Sⁿ を法線の方向に k 次の調和関数で変形すると、一次では計量の共形な変化になる。共形の方向の第二変分の係数は λ_k − n = (k − 1)(k + n)。k = 1 は 0(共形変換、形は変わらない)、k = 2(楕円体)は n + 2、S⁹ では 11。54 個の成分はすべて同じ係数をもつ(SO(10) の対称性)ので、二次の項は方向を選ばない(第二変分の式は外部:山辺の汎関数)。運動学:内部空間 S⁹。作用:EH(内部空間の曲率)。力学:54 は二次では縮退、係数 11 -/
alias X_10B_os_yamabe_factor := CFT.OS.os_yamabe_factor

/-- X.10-B(ダンベル、完(外)):形の揺らぎの二次の項:球面 Sⁿ を法線の方向に k 次の調和関数で変形すると、一次では計量の共形な変化になる。共形の方向の第二変分の係数は λ_k − n = (k − 1)(k + n)。k = 1 は 0(共形変換、形は変わらない)、k = 2(楕円体)は n + 2、S⁹ では 11。54 個の成分はすべて同じ係数をもつ(SO(10) の対称性)ので、二次の項は方向を選ばない(第二変分の式は外部:山辺の汎関数)。運動学:内部空間 S⁹。作用:EH(内部空間の曲率)。力学:54 は二次では縮退、係数 11 -/
alias X_10B_os_yamabe_l1 := CFT.OS.os_yamabe_l1

/-- X.10-B(ダンベル、完(外)):形の揺らぎの二次の項:球面 Sⁿ を法線の方向に k 次の調和関数で変形すると、一次では計量の共形な変化になる。共形の方向の第二変分の係数は λ_k − n = (k − 1)(k + n)。k = 1 は 0(共形変換、形は変わらない)、k = 2(楕円体)は n + 2、S⁹ では 11。54 個の成分はすべて同じ係数をもつ(SO(10) の対称性)ので、二次の項は方向を選ばない(第二変分の式は外部:山辺の汎関数)。運動学:内部空間 S⁹。作用:EH(内部空間の曲率)。力学:54 は二次では縮退、係数 11 -/
alias X_10B_os_yamabe_l2 := CFT.OS.os_yamabe_l2

/-- X.10-B(ダンベル、完(外)):形の揺らぎの二次の項:球面 Sⁿ を法線の方向に k 次の調和関数で変形すると、一次では計量の共形な変化になる。共形の方向の第二変分の係数は λ_k − n = (k − 1)(k + n)。k = 1 は 0(共形変換、形は変わらない)、k = 2(楕円体)は n + 2、S⁹ では 11。54 個の成分はすべて同じ係数をもつ(SO(10) の対称性)ので、二次の項は方向を選ばない(第二変分の式は外部:山辺の汎関数)。運動学:内部空間 S⁹。作用:EH(内部空間の曲率)。力学:54 は二次では縮退、係数 11 -/
alias X_10B_os_shape_S9 := CFT.OS.os_shape_S9

-- X.10-C(ダンベル、未着手):四次の項と符号:随伴 3 の方向が選ばれるか、XI.4 のポテンシャルの形になるか(フラックスと 4 次元の重力との混合を含む計算)。運動学:内部空間 S⁹ と首。作用:—。力学:—(Lean の定理なし:外部定理の引用または未着手)

/-- X.11(ダンベル、完):帽子の線形摂動(共形平坦・球対称・磁気的な部分):三つの共形 Killing の摂動が解、η 方向の可積分性から L[f] = 0、χ 方向は f_χ/sin χ が定数、η 方向は q″ = −q と p″ = −4p の一意性、振幅の変化 cos η は除かれる。摂動はすべてゲージ(GRG 投稿論文の定理 1)。運動学:帽子。作用:EYM(線形化)。力学:共形平坦な摂動はすべてゲージ -/
alias X_11_rr_mode1 := CFT.RR.rr_mode1

/-- X.11(ダンベル、完):帽子の線形摂動(共形平坦・球対称・磁気的な部分):三つの共形 Killing の摂動が解、η 方向の可積分性から L[f] = 0、χ 方向は f_χ/sin χ が定数、η 方向は q″ = −q と p″ = −4p の一意性、振幅の変化 cos η は除かれる。摂動はすべてゲージ(GRG 投稿論文の定理 1)。運動学:帽子。作用:EYM(線形化)。力学:共形平坦な摂動はすべてゲージ -/
alias X_11_rr_eta_integrability := CFT.RR.rr_eta_integrability

/-- X.11(ダンベル、完):帽子の線形摂動(共形平坦・球対称・磁気的な部分):三つの共形 Killing の摂動が解、η 方向の可積分性から L[f] = 0、χ 方向は f_χ/sin χ が定数、η 方向は q″ = −q と p″ = −4p の一意性、振幅の変化 cos η は除かれる。摂動はすべてゲージ(GRG 投稿論文の定理 1)。運動学:帽子。作用:EYM(線形化)。力学:共形平坦な摂動はすべてゲージ -/
alias X_11_rr_cos_mode_excluded := CFT.RR.rr_cos_mode_excluded

/-- X.11(ダンベル、完):帽子の線形摂動(共形平坦・球対称・磁気的な部分):三つの共形 Killing の摂動が解、η 方向の可積分性から L[f] = 0、χ 方向は f_χ/sin χ が定数、η 方向は q″ = −q と p″ = −4p の一意性、振幅の変化 cos η は除かれる。摂動はすべてゲージ(GRG 投稿論文の定理 1)。運動学:帽子。作用:EYM(線形化)。力学:共形平坦な摂動はすべてゲージ -/
alias X_11_oq_osc_unique := CFT.OQ.oq_osc_unique

/-- X.11(ダンベル、完):帽子の線形摂動(共形平坦・球対称・磁気的な部分):三つの共形 Killing の摂動が解、η 方向の可積分性から L[f] = 0、χ 方向は f_χ/sin χ が定数、η 方向は q″ = −q と p″ = −4p の一意性、振幅の変化 cos η は除かれる。摂動はすべてゲージ(GRG 投稿論文の定理 1)。運動学:帽子。作用:EYM(線形化)。力学:共形平坦な摂動はすべてゲージ -/
alias X_11_oq_osc_solution := CFT.OQ.oq_osc_solution

/-- X.11(ダンベル、完):帽子の線形摂動(共形平坦・球対称・磁気的な部分):三つの共形 Killing の摂動が解、η 方向の可積分性から L[f] = 0、χ 方向は f_χ/sin χ が定数、η 方向は q″ = −q と p″ = −4p の一意性、振幅の変化 cos η は除かれる。摂動はすべてゲージ(GRG 投稿論文の定理 1)。運動学:帽子。作用:EYM(線形化)。力学:共形平坦な摂動はすべてゲージ -/
alias X_11_oq_fc_over_sin := CFT.OQ.oq_fc_over_sin

/-- X.11-W(ダンベル、完):帽子の上の YM の試験場(磁気的な実の W、背景の計量は固定):δW = sin²χ·C_n^{(2)}(cos χ)·g(η) で g″ = −(n² + 4n + 1)g。すべて振動し、n = 0(振動数 1)は共形 Killing のゲージモード。帽子の上のポテンシャルは真空の上のもの + 3 なので ω² = (n + 2)² − 3。数値でも n = 0, 1, 2 を確認。運動学:帽子(静的宇宙の上の W)。作用:YM(線形化)。力学:ω² = (n + 2)² − 3 > 0:この ansatz の中に不安定なモードはない -/
alias X_11W_oq_testfield := CFT.OQ.oq_testfield

/-- X.11-W(ダンベル、完):帽子の上の YM の試験場(磁気的な実の W、背景の計量は固定):δW = sin²χ·C_n^{(2)}(cos χ)·g(η) で g″ = −(n² + 4n + 1)g。すべて振動し、n = 0(振動数 1)は共形 Killing のゲージモード。帽子の上のポテンシャルは真空の上のもの + 3 なので ω² = (n + 2)² − 3。数値でも n = 0, 1, 2 を確認。運動学:帽子(静的宇宙の上の W)。作用:YM(線形化)。力学:ω² = (n + 2)² − 3 > 0:この ansatz の中に不安定なモードはない -/
alias X_11W_oq_spectrum := CFT.OQ.oq_spectrum

/-- X.11-W(ダンベル、完):帽子の上の YM の試験場(磁気的な実の W、背景の計量は固定):δW = sin²χ·C_n^{(2)}(cos χ)·g(η) で g″ = −(n² + 4n + 1)g。すべて振動し、n = 0(振動数 1)は共形 Killing のゲージモード。帽子の上のポテンシャルは真空の上のもの + 3 なので ω² = (n + 2)² − 3。数値でも n = 0, 1, 2 を確認。運動学:帽子(静的宇宙の上の W)。作用:YM(線形化)。力学:ω² = (n + 2)² − 3 > 0:この ansatz の中に不安定なモードはない -/
alias X_11W_oq_potential_shift := CFT.OQ.oq_potential_shift

/-- X.11-B(ダンベル、完):一様な YM の方向(スファレロンの方向、磁気的な実の W の ansatz の外):一様等方な部分は Ω(η) と f(η)。f″ = 2f(1 − f²) で f′² + (1 − f²)² は保存、帽子は障壁の頂上 f = 0 にあり δf″ = 2δf(不安定、成長率 √2、帽子の寿命のあいだに e^{√2π} ≈ 85 倍)。一方 Ω″ = −Ω は f によらず、Ω′² + Ω² は保存:場は不安定でも幾何は Tolman 宇宙のまま。運動学:帽子(一様等方な部分)。作用:EYM。力学:場は不安定、幾何は不変 -/
alias X_11B_ol_ym_energy := CFT.OL.ol_ym_energy

/-- X.11-B(ダンベル、完):一様な YM の方向(スファレロンの方向、磁気的な実の W の ansatz の外):一様等方な部分は Ω(η) と f(η)。f″ = 2f(1 − f²) で f′² + (1 − f²)² は保存、帽子は障壁の頂上 f = 0 にあり δf″ = 2δf(不安定、成長率 √2、帽子の寿命のあいだに e^{√2π} ≈ 85 倍)。一方 Ω″ = −Ω は f によらず、Ω′² + Ω² は保存:場は不安定でも幾何は Tolman 宇宙のまま。運動学:帽子(一様等方な部分)。作用:EYM。力学:場は不安定、幾何は不変 -/
alias X_11B_ol_sphaleron_rate := CFT.OL.ol_sphaleron_rate

/-- X.11-B(ダンベル、完):一様な YM の方向(スファレロンの方向、磁気的な実の W の ansatz の外):一様等方な部分は Ω(η) と f(η)。f″ = 2f(1 − f²) で f′² + (1 − f²)² は保存、帽子は障壁の頂上 f = 0 にあり δf″ = 2δf(不安定、成長率 √2、帽子の寿命のあいだに e^{√2π} ≈ 85 倍)。一方 Ω″ = −Ω は f によらず、Ω′² + Ω² は保存:場は不安定でも幾何は Tolman 宇宙のまま。運動学:帽子(一様等方な部分)。作用:EYM。力学:場は不安定、幾何は不変 -/
alias X_11B_ol_geometry_rigid := CFT.OL.ol_geometry_rigid

/-- X.11-C(ダンベル、完):反作用を含む球対称な摂動の方程式の構造:面積 R = r² は R_uv = (Ω/r²)(ℓ²(1 − W²)² − R) をみたし、Weyl の変換で不変な Q = ln(Ω/r²) は Q_uv = 6 r_u r_v/r² − 3Ωℓ²(1 − W²)²/r⁴ + 2Ω/r²。YM の方程式は Q と W だけで閉じる。Q の源の W についての微分は 12Ωℓ²W(1 − W²)/r⁴ ≠ 0:W の摂動は一次で共形平坦からのずれを作る(線形の剛性 X.11 の裏側)。重力に独立な自由度はなく、動くのは W だけ。運動学:帽子とその近く(球対称)。作用:EYM。力学:反作用は一次で避けられない -/
alias X_11C_os_area_linear := CFT.OS.os_area_linear

/-- X.11-C(ダンベル、完):反作用を含む球対称な摂動の方程式の構造:面積 R = r² は R_uv = (Ω/r²)(ℓ²(1 − W²)² − R) をみたし、Weyl の変換で不変な Q = ln(Ω/r²) は Q_uv = 6 r_u r_v/r² − 3Ωℓ²(1 − W²)²/r⁴ + 2Ω/r²。YM の方程式は Q と W だけで閉じる。Q の源の W についての微分は 12Ωℓ²W(1 − W²)/r⁴ ≠ 0:W の摂動は一次で共形平坦からのずれを作る(線形の剛性 X.11 の裏側)。重力に独立な自由度はなく、動くのは W だけ。運動学:帽子とその近く(球対称)。作用:EYM。力学:反作用は一次で避けられない -/
alias X_11C_os_Q_eq := CFT.OS.os_Q_eq

/-- X.11-C(ダンベル、完):反作用を含む球対称な摂動の方程式の構造:面積 R = r² は R_uv = (Ω/r²)(ℓ²(1 − W²)² − R) をみたし、Weyl の変換で不変な Q = ln(Ω/r²) は Q_uv = 6 r_u r_v/r² − 3Ωℓ²(1 − W²)²/r⁴ + 2Ω/r²。YM の方程式は Q と W だけで閉じる。Q の源の W についての微分は 12Ωℓ²W(1 − W²)/r⁴ ≠ 0:W の摂動は一次で共形平坦からのずれを作る(線形の剛性 X.11 の裏側)。重力に独立な自由度はなく、動くのは W だけ。運動学:帽子とその近く(球対称)。作用:EYM。力学:反作用は一次で避けられない -/
alias X_11C_os_backreaction := CFT.OS.os_backreaction

/-- X.11-C(ダンベル、完):反作用を含む球対称な摂動の方程式の構造:面積 R = r² は R_uv = (Ω/r²)(ℓ²(1 − W²)² − R) をみたし、Weyl の変換で不変な Q = ln(Ω/r²) は Q_uv = 6 r_u r_v/r² − 3Ωℓ²(1 − W²)²/r⁴ + 2Ω/r²。YM の方程式は Q と W だけで閉じる。Q の源の W についての微分は 12Ωℓ²W(1 − W²)/r⁴ ≠ 0:W の摂動は一次で共形平坦からのずれを作る(線形の剛性 X.11 の裏側)。重力に独立な自由度はなく、動くのは W だけ。運動学:帽子とその近く(球対称)。作用:EYM。力学:反作用は一次で避けられない -/
alias X_11C_os_backreaction_ne := CFT.OS.os_backreaction_ne

/-- X.11-D(ダンベル、完):反作用を含む摂動は崩壊に向かって成長する(数値):帽子の特性初期値で W に大きさ ε の波束を加え、拘束を解いて非線形の方程式を発展させると(numerics/weyl_growth.py、格子 200・400・800 で収束、ε について線形)、W の摂動は ε の程度のままだが、Weyl の不変量 D = N/r² は η = 0.2 で 0.36ε、η = 1.4 で 118ε、およそ 1/cos²η で成長する。N 自身は 1〜10 ε の程度。等方的な特異点は保たれない(Weyl 曲率仮説の意味で帽子の崩壊は不安定)。厳密な式は XIII.4-C、成長率の証明はしていない。運動学:帽子。作用:EYM(非線形の数値)。力学:Weyl 曲率は 1/cos²η で成長 -/
alias X_11D_ds_N_u := CFT.DS.ds_N_u

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_gauge_singlet := CFT.BridgeTwist.gauge_singlet

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_eps_xsT := CFT.BridgeTwist.eps_xsT

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_xs_sq := CFT.BridgeTwist.xs_sq

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_pole_singlet := CFT.BridgeTwist.pole_singlet

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_chi_deriv := CFT.BridgeTwist.chi_deriv

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_conformal_transfer := CFT.BridgeTwist.conformal_transfer

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_twist_cancel := CFT.BridgeTwist.twist_cancel

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_system_reduce := CFT.BridgeTwist.system_reduce

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_zero_mode := CFT.BridgeTwist.zero_mode

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。外部:Dirac 作用素の共形共変性(Hitchin)、Callias の指数、4 次元の Dirac–湯川系を f′ = −img、g′ = imf へ縮約する部分(この縮約は形式化していない)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_localization := CFT.BridgeTwist.localization

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_dilaton_invariant := CFT.BridgeThermal.dilaton_invariant

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_dilaton_grad := CFT.BridgeThermal.dilaton_grad

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_xi_norm := CFT.BridgeThermal.xi_norm

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_accel_formula := CFT.BridgeThermal.accel_formula

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_accel_identity := CFT.BridgeThermal.accel_identity

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_deser_levin := CFT.BridgeThermal.deser_levin

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_three_classes := CFT.BridgeThermal.three_classes

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_rindler_lapse := CFT.BridgeThermal.rindler_lapse

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_unit_observer := CFT.BridgeThermal.unit_observer

/-- X.13(ダンベル、完(外)):首の温度の幾何:JT の dilaton が選ぶ Killing ベクトル、不変量 I による三つの類、a² − 1/ℓ² = (2πT_loc)²(IX.32 の否定的な結果が指した先)。運動学:首 −dt² + cos²(t/ℓ)dz²、dilaton φ。作用:JT(+ T = κ/2π は外部)。力学:I = (A² + B² − C²)/ℓ²、1/ℓ は温度が生じる臨界の加速度(Deser–Levin の形) -/
alias X_13_junction_tan := CFT.BridgeThermal.junction_tan

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、帽子と首の厳密解(W = r′)を接合で貼り合わせる限り C² にはできない(一般の C² 解についての主張には ODE の一意性が要り、形式化していない)。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_curvature_jump := CFT.RootJunction.curvature_jump

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、帽子と首の厳密解(W = r′)を接合で貼り合わせる限り C² にはできない(一般の C² 解についての主張には ODE の一意性が要り、形式化していない)。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_stress_jump := CFT.RootJunction.stress_jump

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、帽子と首の厳密解(W = r′)を接合で貼り合わせる限り C² にはできない(一般の C² 解についての主張には ODE の一意性が要り、形式化していない)。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_hamC_quadratic := CFT.RootJunction.hamC_quadratic

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、帽子と首の厳密解(W = r′)を接合で貼り合わせる限り C² にはできない(一般の C² 解についての主張には ODE の一意性が要り、形式化していない)。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_junction_two_values := CFT.RootJunction.junction_two_values

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、帽子と首の厳密解(W = r′)を接合で貼り合わせる限り C² にはできない(一般の C² 解についての主張には ODE の一意性が要り、形式化していない)。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_no_C2_junction := CFT.RootJunction.no_C2_junction


/-! ## α-XI 弱い重力予想と首の安定性 -/

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(探索段階の暫定の数値、X.7 で確認予定))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_liouville_actual := CFT.FixNeck.liouville_actual

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(探索段階の暫定の数値、X.7 で確認予定))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_actual_form_neg := CFT.FixNeck.actual_form_neg

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(探索段階の暫定の数値、X.7 で確認予定))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_growth_rate_bound := CFT.FixNeck.growth_rate_bound

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(探索段階の暫定の数値、X.7 で確認予定))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_one_efold_before_collapse := CFT.FixNeck.one_efold_before_collapse

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_mass_function := CFT.Thermo.mass_function

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_lighter_extremal := CFT.Thermo.lighter_extremal

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_extremal_iff_critical := CFT.FixDyn.extremal_iff_critical

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_critical_radius := CFT.FixDyn.critical_radius

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_extremal_mass := CFT.FixDyn.extremal_mass

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_extremal_lighter := CFT.FixDyn.extremal_lighter

/-- XI.2(ダンベル、完(外)):高階補正(F⁴)の符号と穏やかな WGC(アトラクターの形:極限 = M(r) の臨界点)。運動学:首 = 極限の地平線(磁荷の RN)。作用:L = −F²/4 + α(F²)²。力学:p² = r² + 5k/r⁴、M = r + 2k/r⁵ < p、首は細くなる -/
alias XI_2_neck_shrinks := CFT.FixDyn.neck_shrinks

/-- XI.3(ダンベル、完):宇宙検閲:帽子の崩壊の前に捕捉面ができるか。運動学:帽子の波面、首。作用:EYM。力学:崩壊の前に波面の上に周辺的な捕捉面 -/
alias XI_3_no_trapped_in_cap := CFT.Second.no_trapped_in_cap

/-- XI.3(ダンベル、完):宇宙検閲:帽子の崩壊の前に捕捉面ができるか。運動学:帽子の波面、首。作用:EYM。力学:崩壊の前に波面の上に周辺的な捕捉面 -/
alias XI_3_front_marginally_trapped := CFT.FixNeck.front_marginally_trapped

/-- XI.3(ダンベル、完):宇宙検閲:帽子の崩壊の前に捕捉面ができるか。運動学:帽子の波面、首。作用:EYM。力学:崩壊の前に波面の上に周辺的な捕捉面 -/
alias XI_3_neck_marginal := CFT.FixNeck.neck_marginal

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_neck_rho := CFT.HiggsNeck.neck_rho

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_force_W_zero := CFT.HiggsNeck.force_W_zero

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_force_H_zero := CFT.HiggsNeck.force_H_zero

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_quad_expansion := CFT.HiggsNeck.quad_expansion

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_w_mass_neck := CFT.HiggsNeck.w_mass_neck

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_planck_condition := CFT.HiggsNeck.planck_condition

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_hardy_neck := CFT.HiggsNeck.hardy_neck

/-- XI.4(ダンベル、完(外)):首を Higgs 場で支える(EYM–Higgs):首は厳密な解のまま、W の質量 m²ℓ² = −1 + m_W²ℓ²、安定の条件。運動学:首(そのまま)。作用:EYM + 随伴 Higgs。力学:m_W²ℓ² ≥ 3/4(v ≳ 0.244 M_Pl)ならどの長さの首も安定 -/
alias XI_4_no_growing_mode := CFT.HiggsNeck.no_growing_mode

/-- XI.5(ダンベル、完(外)):dyon の首:有効ポテンシャル p²/x + q²x(x = e^{2φ})は x = p/q で最小値 2pq(アトラクター)。電場による有効質量の負のずれ(外部の公式)を入れても W の BF 限界の破れは残る。E·B ∝ pq/r⁴ ≠ 0 で、カイラルアノマリーの源は 0 でない(アノマリーの式は外部)。運動学:首(磁荷 p と電荷 q)。作用:EYM + ディラトン。力学:アトラクター 2pq、不安定性は残る、E·B ≠ 0 -/
alias XI_5_rr_dyon_bf := CFT.RR.rr_dyon_bf

/-- XI.5(ダンベル、完(外)):dyon の首:有効ポテンシャル p²/x + q²x(x = e^{2φ})は x = p/q で最小値 2pq(アトラクター)。電場による有効質量の負のずれ(外部の公式)を入れても W の BF 限界の破れは残る。E·B ∝ pq/r⁴ ≠ 0 で、カイラルアノマリーの源は 0 でない(アノマリーの式は外部)。運動学:首(磁荷 p と電荷 q)。作用:EYM + ディラトン。力学:アトラクター 2pq、不安定性は残る、E·B ≠ 0 -/
alias XI_5_oc_attractor := CFT.OC.oc_attractor

/-- XI.5(ダンベル、完(外)):dyon の首:有効ポテンシャル p²/x + q²x(x = e^{2φ})は x = p/q で最小値 2pq(アトラクター)。電場による有効質量の負のずれ(外部の公式)を入れても W の BF 限界の破れは残る。E·B ∝ pq/r⁴ ≠ 0 で、カイラルアノマリーの源は 0 でない(アノマリーの式は外部)。運動学:首(磁荷 p と電荷 q)。作用:EYM + ディラトン。力学:アトラクター 2pq、不安定性は残る、E·B ≠ 0 -/
alias XI_5_oc_EB := CFT.OC.oc_EB

/-- XI.6(一般、完(外)):実効的な負の宇宙定数(半径 L、V.7-N)での Hawking–Page 型の比較:自由エネルギーの差 F = (r/4G)(1 − r²/L²) は地平線の半径 r > L で負(ブラックホールの相)、転移の温度は 1/(πL)(F と T の式は外部:Hawking–Page 1983)。運動学:首(実効的な AdS の半径 L)。作用:量子応力を含む有効作用。力学:r > L で相が入れ替わる -/
alias XI_6_ol_hp_sign := CFT.OL.ol_hp_sign

/-- XI.6(一般、完(外)):実効的な負の宇宙定数(半径 L、V.7-N)での Hawking–Page 型の比較:自由エネルギーの差 F = (r/4G)(1 − r²/L²) は地平線の半径 r > L で負(ブラックホールの相)、転移の温度は 1/(πL)(F と T の式は外部:Hawking–Page 1983)。運動学:首(実効的な AdS の半径 L)。作用:量子応力を含む有効作用。力学:r > L で相が入れ替わる -/
alias XI_6_ol_hp_temperature := CFT.OL.ol_hp_temperature

/-- XI.7(ダンベル、完):Higgs を入れたときの帽子と首:W = cos χ は Higgs の質量項があると解でない(残差 −Ω²m²h² cos χ)。Higgs が真空の値 h = v にとどまる一様な解は W = 0 を要求する(首は h = v のまま厳密解)。帽子が残るのは対称な相 h ≡ 0 のときで、ポテンシャル λv⁴/4 が宇宙定数として加わる。運動学:帽子・首。作用:EYM + 随伴 Higgs。力学:首は残り、帽子は対称な相でだけ残る -/
alias XI_7_rr_higgs_cap_residual := CFT.RR.rr_higgs_cap_residual

/-- XI.7(ダンベル、完):Higgs を入れたときの帽子と首:W = cos χ は Higgs の質量項があると解でない(残差 −Ω²m²h² cos χ)。Higgs が真空の値 h = v にとどまる一様な解は W = 0 を要求する(首は h = v のまま厳密解)。帽子が残るのは対称な相 h ≡ 0 のときで、ポテンシャル λv⁴/4 が宇宙定数として加わる。運動学:帽子・首。作用:EYM + 随伴 Higgs。力学:首は残り、帽子は対称な相でだけ残る -/
alias XI_7_rr_higgs_cap_nonzero := CFT.RR.rr_higgs_cap_nonzero

/-- XI.7(ダンベル、完):Higgs を入れたときの帽子と首:W = cos χ は Higgs の質量項があると解でない(残差 −Ω²m²h² cos χ)。Higgs が真空の値 h = v にとどまる一様な解は W = 0 を要求する(首は h = v のまま厳密解)。帽子が残るのは対称な相 h ≡ 0 のときで、ポテンシャル λv⁴/4 が宇宙定数として加わる。運動学:帽子・首。作用:EYM + 随伴 Higgs。力学:首は残り、帽子は対称な相でだけ残る -/
alias XI_7_oc_higgs_vev := CFT.OC.oc_higgs_vev

/-- XI.7(ダンベル、完):Higgs を入れたときの帽子と首:W = cos χ は Higgs の質量項があると解でない(残差 −Ω²m²h² cos χ)。Higgs が真空の値 h = v にとどまる一様な解は W = 0 を要求する(首は h = v のまま厳密解)。帽子が残るのは対称な相 h ≡ 0 のときで、ポテンシャル λv⁴/4 が宇宙定数として加わる。運動学:帽子・首。作用:EYM + 随伴 Higgs。力学:首は残り、帽子は対称な相でだけ残る -/
alias XI_7_oc_higgs_sym := CFT.OC.oc_higgs_sym

/-- XI.7-B(ダンベル、完(外)):Higgs が一様でない帽子 = 単極子の芯:平坦な極限の厳密解(Prasad–Sommerfield)W = x/sinh x、h = coth x − 1/x は Bogomolny の方程式 W′ = −Wh、h′ = (1 − W²)/x² をみたす。中心で W = 1、h = 0(帽子の極、対称な相)、遠方で W = 0、h = 1(首の値):帽子の値と首の値を滑らかにつなぐ。重力を入れた解の存在と、臨界で極限 RN の喉になることは外部(Breitenlohner–Forgács–Maison 1992)。運動学:帽子・首。作用:EYM + 随伴 Higgs。力学:滑らかなつなぎ方の実例(単極子) -/
alias XI_7B_ol_ps_W := CFT.OL.ol_ps_W

/-- XI.7-B(ダンベル、完(外)):Higgs が一様でない帽子 = 単極子の芯:平坦な極限の厳密解(Prasad–Sommerfield)W = x/sinh x、h = coth x − 1/x は Bogomolny の方程式 W′ = −Wh、h′ = (1 − W²)/x² をみたす。中心で W = 1、h = 0(帽子の極、対称な相)、遠方で W = 0、h = 1(首の値):帽子の値と首の値を滑らかにつなぐ。重力を入れた解の存在と、臨界で極限 RN の喉になることは外部(Breitenlohner–Forgács–Maison 1992)。運動学:帽子・首。作用:EYM + 随伴 Higgs。力学:滑らかなつなぎ方の実例(単極子) -/
alias XI_7B_ol_ps_h := CFT.OL.ol_ps_h


/-! ## α-XII 新しい柱:ローレンツ群 = 回転 × ブーストと自己双対接続 -/

/-- XII.1(運動学、完):極分解:SL(2,ℂ) の元はただ一通りに 回転(SU(2) = 球面)× ブースト(正の Hermite = 双曲面)に分かれる。運動学:ℍ_ℂ = M₂(ℂ)、I.8 の複素の球面。作用:—。力学:— -/
alias XII_1_ch2 := CFT.Polar.ch2

/-- XII.1(運動学、完):極分解:SL(2,ℂ) の元はただ一通りに 回転(SU(2) = 球面)× ブースト(正の Hermite = 双曲面)に分かれる。運動学:ℍ_ℂ = M₂(ℂ)、I.8 の複素の球面。作用:—。力学:— -/
alias XII_1_polar_exists := CFT.Polar.polar_exists

/-- XII.1(運動学、完):極分解:SL(2,ℂ) の元はただ一通りに 回転(SU(2) = 球面)× ブースト(正の Hermite = 双曲面)に分かれる。運動学:ℍ_ℂ = M₂(ℂ)、I.8 の複素の球面。作用:—。力学:— -/
alias XII_1_polar_unique := CFT.Polar.polar_unique

/-- XII.1(運動学、完):極分解:SL(2,ℂ) の元はただ一通りに 回転(SU(2) = 球面)× ブースト(正の Hermite = 双曲面)に分かれる。運動学:ℍ_ℂ = M₂(ℂ)、I.8 の複素の球面。作用:—。力学:— -/
alias XII_1_boost_from_square := CFT.Polar.boost_from_square

/-- XII.2(運動学、完):球面と双曲面は頂点(恒等変換 = 静止)だけで交わる。運動学:SU(2) と正の Hermite 行列。作用:—。力学:— -/
alias XII_2_sphere_meets_hyperboloid := CFT.Polar.sphere_meets_hyperboloid

/-- XII.2(運動学、完):球面と双曲面は頂点(恒等変換 = 静止)だけで交わる。運動学:SU(2) と正の Hermite 行列。作用:—。力学:— -/
alias XII_2_det_M := CFT.RootDuality.det_M

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_curvature_real := CFT.SelfDual.curvature_real

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_norm_c := CFT.SelfDual.norm_c

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_friedmann_selfdual := CFT.SelfDual.friedmann_selfdual

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_phase_lemma := CFT.SelfDual.phase_lemma

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_cap_hubble := CFT.SelfDual.cap_hubble

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_cap_modulus := CFT.SelfDual.cap_modulus

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇒ |c|² = (8πG/3)ρa²(Lean は一方向)、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_cap_rhs := CFT.SelfDual.cap_rhs

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ(K と Γ の比を位相 t/ℓ と読むのは解釈で、Lean の範囲外)。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる -/
alias XII_4_neck_extrinsic := CFT.SelfDual.neck_extrinsic

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ(K と Γ の比を位相 t/ℓ と読むのは解釈で、Lean の範囲外)。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる -/
alias XII_4_neck_constraint := CFT.SelfDual.neck_constraint

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ(K と Γ の比を位相 t/ℓ と読むのは解釈で、Lean の範囲外)。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる -/
alias XII_4_spin_is_witten := CFT.Action.spin_is_witten

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ(K と Γ の比を位相 t/ℓ と読むのは解釈で、Lean の範囲外)。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる -/
alias XII_4_neck_einstein := CFT.FixGeo.neck_einstein

/-- XII.5(ダンベル、完):共通の時計は共形時間 η:首 AdS₂ の同期座標の焦点(t = πℓ/2)は大域座標で η = π/2、χ = π/2 の一点で、帽子の崩壊 Ω = ℓ cos η = 0 と同じ共形時間。固有時間では帽子 ℓ、首 πℓ/2 で異なる(X.9)。位相 0 → π/2 の読みは η そのもの。運動学:帽子と首。作用:EH + YM。力学:帽子の崩壊と首の焦点は同じ共形時間 η = π/2 -/
alias XII_5_end_phase := CFT.SelfDual.end_phase

/-- XII.5(ダンベル、完):共通の時計は共形時間 η:首 AdS₂ の同期座標の焦点(t = πℓ/2)は大域座標で η = π/2、χ = π/2 の一点で、帽子の崩壊 Ω = ℓ cos η = 0 と同じ共形時間。固有時間では帽子 ℓ、首 πℓ/2 で異なる(X.9)。位相 0 → π/2 の読みは η そのもの。運動学:帽子と首。作用:EH + YM。力学:帽子の崩壊と首の焦点は同じ共形時間 η = π/2 -/
alias XII_5_phase_lemma := CFT.SelfDual.phase_lemma

/-- XII.5(ダンベル、完):共通の時計は共形時間 η:首 AdS₂ の同期座標の焦点(t = πℓ/2)は大域座標で η = π/2、χ = π/2 の一点で、帽子の崩壊 Ω = ℓ cos η = 0 と同じ共形時間。固有時間では帽子 ℓ、首 πℓ/2 で異なる(X.9)。位相 0 → π/2 の読みは η そのもの。運動学:帽子と首。作用:EH + YM。力学:帽子の崩壊と首の焦点は同じ共形時間 η = π/2 -/
alias XII_5_oc_ads_global := CFT.OC.oc_ads_global

/-- XII.5(ダンベル、完):共通の時計は共形時間 η:首 AdS₂ の同期座標の焦点(t = πℓ/2)は大域座標で η = π/2、χ = π/2 の一点で、帽子の崩壊 Ω = ℓ cos η = 0 と同じ共形時間。固有時間では帽子 ℓ、首 πℓ/2 で異なる(X.9)。位相 0 → π/2 の読みは η そのもの。運動学:帽子と首。作用:EH + YM。力学:帽子の崩壊と首の焦点は同じ共形時間 η = π/2 -/
alias XII_5_oc_ads_sync := CFT.OC.oc_ads_sync

/-- XII.5(ダンベル、完):共通の時計は共形時間 η:首 AdS₂ の同期座標の焦点(t = πℓ/2)は大域座標で η = π/2、χ = π/2 の一点で、帽子の崩壊 Ω = ℓ cos η = 0 と同じ共形時間。固有時間では帽子 ℓ、首 πℓ/2 で異なる(X.9)。位相 0 → π/2 の読みは η そのもの。運動学:帽子と首。作用:EH + YM。力学:帽子の崩壊と首の焦点は同じ共形時間 η = π/2 -/
alias XII_5_oc_focus := CFT.OC.oc_focus

/-- XII.6(ダンベル、完):テスト B(範囲を帽子と首の厳密解に限定):そこでは U21′(YM 場 = スピン接続、W = r′)は YM 場 = 自己双対接続の実部(回転の部分)と一致し、すべての時刻で成り立つ。一般の時間発展で YM = Re A が保たれるかは未(新しい原理として仮定)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_real_part := CFT.SelfDual.real_part

/-- XII.6(ダンベル、完):テスト B(範囲を帽子と首の厳密解に限定):そこでは U21′(YM 場 = スピン接続、W = r′)は YM 場 = 自己双対接続の実部(回転の部分)と一致し、すべての時刻で成り立つ。一般の時間発展で YM = Re A が保たれるかは未(新しい原理として仮定)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_cap_real_part := CFT.SelfDual.cap_real_part

/-- XII.6(ダンベル、完):テスト B(範囲を帽子と首の厳密解に限定):そこでは U21′(YM 場 = スピン接続、W = r′)は YM 場 = 自己双対接続の実部(回転の部分)と一致し、すべての時刻で成り立つ。一般の時間発展で YM = Re A が保たれるかは未(新しい原理として仮定)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_spin_is_witten := CFT.Action.spin_is_witten

/-- XII.6(ダンベル、完):テスト B(範囲を帽子と首の厳密解に限定):そこでは U21′(YM 場 = スピン接続、W = r′)は YM 場 = 自己双対接続の実部(回転の部分)と一致し、すべての時刻で成り立つ。一般の時間発展で YM = Re A が保たれるかは未(新しい原理として仮定)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_frw_exact := CFT.EYM.frw_exact

/-- XII.7(ダンベル、完):v6 の再現:帽子の自己双対接続の大きさと位相は v6 の質量殻と量子半球の式と同じ形になる(a/ℓ = cos η = 1/cosh ζ などは定理)。Γ = 質量、K = 運動量、|A| = エネルギー、帽子の一生 = 量子半球を頂点(静止)から赤道(光速)へ、という読みは解釈。運動学:量子半球 Q、質量殻、帽子。作用:EH + YM(自己双対の変数)。力学:a/ℓ = cos η = 1/cosh ζ = m/E、ȧ = −sinh ζ -/
alias XII_7_mass_shell := CFT.SelfDual.mass_shell

/-- XII.7(ダンベル、完):v6 の再現:帽子の自己双対接続の大きさと位相は v6 の質量殻と量子半球の式と同じ形になる(a/ℓ = cos η = 1/cosh ζ などは定理)。Γ = 質量、K = 運動量、|A| = エネルギー、帽子の一生 = 量子半球を頂点(静止)から赤道(光速)へ、という読みは解釈。運動学:量子半球 Q、質量殻、帽子。作用:EH + YM(自己双対の変数)。力学:a/ℓ = cos η = 1/cosh ζ = m/E、ȧ = −sinh ζ -/
alias XII_7_gudermann_phase := CFT.SelfDual.gudermann_phase

/-- XII.7(ダンベル、完):v6 の再現:帽子の自己双対接続の大きさと位相は v6 の質量殻と量子半球の式と同じ形になる(a/ℓ = cos η = 1/cosh ζ などは定理)。Γ = 質量、K = 運動量、|A| = エネルギー、帽子の一生 = 量子半球を頂点(静止)から赤道(光速)へ、という読みは解釈。運動学:量子半球 Q、質量殻、帽子。作用:EH + YM(自己双対の変数)。力学:a/ℓ = cos η = 1/cosh ζ = m/E、ȧ = −sinh ζ -/
alias XII_7_cap_modulus := CFT.SelfDual.cap_modulus

/-- XII.8(ダンベル、完):テスト C(新しい数を出す)の結論:候補 α = 3π/(4n + 2) は、YM のエネルギーを障壁の頂上の値 K = 3π²/g² とおいた半古典の式。一様な YM のハミルトニアン p²/(4K) + K(1 − f²)² の固有値の条件としては、弱結合で準位が 2m + 1(井戸の振動数 2)になり、Ω の準位 n + ½ と決して一致しない(数値でも K = 5, 20, 80 で確認)。この切り詰めからは信頼できる新しい数は出ない(否定的)。運動学:一様なモード。作用:EH + YM(ミニ超空間)。力学:否定的:切り詰めに依存し、弱結合で解なし -/
alias XII_8_quantized := CFT.Conformal.quantized

/-- XII.8(ダンベル、完):テスト C(新しい数を出す)の結論:候補 α = 3π/(4n + 2) は、YM のエネルギーを障壁の頂上の値 K = 3π²/g² とおいた半古典の式。一様な YM のハミルトニアン p²/(4K) + K(1 − f²)² の固有値の条件としては、弱結合で準位が 2m + 1(井戸の振動数 2)になり、Ω の準位 n + ½ と決して一致しない(数値でも K = 5, 20, 80 で確認)。この切り詰めからは信頼できる新しい数は出ない(否定的)。運動学:一様なモード。作用:EH + YM(ミニ超空間)。力学:否定的:切り詰めに依存し、弱結合で解なし -/
alias XII_8_oc_well := CFT.OC.oc_well

/-- XII.8(ダンベル、完):テスト C(新しい数を出す)の結論:候補 α = 3π/(4n + 2) は、YM のエネルギーを障壁の頂上の値 K = 3π²/g² とおいた半古典の式。一様な YM のハミルトニアン p²/(4K) + K(1 − f²)² の固有値の条件としては、弱結合で準位が 2m + 1(井戸の振動数 2)になり、Ω の準位 n + ½ と決して一致しない(数値でも K = 5, 20, 80 で確認)。この切り詰めからは信頼できる新しい数は出ない(否定的)。運動学:一様なモード。作用:EH + YM(ミニ超空間)。力学:否定的:切り詰めに依存し、弱結合で解なし -/
alias XII_8_oc_parity := CFT.OC.oc_parity


/-! ## α-XIII 共形の枠:物理の時空 = Ω² × 量子の球(静的宇宙 ℝ × S³)と滑らかさ -/

/-- XIII.1(ダンベル、完(外)):帽子と首は同じ静的宇宙の共形倍(帽子 Ω = ℓ cos η、首 Ω = ℓ/sin u)で、どちらも同じ線形な方程式 □Ω = Ω をみたす(YM の共形不変性)。(A + Bu)/sin u は静的な解(Lean はこれが方程式をみたすことを示す)。首の両端の無限遠は S³ の極。運動学:静的宇宙(滑らかに閉じた S³)、倍率 Ω。作用:EYM(トレース R = 0、共形変換の公式は外部)。力学:□̂Ω = Ω -/
alias XIII_1_cap_box := CFT.Conformal.cap_box

/-- XIII.1(ダンベル、完(外)):帽子と首は同じ静的宇宙の共形倍(帽子 Ω = ℓ cos η、首 Ω = ℓ/sin u)で、どちらも同じ線形な方程式 □Ω = Ω をみたす(YM の共形不変性)。(A + Bu)/sin u は静的な解(Lean はこれが方程式をみたすことを示す)。首の両端の無限遠は S³ の極。運動学:静的宇宙(滑らかに閉じた S³)、倍率 Ω。作用:EYM(トレース R = 0、共形変換の公式は外部)。力学:□̂Ω = Ω -/
alias XIII_1_neck_derivs := CFT.Conformal.neck_derivs

/-- XIII.1(ダンベル、完(外)):帽子と首は同じ静的宇宙の共形倍(帽子 Ω = ℓ cos η、首 Ω = ℓ/sin u)で、どちらも同じ線形な方程式 □Ω = Ω をみたす(YM の共形不変性)。(A + Bu)/sin u は静的な解(Lean はこれが方程式をみたすことを示す)。首の両端の無限遠は S³ の極。運動学:静的宇宙(滑らかに閉じた S³)、倍率 Ω。作用:EYM(トレース R = 0、共形変換の公式は外部)。力学:□̂Ω = Ω -/
alias XIII_1_neck_box := CFT.Conformal.neck_box

/-- XIII.1(ダンベル、完(外)):帽子と首は同じ静的宇宙の共形倍(帽子 Ω = ℓ cos η、首 Ω = ℓ/sin u)で、どちらも同じ線形な方程式 □Ω = Ω をみたす(YM の共形不変性)。(A + Bu)/sin u は静的な解(Lean はこれが方程式をみたすことを示す)。首の両端の無限遠は S³ の極。運動学:静的宇宙(滑らかに閉じた S³)、倍率 Ω。作用:EYM(トレース R = 0、共形変換の公式は外部)。力学:□̂Ω = Ω -/
alias XIII_1_neck_coordinate := CFT.Conformal.neck_coordinate

/-- XIII.1(ダンベル、完(外)):帽子と首は同じ静的宇宙の共形倍(帽子 Ω = ℓ cos η、首 Ω = ℓ/sin u)で、どちらも同じ線形な方程式 □Ω = Ω をみたす(YM の共形不変性)。(A + Bu)/sin u は静的な解(Lean はこれが方程式をみたすことを示す)。首の両端の無限遠は S³ の極。運動学:静的宇宙(滑らかに閉じた S³)、倍率 Ω。作用:EYM(トレース R = 0、共形変換の公式は外部)。力学:□̂Ω = Ω -/
alias XIII_1_static_general := CFT.Conformal.static_general

/-- XIII.1(ダンベル、完(外)):帽子と首は同じ静的宇宙の共形倍(帽子 Ω = ℓ cos η、首 Ω = ℓ/sin u)で、どちらも同じ線形な方程式 □Ω = Ω をみたす(YM の共形不変性)。(A + Bu)/sin u は静的な解(Lean はこれが方程式をみたすことを示す)。首の両端の無限遠は S³ の極。運動学:静的宇宙(滑らかに閉じた S³)、倍率 Ω。作用:EYM(トレース R = 0、共形変換の公式は外部)。力学:□̂Ω = Ω -/
alias XIII_1_static_general_deriv := CFT.Conformal.static_general_deriv

/-- XIII.2(ダンベル、完):接合の跳び(X.14)は倍率の 2 階微分の縫い目:u = π/2 で Ω、Ω′ は一致、Ω″ は 0 と ℓ。物理の W = r′ は cos u + (Ω′/Ω) sin u。運動学:接合。作用:—。力学:跳び = Ω″ の跳び -/
alias XIII_2_junction_seam := CFT.Conformal.junction_seam

/-- XIII.2(ダンベル、完):接合の跳び(X.14)は倍率の 2 階微分の縫い目:u = π/2 で Ω、Ω′ は一致、Ω″ は 0 と ℓ。物理の W = r′ は cos u + (Ω′/Ω) sin u。運動学:接合。作用:—。力学:跳び = Ω″ の跳び -/
alias XIII_2_r_prime_conformal := CFT.Conformal.r_prime_conformal

/-- XIII.3(ダンベル、完(外)):Einstein の ηη 成分を共形の枠で再現:首 Ω² + Ω′² = ℓ²/sin⁴u、帽子 3(Ω² + Ω̇²) = 3ℓ²、どちらも ℓ² = 4πG/g²。運動学:帽子と首。作用:EYM(共形変換の公式は外部)。力学:IX.11・IX.17 と一致 -/
alias XIII_3_eta_neck := CFT.Conformal.eta_neck

/-- XIII.3(ダンベル、完(外)):Einstein の ηη 成分を共形の枠で再現:首 Ω² + Ω′² = ℓ²/sin⁴u、帽子 3(Ω² + Ω̇²) = 3ℓ²、どちらも ℓ² = 4πG/g²。運動学:帽子と首。作用:EYM(共形変換の公式は外部)。力学:IX.11・IX.17 と一致 -/
alias XIII_3_eta_cap := CFT.Conformal.eta_cap

/-- XIII.4(ダンベル、完):共形平坦(一つの Ω)のままでは跳びは消えない:静的な場合は数値、時間に依存する場合も W = r′ 型の時間対称な切り口では極値球面で r″ = Ω_ηη/Ω² ∈ {0, −1/ℓ}(二つの根)。運動学:共形の枠の時間対称な切り口。作用:EYM(トレースとハミルトン拘束)。力学:否定的(定理) -/
alias XIII_4_rr_hessian_char := CFT.RR.rr_hessian_char

/-- XIII.4(ダンベル、完):共形平坦(一つの Ω)のままでは跳びは消えない:静的な場合は数値、時間に依存する場合も W = r′ 型の時間対称な切り口では極値球面で r″ = Ω_ηη/Ω² ∈ {0, −1/ℓ}(二つの根)。運動学:共形の枠の時間対称な切り口。作用:EYM(トレースとハミルトン拘束)。力学:否定的(定理) -/
alias XIII_4_rr_two_roots := CFT.RR.rr_two_roots

/-- XIII.4(ダンベル、完):共形平坦(一つの Ω)のままでは跳びは消えない:静的な場合は数値、時間に依存する場合も W = r′ 型の時間対称な切り口では極値球面で r″ = Ω_ηη/Ω² ∈ {0, −1/ℓ}(二つの根)。運動学:共形の枠の時間対称な切り口。作用:EYM(トレースとハミルトン拘束)。力学:否定的(定理) -/
alias XIII_4_rr_conformal_two_values := CFT.RR.rr_conformal_two_values

/-- XIII.4-G(ダンベル、完):一般の W では二つの根は消える:極値球面で r″ = (W² − W⁴/2 − ℓ²W′²)/ℓ、W = 0 なら任意の r″ ≤ 0 が W′ で実現できる。離散的な跳びは W = r′(スピン接続型)に固有。運動学:極値球面の初期データ。作用:EYM(ハミルトン拘束)。力学:跳びの離散性は W = r′ による -/
alias XIII_4G_rr_general_W_rpp := CFT.RR.rr_general_W_rpp

/-- XIII.4-G(ダンベル、完):一般の W では二つの根は消える:極値球面で r″ = (W² − W⁴/2 − ℓ²W′²)/ℓ、W = 0 なら任意の r″ ≤ 0 が W′ で実現できる。離散的な跳びは W = r′(スピン接続型)に固有。運動学:極値球面の初期データ。作用:EYM(ハミルトン拘束)。力学:跳びの離散性は W = r′ による -/
alias XIII_4G_rr_general_W_any := CFT.RR.rr_general_W_any

/-- XIII.4-A(ダンベル、完):定理 A(つなぎ方の一意性):球対称・磁気的で W = r′ の類の中では、帽子と首のつなぎ方に選択の余地がない。面積半径が連続になる場所は赤道 x = πℓ/2 だけ、そこで r′ は自動的に一致(C¹)、r″ は −1/ℓ と 0 で拘束の根はこの二つだけ(C² にできない)、時間的な管ではつなげず、ヌルの前線の上で [W_u] = 1/(√2ℓ) のまま。「なぜつなぐのか」(定理 B)は含まない。運動学:帽子・首(赤道の球面)。作用:EYM(拘束)。力学:つなぐならこの形しかない -/
alias XIII_4A_ju_location := CFT.JU.ju_location

/-- XIII.4-A(ダンベル、完):定理 A(つなぎ方の一意性):球対称・磁気的で W = r′ の類の中では、帽子と首のつなぎ方に選択の余地がない。面積半径が連続になる場所は赤道 x = πℓ/2 だけ、そこで r′ は自動的に一致(C¹)、r″ は −1/ℓ と 0 で拘束の根はこの二つだけ(C² にできない)、時間的な管ではつなげず、ヌルの前線の上で [W_u] = 1/(√2ℓ) のまま。「なぜつなぐのか」(定理 B)は含まない。運動学:帽子・首(赤道の球面)。作用:EYM(拘束)。力学:つなぐならこの形しかない -/
alias XIII_4A_ju_C1_auto := CFT.JU.ju_C1_auto

/-- XIII.4-A(ダンベル、完):定理 A(つなぎ方の一意性):球対称・磁気的で W = r′ の類の中では、帽子と首のつなぎ方に選択の余地がない。面積半径が連続になる場所は赤道 x = πℓ/2 だけ、そこで r′ は自動的に一致(C¹)、r″ は −1/ℓ と 0 で拘束の根はこの二つだけ(C² にできない)、時間的な管ではつなげず、ヌルの前線の上で [W_u] = 1/(√2ℓ) のまま。「なぜつなぐのか」(定理 B)は含まない。運動学:帽子・首(赤道の球面)。作用:EYM(拘束)。力学:つなぐならこの形しかない -/
alias XIII_4A_ju_cap_second := CFT.JU.ju_cap_second

/-- XIII.4-A(ダンベル、完):定理 A(つなぎ方の一意性):球対称・磁気的で W = r′ の類の中では、帽子と首のつなぎ方に選択の余地がない。面積半径が連続になる場所は赤道 x = πℓ/2 だけ、そこで r′ は自動的に一致(C¹)、r″ は −1/ℓ と 0 で拘束の根はこの二つだけ(C² にできない)、時間的な管ではつなげず、ヌルの前線の上で [W_u] = 1/(√2ℓ) のまま。「なぜつなぐのか」(定理 B)は含まない。運動学:帽子・首(赤道の球面)。作用:EYM(拘束)。力学:つなぐならこの形しかない -/
alias XIII_4A_ju_jump_fixed := CFT.JU.ju_jump_fixed

/-- XIII.4-A(ダンベル、完):定理 A(つなぎ方の一意性):球対称・磁気的で W = r′ の類の中では、帽子と首のつなぎ方に選択の余地がない。面積半径が連続になる場所は赤道 x = πℓ/2 だけ、そこで r′ は自動的に一致(C¹)、r″ は −1/ℓ と 0 で拘束の根はこの二つだけ(C² にできない)、時間的な管ではつなげず、ヌルの前線の上で [W_u] = 1/(√2ℓ) のまま。「なぜつなぐのか」(定理 B)は含まない。運動学:帽子・首(赤道の球面)。作用:EYM(拘束)。力学:つなぐならこの形しかない -/
alias XIII_4A_ju_theorem_A := CFT.JU.ju_theorem_A

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_circle_of_flat := CFT.DS.ds_circle_of_flat

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_cap_on_circle := CFT.DS.ds_cap_on_circle

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_neck_on_circle := CFT.DS.ds_neck_on_circle

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_cap_disc := CFT.DS.ds_cap_disc

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_slope_disc := CFT.DS.ds_slope_disc

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_slope_real := CFT.DS.ds_slope_real

/-- XIII.4-B(ダンベル、完):ダンベルの形の定理:時間対称・W = r′・共形平坦な切り口は(W² ≠ 1 なら)1 階の方程式 r² + ℓ²r′² = ℓ² をみたす。(r, ℓW) の平面で帽子は円を一周し、首は円の上の一点 (ℓ, 0)、帽子の時空の全体は円板の中。この方程式の解は各点で r″ = −r/ℓ²(帽子、正則な解)か r′ = 0(首、特異解 = 帽子の族の包絡線)。ダンベルは正則な解と特異解を C¹ でつないだもので、C¹ で C² でないこと(定理 A)は包絡線に接することの言いかえ。共形平坦な解のヌル方向の傾き dW/dr は二次方程式の根で、実の根があるのは円板の中だけ、円の上で重なる(C¹ の解すべての分類は未形式化)。運動学:帽子・首。作用:EYM(拘束)と共形平坦。力学:首は帽子の包絡線 -/
alias XIII_4B_ds_branch := CFT.DS.ds_branch

/-- XIII.4-C(ダンベル、完):Weyl 曲率 = 質量 − 磁気の自己エネルギー:球対称な EYM で Weyl の不変量は 3(2m/r − ℓ²(1 − W²)²/r²)(m は Misner–Sharp の質量)。共形平坦 ⇔ 2mr = ℓ²(1 − W²)²(各球面で極限 RN と同じ関係)。N = 2mr − ℓ²(1 − W²)² は輸送の式 N_u − (r_u/r)N = Σ_u に従う。Weyl 曲率と Misner–Sharp の質量とエネルギー密度の一般の関係は既知で、これはその EYM の場合。運動学:球対称な EYM の全体。作用:EYM。力学:共形平坦 = 質量がすべて磁気の自己エネルギー -/
alias XIII_4C_ds_weyl_mass := CFT.DS.ds_weyl_mass

/-- XIII.4-C(ダンベル、完):Weyl 曲率 = 質量 − 磁気の自己エネルギー:球対称な EYM で Weyl の不変量は 3(2m/r − ℓ²(1 − W²)²/r²)(m は Misner–Sharp の質量)。共形平坦 ⇔ 2mr = ℓ²(1 − W²)²(各球面で極限 RN と同じ関係)。N = 2mr − ℓ²(1 − W²)² は輸送の式 N_u − (r_u/r)N = Σ_u に従う。Weyl 曲率と Misner–Sharp の質量とエネルギー密度の一般の関係は既知で、これはその EYM の場合。運動学:球対称な EYM の全体。作用:EYM。力学:共形平坦 = 質量がすべて磁気の自己エネルギー -/
alias XIII_4C_ds_mass_u := CFT.DS.ds_mass_u

/-- XIII.4-C(ダンベル、完):Weyl 曲率 = 質量 − 磁気の自己エネルギー:球対称な EYM で Weyl の不変量は 3(2m/r − ℓ²(1 − W²)²/r²)(m は Misner–Sharp の質量)。共形平坦 ⇔ 2mr = ℓ²(1 − W²)²(各球面で極限 RN と同じ関係)。N = 2mr − ℓ²(1 − W²)² は輸送の式 N_u − (r_u/r)N = Σ_u に従う。Weyl 曲率と Misner–Sharp の質量とエネルギー密度の一般の関係は既知で、これはその EYM の場合。運動学:球対称な EYM の全体。作用:EYM。力学:共形平坦 = 質量がすべて磁気の自己エネルギー -/
alias XIII_4C_ds_N_u := CFT.DS.ds_N_u

/-- XIII.4-D(ダンベル、完):W = r′ は仮定ではなく等号の場合:時間対称な切り口で、拘束は質量の形 m′ = r′ℓ²(W′² + (1 − W²)²/(2r²)) に書ける。共形平坦(2mr = ℓ²(1 − W²)²)と合わせると平方の完成ができて、W² ≠ 1 なら r′² ≤ W²。等号 W² = r′²(スピン接続型)は不等式がちょうど成り立つ端で、そのとき 1 階の方程式 r r′W′ = −W(1 − W²) になる。時間の方向の拘束 Ω² + Ω_η² = ℓ² は空間の方向の r² + ℓ²r′² = ℓ² と同じ形。運動学:時間対称な切り口。作用:EYM(拘束)と共形平坦。力学:スピン接続型は不等式の等号 -/
alias XIII_4D_ds2_mass_prime := CFT.DS.ds2_mass_prime

/-- XIII.4-D(ダンベル、完):W = r′ は仮定ではなく等号の場合:時間対称な切り口で、拘束は質量の形 m′ = r′ℓ²(W′² + (1 − W²)²/(2r²)) に書ける。共形平坦(2mr = ℓ²(1 − W²)²)と合わせると平方の完成ができて、W² ≠ 1 なら r′² ≤ W²。等号 W² = r′²(スピン接続型)は不等式がちょうど成り立つ端で、そのとき 1 階の方程式 r r′W′ = −W(1 − W²) になる。時間の方向の拘束 Ω² + Ω_η² = ℓ² は空間の方向の r² + ℓ²r′² = ℓ² と同じ形。運動学:時間対称な切り口。作用:EYM(拘束)と共形平坦。力学:スピン接続型は不等式の等号 -/
alias XIII_4D_ds2_bogomolny := CFT.DS.ds2_bogomolny

/-- XIII.4-D(ダンベル、完):W = r′ は仮定ではなく等号の場合:時間対称な切り口で、拘束は質量の形 m′ = r′ℓ²(W′² + (1 − W²)²/(2r²)) に書ける。共形平坦(2mr = ℓ²(1 − W²)²)と合わせると平方の完成ができて、W² ≠ 1 なら r′² ≤ W²。等号 W² = r′²(スピン接続型)は不等式がちょうど成り立つ端で、そのとき 1 階の方程式 r r′W′ = −W(1 − W²) になる。時間の方向の拘束 Ω² + Ω_η² = ℓ² は空間の方向の r² + ℓ²r′² = ℓ² と同じ形。運動学:時間対称な切り口。作用:EYM(拘束)と共形平坦。力学:スピン接続型は不等式の等号 -/
alias XIII_4D_ds2_num := CFT.DS.ds2_num

/-- XIII.4-D(ダンベル、完):W = r′ は仮定ではなく等号の場合:時間対称な切り口で、拘束は質量の形 m′ = r′ℓ²(W′² + (1 − W²)²/(2r²)) に書ける。共形平坦(2mr = ℓ²(1 − W²)²)と合わせると平方の完成ができて、W² ≠ 1 なら r′² ≤ W²。等号 W² = r′²(スピン接続型)は不等式がちょうど成り立つ端で、そのとき 1 階の方程式 r r′W′ = −W(1 − W²) になる。時間の方向の拘束 Ω² + Ω_η² = ℓ² は空間の方向の r² + ℓ²r′² = ℓ² と同じ形。運動学:時間対称な切り口。作用:EYM(拘束)と共形平坦。力学:スピン接続型は不等式の等号 -/
alias XIII_4D_ds2_W_ge := CFT.DS.ds2_W_ge

/-- XIII.4-D(ダンベル、完):W = r′ は仮定ではなく等号の場合:時間対称な切り口で、拘束は質量の形 m′ = r′ℓ²(W′² + (1 − W²)²/(2r²)) に書ける。共形平坦(2mr = ℓ²(1 − W²)²)と合わせると平方の完成ができて、W² ≠ 1 なら r′² ≤ W²。等号 W² = r′²(スピン接続型)は不等式がちょうど成り立つ端で、そのとき 1 階の方程式 r r′W′ = −W(1 − W²) になる。時間の方向の拘束 Ω² + Ω_η² = ℓ² は空間の方向の r² + ℓ²r′² = ℓ² と同じ形。運動学:時間対称な切り口。作用:EYM(拘束)と共形平坦。力学:スピン接続型は不等式の等号 -/
alias XIII_4D_ds2_saturated := CFT.DS.ds2_saturated

/-- XIII.4-D(ダンベル、完):W = r′ は仮定ではなく等号の場合:時間対称な切り口で、拘束は質量の形 m′ = r′ℓ²(W′² + (1 − W²)²/(2r²)) に書ける。共形平坦(2mr = ℓ²(1 − W²)²)と合わせると平方の完成ができて、W² ≠ 1 なら r′² ≤ W²。等号 W² = r′²(スピン接続型)は不等式がちょうど成り立つ端で、そのとき 1 階の方程式 r r′W′ = −W(1 − W²) になる。時間の方向の拘束 Ω² + Ω_η² = ℓ² は空間の方向の r² + ℓ²r′² = ℓ² と同じ形。運動学:時間対称な切り口。作用:EYM(拘束)と共形平坦。力学:スピン接続型は不等式の等号 -/
alias XIII_4D_ds2_friedmann := CFT.DS.ds2_friedmann

/-- XIII.4-E(ダンベル、完(外)):首の作用は角で決まる:首(R = 0、磁場だけ)のユークリッド作用の体積の項は A/(2G)(A は 2 次元の部分の面積)。Gauss–Bonnet(外部)で A = ℓ²(∮k ds + Σ(π − θ_i) − 2πχ) なので、測地線で囲んだ領域では辺の長さによらず、角の角度と位相だけで決まる。位相の項 −πℓ²/G は極限ブラックホールのエントロピーと同じ大きさ。首の長さは体積の項では決まらない(境界の GHY の項は未計算)。先行研究:面積と電荷の不等式 A ≥ 4πQ² の等号は積 [0, L] × S²(長さ L は自由)に限る(Dain–Jaramillo–Reiris 2012、Cruz–Mendes 2025、Einstein–Maxwell の場合)。首はその等号の場合にあたる。運動学:首。作用:EH + YM(ユークリッド)。力学:首の長さは体積の作用の平坦な方向 -/
alias XIII_4E_ds2_neck_action := CFT.DS.ds2_neck_action

/-- XIII.5(ダンベル、完(外)):滑らかな解は Weyl 曲率を許すと存在する:Bartnik–McKinnon 解の列(n 個の節)は n → ∞ で、滑らかな芯 + 半径ちょうど ℓ の無限に長い喉(W ≈ 0、N → 0、質量 → 極限の値)に近づく。接合も殻もない(数値で b_n = 0.4537、0.6517、0.6970、0.7048、0.7062 を再現。前回報告の 0.6973、0.7055 は積分の打ち切りによる誤りで、ここで訂正)。運動学:芯(帽子の代わり)と首。作用:EYM(磁場だけ、Higgs なし)。力学:跳びのないダンベルの半分(極限で) -/
alias XIII_5_extremal_limit := CFT.Conformal.extremal_limit

/-- XIII.6(ダンベル、完(外)):ミニ超空間:一様な Ω の作用 (3π/4G)∫(Ω² − Ω̇²)、解は周期 2π(巡回)、エネルギーは負で YM のエネルギー 3π²/g² と打ち消し合う ⇔ ℓ² = 4πG/g²。運動学:帽子(静的宇宙の上の一様な Ω)。作用:EH(共形の枠、外部)+ YM。力学:Hamilton 拘束 = エネルギーの釣り合い -/
alias XIII_6_periodic := CFT.Conformal.periodic

/-- XIII.6(ダンベル、完(外)):ミニ超空間:一様な Ω の作用 (3π/4G)∫(Ω² − Ω̇²)、解は周期 2π(巡回)、エネルギーは負で YM のエネルギー 3π²/g² と打ち消し合う ⇔ ℓ² = 4πG/g²。運動学:帽子(静的宇宙の上の一様な Ω)。作用:EH(共形の枠、外部)+ YM。力学:Hamilton 拘束 = エネルギーの釣り合い -/
alias XIII_6_cap_energy := CFT.Conformal.cap_energy

/-- XIII.6(ダンベル、完(外)):ミニ超空間:一様な Ω の作用 (3π/4G)∫(Ω² − Ω̇²)、解は周期 2π(巡回)、エネルギーは負で YM のエネルギー 3π²/g² と打ち消し合う ⇔ ℓ² = 4πG/g²。運動学:帽子(静的宇宙の上の一様な Ω)。作用:EH(共形の枠、外部)+ YM。力学:Hamilton 拘束 = エネルギーの釣り合い -/
alias XIII_6_energy_balance := CFT.Conformal.energy_balance

/-- XIII.7(ダンベル、完(外)):量子化(半古典):Ω は振動数 1 の負のエネルギーの振動子(基底状態の固有値 ½)。YM を帽子の古典の値に固定すると拘束 3π²/g² = n + ½ から ℓ²/ℓ_P² = 4(n + ½)/(3π)、α = 3π/(4n + 2)。運動学:帽子。作用:量子化した Ω + 古典の YM。力学:ℓ と g のとびとびの値(候補) -/
alias XIII_7_ground_state := CFT.Conformal.ground_state

/-- XIII.7(ダンベル、完(外)):量子化(半古典):Ω は振動数 1 の負のエネルギーの振動子(基底状態の固有値 ½)。YM を帽子の古典の値に固定すると拘束 3π²/g² = n + ½ から ℓ²/ℓ_P² = 4(n + ½)/(3π)、α = 3π/(4n + 2)。運動学:帽子。作用:量子化した Ω + 古典の YM。力学:ℓ と g のとびとびの値(候補) -/
alias XIII_7_quantized := CFT.Conformal.quantized


/-! ## α-XIV 滑らかさの地図:静的な形の分類と、閉じた滑らかな形(葉巻) -/

/-- XIV.1(ダンベル、完):静的な喉はない:r′ = 0 の点では r″ = −2W′²/r ≤ 0。静的な形はくびれをもてず、くびれの極限は r″ = 0 の円柱だけ(ヌルエネルギー条件)。運動学:断面 r(s)。作用:EYM + Λ(静的)。力学:ダンベルの首は静的には作れない。首は円柱(境界の場合) -/
alias XIV_1_no_static_throat := CFT.Smooth.no_static_throat

/-- XIV.2(ダンベル、完):首(円柱)の族:W = 0、半径 R の円柱は Λ = 1/R² − 1/R⁴、時間の向き k² = (2 − R²)/R⁴(AdS₂ × S²、平坦 × S²、dS₂ × S²)。Λ ≤ 1/(4ℓ²)、等号は R = √2ℓ(磁荷 1 の RN–de Sitter の超冷極限、Plebański–Hacyan の Minkowski₂ × S²)。Λ = 0 では R = ℓ(新しい柱の首 = ブースト × 回転)。dS₂ × S²(k² < 0)は ν′ が定数の形では表せず、Lean の範囲外。運動学:首。作用:EYM + Λ。力学:首の三つの顔 -/
alias XIV_2_cylinder_family := CFT.Smooth.cylinder_family

/-- XIV.2(ダンベル、完):首(円柱)の族:W = 0、半径 R の円柱は Λ = 1/R² − 1/R⁴、時間の向き k² = (2 − R²)/R⁴(AdS₂ × S²、平坦 × S²、dS₂ × S²)。Λ ≤ 1/(4ℓ²)、等号は R = √2ℓ(磁荷 1 の RN–de Sitter の超冷極限、Plebański–Hacyan の Minkowski₂ × S²)。Λ = 0 では R = ℓ(新しい柱の首 = ブースト × 回転)。dS₂ × S²(k² < 0)は ν′ が定数の形では表せず、Lean の範囲外。運動学:首。作用:EYM + Λ。力学:首の三つの顔 -/
alias XIV_2_cylinder_max := CFT.Smooth.cylinder_max

/-- XIV.3(ダンベル、完):静的宇宙 + YM は厳密解:r = √2ℓ sin(s/√2ℓ)、W = cos(s/√2ℓ)、Λ = 3/(4ℓ²)。帽子(量子の球)をそのまま閉じた静的な世界。運動学:帽子(S³ 全体)。作用:EYM + Λ。力学:閉じた滑らかな形の n = 1 -/
alias XIV_3_esu_ym := CFT.Smooth.esu_ym

/-- XIV.4(ダンベル、完(外)):閉じた滑らかな形の列(葉巻):EYM + Λ には極から極まで縫い目のない静的な解が Λ_n = 3/4、0.364244、0.293218、0.270328、0.260895、… → 1/4 で並ぶ(数値で 10 段まで、文献と 6 桁一致)。n が増えると中央は半径 √2ℓ の円柱(超冷)に近づき(長さの 53% → 71%)、1 段ごとの長さの伸びは漸近的に π√2ℓ(静的宇宙 1 個分)に近づく(n = 10 で 4.34ℓ)。中央の YM は cos(s/√2ℓ)(静的宇宙と同じ関数)。運動学:帽子 + 首 + 帽子(縫い目なし)。作用:EYM + Λ(外部:Volkov ほか 1996、hep-th/9605089)。力学:滑らかなダンベル(太さのそろった葉巻) -/
alias XIV_4_cylinder_mode := CFT.Smooth.cylinder_mode

/-- XIV.4(ダンベル、完(外)):閉じた滑らかな形の列(葉巻):EYM + Λ には極から極まで縫い目のない静的な解が Λ_n = 3/4、0.364244、0.293218、0.270328、0.260895、… → 1/4 で並ぶ(数値で 10 段まで、文献と 6 桁一致)。n が増えると中央は半径 √2ℓ の円柱(超冷)に近づき(長さの 53% → 71%)、1 段ごとの長さの伸びは漸近的に π√2ℓ(静的宇宙 1 個分)に近づく(n = 10 で 4.34ℓ)。中央の YM は cos(s/√2ℓ)(静的宇宙と同じ関数)。運動学:帽子 + 首 + 帽子(縫い目なし)。作用:EYM + Λ(外部:Volkov ほか 1996、hep-th/9605089)。力学:滑らかなダンベル(太さのそろった葉巻) -/
alias XIV_4_esu_ym := CFT.Smooth.esu_ym

/-- XIV.4(ダンベル、完(外)):閉じた滑らかな形の列(葉巻):EYM + Λ には極から極まで縫い目のない静的な解が Λ_n = 3/4、0.364244、0.293218、0.270328、0.260895、… → 1/4 で並ぶ(数値で 10 段まで、文献と 6 桁一致)。n が増えると中央は半径 √2ℓ の円柱(超冷)に近づき(長さの 53% → 71%)、1 段ごとの長さの伸びは漸近的に π√2ℓ(静的宇宙 1 個分)に近づく(n = 10 で 4.34ℓ)。中央の YM は cos(s/√2ℓ)(静的宇宙と同じ関数)。運動学:帽子 + 首 + 帽子(縫い目なし)。作用:EYM + Λ(外部:Volkov ほか 1996、hep-th/9605089)。力学:滑らかなダンベル(太さのそろった葉巻) -/
alias XIV_4_cylinder_max := CFT.Smooth.cylinder_max

/-- XIV.5(ダンベル、完):喉(AdS₂ × S²)の中の YM は BF 下限を破る:有効質量 −1 < −1/4、解 e^{−s/2}cos(√3 s/2)。これが BM の節が無限に続く理由。運動学:首。作用:YM(喉の上の線形化)。力学:首の不安定性(XI と整合) -/
alias XIV_5_throat_mode := CFT.Smooth.throat_mode

/-- XIV.5(ダンベル、完):喉(AdS₂ × S²)の中の YM は BF 下限を破る:有効質量 −1 < −1/4、解 e^{−s/2}cos(√3 s/2)。これが BM の節が無限に続く理由。運動学:首。作用:YM(喉の上の線形化)。力学:首の不安定性(XI と整合) -/
alias XIV_5_bf_violation := CFT.Smooth.bf_violation

/-- XIV.6(ダンベル、完(外)):BM 列の量子化:1 − M_n ∝ e^{−πn/√3}(比 6.13、n = 8 まで)、喉の長さは 1 段ごとに π/√3 ℓ ずつ伸び、喉の中の節の間隔は 2π/√3 ℓ(数値と XIV.5 の線形解析が一致)。運動学:首。作用:EYM。力学:首の長さが n で量子化される -/
alias XIV_6_throat_mode := CFT.Smooth.throat_mode

/-- XIV.6(ダンベル、完(外)):BM 列の量子化:1 − M_n ∝ e^{−πn/√3}(比 6.13、n = 8 まで)、喉の長さは 1 段ごとに π/√3 ℓ ずつ伸び、喉の中の節の間隔は 2π/√3 ℓ(数値と XIV.5 の線形解析が一致)。運動学:首。作用:EYM。力学:首の長さが n で量子化される -/
alias XIV_6_bf_violation := CFT.Smooth.bf_violation

/-- XIV.7(ダンベル、完):二つの n は別物:量子の n は sl(2,ℝ) の離散系列(実のウェイト h、Casimir h(h − 1) ≥ −1/4)の準位。古典の n(YM の節の数)は首の W の Casimir −1(主系列、Δ = ½ ± i√3/2)の対数周期の節で、間隔は 2π/√3。Casimir −1 は離散系列に現れない。運動学:首。作用:—。力学:二つの n は別の種類の表現に属する -/
alias XIV_7_oc_discrete_casimir := CFT.OC.oc_discrete_casimir

/-- XIV.7(ダンベル、完):二つの n は別物:量子の n は sl(2,ℝ) の離散系列(実のウェイト h、Casimir h(h − 1) ≥ −1/4)の準位。古典の n(YM の節の数)は首の W の Casimir −1(主系列、Δ = ½ ± i√3/2)の対数周期の節で、間隔は 2π/√3。Casimir −1 は離散系列に現れない。運動学:首。作用:—。力学:二つの n は別の種類の表現に属する -/
alias XIV_7_oc_principal := CFT.OC.oc_principal

/-- XIV.7(ダンベル、完):二つの n は別物:量子の n は sl(2,ℝ) の離散系列(実のウェイト h、Casimir h(h − 1) ≥ −1/4)の準位。古典の n(YM の節の数)は首の W の Casimir −1(主系列、Δ = ½ ± i√3/2)の対数周期の節で、間隔は 2π/√3。Casimir −1 は離散系列に現れない。運動学:首。作用:—。力学:二つの n は別の種類の表現に属する -/
alias XIV_7_oc_node_spacing := CFT.OC.oc_node_spacing

/-- XIV.8(ダンベル、完):帽子と首の倍率の足し算 Ω = A cos η + B/sin u(AB ≠ 0)は、どの時間帯でも EYM の解にならない:kl 成分から (1 − W²)² = A²S⁴ + 2ABcS + B²、これを微分した式と N₊ − N₋ を合わせると √D の 3 次式になり、開集合の上では成り立たない(定理)。AB cos η > 0 の極の近くではヌルエネルギー条件も破る。運動学:静的宇宙の上の Ω の重ね合わせ。作用:EYM。力学:否定的(定理):Ω の方程式は線形でも、拘束が重ね合わせを禁じる -/
alias XIV_8_superpos_null := CFT.Smooth.superpos_null

/-- XIV.8(ダンベル、完):帽子と首の倍率の足し算 Ω = A cos η + B/sin u(AB ≠ 0)は、どの時間帯でも EYM の解にならない:kl 成分から (1 − W²)² = A²S⁴ + 2ABcS + B²、これを微分した式と N₊ − N₋ を合わせると √D の 3 次式になり、開集合の上では成り立たない(定理)。AB cos η > 0 の極の近くではヌルエネルギー条件も破る。運動学:静的宇宙の上の Ω の重ね合わせ。作用:EYM。力学:否定的(定理):Ω の方程式は線形でも、拘束が重ね合わせを禁じる -/
alias XIV_8_oq_M_superpos := CFT.OQ.oq_M_superpos

/-- XIV.8(ダンベル、完):帽子と首の倍率の足し算 Ω = A cos η + B/sin u(AB ≠ 0)は、どの時間帯でも EYM の解にならない:kl 成分から (1 − W²)² = A²S⁴ + 2ABcS + B²、これを微分した式と N₊ − N₋ を合わせると √D の 3 次式になり、開集合の上では成り立たない(定理)。AB cos η > 0 の極の近くではヌルエネルギー条件も破る。運動学:静的宇宙の上の Ω の重ね合わせ。作用:EYM。力学:否定的(定理):Ω の方程式は線形でも、拘束が重ね合わせを禁じる -/
alias XIV_8_oq_product := CFT.OQ.oq_product

/-- XIV.8(ダンベル、完):帽子と首の倍率の足し算 Ω = A cos η + B/sin u(AB ≠ 0)は、どの時間帯でも EYM の解にならない:kl 成分から (1 − W²)² = A²S⁴ + 2ABcS + B²、これを微分した式と N₊ − N₋ を合わせると √D の 3 次式になり、開集合の上では成り立たない(定理)。AB cos η > 0 の極の近くではヌルエネルギー条件も破る。運動学:静的宇宙の上の Ω の重ね合わせ。作用:EYM。力学:否定的(定理):Ω の方程式は線形でも、拘束が重ね合わせを禁じる -/
alias XIV_8_oq_no_superposition := CFT.OQ.oq_no_superposition


/-! ## α-XV Ω の量子幾何学:負の符号の自由場 Ω と YM、拘束でつながる -/

/-- XV.1(ダンベル、完(外)):共形の枠の Einstein–Hilbert の密度は √g R = 6Ω² − 6Ω□̂Ω で Ω の 2 次式。共形平坦な部分では、重力は静的宇宙の上の自由場 Ω(運動項の符号は負)で、YM は共形不変なので Ω と直接は結合しない。両者をつなぐのは拘束(N±、M:全体の応力が 0)だけ。運動学:静的宇宙 ℝ × S³ の上の Ω と W。作用:EH + YM(共形の枠)。力学:□̂Ω = Ω(線形)、拘束 = 全応力 0 -/
alias XV_1_oq_action_quadratic := CFT.OQ.oq_action_quadratic

/-- XV.2(ダンベル、完):面積半径 r = Ω sin χ は平らな 2 次元の波動方程式 r_ηη = r_χχ の解(トレースの方程式と同値)。r = F(η + χ) − F(η − χ)、帽子は F = (ℓ/2) sin、首は r = ℓ(定数)。運動学:面積半径 r(η, χ)。作用:EH(トレース)。力学:ダランベールの解 -/
alias XV_2_oq_radius_wave := CFT.OQ.oq_radius_wave

/-- XV.2(ダンベル、完):面積半径 r = Ω sin χ は平らな 2 次元の波動方程式 r_ηη = r_χχ の解(トレースの方程式と同値)。r = F(η + χ) − F(η − χ)、帽子は F = (ℓ/2) sin、首は r = ℓ(定数)。運動学:面積半径 r(η, χ)。作用:EH(トレース)。力学:ダランベールの解 -/
alias XV_2_oq_cap_dalembert := CFT.OQ.oq_cap_dalembert

/-- XV.3(ダンベル、完):両方の極で正則なら F は周期 2π。対蹠の写像 (η, χ) ↦ (η + π, π − χ) で Ω ↦ −Ω、計量 Ω²ĝ は不変:Ω = 0 の面(始まりと終わり)を越えると宇宙は対蹠の像として繰り返す(共形の時間で周期 π)。運動学:静的宇宙の対蹠の写像。作用:EH(トレース)。力学:共形的に周期的な宇宙 -/
alias XV_3_oq_periodic := CFT.OQ.oq_periodic

/-- XV.3(ダンベル、完):両方の極で正則なら F は周期 2π。対蹠の写像 (η, χ) ↦ (η + π, π − χ) で Ω ↦ −Ω、計量 Ω²ĝ は不変:Ω = 0 の面(始まりと終わり)を越えると宇宙は対蹠の像として繰り返す(共形の時間で周期 π)。運動学:静的宇宙の対蹠の写像。作用:EH(トレース)。力学:共形的に周期的な宇宙 -/
alias XV_3_oq_antipodal := CFT.OQ.oq_antipodal

/-- XV.4(ダンベル、完):一様なモードの量子化(仮定を明示した形):Ω は質量 M = 3π/(2G)、振動数 1 の振動子(符号は負)で、エネルギー (M/2)ℓ² = n + ½ ⇔ ℓ² = (2n + 1)/M、つまり ℓ²/G = 4(n + ½)/(3π)。古典の拘束は ℓ² = 4πG/g²。YM 側を障壁の頂上の値 K とおけば g²/(4π) = 3π/(4n + 2)(半古典。固有値としての扱いは XII.8)。運動学:一様なモード(振動数 1)。作用:EH + YM(ミニ超空間)。力学:ℓ² の量子化(Ω の振動子) -/
alias XV_4_oq_energy_coeff := CFT.OQ.oq_energy_coeff

/-- XV.4(ダンベル、完):一様なモードの量子化(仮定を明示した形):Ω は質量 M = 3π/(2G)、振動数 1 の振動子(符号は負)で、エネルギー (M/2)ℓ² = n + ½ ⇔ ℓ² = (2n + 1)/M、つまり ℓ²/G = 4(n + ½)/(3π)。古典の拘束は ℓ² = 4πG/g²。YM 側を障壁の頂上の値 K とおけば g²/(4π) = 3π/(4n + 2)(半古典。固有値としての扱いは XII.8)。運動学:一様なモード(振動数 1)。作用:EH + YM(ミニ超空間)。力学:ℓ² の量子化(Ω の振動子) -/
alias XV_4_oq_classical_scale := CFT.OQ.oq_classical_scale

/-- XV.4(ダンベル、完):一様なモードの量子化(仮定を明示した形):Ω は質量 M = 3π/(2G)、振動数 1 の振動子(符号は負)で、エネルギー (M/2)ℓ² = n + ½ ⇔ ℓ² = (2n + 1)/M、つまり ℓ²/G = 4(n + ½)/(3π)。古典の拘束は ℓ² = 4πG/g²。YM 側を障壁の頂上の値 K とおけば g²/(4π) = 3π/(4n + 2)(半古典。固有値としての扱いは XII.8)。運動学:一様なモード(振動数 1)。作用:EH + YM(ミニ超空間)。力学:ℓ² の量子化(Ω の振動子) -/
alias XV_4_oq_quantized_scale := CFT.OQ.oq_quantized_scale

/-- XV.4(ダンベル、完):一様なモードの量子化(仮定を明示した形):Ω は質量 M = 3π/(2G)、振動数 1 の振動子(符号は負)で、エネルギー (M/2)ℓ² = n + ½ ⇔ ℓ² = (2n + 1)/M、つまり ℓ²/G = 4(n + ½)/(3π)。古典の拘束は ℓ² = 4πG/g²。YM 側を障壁の頂上の値 K とおけば g²/(4π) = 3π/(4n + 2)(半古典。固有値としての扱いは XII.8)。運動学:一様なモード(振動数 1)。作用:EH + YM(ミニ超空間)。力学:ℓ² の量子化(Ω の振動子) -/
alias XV_4_oc_omega_level := CFT.OC.oc_omega_level

/-- XV.5(ダンベル、完):状態と境界条件:sl(2,ℝ) で不変な配位は r = Ω sin χ が定数(首)。極で r = 0(正則)なら恒等的に 0。正則な宇宙(帽子)は対称性で不変になれず、必ず軌道の上を動く。首は極が無限遠にある不変な配位。運動学:帽子と首。作用:EH + YM。力学:正則な宇宙は対称性を破る -/
alias XV_5_oq_neck_unique := CFT.OQ.oq_neck_unique

/-- XV.5(ダンベル、完):状態と境界条件:sl(2,ℝ) で不変な配位は r = Ω sin χ が定数(首)。極で r = 0(正則)なら恒等的に 0。正則な宇宙(帽子)は対称性で不変になれず、必ず軌道の上を動く。首は極が無限遠にある不変な配位。運動学:帽子と首。作用:EH + YM。力学:正則な宇宙は対称性を破る -/
alias XV_5_oc_invariant_not_regular := CFT.OC.oc_invariant_not_regular

/-- XV.6(ダンベル、完(外)):残るゲージの対称性:共形平坦・球対称な部分で、座標の取り直しとして残るのは三つの共形 Killing ベクトルで、交換関係は so(2,1) ≅ sl(2,ℝ)([∂_η, ξ₁] = ξ₂、[∂_η, ξ₂] = −ξ₁、[ξ₁, ξ₂] = −∂_η)。sl(2,ℝ) は中心拡大をもたない(半単純、外部の定理)。局所的な拘束 N±、M は W を Ω から決めてしまい、線形の剛性(X.11)により局所の自由度を残さない。運動学:三つの共形 Killing ベクトル。作用:EH + YM(共形平坦な部分)。力学:残る対称性は sl(2,ℝ) -/
alias XV_6_oq_sl2_bracket := CFT.OQ.oq_sl2_bracket

/-- XV.7(ダンベル、完):首は sl(2,ℝ) で不変なただ一つの配位:Ω = ℓ/sin χ、W = 0 は三つの生成子すべてで δΩ = 0、δW = 0。逆に、静的で ξ₁ で不変な Ω は定数/sin χ だけ。帽子のゲージの対称性(静的宇宙の共形 Killing)は、ちょうど首 AdS₂ の等長変換。帽子は不変でなく、sl(2,ℝ) の軌道の上を動く。運動学:首と帽子。作用:EH + YM。力学:首 = 不変な配位(真空にあたる)、帽子 = その上の軌道 -/
alias XV_7_oq_neck_invariant := CFT.OQ.oq_neck_invariant

/-- XV.7(ダンベル、完):首は sl(2,ℝ) で不変なただ一つの配位:Ω = ℓ/sin χ、W = 0 は三つの生成子すべてで δΩ = 0、δW = 0。逆に、静的で ξ₁ で不変な Ω は定数/sin χ だけ。帽子のゲージの対称性(静的宇宙の共形 Killing)は、ちょうど首 AdS₂ の等長変換。帽子は不変でなく、sl(2,ℝ) の軌道の上を動く。運動学:首と帽子。作用:EH + YM。力学:首 = 不変な配位(真空にあたる)、帽子 = その上の軌道 -/
alias XV_7_oq_neck_unique := CFT.OQ.oq_neck_unique

/-- XV.8(ダンベル、完(外)):すべてのモードの量子化の結論:球対称に縮約した重力の作用は r の自由な波動(符号は負)。共形平坦・球対称・磁気的な部分では、ゲージが Ω の k = 1、k = 2 と W の n = 0 の 3 つの振動子(位相空間の 6 次元 = 生成子 3 × 2)を除き、残りは拘束が禁じる(線形の剛性):局所の自由度はなく、この部分の量子論は自明(状態は一つ)。一様等方な部分(Ω と f)では Wheeler–DeWitt 方程式が厳密で、解は YM の固有関数と Ω の放物柱関数の積(Ω が時計、既知の構造)。結合定数は量子化されない。運動学:Ω と W のすべてのモード。作用:EH + YM。力学:共形平坦な部分は量子論でも剛い。新しい数には共形平坦の外が要る -/
alias XV_8_ol_reduced_action := CFT.OL.ol_reduced_action

/-- XV.8(ダンベル、完(外)):すべてのモードの量子化の結論:球対称に縮約した重力の作用は r の自由な波動(符号は負)。共形平坦・球対称・磁気的な部分では、ゲージが Ω の k = 1、k = 2 と W の n = 0 の 3 つの振動子(位相空間の 6 次元 = 生成子 3 × 2)を除き、残りは拘束が禁じる(線形の剛性):局所の自由度はなく、この部分の量子論は自明(状態は一つ)。一様等方な部分(Ω と f)では Wheeler–DeWitt 方程式が厳密で、解は YM の固有関数と Ω の放物柱関数の積(Ω が時計、既知の構造)。結合定数は量子化されない。運動学:Ω と W のすべてのモード。作用:EH + YM。力学:共形平坦な部分は量子論でも剛い。新しい数には共形平坦の外が要る -/
alias XV_8_ol_gauge_k2 := CFT.OL.ol_gauge_k2

/-- XV.8(ダンベル、完(外)):すべてのモードの量子化の結論:球対称に縮約した重力の作用は r の自由な波動(符号は負)。共形平坦・球対称・磁気的な部分では、ゲージが Ω の k = 1、k = 2 と W の n = 0 の 3 つの振動子(位相空間の 6 次元 = 生成子 3 × 2)を除き、残りは拘束が禁じる(線形の剛性):局所の自由度はなく、この部分の量子論は自明(状態は一つ)。一様等方な部分(Ω と f)では Wheeler–DeWitt 方程式が厳密で、解は YM の固有関数と Ω の放物柱関数の積(Ω が時計、既知の構造)。結合定数は量子化されない。運動学:Ω と W のすべてのモード。作用:EH + YM。力学:共形平坦な部分は量子論でも剛い。新しい数には共形平坦の外が要る -/
alias XV_8_ol_gauge_count := CFT.OL.ol_gauge_count

/-- XV.9(ダンベル、完(外)):共形平坦の外の線形の量子化(重力波):帽子の幾何(a″ = −a)の上で、非等方な応力の摂動がないとき、テンソルの摂動 h″ + 2(a′/a)h′ + (n² − 1)h = 0 は μ = a h で μ″ = −n²μ。共形時間で整数の振動数 n ≥ 3 の調和振動子(縮退度 2(n² − 4))で、Fock 空間による量子化ができる。Ω(振動数 1、符号は負)、YM(√((n+2)² − 3))と並ぶ三つ目の系列(テンソルの調和関数の固有値は外部)。運動学:帽子の上のテンソルのモード。作用:EH(二次まで)。力学:重力波は整数の振動数の振動子 -/
alias XV_9_os_graviton := CFT.OS.os_graviton

/-- XV.9(ダンベル、完(外)):共形平坦の外の線形の量子化(重力波):帽子の幾何(a″ = −a)の上で、非等方な応力の摂動がないとき、テンソルの摂動 h″ + 2(a′/a)h′ + (n² − 1)h = 0 は μ = a h で μ″ = −n²μ。共形時間で整数の振動数 n ≥ 3 の調和振動子(縮退度 2(n² − 4))で、Fock 空間による量子化ができる。Ω(振動数 1、符号は負)、YM(√((n+2)² − 3))と並ぶ三つ目の系列(テンソルの調和関数の固有値は外部)。運動学:帽子の上のテンソルのモード。作用:EH(二次まで)。力学:重力波は整数の振動数の振動子 -/
alias XV_9_os_graviton_count := CFT.OS.os_graviton_count

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_hamiltonian := CFT.KS.ks_hamiltonian

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_rn := CFT.KS.ks_rn

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_hj := CFT.KS.ks_hj

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_hj_solves := CFT.KS.ks_hj_solves

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_inversion_theta := CFT.KS.ks_inversion_theta

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_inversion_sigma := CFT.KS.ks_inversion_sigma

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_fold_id := CFT.KS.ks_fold_id

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_fold_le := CFT.KS.ks_fold_le

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_fold_eq := CFT.KS.ks_fold_eq

/-- XV.9-K(ダンベル、完):首の側の量子重力の方程式(Kantowski–Sachs 型のミニ超空間 a(t)、r(t)、W(t)):拘束は −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c² a(1 − ℓ²(1 − W²)²/r²) で、p_r について 1 次(r が時計)。W = 0 の部分は σ = a²r/2、θ = −(r + ℓ²/r)/2 で ∂_σ∂_θΨ = −4c²Ψ(平坦な 2 次元の Klein–Gordon、厳密に解ける。演算子の順序を一つ選んだ場合)。反転 r → ℓ²/r、a → a r/ℓ は対称性で、θ ≤ −ℓ、等号は r = ℓ だけ:首はミニ超空間の折り目にあり、波動関数は反転について偶か奇かの境界条件を要する。W の方向は W = 0 で逆さの振動子(首の不安定性 XI.1 の量子版)。RN の内部の KS 型の WDW は先行研究がある(要確認)。運動学:首と RN の内部。作用:EH + YM(ミニ超空間)。力学:首はミニ超空間の折り目 -/
alias XV_9K_ks_inverted := CFT.KS.ks_inverted

-- XV.10(ダンベル、未着手):量子重力の本体:YM の背景ではテンソルのモードがゲージ場のテンソルのモードと混ざる(非等方な応力)。その結合と、線形を超えた量子化。運動学:一般の計量。作用:EH + YM。力学:—(Lean の定理なし:外部定理の引用または未着手)


end CFT.Index
