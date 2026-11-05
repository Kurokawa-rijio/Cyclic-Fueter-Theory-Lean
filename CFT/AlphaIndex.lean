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
import CFT.AlphaPillar_Polar
import CFT.AlphaPillar_SelfDual
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

/-- III.1(ダンベル、部):Israel 接合と法線応力の跳び。運動学:接合面。作用:EYM の Einstein 方程式。力学:法線応力の跳び -/
alias III_1_israel_jump := CFT.AlphaIII.israel_jump

/-- III.1(ダンベル、部):Israel 接合と法線応力の跳び。運動学:接合面。作用:EYM の Einstein 方程式。力学:法線応力の跳び -/
alias III_1_gauss_tube := CFT.S4J.gauss_tube

/-- III.2(ダンベル、部):波面での k^μ[T_μν] = 0。運動学:ヌルの波面。作用:EYM。力学:応力の跳びの条件 -/
alias III_2_null_front := CFT.AlphaIII.null_front

/-- III.2(ダンベル、部):波面での k^μ[T_μν] = 0。運動学:ヌルの波面。作用:EYM。力学:応力の跳びの条件 -/
alias III_2_jump_mixed := CFT.S4J.jump_mixed

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

/-- III.9(ダンベル、部):Gauss–Codazzi、時間的・空間的・ヌルの接合。運動学:接合面。作用:Einstein 方程式。力学:接合条件の分類 -/
alias III_9_no_shell_iff := CFT.Junction.no_shell_iff

/-- III.9(ダンベル、部):Gauss–Codazzi、時間的・空間的・ヌルの接合。運動学:接合面。作用:Einstein 方程式。力学:接合条件の分類 -/
alias III_9_constraint_form := CFT.Junction.constraint_form


/-! ## α-IV 時間発展と崩壊 -/

/-- IV.1(ダンベル、完(外)):初期データと適切性。運動学:帽子・首の初期データ。作用:EYM。力学:拘束と適切性 -/
alias IV_1_cap_constraint := CFT.AlphaIntegrals.cap_constraint

/-- IV.1(ダンベル、完(外)):初期データと適切性。運動学:帽子・首の初期データ。作用:EYM。力学:拘束と適切性 -/
alias IV_1_neck_constraint := CFT.SelfDual.neck_constraint

/-- IV.1(ダンベル、完(外)):初期データと適切性。運動学:帽子・首の初期データ。作用:EYM。力学:拘束と適切性 -/
alias IV_1_junction_jumps := CFT.AlphaIntegrals.junction_jumps

/-- IV.2(ダンベル、部):波面での跳びの輸送 [W_u]、[r_uu]。運動学:波面。作用:EYM(二重ヌル)。力学:跳びの輸送 -/
alias IV_2_jump_const := CFT.AlphaIV.jump_const

/-- IV.2(ダンベル、部):波面での跳びの輸送 [W_u]、[r_uu]。運動学:波面。作用:EYM(二重ヌル)。力学:跳びの輸送 -/
alias IV_2_ruu_jump := CFT.AlphaIV.ruu_jump

/-- IV.2(ダンベル、部):波面での跳びの輸送 [W_u]、[r_uu]。運動学:波面。作用:EYM(二重ヌル)。力学:跳びの輸送 -/
alias IV_2_goursat_W := CFT.S5.goursat_W

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
alias VII_7_zero_mode := CFT.BridgeTwist.zero_mode

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
alias IX_9_mass_shell := CFT.SelfDual.mass_shell

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

/-- X.6(—、部):すべての最終定理に非空性。運動学:—。作用:—。力学:— -/
alias X_6_nonempty_cap := CFT.Unify.nonempty_cap

/-- X.6(—、部):すべての最終定理に非空性。運動学:—。作用:—。力学:— -/
alias X_6_nonempty_magnetic := CFT.FixThermo.nonempty_magnetic

/-- X.6(—、部):すべての最終定理に非空性。運動学:—。作用:—。力学:— -/
alias X_6_nonempty_window := CFT.FixNeck.nonempty_window

-- X.7(ダンベル、未着手):数値:くさびの特性発展と大域的な継続。運動学:帽子・首・接合。作用:EYM。力学:—(Lean の定理なし:外部定理の引用または未着手)

-- X.8(ダンベル、未着手):閉じたダンベルの全エネルギーは 0(ハミルトン拘束の積分)。運動学:ダンベル全体(閉じた空間)。作用:EYM + GHY。力学:—(Lean の定理なし:外部定理の引用または未着手)

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

-- X.10(ダンベル、未着手):作用はどこから決まるか:XI.4 の随伴 Higgs の出どころ(VII.8 の SO(10) の破れ、S⁹ の楕円体との関係)。運動学:内部空間 S⁹ と首。作用:—。力学:—(Lean の定理なし:外部定理の引用または未着手)

-- X.11(ダンベル、未着手):帽子そのものの安定性(閉じた輻射 FRW の線形摂動)。運動学:帽子。作用:EYM。力学:—(Lean の定理なし:外部定理の引用または未着手)

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_gauge_singlet := CFT.BridgeTwist.gauge_singlet

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_eps_xsT := CFT.BridgeTwist.eps_xsT

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_xs_sq := CFT.BridgeTwist.xs_sq

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_pole_singlet := CFT.BridgeTwist.pole_singlet

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_chi_deriv := CFT.BridgeTwist.chi_deriv

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_conformal_transfer := CFT.BridgeTwist.conformal_transfer

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_twist_cancel := CFT.BridgeTwist.twist_cancel

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_system_reduce := CFT.BridgeTwist.system_reduce

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
alias X_12_zero_mode := CFT.BridgeTwist.zero_mode

/-- X.12(ダンベル、完(外)):W = r′ はねじれ:スピンとアイソスピンの一重項の上でスピン接続とゲージ場が打ち消し合う。湯川を入れたゼロモードは exp(∓∫m) で、二つの帽子に一つずつ局在(VII.8-C の否定的な結果が指した先)。運動学:断面 dρ² + r²dΩ²、W = r′、極 2 の純粋ゲージ。作用:Dirac + 随伴 Higgs の湯川。力学:係数 (r′ − W)/r = 0、f = exp(∓∫m)、g = ±if、首で |f|² ≤ e^{−2m₀x} -/
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

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、純粋に磁気的な EYM(W = r′)の中では C² のダンベルはない。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_curvature_jump := CFT.RootJunction.curvature_jump

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、純粋に磁気的な EYM(W = r′)の中では C² のダンベルはない。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_stress_jump := CFT.RootJunction.stress_jump

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、純粋に磁気的な EYM(W = r′)の中では C² のダンベルはない。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_hamC_quadratic := CFT.RootJunction.hamC_quadratic

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、純粋に磁気的な EYM(W = r′)の中では C² のダンベルはない。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_junction_two_values := CFT.RootJunction.junction_two_values

/-- X.14(ダンベル、完):接合での跳びの診断:形は C¹ でつながるが、曲率 ³R は 6/ℓ² → 2/ℓ²、密度は 3 分の 1、半径方向の圧力は符号が変わる。ハミルトン拘束は r″ の 2 次式で、接合では r″ = 0 と −1/ℓ の二つだけなので、純粋に磁気的な EYM(W = r′)の中では C² のダンベルはない。運動学:帽子と首の接合 (r, r′) = (ℓ, 0)。作用:EYM + ハミルトン拘束。力学:C² の接合は不可能(つなぎ方か作用を変える必要) -/
alias X_14_no_C2_junction := CFT.RootJunction.no_C2_junction


/-! ## α-XI 弱い重力予想と首の安定性 -/

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(数値、X.7))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_liouville_actual := CFT.FixNeck.liouville_actual

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(数値、X.7))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_actual_form_neg := CFT.FixNeck.actual_form_neg

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(数値、X.7))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
alias XI_1_growth_rate_bound := CFT.FixNeck.growth_rate_bound

/-- XI.1(ダンベル、完(外)):首の不安定性の時間スケール(崩壊前の e 倍は首の中心の時計 = 共通のガウス時間で。接合のそばで測ると L によらず約 0.4 回(数値、X.7))。運動学:首(大域 AdS₂)と接合 u_c。作用:W の 2 次の作用。力学:λ² ≥ (3/4 − π²/16)e^{2(L/ℓ−4)}/π²、L/ℓ ≥ 7 で崩壊前に e 倍 -/
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

-- XI.5(ダンベル、未着手):dyon の首:電荷 q を加えたアトラクター(2pq = ℓ²)と W の安定性。E·B ≠ 0 で本当のカイラリティ(アノマリー)が出るか(X.12 の続き)。運動学:首(磁荷 p と電荷 q)。作用:EYM(+ ディラトン)。力学:—(Lean の定理なし:外部定理の引用または未着手)

-- XI.6(ダンベル、未着手):実効的な負の宇宙定数(V.7-N)での Hawking–Page 型の相転移。運動学:首。作用:量子応力を含む有効作用。力学:—(Lean の定理なし:外部定理の引用または未着手)

-- XI.7(ダンベル、未着手):Higgs を入れたときの帽子と接合(W = cos χ の解の変化)。運動学:帽子・接合。作用:EYM + 随伴 Higgs。力学:—(Lean の定理なし:外部定理の引用または未着手)


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

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_curvature_real := CFT.SelfDual.curvature_real

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_norm_c := CFT.SelfDual.norm_c

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_friedmann_selfdual := CFT.SelfDual.friedmann_selfdual

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_phase_lemma := CFT.SelfDual.phase_lemma

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_cap_hubble := CFT.SelfDual.cap_hubble

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_cap_modulus := CFT.SelfDual.cap_modulus

/-- XII.3(ダンベル、完(外)):自己双対接続 A = Γ + iK で帽子を書く:c = 1 + iȧ、曲率の係数 c² − 2c = −|c|² は実数、Friedmann ⇔ |c|² = (8πG/3)ρa²、位相 = 共形時間 η(c·cos η = e^{−iη})。運動学:帽子 a = ℓ cos η(Γ = 回転、K = ȧ = ブースト)。作用:EH(Ashtekar の自己双対の変数、外部:拘束の同値)+ YM。力学:|c| = ℓ/a、arg c = −η -/
alias XII_3_cap_rhs := CFT.SelfDual.cap_rhs

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる、位相 t/ℓ -/
alias XII_4_neck_extrinsic := CFT.SelfDual.neck_extrinsic

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる、位相 t/ℓ -/
alias XII_4_neck_constraint := CFT.SelfDual.neck_constraint

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる、位相 t/ℓ -/
alias XII_4_spin_is_witten := CFT.Action.spin_is_witten

/-- XII.4(ダンベル、完(外)):首は「回転(S²)× ブースト(AdS₂)」:S² の向きは単極子 cos θ dφ(回転だけ)、AdS₂ の向きは K^z_z = −tan(t/ℓ)/ℓ(ブーストだけ)、拘束は ³R = 16πGρ。運動学:首(同期の座標)。作用:EH(自己双対の変数)+ YM。力学:極分解が首の幾何として現れる、位相 t/ℓ -/
alias XII_4_neck_einstein := CFT.FixGeo.neck_einstein

/-- XII.5(ダンベル、完):始まりと終わり:位相 0(純粋な回転 = 頂点、時間対称な瞬間)から π/2(純粋なブースト:帽子の崩壊と首の焦点)へ、帽子と首が同じ位相の時計で同時に回り切る。運動学:帽子と首。作用:EH + YM。力学:e^{−i0} = 1、e^{−iπ/2} = −i -/
alias XII_5_end_phase := CFT.SelfDual.end_phase

/-- XII.5(ダンベル、完):始まりと終わり:位相 0(純粋な回転 = 頂点、時間対称な瞬間)から π/2(純粋なブースト:帽子の崩壊と首の焦点)へ、帽子と首が同じ位相の時計で同時に回り切る。運動学:帽子と首。作用:EH + YM。力学:e^{−i0} = 1、e^{−iπ/2} = −i -/
alias XII_5_phase_lemma := CFT.SelfDual.phase_lemma

/-- XII.6(ダンベル、完(外)):テスト B:U21′(YM 場 = スピン接続、W = r′)は「YM 場 = 自己双対接続の実部(回転の部分)」と同じで、帽子と首ではすべての時刻で成り立つ(くさびの中の一般の発展では未)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM + 新しい原理(YM = Re A)。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_real_part := CFT.SelfDual.real_part

/-- XII.6(ダンベル、完(外)):テスト B:U21′(YM 場 = スピン接続、W = r′)は「YM 場 = 自己双対接続の実部(回転の部分)」と同じで、帽子と首ではすべての時刻で成り立つ(くさびの中の一般の発展では未)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM + 新しい原理(YM = Re A)。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_cap_real_part := CFT.SelfDual.cap_real_part

/-- XII.6(ダンベル、完(外)):テスト B:U21′(YM 場 = スピン接続、W = r′)は「YM 場 = 自己双対接続の実部(回転の部分)」と同じで、帽子と首ではすべての時刻で成り立つ(くさびの中の一般の発展では未)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM + 新しい原理(YM = Re A)。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_spin_is_witten := CFT.Action.spin_is_witten

/-- XII.6(ダンベル、完(外)):テスト B:U21′(YM 場 = スピン接続、W = r′)は「YM 場 = 自己双対接続の実部(回転の部分)」と同じで、帽子と首ではすべての時刻で成り立つ(くさびの中の一般の発展では未)。運動学:帽子(W = cos χ は半径 a によらない)、首(W = 0)。作用:EYM + 新しい原理(YM = Re A)。力学:厳密な領域で力学と矛盾しない -/
alias XII_6_frw_exact := CFT.EYM.frw_exact

/-- XII.7(ダンベル、完):v6 の再現:帽子の自己双対接続は v6 の質量殻と量子半球をなぞる(Γ = 質量、K = 運動量、|A| = エネルギー、位相 = Gudermann の角)。帽子の一生 = 量子半球を頂点(静止)から赤道(光速)へ。運動学:量子半球 Q、質量殻、帽子。作用:EH + YM(自己双対の変数)。力学:a/ℓ = cos η = 1/cosh ζ = m/E、ȧ = −sinh ζ -/
alias XII_7_mass_shell := CFT.SelfDual.mass_shell

/-- XII.7(ダンベル、完):v6 の再現:帽子の自己双対接続は v6 の質量殻と量子半球をなぞる(Γ = 質量、K = 運動量、|A| = エネルギー、位相 = Gudermann の角)。帽子の一生 = 量子半球を頂点(静止)から赤道(光速)へ。運動学:量子半球 Q、質量殻、帽子。作用:EH + YM(自己双対の変数)。力学:a/ℓ = cos η = 1/cosh ζ = m/E、ȧ = −sinh ζ -/
alias XII_7_gudermann_phase := CFT.SelfDual.gudermann_phase

/-- XII.7(ダンベル、完):v6 の再現:帽子の自己双対接続は v6 の質量殻と量子半球をなぞる(Γ = 質量、K = 運動量、|A| = エネルギー、位相 = Gudermann の角)。帽子の一生 = 量子半球を頂点(静止)から赤道(光速)へ。運動学:量子半球 Q、質量殻、帽子。作用:EH + YM(自己双対の変数)。力学:a/ℓ = cos η = 1/cosh ζ = m/E、ȧ = −sinh ζ -/
alias XII_7_cap_modulus := CFT.SelfDual.cap_modulus

-- XII.8(ダンベル、未着手):テスト C:新しい柱から新しい数を出す(WGC の窓、質量ギャップなど)。運動学:—。作用:—。力学:—(Lean の定理なし:外部定理の引用または未着手)


end CFT.Index
