import CFT.Spherical.WedgeDifferenceSystem
import CFT.Spherical.WedgeEnergyBalance
import CFT.Spherical.WedgeEnergyAnalytic
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 4-7（一意性）の第3歩：差の場へのエネルギー評価の
  出発点を、δW（`WedgeDifferenceEnergy.lean`）から δr・δΩ へ広げる。
  `WedgeDifferenceSystem.lean` で導出した差の線形系のうち r 方程式
    Duv δr = a_r·δOm + b_r·δW + c_r·δr + d_r·δru + e_r·δrv
  と Ω 方程式
    Duv δΩ = a_Om·δOu + b_Om·δOv + c_Om·δOm + d_Om·δruv + e_Om·δr + f_Om·δW
  （係数は2つの解で決まる）を解析版（`CFT.Wedge.Du` / `Dv` / `Duv`）で述べ、
  それぞれ u・v 方向のエネルギー恒等式とフラックス形を証明し、矩形上の発散定理
  （`WedgeEnergyBalance.rect_divergence`）と組み合わせて矩形上のエネルギー収支を
  得る。v 方向の恒等式では 4-5・δW 版と同じく混合偏微分の可換性を仮定する。
  これで差の場 (δr, δΩ, δW) の三つすべてにエネルギー収支が揃った。
  残り：差の線形系へのエネルギー評価と特性方向のグロンウォール（4-7 の本体）、
  拘束の差の線形系。
-/

open CFT.Wedge
open CFT.WedgeBalance
open CFT.WedgeDifference
open MeasureTheory intervalIntegral
open scoped Interval

namespace CFT.WedgeDifferenceEnergyROm

noncomputable section

/-! ### δr の差のエネルギー -/

/-- 2つの動径場の差 δr = r - r'。 -/
noncomputable def diffRFun (r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  r u v - r' u v

/-- 差の r 方程式の右辺の δOm 係数（`wedgeRuv_diff_linear` の第1項）。 -/
noncomputable def diffRCoefOm (W r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  2⁻¹ * ((1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2 - 1) * (r u v)⁻¹

/-- 差の r 方程式の右辺の δW 係数（`wedgeRuv_diff_linear` の第2項）。 -/
noncomputable def diffRCoefW (Om' W W' r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  2⁻¹ * Om' u v * (-((W u v) + (W' u v)) * (2 - (W u v) ^ 2 - (W' u v) ^ 2)
    * ((r u v)⁻¹) ^ 3)

/-- 差の r 方程式の右辺の δr 係数（`wedgeRuv_diff_linear` の第3・4項の δr 部分）。 -/
noncomputable def diffRCoefR (Om' W' r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  2⁻¹ * Om' u v * ((1 - (W' u v) ^ 2) ^ 2
      * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
        * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3)
    + (r u v)⁻¹ * (r' u v)⁻¹)
    + (Du r' u v) * (Dv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹

/-- 差の r 方程式の右辺の δru 係数（ru = Du r、係数は -rv * r⁻¹）。 -/
noncomputable def diffRCoefRu (r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  -(Dv r u v) * (r u v)⁻¹

/-- 差の r 方程式の右辺の δrv 係数（rv = Dv r、係数は -ru' * r⁻¹）。 -/
noncomputable def diffRCoefRv (r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  -(Du r' u v) * (r u v)⁻¹

/-- 差の r 方程式の右辺（線形源項）。 -/
noncomputable def diffRSource (Om Om' W W' r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  diffRCoefOm W r u v * (Om u v - Om' u v)
    + diffRCoefW Om' W W' r u v * (W u v - W' u v)
    + diffRCoefR Om' W' r r' u v * (r u v - r' u v)
    + diffRCoefRu r u v * (Du r u v - Du r' u v)
    + diffRCoefRv r r' u v * (Dv r u v - Dv r' u v)

/-- `rhsR` は導分代数版の `wedgeRuv` と同じ値（r ≠ 0 のもと）。 -/
theorem rhsR_eq_wedgeRuv {Om W ru rv r : ℝ} (hr : r ≠ 0) :
    CFT.Wedge.rhsR Om W ru rv r = CFT.WedgeDifference.wedgeRuv Om W ru rv r := by
  show (1 / 2) * Om * ((1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r
    = 2⁻¹ * Om * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹ - ru * rv * r⁻¹
  field_simp

/-- 2つの解の r 方程式の右辺の差は、差の線形源項に等しい。 -/
theorem rhsR_sub_eq_source {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0) :
    CFT.Wedge.rhsR (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v)
      - CFT.Wedge.rhsR (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v)
      = diffRSource Om Om' W W' r r' u v := by
  rw [rhsR_eq_wedgeRuv hr, rhsR_eq_wedgeRuv hr']
  show CFT.WedgeDifference.wedgeRuv (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v)
      - CFT.WedgeDifference.wedgeRuv (Om' u v) (W' u v) (Du r' u v) (Dv r' u v)
          (r' u v)
      = diffRSource Om Om' W W' r r' u v
  rw [wedgeRuv_diff_linear (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v)
    (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v) hr hr']
  simp only [diffRSource, diffRCoefOm, diffRCoefW, diffRCoefR, diffRCoefRu,
    diffRCoefRv]
  ring

/-- δr の v 偏微分は各解の v 偏微分の差。 -/
theorem diffR_Dv_eq {r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hrv : Differentiable ℝ (fun v' => r u v'))
    (hrv' : Differentiable ℝ (fun v' => r' u v')) :
    Dv (diffRFun r r') u v = Dv r u v - Dv r' u v := by
  show deriv (fun v' => r u v' - r' u v') v
    = deriv (fun v' => r u v') v - deriv (fun v' => r' u v') v
  rw [deriv_sub (hrv v) (hrv' v)]

/-- δr の u 偏微分は各解の u 偏微分の差。 -/
theorem diffR_Du_eq {r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hru : Differentiable ℝ (fun u' => r u' v))
    (hru' : Differentiable ℝ (fun u' => r' u' v)) :
    Du (diffRFun r r') u v = Du r u v - Du r' u v := by
  show deriv (fun u' => r u' v - r' u' v) u
    = deriv (fun u' => r u' v) u - deriv (fun u' => r' u' v) u
  rw [deriv_sub (hru u) (hru' u)]

/-- 差の r 方程式（解析版）：Duv δr = 線形源項。 -/
theorem diffR_eq_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hrv' : ∀ u, Differentiable ℝ (fun v' => r' u v'))
    (hDvRu : Differentiable ℝ (fun u' => Dv r u' v))
    (hDvR'u : Differentiable ℝ (fun u' => Dv r' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hRuv : Duv r u v
      = CFT.Wedge.rhsR (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v))
    (hRuv' : Duv r' u v
      = CFT.Wedge.rhsR (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v)) :
    Duv (diffRFun r r') u v = diffRSource Om Om' W W' r r' u v := by
  have hfun : (fun u' => Dv (diffRFun r r') u' v)
      = (fun u' => Dv r u' v - Dv r' u' v) :=
    funext fun u' => diffR_Dv_eq (hrv u') (hrv' u')
  have hDuv : Duv (diffRFun r r') u v = Duv r u v - Duv r' u v := by
    show deriv (fun u' => Dv (diffRFun r r') u' v) u
      = deriv (fun u' => Dv r u' v) u - deriv (fun u' => Dv r' u' v) u
    rw [hfun]
    exact deriv_sub (hDvRu u) (hDvR'u u)
  rw [hDuv, hRuv, hRuv']
  exact rhsR_sub_eq_source hr hr'

/-- δr の v 偏微分の u スライスの微分可能性。 -/
theorem diffR_Dv_diff_u {r r' : ℝ → ℝ → ℝ} {v : ℝ}
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hrv' : ∀ u, Differentiable ℝ (fun v' => r' u v'))
    (hDvRu : Differentiable ℝ (fun u' => Dv r u' v))
    (hDvR'u : Differentiable ℝ (fun u' => Dv r' u' v)) :
    Differentiable ℝ (fun u' => Dv (diffRFun r r') u' v) := by
  have hfun : (fun u' => Dv (diffRFun r r') u' v)
      = (fun u' => Dv r u' v - Dv r' u' v) :=
    funext fun u' => diffR_Dv_eq (hrv u') (hrv' u')
  rw [hfun]
  exact hDvRu.sub hDvR'u

/-- δr の u 偏微分の v スライスの微分可能性。 -/
theorem diffR_Du_diff_v {r r' : ℝ → ℝ → ℝ} {u : ℝ}
    (hru : ∀ v, Differentiable ℝ (fun u' => r u' v))
    (hru' : ∀ v, Differentiable ℝ (fun u' => r' u' v))
    (hDuRv : Differentiable ℝ (fun v' => Du r u v'))
    (hDuR'v : Differentiable ℝ (fun v' => Du r' u v')) :
    Differentiable ℝ (fun v' => Du (diffRFun r r') u v') := by
  have hfun : (fun v' => Du (diffRFun r r') u v')
      = (fun v' => Du r u v' - Du r' u v') :=
    funext fun v' => diffR_Du_eq (hru v') (hru' v')
  rw [hfun]
  exact hDuRv.sub hDuR'v

/-- 4-7（差の場 δr の u 方向のエネルギー恒等式の解析版）：
    ∂_u ((δr_v)²/2) = (δr_v)·(線形源項)。
    可換性を使わない（差の r 方程式を Duv の形で直接使う）。 -/
theorem diffR_energy_u_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hrv' : ∀ u, Differentiable ℝ (fun v' => r' u v'))
    (hDvRu : Differentiable ℝ (fun u' => Dv r u' v))
    (hDvR'u : Differentiable ℝ (fun u' => Dv r' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hRuv : Duv r u v
      = CFT.Wedge.rhsR (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v))
    (hRuv' : Duv r' u v
      = CFT.Wedge.rhsR (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v)) :
    Du (fun u v => (Dv (diffRFun r r') u v) ^ 2 / 2) u v
      = (Dv (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v := by
  have hdiff : Differentiable ℝ (fun u' => Dv (diffRFun r r') u' v) :=
    diffR_Dv_diff_u hrv hrv' hDvRu hDvR'u
  have h1 : deriv (fun u' => (Dv (diffRFun r r') u' v) ^ 2 / 2) u
      = (Dv (diffRFun r r') u v) * (Du (Dv (diffRFun r r')) u v) := by
    have h : HasDerivAt (fun u' => (Dv (diffRFun r r') u' v) ^ 2 / 2)
        ((2 : ℝ) * (Dv (diffRFun r r') u v) ^ (2 - 1)
          * (Du (Dv (diffRFun r r')) u v) / 2) u :=
      ((hdiff u).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : Du (Dv (diffRFun r r')) u v = diffRSource Om Om' W W' r r' u v :=
    diffR_eq_analytic hrv hrv' hDvRu hDvR'u hr hr' hRuv hRuv'
  show deriv (fun u' => (Dv (diffRFun r r') u' v) ^ 2 / 2) u
    = (Dv (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v
  rw [h1, h2]

/-- 4-7（差の場 δr の v 方向のエネルギー恒等式の解析版）：
    ∂_v ((δr_u)²/2) = (δr_u)·(線形源項)。
    混合偏微分の可換性 Dv (Du δr) = Duv δr を仮定する。 -/
theorem diffR_energy_v_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hru : ∀ v, Differentiable ℝ (fun u' => r u' v))
    (hru' : ∀ v, Differentiable ℝ (fun u' => r' u' v))
    (hDuRv : Differentiable ℝ (fun v' => Du r u v'))
    (hDuR'v : Differentiable ℝ (fun v' => Du r' u v'))
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hrv' : ∀ u, Differentiable ℝ (fun v' => r' u v'))
    (hDvRu : Differentiable ℝ (fun u' => Dv r u' v))
    (hDvR'u : Differentiable ℝ (fun u' => Dv r' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hRuv : Duv r u v
      = CFT.Wedge.rhsR (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v))
    (hRuv' : Duv r' u v
      = CFT.Wedge.rhsR (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v))
    (hcomm : Dv (Du (diffRFun r r')) u v = Duv (diffRFun r r') u v) :
    Dv (fun u v => (Du (diffRFun r r') u v) ^ 2 / 2) u v
      = (Du (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v := by
  have hdiff : Differentiable ℝ (fun v' => Du (diffRFun r r') u v') :=
    diffR_Du_diff_v hru hru' hDuRv hDuR'v
  have h1 : deriv (fun v' => (Du (diffRFun r r') u v') ^ 2 / 2) v
      = (Du (diffRFun r r') u v) * (Dv (Du (diffRFun r r')) u v) := by
    have h : HasDerivAt (fun v' => (Du (diffRFun r r') u v') ^ 2 / 2)
        ((2 : ℝ) * (Du (diffRFun r r') u v) ^ (2 - 1)
          * (Dv (Du (diffRFun r r')) u v) / 2) v :=
      ((hdiff v).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : Dv (Du (diffRFun r r')) u v = diffRSource Om Om' W W' r r' u v := by
    rw [hcomm]
    exact diffR_eq_analytic hrv hrv' hDvRu hDvR'u hr hr' hRuv hRuv'
  show deriv (fun v' => (Du (diffRFun r r') u v') ^ 2 / 2) v
    = (Du (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v
  rw [h1, h2]

/-- 差の場 δr のフラックスの u 成分 F^u = (δr_v)²/2。 -/
noncomputable def diffRFuFun (r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Dv (diffRFun r r') u v) ^ 2 / 2

/-- 差の場 δr のフラックスの v 成分 F^v = (δr_u)²/2。 -/
noncomputable def diffRFvFun (r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Du (diffRFun r r') u v) ^ 2 / 2

/-- 4-7（差の場 δr のフラックス恒等式の解析版）：
    ∂_u F^u + ∂_v F^v = (δr_v + δr_u)·(線形源項)。 -/
theorem diffR_flux_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hrv' : ∀ u, Differentiable ℝ (fun v' => r' u v'))
    (hru : ∀ v, Differentiable ℝ (fun u' => r u' v))
    (hru' : ∀ v, Differentiable ℝ (fun u' => r' u' v))
    (hDvRu : Differentiable ℝ (fun u' => Dv r u' v))
    (hDvR'u : Differentiable ℝ (fun u' => Dv r' u' v))
    (hDuRv : Differentiable ℝ (fun v' => Du r u v'))
    (hDuR'v : Differentiable ℝ (fun v' => Du r' u v'))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hRuv : Duv r u v
      = CFT.Wedge.rhsR (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v))
    (hRuv' : Duv r' u v
      = CFT.Wedge.rhsR (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v))
    (hcomm : Dv (Du (diffRFun r r')) u v = Duv (diffRFun r r') u v) :
    Du (diffRFuFun r r') u v + Dv (diffRFvFun r r') u v
      = (Dv (diffRFun r r') u v + Du (diffRFun r r') u v)
        * diffRSource Om Om' W W' r r' u v := by
  have hu := diffR_energy_u_analytic hrv hrv' hDvRu hDvR'u hr hr' hRuv hRuv'
  have hv := diffR_energy_v_analytic hru hru' hDuRv hDuR'v hrv hrv' hDvRu hDvR'u
    hr hr' hRuv hRuv' hcomm
  show Du (fun u v => (Dv (diffRFun r r') u v) ^ 2 / 2) u v
      + Dv (fun u v => (Du (diffRFun r r') u v) ^ 2 / 2) u v
      = (Dv (diffRFun r r') u v + Du (diffRFun r r') u v)
        * diffRSource Om Om' W W' r r' u v
  linear_combination hu + hv

/-- 4-7（差の場 δr の矩形上のエネルギー収支）：
    差のフラックス恒等式と矩形上の発散定理を組み合わせ、境界フラックス =
    源 (δr_v + δr_u)·(線形源項) の二重積分を得る。
    dFu・dFv の連続性は仮定する。 -/
theorem diffR_energy_balance_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ}
    {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hrv' : ∀ u, Differentiable ℝ (fun v' => r' u v'))
    (hru : ∀ v, Differentiable ℝ (fun u' => r u' v))
    (hru' : ∀ v, Differentiable ℝ (fun u' => r' u' v))
    (hDvR : ∀ v, Differentiable ℝ (fun u' => Dv r u' v))
    (hDvR' : ∀ v, Differentiable ℝ (fun u' => Dv r' u' v))
    (hDuR : ∀ u, Differentiable ℝ (fun v' => Du r u v'))
    (hDuR' : ∀ u, Differentiable ℝ (fun v' => Du r' u v'))
    (hr0 : ∀ u v, r u v ≠ 0) (hr0' : ∀ u v, r' u v ≠ 0)
    (hRuv : ∀ u v, Duv r u v
      = CFT.Wedge.rhsR (Om u v) (W u v) (Du r u v) (Dv r u v) (r u v))
    (hRuv' : ∀ u v, Duv r' u v
      = CFT.Wedge.rhsR (Om' u v) (W' u v) (Du r' u v) (Dv r' u v) (r' u v))
    (hcomm : ∀ u v, Dv (Du (diffRFun r r')) u v = Duv (diffRFun r r') u v)
    (hFu_c : Continuous (Function.uncurry fun u v =>
      (Dv (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v))
    (hFv_c : Continuous (Function.uncurry fun u v =>
      (Du (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v)) :
    (∫ v in v0..v1, (diffRFuFun r r' u1 v - diffRFuFun r r' u0 v))
      + (∫ u in u0..u1, (diffRFvFun r r' u v1 - diffRFvFun r r' u v0))
      = ∫ u in u0..u1, ∫ v in v0..v1,
          (Dv (diffRFun r r') u v + Du (diffRFun r r') u v)
            * diffRSource Om Om' W W' r r' u v := by
  have hFu_diff : ∀ v, Differentiable ℝ (fun u' => diffRFuFun r r' u' v) := by
    intro v
    show Differentiable ℝ (fun u' => (Dv (diffRFun r r') u' v) ^ 2 / 2)
    exact ((diffR_Dv_diff_u hrv hrv' (hDvR v) (hDvR' v)).pow 2).div_const 2
  have hFv_diff : ∀ u, Differentiable ℝ (fun v' => diffRFvFun r r' u v') := by
    intro u
    show Differentiable ℝ (fun v' => (Du (diffRFun r r') u v') ^ 2 / 2)
    exact ((diffR_Du_diff_v hru hru' (hDuR u) (hDuR' u)).pow 2).div_const 2
  have hFu_deriv : ∀ v, ∀ u, HasDerivAt (fun u' => diffRFuFun r r' u' v)
      ((Dv (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v) u := by
    intro v u
    have h := diffR_energy_u_analytic hrv hrv' (hDvR v) (hDvR' v)
      (hr0 u v) (hr0' u v) (hRuv u v) (hRuv' u v)
    have hder : deriv (fun u' => diffRFuFun r r' u' v) u
        = (Dv (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v := h
    exact (hFu_diff v u).hasDerivAt.congr_deriv hder
  have hFv_deriv : ∀ u, ∀ v, HasDerivAt (fun v' => diffRFvFun r r' u v')
      ((Du (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v) v := by
    intro u v
    have h := diffR_energy_v_analytic hru hru' (hDuR u) (hDuR' u) hrv hrv'
      (hDvR v) (hDvR' v) (hr0 u v) (hr0' u v) (hRuv u v) (hRuv' u v) (hcomm u v)
    have hder : deriv (fun v' => diffRFvFun r r' u v') v
        = (Du (diffRFun r r') u v) * diffRSource Om Om' W W' r r' u v := h
    exact (hFv_diff u v).hasDerivAt.congr_deriv hder
  have h := rect_divergence hu hv hFu_deriv hFv_deriv hFu_c hFv_c
  rw [h]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  ring

/-! ### δΩ の差のエネルギー -/

/-- 2つの計量関数の差 δΩ = Ω - Ω'。 -/
noncomputable def diffOmFun (Om Om' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  Om u v - Om' u v

/-- 差の Ω 方程式の右辺の δOu 係数（Ou = Du Ω、係数は Ov * Om⁻¹）。 -/
noncomputable def diffOmCoefOu (Om : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Dv Om u v) * (Om u v)⁻¹

/-- 差の Ω 方程式の右辺の δOv 係数（Ov = Dv Ω、係数は Ou' * Om⁻¹）。 -/
noncomputable def diffOmCoefOv (Om Om' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Du Om' u v) * (Om u v)⁻¹

/-- 差の Ω 方程式の右辺の δOm 係数（`wedgeOmuv_diff_linear` の δOm 部分）。 -/
noncomputable def diffOmCoefOm (Om Om' W r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  -(Du Om' u v) * (Dv Om' u v) * (Om u v)⁻¹ * (Om' u v)⁻¹
    - 2 * (Duv r u v) * (r u v)⁻¹
    - ((Om u v) + (Om' u v)) * (1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 4

/-- 差の Ω 方程式の右辺の δruv 係数（ruv = Duv r、係数は -2 * Om' * r⁻¹）。 -/
noncomputable def diffOmCoefRuv (Om' r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  -2 * Om' u v * (r u v)⁻¹

/-- 差の Ω 方程式の右辺の δr 係数（`wedgeOmuv_diff_linear` の δr 部分）。 -/
noncomputable def diffOmCoefR (Om' W' r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  2 * Om' u v * (Duv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹
    + (Om' u v) ^ 2 * (1 - (W' u v) ^ 2) ^ 2
      * ((r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2
        + (r' u v) ^ 3) * ((r u v)⁻¹) ^ 4 * ((r' u v)⁻¹) ^ 4

/-- 差の Ω 方程式の右辺の δW 係数（`wedgeOmuv_diff_linear` の δW 部分）。 -/
noncomputable def diffOmCoefW (Om' W W' r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Om' u v) ^ 2 * ((W u v) + (W' u v)) * (2 - (W u v) ^ 2 - (W' u v) ^ 2)
    * ((r u v)⁻¹) ^ 4

/-- 差の Ω 方程式の右辺（線形源項）。 -/
noncomputable def diffOmSource (Om Om' W W' r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  diffOmCoefOu Om u v * (Du Om u v - Du Om' u v)
    + diffOmCoefOv Om Om' u v * (Dv Om u v - Dv Om' u v)
    + diffOmCoefOm Om Om' W r u v * (Om u v - Om' u v)
    + diffOmCoefRuv Om' r u v * (Duv r u v - Duv r' u v)
    + diffOmCoefR Om' W' r r' u v * (r u v - r' u v)
    + diffOmCoefW Om' W W' r u v * (W u v - W' u v)

/-- `rhsOm` は導分代数版の `wedgeOmuv` と同じ値（r ≠ 0、Ω ≠ 0 のもと）。 -/
theorem rhsOm_eq_wedgeOmuv {Om Ou Ov ruv r W : ℝ} (hr : r ≠ 0) (hOm : Om ≠ 0) :
    CFT.Wedge.rhsOm Om Ou Ov ruv r W
      = CFT.WedgeDifference.wedgeOmuv Om Ou Ov ruv r W := by
  show Ou * Ov / Om - 2 * Om * ruv / r - Om ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4
    = Ou * Ov * Om⁻¹ - 2 * Om * ruv * r⁻¹ - Om ^ 2 * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4
  field_simp

/-- 2つの解の Ω 方程式の右辺の差は、差の線形源項に等しい。 -/
theorem rhsOm_sub_eq_source {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hOm : Om u v ≠ 0) (hOm' : Om' u v ≠ 0) :
    CFT.Wedge.rhsOm (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v) (W u v)
      - CFT.Wedge.rhsOm (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v)
          (r' u v) (W' u v)
      = diffOmSource Om Om' W W' r r' u v := by
  rw [rhsOm_eq_wedgeOmuv hr hOm, rhsOm_eq_wedgeOmuv hr' hOm']
  show CFT.WedgeDifference.wedgeOmuv (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v)
        (r u v) (W u v)
      - CFT.WedgeDifference.wedgeOmuv (Om' u v) (Du Om' u v) (Dv Om' u v)
          (Duv r' u v) (r' u v) (W' u v)
      = diffOmSource Om Om' W W' r r' u v
  rw [wedgeOmuv_diff_linear (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v)
    (W u v) (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v) (r' u v) (W' u v)
    hr hr' hOm hOm']
  simp only [diffOmSource, diffOmCoefOu, diffOmCoefOv, diffOmCoefOm, diffOmCoefRuv,
    diffOmCoefR, diffOmCoefW]
  ring

/-- δΩ の v 偏微分は各解の v 偏微分の差。 -/
theorem diffOm_Dv_eq {Om Om' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOmv : Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : Differentiable ℝ (fun v' => Om' u v')) :
    Dv (diffOmFun Om Om') u v = Dv Om u v - Dv Om' u v := by
  show deriv (fun v' => Om u v' - Om' u v') v
    = deriv (fun v' => Om u v') v - deriv (fun v' => Om' u v') v
  rw [deriv_sub (hOmv v) (hOmv' v)]

/-- δΩ の u 偏微分は各解の u 偏微分の差。 -/
theorem diffOm_Du_eq {Om Om' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOmu : Differentiable ℝ (fun u' => Om u' v))
    (hOmu' : Differentiable ℝ (fun u' => Om' u' v)) :
    Du (diffOmFun Om Om') u v = Du Om u v - Du Om' u v := by
  show deriv (fun u' => Om u' v - Om' u' v) u
    = deriv (fun u' => Om u' v) u - deriv (fun u' => Om' u' v) u
  rw [deriv_sub (hOmu u) (hOmu' u)]

/-- 差の Ω 方程式（解析版）：Duv δΩ = 線形源項。 -/
theorem diffOm_eq_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : ∀ u, Differentiable ℝ (fun v' => Om' u v'))
    (hDvOmu : Differentiable ℝ (fun u' => Dv Om u' v))
    (hDvOm'u : Differentiable ℝ (fun u' => Dv Om' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hOm : Om u v ≠ 0) (hOm' : Om' u v ≠ 0)
    (hOmuv : Duv Om u v
      = CFT.Wedge.rhsOm (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v)
          (W u v))
    (hOmuv' : Duv Om' u v
      = CFT.Wedge.rhsOm (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v)
          (r' u v) (W' u v)) :
    Duv (diffOmFun Om Om') u v = diffOmSource Om Om' W W' r r' u v := by
  have hfun : (fun u' => Dv (diffOmFun Om Om') u' v)
      = (fun u' => Dv Om u' v - Dv Om' u' v) :=
    funext fun u' => diffOm_Dv_eq (hOmv u') (hOmv' u')
  have hDuv : Duv (diffOmFun Om Om') u v = Duv Om u v - Duv Om' u v := by
    show deriv (fun u' => Dv (diffOmFun Om Om') u' v) u
      = deriv (fun u' => Dv Om u' v) u - deriv (fun u' => Dv Om' u' v) u
    rw [hfun]
    exact deriv_sub (hDvOmu u) (hDvOm'u u)
  rw [hDuv, hOmuv, hOmuv']
  exact rhsOm_sub_eq_source hr hr' hOm hOm'

/-- δΩ の v 偏微分の u スライスの微分可能性。 -/
theorem diffOm_Dv_diff_u {Om Om' : ℝ → ℝ → ℝ} {v : ℝ}
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : ∀ u, Differentiable ℝ (fun v' => Om' u v'))
    (hDvOmu : Differentiable ℝ (fun u' => Dv Om u' v))
    (hDvOm'u : Differentiable ℝ (fun u' => Dv Om' u' v)) :
    Differentiable ℝ (fun u' => Dv (diffOmFun Om Om') u' v) := by
  have hfun : (fun u' => Dv (diffOmFun Om Om') u' v)
      = (fun u' => Dv Om u' v - Dv Om' u' v) :=
    funext fun u' => diffOm_Dv_eq (hOmv u') (hOmv' u')
  rw [hfun]
  exact hDvOmu.sub hDvOm'u

/-- δΩ の u 偏微分の v スライスの微分可能性。 -/
theorem diffOm_Du_diff_v {Om Om' : ℝ → ℝ → ℝ} {u : ℝ}
    (hOmu : ∀ v, Differentiable ℝ (fun u' => Om u' v))
    (hOmu' : ∀ v, Differentiable ℝ (fun u' => Om' u' v))
    (hDuOmv : Differentiable ℝ (fun v' => Du Om u v'))
    (hDuOm'v : Differentiable ℝ (fun v' => Du Om' u v')) :
    Differentiable ℝ (fun v' => Du (diffOmFun Om Om') u v') := by
  have hfun : (fun v' => Du (diffOmFun Om Om') u v')
      = (fun v' => Du Om u v' - Du Om' u v') :=
    funext fun v' => diffOm_Du_eq (hOmu v') (hOmu' v')
  rw [hfun]
  exact hDuOmv.sub hDuOm'v

/-- 4-7（差の場 δΩ の u 方向のエネルギー恒等式の解析版）：
    ∂_u ((δΩ_v)²/2) = (δΩ_v)·(線形源項)。
    可換性を使わない（差の Ω 方程式を Duv の形で直接使う）。 -/
theorem diffOm_energy_u_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : ∀ u, Differentiable ℝ (fun v' => Om' u v'))
    (hDvOmu : Differentiable ℝ (fun u' => Dv Om u' v))
    (hDvOm'u : Differentiable ℝ (fun u' => Dv Om' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hOm : Om u v ≠ 0) (hOm' : Om' u v ≠ 0)
    (hOmuv : Duv Om u v
      = CFT.Wedge.rhsOm (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v)
          (W u v))
    (hOmuv' : Duv Om' u v
      = CFT.Wedge.rhsOm (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v)
          (r' u v) (W' u v)) :
    Du (fun u v => (Dv (diffOmFun Om Om') u v) ^ 2 / 2) u v
      = (Dv (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v := by
  have hdiff : Differentiable ℝ (fun u' => Dv (diffOmFun Om Om') u' v) :=
    diffOm_Dv_diff_u hOmv hOmv' hDvOmu hDvOm'u
  have h1 : deriv (fun u' => (Dv (diffOmFun Om Om') u' v) ^ 2 / 2) u
      = (Dv (diffOmFun Om Om') u v) * (Du (Dv (diffOmFun Om Om')) u v) := by
    have h : HasDerivAt (fun u' => (Dv (diffOmFun Om Om') u' v) ^ 2 / 2)
        ((2 : ℝ) * (Dv (diffOmFun Om Om') u v) ^ (2 - 1)
          * (Du (Dv (diffOmFun Om Om')) u v) / 2) u :=
      ((hdiff u).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : Du (Dv (diffOmFun Om Om')) u v
      = diffOmSource Om Om' W W' r r' u v :=
    diffOm_eq_analytic hOmv hOmv' hDvOmu hDvOm'u hr hr' hOm hOm' hOmuv hOmuv'
  show deriv (fun u' => (Dv (diffOmFun Om Om') u' v) ^ 2 / 2) u
    = (Dv (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v
  rw [h1, h2]

/-- 4-7（差の場 δΩ の v 方向のエネルギー恒等式の解析版）：
    ∂_v ((δΩ_u)²/2) = (δΩ_u)·(線形源項)。
    混合偏微分の可換性 Dv (Du δΩ) = Duv δΩ を仮定する。 -/
theorem diffOm_energy_v_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOmu : ∀ v, Differentiable ℝ (fun u' => Om u' v))
    (hOmu' : ∀ v, Differentiable ℝ (fun u' => Om' u' v))
    (hDuOmv : Differentiable ℝ (fun v' => Du Om u v'))
    (hDuOm'v : Differentiable ℝ (fun v' => Du Om' u v'))
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : ∀ u, Differentiable ℝ (fun v' => Om' u v'))
    (hDvOmu : Differentiable ℝ (fun u' => Dv Om u' v))
    (hDvOm'u : Differentiable ℝ (fun u' => Dv Om' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hOm : Om u v ≠ 0) (hOm' : Om' u v ≠ 0)
    (hOmuv : Duv Om u v
      = CFT.Wedge.rhsOm (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v)
          (W u v))
    (hOmuv' : Duv Om' u v
      = CFT.Wedge.rhsOm (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v)
          (r' u v) (W' u v))
    (hcomm : Dv (Du (diffOmFun Om Om')) u v = Duv (diffOmFun Om Om') u v) :
    Dv (fun u v => (Du (diffOmFun Om Om') u v) ^ 2 / 2) u v
      = (Du (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v := by
  have hdiff : Differentiable ℝ (fun v' => Du (diffOmFun Om Om') u v') :=
    diffOm_Du_diff_v hOmu hOmu' hDuOmv hDuOm'v
  have h1 : deriv (fun v' => (Du (diffOmFun Om Om') u v') ^ 2 / 2) v
      = (Du (diffOmFun Om Om') u v) * (Dv (Du (diffOmFun Om Om')) u v) := by
    have h : HasDerivAt (fun v' => (Du (diffOmFun Om Om') u v') ^ 2 / 2)
        ((2 : ℝ) * (Du (diffOmFun Om Om') u v) ^ (2 - 1)
          * (Dv (Du (diffOmFun Om Om')) u v) / 2) v :=
      ((hdiff v).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : Dv (Du (diffOmFun Om Om')) u v
      = diffOmSource Om Om' W W' r r' u v := by
    rw [hcomm]
    exact diffOm_eq_analytic hOmv hOmv' hDvOmu hDvOm'u hr hr' hOm hOm' hOmuv hOmuv'
  show deriv (fun v' => (Du (diffOmFun Om Om') u v') ^ 2 / 2) v
    = (Du (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v
  rw [h1, h2]

/-- 差の場 δΩ のフラックスの u 成分 F^u = (δΩ_v)²/2。 -/
noncomputable def diffOmFuFun (Om Om' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Dv (diffOmFun Om Om') u v) ^ 2 / 2

/-- 差の場 δΩ のフラックスの v 成分 F^v = (δΩ_u)²/2。 -/
noncomputable def diffOmFvFun (Om Om' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Du (diffOmFun Om Om') u v) ^ 2 / 2

/-- 4-7（差の場 δΩ のフラックス恒等式の解析版）：
    ∂_u F^u + ∂_v F^v = (δΩ_v + δΩ_u)·(線形源項)。 -/
theorem diffOm_flux_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : ∀ u, Differentiable ℝ (fun v' => Om' u v'))
    (hOmu : ∀ v, Differentiable ℝ (fun u' => Om u' v))
    (hOmu' : ∀ v, Differentiable ℝ (fun u' => Om' u' v))
    (hDvOmu : Differentiable ℝ (fun u' => Dv Om u' v))
    (hDvOm'u : Differentiable ℝ (fun u' => Dv Om' u' v))
    (hDuOmv : Differentiable ℝ (fun v' => Du Om u v'))
    (hDuOm'v : Differentiable ℝ (fun v' => Du Om' u v'))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hOm : Om u v ≠ 0) (hOm' : Om' u v ≠ 0)
    (hOmuv : Duv Om u v
      = CFT.Wedge.rhsOm (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v)
          (W u v))
    (hOmuv' : Duv Om' u v
      = CFT.Wedge.rhsOm (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v)
          (r' u v) (W' u v))
    (hcomm : Dv (Du (diffOmFun Om Om')) u v = Duv (diffOmFun Om Om') u v) :
    Du (diffOmFuFun Om Om') u v + Dv (diffOmFvFun Om Om') u v
      = (Dv (diffOmFun Om Om') u v + Du (diffOmFun Om Om') u v)
        * diffOmSource Om Om' W W' r r' u v := by
  have hu := diffOm_energy_u_analytic hOmv hOmv' hDvOmu hDvOm'u hr hr' hOm hOm'
    hOmuv hOmuv'
  have hv := diffOm_energy_v_analytic hOmu hOmu' hDuOmv hDuOm'v hOmv hOmv' hDvOmu
    hDvOm'u hr hr' hOm hOm' hOmuv hOmuv' hcomm
  show Du (fun u v => (Dv (diffOmFun Om Om') u v) ^ 2 / 2) u v
      + Dv (fun u v => (Du (diffOmFun Om Om') u v) ^ 2 / 2) u v
      = (Dv (diffOmFun Om Om') u v + Du (diffOmFun Om Om') u v)
        * diffOmSource Om Om' W W' r r' u v
  linear_combination hu + hv

/-- 4-7（差の場 δΩ の矩形上のエネルギー収支）：
    差のフラックス恒等式と矩形上の発散定理を組み合わせ、境界フラックス =
    源 (δΩ_v + δΩ_u)·(線形源項) の二重積分を得る。
    dFu・dFv の連続性は仮定する。 -/
theorem diffOm_energy_balance_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ}
    {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hOmv' : ∀ u, Differentiable ℝ (fun v' => Om' u v'))
    (hOmu : ∀ v, Differentiable ℝ (fun u' => Om u' v))
    (hOmu' : ∀ v, Differentiable ℝ (fun u' => Om' u' v))
    (hDvOm : ∀ v, Differentiable ℝ (fun u' => Dv Om u' v))
    (hDvOm' : ∀ v, Differentiable ℝ (fun u' => Dv Om' u' v))
    (hDuOm : ∀ u, Differentiable ℝ (fun v' => Du Om u v'))
    (hDuOm' : ∀ u, Differentiable ℝ (fun v' => Du Om' u v'))
    (hr0 : ∀ u v, r u v ≠ 0) (hr0' : ∀ u v, r' u v ≠ 0)
    (hOm0 : ∀ u v, Om u v ≠ 0) (hOm0' : ∀ u v, Om' u v ≠ 0)
    (hOmuv : ∀ u v, Duv Om u v
      = CFT.Wedge.rhsOm (Om u v) (Du Om u v) (Dv Om u v) (Duv r u v) (r u v)
          (W u v))
    (hOmuv' : ∀ u v, Duv Om' u v
      = CFT.Wedge.rhsOm (Om' u v) (Du Om' u v) (Dv Om' u v) (Duv r' u v)
          (r' u v) (W' u v))
    (hcomm : ∀ u v, Dv (Du (diffOmFun Om Om')) u v = Duv (diffOmFun Om Om') u v)
    (hFu_c : Continuous (Function.uncurry fun u v =>
      (Dv (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v))
    (hFv_c : Continuous (Function.uncurry fun u v =>
      (Du (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v)) :
    (∫ v in v0..v1, (diffOmFuFun Om Om' u1 v - diffOmFuFun Om Om' u0 v))
      + (∫ u in u0..u1, (diffOmFvFun Om Om' u v1 - diffOmFvFun Om Om' u v0))
      = ∫ u in u0..u1, ∫ v in v0..v1,
          (Dv (diffOmFun Om Om') u v + Du (diffOmFun Om Om') u v)
            * diffOmSource Om Om' W W' r r' u v := by
  have hFu_diff : ∀ v, Differentiable ℝ (fun u' => diffOmFuFun Om Om' u' v) := by
    intro v
    show Differentiable ℝ (fun u' => (Dv (diffOmFun Om Om') u' v) ^ 2 / 2)
    exact ((diffOm_Dv_diff_u hOmv hOmv' (hDvOm v) (hDvOm' v)).pow 2).div_const 2
  have hFv_diff : ∀ u, Differentiable ℝ (fun v' => diffOmFvFun Om Om' u v') := by
    intro u
    show Differentiable ℝ (fun v' => (Du (diffOmFun Om Om') u v') ^ 2 / 2)
    exact ((diffOm_Du_diff_v hOmu hOmu' (hDuOm u) (hDuOm' u)).pow 2).div_const 2
  have hFu_deriv : ∀ v, ∀ u, HasDerivAt (fun u' => diffOmFuFun Om Om' u' v)
      ((Dv (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v) u := by
    intro v u
    have h := diffOm_energy_u_analytic hOmv hOmv' (hDvOm v) (hDvOm' v)
      (hr0 u v) (hr0' u v) (hOm0 u v) (hOm0' u v) (hOmuv u v) (hOmuv' u v)
    have hder : deriv (fun u' => diffOmFuFun Om Om' u' v) u
        = (Dv (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v := h
    exact (hFu_diff v u).hasDerivAt.congr_deriv hder
  have hFv_deriv : ∀ u, ∀ v, HasDerivAt (fun v' => diffOmFvFun Om Om' u v')
      ((Du (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v) v := by
    intro u v
    have h := diffOm_energy_v_analytic hOmu hOmu' (hDuOm u) (hDuOm' u) hOmv hOmv'
      (hDvOm v) (hDvOm' v) (hr0 u v) (hr0' u v) (hOm0 u v) (hOm0' u v)
      (hOmuv u v) (hOmuv' u v) (hcomm u v)
    have hder : deriv (fun v' => diffOmFvFun Om Om' u v') v
        = (Du (diffOmFun Om Om') u v) * diffOmSource Om Om' W W' r r' u v := h
    exact (hFv_diff u v).hasDerivAt.congr_deriv hder
  have h := rect_divergence hu hv hFu_deriv hFv_deriv hFu_c hFv_c
  rw [h]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  ring

end

end CFT.WedgeDifferenceEnergyROm
