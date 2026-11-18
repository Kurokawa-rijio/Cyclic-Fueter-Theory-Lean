import CFT.Spherical.WedgeDifferenceSystem
import CFT.Spherical.WedgeEnergyBalance
import CFT.Spherical.WedgeEnergyAnalytic
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 4-7（一意性）の第2歩：差の場へのエネルギー評価の
  出発点として、4-5 のエネルギー恒等式・矩形上の積分収支を差の場 δW に当てはめる。
  `WedgeDifferenceSystem.lean` で導出した差の線形系のうち W 方程式
    Duv δW = a·δOm + b·δW + c·δr
  （係数 a・b・c は2つの解で決まる）を解析版（`CFT.Wedge.Du` / `Dv` / `Duv`）で
  述べ、u・v 方向のエネルギー恒等式
    ∂_u ((δW_v)²/2) = (δW_v)·(a·δOm + b·δW + c·δr)、
    ∂_v ((δW_u)²/2) = (δW_u)·(a·δOm + b·δW + c·δr)
  とフラックス形 ∂_u F^u + ∂_v F^v = (δW_v + δW_u)·(a·δOm + b·δW + c·δr)
  （F^u = (δW_v)²/2、F^v = (δW_u)²/2）を証明し、矩形上の発散定理
  （`WedgeEnergyBalance.rect_divergence`）と組み合わせて差の場の矩形上の
  エネルギー収支（境界フラックス = 源の二重積分）を得る。v 方向の恒等式では
  4-5 と同じく混合偏微分の可換性 Dv (Du δW) = Duv δW を仮定する。
  残り：差の線形系へのエネルギー評価と特性方向のグロンウォール（4-7 の本体）、
  r・Ω の差への同様の当てはめ、拘束の差の線形系。
-/

open CFT.Wedge
open CFT.WedgeBalance
open CFT.WedgeDifference
open MeasureTheory intervalIntegral
open scoped Interval

namespace CFT.WedgeDifferenceEnergy

noncomputable section

/-- 2つのゲージ場の差 δW = W - W'。 -/
noncomputable def diffWFun (W W' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  W u v - W' u v

/-- 差の W 方程式の右辺の δOm 係数（`wedgeWuv_diff_linear` の第1項）。 -/
noncomputable def diffWCoefOm (W r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  2⁻¹ * W u v * (1 - (W u v) ^ 2) * ((r u v)⁻¹) ^ 2

/-- 差の W 方程式の右辺の δW 係数（`wedgeWuv_diff_linear` の第2項）。 -/
noncomputable def diffWCoefW (Om' W W' r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  2⁻¹ * Om' u v * (1 - (W u v) ^ 2 - W u v * W' u v - (W' u v) ^ 2) * ((r u v)⁻¹) ^ 2

/-- 差の W 方程式の右辺の δr 係数（`wedgeWuv_diff_linear` の第3項）。 -/
noncomputable def diffWCoefR (Om' W' r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  -2⁻¹ * Om' u v * W' u v * (1 - (W' u v) ^ 2) * (r u v + r' u v)
    * ((r u v)⁻¹) ^ 2 * ((r' u v)⁻¹) ^ 2

/-- 差の W 方程式の右辺（線形源項）：a·δOm + b·δW + c·δr。 -/
noncomputable def diffWSource (Om Om' W W' r r' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  diffWCoefOm W r u v * (Om u v - Om' u v)
    + diffWCoefW Om' W W' r u v * (W u v - W' u v)
    + diffWCoefR Om' W' r r' u v * (r u v - r' u v)

/-- `rhsW` は導分代数版の `wedgeWuv` と同じ値（r ≠ 0 のもと）。 -/
theorem rhsW_eq_wedgeWuv {Om W r : ℝ} (hr : r ≠ 0) :
    CFT.Wedge.rhsW Om W r = CFT.WedgeEnergy.wedgeWuv Om W r := by
  show (1 / 2) * Om * W * (1 - W ^ 2) / r ^ 2
    = 2⁻¹ * Om * W * (1 - W ^ 2) * (r⁻¹) ^ 2
  field_simp

/-- 2つの解の W 方程式の右辺の差は、差の線形源項に等しい。 -/
theorem rhsW_sub_eq_source {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0) :
    CFT.Wedge.rhsW (Om u v) (W u v) (r u v)
      - CFT.Wedge.rhsW (Om' u v) (W' u v) (r' u v)
      = diffWSource Om Om' W W' r r' u v := by
  rw [rhsW_eq_wedgeWuv hr, rhsW_eq_wedgeWuv hr']
  show CFT.WedgeEnergy.wedgeWuv (Om u v) (W u v) (r u v)
      - CFT.WedgeEnergy.wedgeWuv (Om' u v) (W' u v) (r' u v)
      = diffWSource Om Om' W W' r r' u v
  rw [wedgeWuv_diff_linear (Om u v) (W u v) (r u v) (Om' u v) (W' u v) (r' u v) hr hr']
  simp only [diffWSource, diffWCoefOm, diffWCoefW, diffWCoefR]
  ring

/-- δW の v 偏微分は各解の v 偏微分の差。 -/
theorem diffW_Dv_eq {W W' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hWv : Differentiable ℝ (fun v' => W u v'))
    (hWv' : Differentiable ℝ (fun v' => W' u v')) :
    Dv (diffWFun W W') u v = Dv W u v - Dv W' u v := by
  show deriv (fun v' => W u v' - W' u v') v
    = deriv (fun v' => W u v') v - deriv (fun v' => W' u v') v
  rw [deriv_sub (hWv v) (hWv' v)]

/-- δW の u 偏微分は各解の u 偏微分の差。 -/
theorem diffW_Du_eq {W W' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hWu : Differentiable ℝ (fun u' => W u' v))
    (hWu' : Differentiable ℝ (fun u' => W' u' v)) :
    Du (diffWFun W W') u v = Du W u v - Du W' u v := by
  show deriv (fun u' => W u' v - W' u' v) u
    = deriv (fun u' => W u' v) u - deriv (fun u' => W' u' v) u
  rw [deriv_sub (hWu u) (hWu' u)]

/-- 差の W 方程式（解析版）：Duv δW = a·δOm + b·δW + c·δr。 -/
theorem diffW_eq_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hWv' : ∀ u, Differentiable ℝ (fun v' => W' u v'))
    (hDvWu : Differentiable ℝ (fun u' => Dv W u' v))
    (hDvW'u : Differentiable ℝ (fun u' => Dv W' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hWuv' : Duv W' u v = CFT.Wedge.rhsW (Om' u v) (W' u v) (r' u v)) :
    Duv (diffWFun W W') u v = diffWSource Om Om' W W' r r' u v := by
  have hfun : (fun u' => Dv (diffWFun W W') u' v)
      = (fun u' => Dv W u' v - Dv W' u' v) :=
    funext fun u' => diffW_Dv_eq (hWv u') (hWv' u')
  have hDuv : Duv (diffWFun W W') u v = Duv W u v - Duv W' u v := by
    show deriv (fun u' => Dv (diffWFun W W') u' v) u
      = deriv (fun u' => Dv W u' v) u - deriv (fun u' => Dv W' u' v) u
    rw [hfun]
    exact deriv_sub (hDvWu u) (hDvW'u u)
  rw [hDuv, hWuv, hWuv']
  exact rhsW_sub_eq_source hr hr'

/-- δW の v 偏微分の u スライスの微分可能性。 -/
theorem diffW_Dv_diff_u {W W' : ℝ → ℝ → ℝ} {v : ℝ}
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hWv' : ∀ u, Differentiable ℝ (fun v' => W' u v'))
    (hDvWu : Differentiable ℝ (fun u' => Dv W u' v))
    (hDvW'u : Differentiable ℝ (fun u' => Dv W' u' v)) :
    Differentiable ℝ (fun u' => Dv (diffWFun W W') u' v) := by
  have hfun : (fun u' => Dv (diffWFun W W') u' v)
      = (fun u' => Dv W u' v - Dv W' u' v) :=
    funext fun u' => diffW_Dv_eq (hWv u') (hWv' u')
  rw [hfun]
  exact hDvWu.sub hDvW'u

/-- δW の u 偏微分の v スライスの微分可能性。 -/
theorem diffW_Du_diff_v {W W' : ℝ → ℝ → ℝ} {u : ℝ}
    (hWu : ∀ v, Differentiable ℝ (fun u' => W u' v))
    (hWu' : ∀ v, Differentiable ℝ (fun u' => W' u' v))
    (hDuWv : Differentiable ℝ (fun v' => Du W u v'))
    (hDuW'v : Differentiable ℝ (fun v' => Du W' u v')) :
    Differentiable ℝ (fun v' => Du (diffWFun W W') u v') := by
  have hfun : (fun v' => Du (diffWFun W W') u v')
      = (fun v' => Du W u v' - Du W' u v') :=
    funext fun v' => diffW_Du_eq (hWu v') (hWu' v')
  rw [hfun]
  exact hDuWv.sub hDuW'v

/-- 4-7（差の場の u 方向のエネルギー恒等式の解析版）：
    ∂_u ((δW_v)²/2) = (δW_v)·(a·δOm + b·δW + c·δr)。
    可換性を使わない（差の W 方程式を Duv の形で直接使う）。 -/
theorem diffW_energy_u_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hWv' : ∀ u, Differentiable ℝ (fun v' => W' u v'))
    (hDvWu : Differentiable ℝ (fun u' => Dv W u' v))
    (hDvW'u : Differentiable ℝ (fun u' => Dv W' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hWuv' : Duv W' u v = CFT.Wedge.rhsW (Om' u v) (W' u v) (r' u v)) :
    Du (fun u v => (Dv (diffWFun W W') u v) ^ 2 / 2) u v
      = (Dv (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v := by
  have hdiff : Differentiable ℝ (fun u' => Dv (diffWFun W W') u' v) :=
    diffW_Dv_diff_u hWv hWv' hDvWu hDvW'u
  have h1 : deriv (fun u' => (Dv (diffWFun W W') u' v) ^ 2 / 2) u
      = (Dv (diffWFun W W') u v) * (Du (Dv (diffWFun W W')) u v) := by
    have h : HasDerivAt (fun u' => (Dv (diffWFun W W') u' v) ^ 2 / 2)
        ((2 : ℝ) * (Dv (diffWFun W W') u v) ^ (2 - 1)
          * (Du (Dv (diffWFun W W')) u v) / 2) u :=
      ((hdiff u).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : Du (Dv (diffWFun W W')) u v = diffWSource Om Om' W W' r r' u v :=
    diffW_eq_analytic hWv hWv' hDvWu hDvW'u hr hr' hWuv hWuv'
  show deriv (fun u' => (Dv (diffWFun W W') u' v) ^ 2 / 2) u
    = (Dv (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v
  rw [h1, h2]

/-- 4-7（差の場の v 方向のエネルギー恒等式の解析版）：
    ∂_v ((δW_u)²/2) = (δW_u)·(a·δOm + b·δW + c·δr)。
    混合偏微分の可換性 Dv (Du δW) = Duv δW を仮定する。 -/
theorem diffW_energy_v_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hWu : ∀ v, Differentiable ℝ (fun u' => W u' v))
    (hWu' : ∀ v, Differentiable ℝ (fun u' => W' u' v))
    (hDuWv : Differentiable ℝ (fun v' => Du W u v'))
    (hDuW'v : Differentiable ℝ (fun v' => Du W' u v'))
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hWv' : ∀ u, Differentiable ℝ (fun v' => W' u v'))
    (hDvWu : Differentiable ℝ (fun u' => Dv W u' v))
    (hDvW'u : Differentiable ℝ (fun u' => Dv W' u' v))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hWuv' : Duv W' u v = CFT.Wedge.rhsW (Om' u v) (W' u v) (r' u v))
    (hcomm : Dv (Du (diffWFun W W')) u v = Duv (diffWFun W W') u v) :
    Dv (fun u v => (Du (diffWFun W W') u v) ^ 2 / 2) u v
      = (Du (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v := by
  have hdiff : Differentiable ℝ (fun v' => Du (diffWFun W W') u v') :=
    diffW_Du_diff_v hWu hWu' hDuWv hDuW'v
  have h1 : deriv (fun v' => (Du (diffWFun W W') u v') ^ 2 / 2) v
      = (Du (diffWFun W W') u v) * (Dv (Du (diffWFun W W')) u v) := by
    have h : HasDerivAt (fun v' => (Du (diffWFun W W') u v') ^ 2 / 2)
        ((2 : ℝ) * (Du (diffWFun W W') u v) ^ (2 - 1)
          * (Dv (Du (diffWFun W W')) u v) / 2) v :=
      ((hdiff v).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : Dv (Du (diffWFun W W')) u v = diffWSource Om Om' W W' r r' u v := by
    rw [hcomm]
    exact diffW_eq_analytic hWv hWv' hDvWu hDvW'u hr hr' hWuv hWuv'
  show deriv (fun v' => (Du (diffWFun W W') u v') ^ 2 / 2) v
    = (Du (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v
  rw [h1, h2]

/-- 差の場のフラックスの u 成分 F^u = (δW_v)²/2。 -/
noncomputable def diffWFuFun (W W' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Dv (diffWFun W W') u v) ^ 2 / 2

/-- 差の場のフラックスの v 成分 F^v = (δW_u)²/2。 -/
noncomputable def diffWFvFun (W W' : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Du (diffWFun W W') u v) ^ 2 / 2

/-- 4-7（差の場のフラックス恒等式の解析版）：
    ∂_u F^u + ∂_v F^v = (δW_v + δW_u)·(a·δOm + b·δW + c·δr)。 -/
theorem diffW_flux_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ} {u v : ℝ}
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hWv' : ∀ u, Differentiable ℝ (fun v' => W' u v'))
    (hWu : ∀ v, Differentiable ℝ (fun u' => W u' v))
    (hWu' : ∀ v, Differentiable ℝ (fun u' => W' u' v))
    (hDvWu : Differentiable ℝ (fun u' => Dv W u' v))
    (hDvW'u : Differentiable ℝ (fun u' => Dv W' u' v))
    (hDuWv : Differentiable ℝ (fun v' => Du W u v'))
    (hDuW'v : Differentiable ℝ (fun v' => Du W' u v'))
    (hr : r u v ≠ 0) (hr' : r' u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hWuv' : Duv W' u v = CFT.Wedge.rhsW (Om' u v) (W' u v) (r' u v))
    (hcomm : Dv (Du (diffWFun W W')) u v = Duv (diffWFun W W') u v) :
    Du (diffWFuFun W W') u v + Dv (diffWFvFun W W') u v
      = (Dv (diffWFun W W') u v + Du (diffWFun W W') u v)
        * diffWSource Om Om' W W' r r' u v := by
  have hu := diffW_energy_u_analytic hWv hWv' hDvWu hDvW'u hr hr' hWuv hWuv'
  have hv := diffW_energy_v_analytic hWu hWu' hDuWv hDuW'v hWv hWv' hDvWu hDvW'u
    hr hr' hWuv hWuv' hcomm
  show Du (fun u v => (Dv (diffWFun W W') u v) ^ 2 / 2) u v
      + Dv (fun u v => (Du (diffWFun W W') u v) ^ 2 / 2) u v
      = (Dv (diffWFun W W') u v + Du (diffWFun W W') u v)
        * diffWSource Om Om' W W' r r' u v
  linear_combination hu + hv

/-- 4-7（差の場の矩形上のエネルギー収支）：
    差のフラックス恒等式と矩形上の発散定理を組み合わせ、境界フラックス =
    源 (δW_v + δW_u)·(a·δOm + b·δW + c·δr) の二重積分を得る。
    dFu・dFv の連続性は仮定する。 -/
theorem diffW_energy_balance_analytic {Om Om' W W' r r' : ℝ → ℝ → ℝ}
    {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hWv' : ∀ u, Differentiable ℝ (fun v' => W' u v'))
    (hWu : ∀ v, Differentiable ℝ (fun u' => W u' v))
    (hWu' : ∀ v, Differentiable ℝ (fun u' => W' u' v))
    (hDvW : ∀ v, Differentiable ℝ (fun u' => Dv W u' v))
    (hDvW' : ∀ v, Differentiable ℝ (fun u' => Dv W' u' v))
    (hDuW : ∀ u, Differentiable ℝ (fun v' => Du W u v'))
    (hDuW' : ∀ u, Differentiable ℝ (fun v' => Du W' u v'))
    (hr0 : ∀ u v, r u v ≠ 0) (hr0' : ∀ u v, r' u v ≠ 0)
    (hWuv : ∀ u v, Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hWuv' : ∀ u v, Duv W' u v = CFT.Wedge.rhsW (Om' u v) (W' u v) (r' u v))
    (hcomm : ∀ u v, Dv (Du (diffWFun W W')) u v = Duv (diffWFun W W') u v)
    (hFu_c : Continuous (Function.uncurry fun u v =>
      (Dv (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v))
    (hFv_c : Continuous (Function.uncurry fun u v =>
      (Du (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v)) :
    (∫ v in v0..v1, (diffWFuFun W W' u1 v - diffWFuFun W W' u0 v))
      + (∫ u in u0..u1, (diffWFvFun W W' u v1 - diffWFvFun W W' u v0))
      = ∫ u in u0..u1, ∫ v in v0..v1,
          (Dv (diffWFun W W') u v + Du (diffWFun W W') u v)
            * diffWSource Om Om' W W' r r' u v := by
  have hFu_diff : ∀ v, Differentiable ℝ (fun u' => diffWFuFun W W' u' v) := by
    intro v
    show Differentiable ℝ (fun u' => (Dv (diffWFun W W') u' v) ^ 2 / 2)
    exact ((diffW_Dv_diff_u hWv hWv' (hDvW v) (hDvW' v)).pow 2).div_const 2
  have hFv_diff : ∀ u, Differentiable ℝ (fun v' => diffWFvFun W W' u v') := by
    intro u
    show Differentiable ℝ (fun v' => (Du (diffWFun W W') u v') ^ 2 / 2)
    exact ((diffW_Du_diff_v hWu hWu' (hDuW u) (hDuW' u)).pow 2).div_const 2
  have hFu_deriv : ∀ v, ∀ u, HasDerivAt (fun u' => diffWFuFun W W' u' v)
      ((Dv (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v) u := by
    intro v u
    have h := diffW_energy_u_analytic hWv hWv' (hDvW v) (hDvW' v)
      (hr0 u v) (hr0' u v) (hWuv u v) (hWuv' u v)
    have hder : deriv (fun u' => diffWFuFun W W' u' v) u
        = (Dv (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v := h
    exact (hFu_diff v u).hasDerivAt.congr_deriv hder
  have hFv_deriv : ∀ u, ∀ v, HasDerivAt (fun v' => diffWFvFun W W' u v')
      ((Du (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v) v := by
    intro u v
    have h := diffW_energy_v_analytic hWu hWu' (hDuW u) (hDuW' u) hWv hWv'
      (hDvW v) (hDvW' v) (hr0 u v) (hr0' u v) (hWuv u v) (hWuv' u v) (hcomm u v)
    have hder : deriv (fun v' => diffWFvFun W W' u v') v
        = (Du (diffWFun W W') u v) * diffWSource Om Om' W W' r r' u v := h
    exact (hFv_diff u v).hasDerivAt.congr_deriv hder
  have h := rect_divergence hu hv hFu_deriv hFv_deriv hFu_c hFv_c
  rw [h]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  ring

end

end CFT.WedgeDifferenceEnergy
