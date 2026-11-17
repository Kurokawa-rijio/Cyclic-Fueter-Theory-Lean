import CFT.Spherical.WedgeEYMSystem
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 4-4（輸送部分の常微分方程式化、残りの解析版への移行）：
  4-2 の伝播恒等式 ∂_v C_u = -(r_v/r) C_u は導分代数の流儀で既に証明され、
  積分因子による明示解（`WedgeTransportIntegratingFactor`）と
  ピカール–リンデレーフによる局所存在（`WedgeTransportODE`）も閉じている。
  このモジュールでは同じ恒等式を解析的な `deriv` / `HasDerivAt` の言葉に移す：
  固定した特性曲線に沿い、c' = -(r'/r) c なら c * r は定数（平均値定理）、
  定数 λ に対し λ * r⁻¹ は同じ輸送方程式を満たす（一般解の形）、
  2 解の差も積分因子で定数（一意性の核）。
  くさびへの適用は `CFT.Wedge.Du` / `Dv`（スライスの `deriv`）で述べる。
  これで 4-4 は、積分因子・局所存在・解析版の移行まですべて閉じる。
-/

open CFT.Wedge

namespace CFT.WedgeTransportAnalytic

/-- 1変数の核：輸送方程式 c' = -(r'/r) c の解は、積分因子 r を掛けると定数。 -/
theorem transport_mul_const {c r : ℝ → ℝ}
    (hc : Differentiable ℝ c) (hr : Differentiable ℝ r)
    (hr0 : ∀ t, r t ≠ 0)
    (heq : ∀ t, deriv c t = -(deriv r t / r t) * c t)
    (t₀ t : ℝ) : c t * r t = c t₀ * r t₀ := by
  have hmul : Differentiable ℝ (fun t => c t * r t) := hc.mul hr
  have hderiv : ∀ t, deriv (fun t => c t * r t) t = 0 := by
    intro t
    have hrt : r t ≠ 0 := hr0 t
    rw [deriv_mul (hc t) (hr t), heq t]
    field_simp
    ring
  exact is_const_of_deriv_eq_zero hmul hderiv t t₀

/-- 1変数の一般解の形：定数 λ に対し λ * r⁻¹ は輸送方程式を満たす。 -/
theorem transport_general_solution_analytic {r : ℝ → ℝ}
    (hr : Differentiable ℝ r) (hr0 : ∀ t, r t ≠ 0) (lam t : ℝ) :
    HasDerivAt (fun t => lam * (r t)⁻¹) (-(deriv r t / r t) * (lam * (r t)⁻¹)) t := by
  have hrt : r t ≠ 0 := hr0 t
  have hinv : HasDerivAt (fun t => (r t)⁻¹) (-(deriv r t) / (r t) ^ 2) t :=
    (hr t).hasDerivAt.inv hrt
  have hmul := hinv.const_mul lam
  convert hmul using 1
  field_simp
  ring

/-- 1変数の差：同じ方程式の2解の差も積分因子で定数（一意性の核）。 -/
theorem transport_difference_const_analytic {c₁ c₂ r : ℝ → ℝ}
    (hc₁ : Differentiable ℝ c₁) (hc₂ : Differentiable ℝ c₂) (hr : Differentiable ℝ r)
    (hr0 : ∀ t, r t ≠ 0)
    (heq₁ : ∀ t, deriv c₁ t = -(deriv r t / r t) * c₁ t)
    (heq₂ : ∀ t, deriv c₂ t = -(deriv r t / r t) * c₂ t)
    (t₀ t : ℝ) : (c₁ t - c₂ t) * r t = (c₁ t₀ - c₂ t₀) * r t₀ := by
  apply transport_mul_const (hc₁.sub hc₂) hr hr0 _ t₀ t
  intro t
  rw [deriv_sub (hc₁ t) (hc₂ t), heq₁ t, heq₂ t]
  ring

/-- くさびへの適用（v 方向）：C_u の輸送方程式の解析版。C_u * r は v-定数。 -/
theorem wedge_cu_times_r_const_analytic {C r : ℝ → ℝ → ℝ}
    (hC : ∀ u, Differentiable ℝ (fun v => C u v))
    (hr : ∀ u, Differentiable ℝ (fun v => r u v))
    (hr0 : ∀ u v, r u v ≠ 0)
    (heq : ∀ u v, Dv C u v = -(Dv r u v / r u v) * C u v)
    (u v₀ v : ℝ) : C u v * r u v = C u v₀ * r u v₀ := by
  apply transport_mul_const (hC u) (hr u) (fun t => hr0 u t) _ v₀ v
  intro t
  exact heq u t

/-- くさびへの適用（u 方向）：C_v の輸送方程式の解析版。C_v * r は u-定数。 -/
theorem wedge_cv_times_r_const_analytic {C r : ℝ → ℝ → ℝ}
    (hC : ∀ v, Differentiable ℝ (fun u => C u v))
    (hr : ∀ v, Differentiable ℝ (fun u => r u v))
    (hr0 : ∀ u v, r u v ≠ 0)
    (heq : ∀ u v, Du C u v = -(Du r u v / r u v) * C u v)
    (v u₀ u : ℝ) : C u v * r u v = C u₀ v * r u₀ v := by
  apply transport_mul_const (hC v) (hr v) (fun t => hr0 t v) _ u₀ u
  intro t
  exact heq t v

/-- くさびへの適用（v 方向の一般解）：v-定数 λ に対し λ * r⁻¹ は輸送方程式を満たす。 -/
theorem wedge_cu_general_solution_analytic {r : ℝ → ℝ → ℝ}
    (hr : ∀ u, Differentiable ℝ (fun v => r u v))
    (hr0 : ∀ u v, r u v ≠ 0) (lam u v : ℝ) :
    HasDerivAt (fun v' => lam * (r u v')⁻¹)
      (-(Dv r u v / r u v) * (lam * (r u v)⁻¹)) v :=
  transport_general_solution_analytic (hr u) (fun t => hr0 u t) lam v

/-- くさびへの適用（u 方向の一般解）：u-定数 λ に対し λ * r⁻¹ は輸送方程式を満たす。 -/
theorem wedge_cv_general_solution_analytic {r : ℝ → ℝ → ℝ}
    (hr : ∀ v, Differentiable ℝ (fun u => r u v))
    (hr0 : ∀ u v, r u v ≠ 0) (lam u v : ℝ) :
    HasDerivAt (fun u' => lam * (r u' v)⁻¹)
      (-(Du r u v / r u v) * (lam * (r u v)⁻¹)) u :=
  transport_general_solution_analytic (hr v) (fun t => hr0 t v) lam u

end CFT.WedgeTransportAnalytic
