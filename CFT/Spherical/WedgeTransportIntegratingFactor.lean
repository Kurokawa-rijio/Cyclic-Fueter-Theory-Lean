/-
  命題集 `LEAN_GAP_TREES.md` 4-4（輸送部分の常微分方程式化、部分葉）：
  4-2 で証明された拘束の伝播恒等式 ∂_v C_u = -(r_v/r) C_u は、v 方向の
  一階線形輸送方程式である。このモジュールでは積分因子 r による明示解を示す：
  C_u * r は v-定数であり、逆に v-定数 λ に対し λ * r⁻¹ が同じ輸送方程式を
  満たす（一般解の形）。特性曲線上の常微分方程式への帰着とその解法の部分。
  ピカール–リンデレーフによる局所存在への適用と、解析的な `deriv` 版への
  移行は別葉。
  証明は 4-2 と同じ導分代数の流儀（場を体 S の元、∂_u, ∂_v を可換な導分）。
-/
import CFT.Spherical.WedgeConstraintPropagation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.WedgeTransport

variable {S : Type*} [Field S] [CharZero S]

omit [CharZero S] in
/-- 積分因子：輸送方程式 d c = -(d r * r⁻¹) * c の解は c * r が d-定数。 -/
theorem transport_integrating_factor (d : Derivation ℤ S S) (c r : S) (hr : r ≠ 0)
    (h : d c = -(d r * r⁻¹) * c) : d (c * r) = 0 := by
  have hleib : d (c * r) = c * d r + r * d c := by
    rw [Derivation.leibniz]; simp [smul_eq_mul]
  rw [hleib, h]
  field_simp
  ring

/-- 一般解の形：d-定数 λ に対し λ * r⁻¹ は輸送方程式を満たす。 -/
theorem transport_general_solution (d : Derivation ℤ S S) (lam r : S) (hr : r ≠ 0)
    (hlam : d lam = 0) :
    d (lam * r⁻¹) = -(d r * r⁻¹) * (lam * r⁻¹) := by
  have hleib : d (lam * r⁻¹) = lam * d r⁻¹ + r⁻¹ * d lam := by
    rw [Derivation.leibniz]; simp [smul_eq_mul]
  rw [hleib, CFT.WedgePropagation.deriv_inv d r hr, hlam]
  field_simp
  ring

omit [CharZero S] in
/-- 差の輸送：同じ方程式の2解の差も積分因子で d-定数（一意性の核）。 -/
theorem transport_difference_const (d : Derivation ℤ S S) (c₁ c₂ r : S) (hr : r ≠ 0)
    (h₁ : d c₁ = -(d r * r⁻¹) * c₁) (h₂ : d c₂ = -(d r * r⁻¹) * c₂) :
    d ((c₁ - c₂) * r) = 0 := by
  apply transport_integrating_factor d _ _ hr
  rw [map_sub, h₁, h₂]
  ring

section
variable (du dv : Derivation ℤ S S) (r Om W : S)
  (hOm : Om ≠ 0) (hr : r ≠ 0)
  (hc : ∀ f, du (dv f) = dv (du f))
  (eR : du (dv r) = CFT.WedgePropagation.wedgeRuv Om W (du r) (dv r) r)
  (eOm : du (dv Om)
    = CFT.WedgePropagation.wedgeOuv Om W (du Om) (dv Om) (du (dv r)) r)
  (eW : du (dv W) = CFT.WedgePropagation.wedgeWuv Om W r)
include hOm hr hc eR eOm eW

/-- 4-4（u 拘束の輸送の明示解）：C_u * r は v-定数。 -/
theorem wedge_cu_times_r_const :
    dv (CFT.WedgePropagation.wedgeCu du r Om W * r) = 0 :=
  transport_integrating_factor dv _ _ hr
    (CFT.WedgePropagation.wedge_cu_propagation du dv r Om W hOm hr hc eR eOm eW)

/-- 4-4（v 拘束の輸送の明示解）：C_v * r は u-定数。 -/
theorem wedge_cv_times_r_const :
    du (CFT.WedgePropagation.wedgeCv dv r Om W * r) = 0 :=
  transport_integrating_factor du _ _ hr
    (CFT.WedgePropagation.wedge_cv_propagation du dv r Om W hOm hr hc eR eOm eW)

end

/-- 4-4（一般解の形、u 拘束側）：v-定数 λ に対し λ * r⁻¹ は C_u と同じ輸送方程式を満たす。 -/
theorem wedge_cu_general_solution (dv : Derivation ℤ S S) (r : S) (hr : r ≠ 0)
    (lam : S) (hlam : dv lam = 0) :
    dv (lam * r⁻¹) = -(dv r * r⁻¹) * (lam * r⁻¹) :=
  transport_general_solution dv lam r hr hlam

/-- 4-4（一般解の形、v 拘束側）：u-定数 λ に対し λ * r⁻¹ は C_v と同じ輸送方程式を満たす。 -/
theorem wedge_cv_general_solution (du : Derivation ℤ S S) (r : S) (hr : r ≠ 0)
    (lam : S) (hlam : du lam = 0) :
    du (lam * r⁻¹) = -(du r * r⁻¹) * (lam * r⁻¹) :=
  transport_general_solution du lam r hr hlam

omit [CharZero S] in
/-- 4-4（差の一意性核）：同じ輸送方程式の2解の差は積分因子で v-定数。 -/
theorem wedge_cu_difference_const (dv : Derivation ℤ S S) (r : S) (hr : r ≠ 0)
    (c₁ c₂ : S)
    (h₁ : dv c₁ = -(dv r * r⁻¹) * c₁) (h₂ : dv c₂ = -(dv r * r⁻¹) * c₂) :
    dv ((c₁ - c₂) * r) = 0 :=
  transport_difference_const dv c₁ c₂ r hr h₁ h₂

end CFT.WedgeTransport
