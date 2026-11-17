/-
  命題集 `LEAN_GAP_TREES.md` 9-1（シュワルツシルト極限：ミスナー–シャープ質量の保存）：
  真空では m = (r/2)(1 + 2 r_u r_v/Ω) が u・v 両方向に定数になる。
  証明は 4-2・4-5 と同じ導分代数の流儀（場を体 S の元、∂_u, ∂_v を可換な導分）。
  使うのは真空の r 方程式 r_uv = -Ω/(2r) - r_u r_v/r（`WedgeVacuumReduction.vacRhsR`
  の式そのもの）と拘束 r_uu = (Ω_u/Ω) r_u、r_vv = (Ω_v/Ω) r_v のみ
  （Ω 方程式は使わない。m の微分に現れる Ω_u は拘束経由で相殺されるため）。
  恒等式は sympy による展開計算（`/tmp/check91mass.py`）でも照合済み。
  解析的な `deriv` 版への移行と、シュワルツシルト解そのものの明示は別葉。
-/
import CFT.Spherical.WedgeConstraintPropagation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.WedgeMass

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]

variable (du dv : Derivation ℤ S S) (r Om : S)

/-- ミスナー–シャープ質量 m = (r/2)(1 + 2 r_u r_v/Ω)。
    二重ヌル座標 ds² = -2Ω du dv + r² dΩ² では 1 - 2m/r = -2 r_u r_v/Ω。 -/
noncomputable def misnerSharpMass : S := r / 2 * (1 + 2 * du r * dv r / Om)

/-- 別形：m = r/2 + r r_u r_v/Ω。 -/
theorem mass_alt : misnerSharpMass du dv r Om = r / 2 + r * du r * dv r / Om := by
  simp only [misnerSharpMass]
  ring

/-- 定義恒等式：1 - 2m/r = -2 r_u r_v/Ω。 -/
theorem mass_defining (hr : r ≠ 0) :
    1 - 2 * misnerSharpMass du dv r Om / r = -2 * du r * dv r / Om := by
  simp only [misnerSharpMass]
  field_simp
  try ring

/-- 真空での質量保存（u 方向）：r 方程式と C_u 拘束だけから du m = 0。 -/
theorem mass_du (hr : r ≠ 0) (hOm : Om ≠ 0)
    (hR : du (dv r) = -Om / (2 * r) - du r * dv r / r)
    (hCu : du (du r) = du Om / Om * du r) :
    du (misnerSharpMass du dv r Om) = 0 := by
  have h2 : du (2⁻¹ : S) = 0 := by
    rw [CFT.WedgePropagation.deriv_inv _ _ two_ne_zero,
      CFT.WedgePropagation.deriv_ofNat du 2]; ring
  simp only [misnerSharpMass, div_eq_mul_inv, map_add, map_sub,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr, CFT.WedgePropagation.deriv_inv _ _ hOm,
    CFT.WedgePropagation.deriv_ofNat, Derivation.map_one_eq_zero, h2, hR, hCu,
    CFT.WedgePropagation.deriv_ofNat du 2, nsmul_eq_mul, Nat.cast_ofNat]
  ring_nf
  field_simp
  try ring

/-- 真空での質量保存（v 方向）：r 方程式と C_v 拘束だけから dv m = 0。 -/
theorem mass_dv (hr : r ≠ 0) (hOm : Om ≠ 0)
    (hc : ∀ f, du (dv f) = dv (du f))
    (hR : du (dv r) = -Om / (2 * r) - du r * dv r / r)
    (hCv : dv (dv r) = dv Om / Om * dv r) :
    dv (misnerSharpMass du dv r Om) = 0 := by
  have hR' : dv (du r) = -Om / (2 * r) - du r * dv r / r := by rw [← hc r, hR]
  have h2 : dv (2⁻¹ : S) = 0 := by
    rw [CFT.WedgePropagation.deriv_inv _ _ two_ne_zero,
      CFT.WedgePropagation.deriv_ofNat dv 2]; ring
  simp only [misnerSharpMass, div_eq_mul_inv, map_add, map_sub,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr, CFT.WedgePropagation.deriv_inv _ _ hOm,
    CFT.WedgePropagation.deriv_ofNat, Derivation.map_one_eq_zero, h2, hR', hCv,
    CFT.WedgePropagation.deriv_ofNat dv 2, nsmul_eq_mul, Nat.cast_ofNat]
  ring_nf
  field_simp
  try ring

/-- 両方向あわせた保存：真空では m は u・v 両方向に定数。 -/
theorem mass_const (hr : r ≠ 0) (hOm : Om ≠ 0)
    (hc : ∀ f, du (dv f) = dv (du f))
    (hR : du (dv r) = -Om / (2 * r) - du r * dv r / r)
    (hCu : du (du r) = du Om / Om * du r)
    (hCv : dv (dv r) = dv Om / Om * dv r) :
    du (misnerSharpMass du dv r Om) = 0 ∧ dv (misnerSharpMass du dv r Om) = 0 :=
  ⟨mass_du du dv r Om hr hOm hR hCu, mass_dv du dv r Om hr hOm hc hR hCv⟩

/-- 視界（r_u = 0）では m = r/2。 -/
theorem mass_at_horizon_u (hru : du r = 0) :
    misnerSharpMass du dv r Om = r / 2 := by
  simp only [misnerSharpMass, hru]
  ring

/-- 視界（r_v = 0）では m = r/2。 -/
theorem mass_at_horizon_v (hrv : dv r = 0) :
    misnerSharpMass du dv r Om = r / 2 := by
  simp only [misnerSharpMass, hrv]
  ring

end CFT.WedgeMass
