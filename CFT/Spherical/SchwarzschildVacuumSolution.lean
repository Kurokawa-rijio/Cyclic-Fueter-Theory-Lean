/-
  命題集 `LEAN_GAP_TREES.md` 9-1（シュワルツシルト極限：解そのものの明示）：
  二重ヌル座標でのシュワルツシルト解が真空の発展方程式と拘束を満たし、
  ミスナー–シャープ質量がちょうど M になることを示す。

  証明は 4-2・4-5・9-1（質量保存）と同じ導分代数の流儀（場を体 S の元、
  ∂_u, ∂_v を導分として扱う）。シュワルツシルト場はトータス関係
    2Ω = 1 − 2M/r、r_u = −Ω、r_v = +Ω
  で特徴づける（`SchwarzschildField`）。ここで s = v − u はトータス座標の
  2 倍で、dρ/ds = (1 − 2M/ρ)/2 が r_u = −Ω、r_v = +Ω の形になる。
  M は定数（質量パラメータ）。

  注意（命題集の記述の訂正）：命題集は「r と Ω を u + v の関数として書く」と
  するが、コードの規約（ds² = −2Ω du dv、真空方程式は
  `WedgeVacuumReduction` の形）では r が u + v の関数だと r_u r_v = (ρ')² ≥ 0
  となり、r 方程式を満たさない（残差 (r − 2M)²/(2r³) ≠ 0、sympy で確認）。
  正しくは v − u の関数（r_u r_v = −Ω² < 0、地平線の外側）である。
  5 つの恒等式（r 方程式・Ω 方程式・C_u・C_v・質量 = M）はすべて
  sympy による有理関数計算（`/tmp/check91schw.py`）でも照合済み。

  残り：トータス ODE を満たす ρ の存在そのもの（陰関数／ODE の存在定理）、
  解析的な `deriv` 版（`Du`/`Dv`）への移行、地平線 r = 2M（Ω = 0）の扱いは
  本モジュールの範囲外（Om ≠ 0 を仮定）。
-/
import CFT.Spherical.WedgeConstraintPropagation
import CFT.Spherical.WedgeMisnerSharpMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.Schwarzschild

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]

variable (du dv : Derivation ℤ S S) (r Om M : S)

/-- シュワルツシルト場の特徴づけ（トータス関係）。
    s = v − u に対するトータス ODE dρ/ds = (1 − 2M/ρ)/2 の導分代数版：
    Ω = (1 − 2M/r)/2、r_u = −Ω、r_v = +Ω。M は定数（質量パラメータ）。 -/
def SchwarzschildField : Prop :=
  2 * Om = 1 - 2 * M / r ∧ du r = -Om ∧ dv r = Om ∧ du M = 0 ∧ dv M = 0

set_option linter.unusedSectionVars false in
/-- 分母を払った形：2 Ω r = r − 2M。 -/
theorem schwarzschild_Om_mul (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0) :
    2 * Om * r = r - 2 * M := by
  have hOm := h.1
  have h1 : (2 * Om) * r = (1 - 2 * M / r) * r := congrArg (· * r) hOm
  have h2 : (1 - 2 * M / r) * r = r - 2 * M := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hr]
  rw [h2] at h1
  exact h1

/-- Ω の u 微分：du Ω = −MΩ/r²（トータス関係の微分）。 -/
theorem schwarzschild_du_Om (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0) :
    du Om = -M * Om / r ^ 2 := by
  have hOm := h.1
  have hru := h.2.1
  have hMu := h.2.2.2.1
  have h1 : du (2 * Om) = du (1 - 2 * M / r) := by rw [hOm]
  simp only [div_eq_mul_inv, map_sub, Derivation.leibniz, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr, CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hru, hMu, zero_sub,
    CFT.WedgePropagation.deriv_ofNat du 2, nsmul_eq_mul, Nat.cast_ofNat] at h1
  rw [div_eq_mul_inv]
  linear_combination h1 / 2

/-- Ω の v 微分：dv Ω = +MΩ/r²。 -/
theorem schwarzschild_dv_Om (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0) :
    dv Om = M * Om / r ^ 2 := by
  have hOm := h.1
  have hrv := h.2.2.1
  have hMv := h.2.2.2.2
  have h1 : dv (2 * Om) = dv (1 - 2 * M / r) := by rw [hOm]
  simp only [div_eq_mul_inv, map_sub, Derivation.leibniz, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr, CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hrv, hMv, zero_sub,
    CFT.WedgePropagation.deriv_ofNat dv 2, nsmul_eq_mul, Nat.cast_ofNat] at h1
  rw [div_eq_mul_inv]
  linear_combination h1 / 2

/-- 真空の r 方程式（`vacRhsR` の式）：r_uv = −Ω/(2r) − r_u r_v/r。 -/
theorem schwarzschild_r_eq (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0) :
    du (dv r) = -Om / (2 * r) - du r * dv r / r := by
  have hru := h.2.1
  have hrv := h.2.2.1
  have hOm' := schwarzschild_Om_mul du dv r Om M h hr
  have hdu := schwarzschild_du_Om du dv r Om M h hr
  rw [hrv, hdu, hru]
  field_simp
  linear_combination (-r ^ 2 * Om) * hOm'

/-- 真空の Ω 方程式（`vacRhsOm` の式）：Ω_uv = Ω_u Ω_v/Ω − 2Ω r_uv/r。 -/
theorem schwarzschild_Om_eq (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (dv Om) = du Om * dv Om / Om - 2 * Om * du (dv r) / r := by
  have hru := h.2.1
  have hrv := h.2.2.1
  have hMu := h.2.2.2.1
  have hdu := schwarzschild_du_Om du dv r Om M h hr
  have hdv := schwarzschild_dv_Om du dv r Om M h hr
  simp only [hdv, hdu, hrv]
  simp only [div_eq_mul_inv, map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr,
    CFT.WedgePropagation.deriv_inv _ _ (pow_ne_zero 2 hr),
    CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hdu, hru, hMu,
    CFT.WedgePropagation.deriv_ofNat du 2, nsmul_eq_mul, Nat.cast_ofNat]
  ring_nf
  field_simp [hOm0]
  try ring

/-- 拘束 C_u：r_uu − (Ω_u/Ω) r_u = 0。 -/
theorem schwarzschild_constraint_u (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (du r) - du Om / Om * du r = 0 := by
  have hru := h.2.1
  have hdu := schwarzschild_du_Om du dv r Om M h hr
  simp only [hru, map_neg, hdu]
  field_simp
  ring

/-- 拘束 C_v：r_vv − (Ω_v/Ω) r_v = 0。 -/
theorem schwarzschild_constraint_v (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    dv (dv r) - dv Om / Om * dv r = 0 := by
  have hrv := h.2.2.1
  have hdv := schwarzschild_dv_Om du dv r Om M h hr
  simp only [hrv, map_neg, hdv]
  field_simp
  ring

/-- ミスナー–シャープ質量は M：m = r/2 + r r_u r_v/Ω = M。 -/
theorem schwarzschild_mass (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    CFT.WedgeMass.misnerSharpMass du dv r Om = M := by
  have hru := h.2.1
  have hrv := h.2.2.1
  have hOm' := schwarzschild_Om_mul du dv r Om M h hr
  rw [CFT.WedgeMass.mass_alt, hru, hrv]
  field_simp
  linear_combination (-Om) * hOm'

/-- まとめ：シュワルツシルト場は真空の発展方程式と拘束を満たす。 -/
theorem schwarzschild_vacuum (h : SchwarzschildField du dv r Om M) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (dv r) = -Om / (2 * r) - du r * dv r / r
      ∧ du (dv Om) = du Om * dv Om / Om - 2 * Om * du (dv r) / r
      ∧ du (du r) - du Om / Om * du r = 0
      ∧ dv (dv r) - dv Om / Om * dv r = 0 :=
  ⟨schwarzschild_r_eq du dv r Om M h hr,
   schwarzschild_Om_eq du dv r Om M h hr hOm0,
   schwarzschild_constraint_u du dv r Om M h hr hOm0,
   schwarzschild_constraint_v du dv r Om M h hr hOm0⟩

end CFT.Schwarzschild
