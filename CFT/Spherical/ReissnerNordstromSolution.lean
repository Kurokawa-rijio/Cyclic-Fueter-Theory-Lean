/-
  命題集 `LEAN_GAP_TREES.md` 12-7.6（荷電セクター：RN 解の明示）：
  二重ヌル座標での Reissner–Nordström 解を、真空方程式に対する
  残差形で明示する。トータス関係は
    2Ω = 1 − 2M/r + Q²/r²、r_u = −Ω、r_v = +Ω
  （M, Q は定数）。9-1 のシュワルツシルト版と同じ導分代数の流儀
  （場を体 S の元、∂_u, ∂_v を導分として扱う）。

  恒等式はすべて sympy による有理関数計算でも照合済み
  （`numerics/RNCheck.py`、準備文書 `GAP_12-7-6_prep.md`・
  `GAP_RN_EXPLICIT_prep.md`）：
  - Ω の微分：du Ω = −MΩ/r² + Q²Ω/r³、dv Ω = +MΩ/r² − Q²Ω/r³。
  - 拘束はそのまま 0（トータス型アンザッツの幾何的恒等式で Q によらない）。
  - 真空の発展方程式は成り立たない。残差はちょうど Q² の項：
    r 方程式の残差 Q²Ω/(2r³)、Ω 方程式の残差 −Q²Ω²/r⁴。
  - ミスナー–シャープ質量は定数ではない：m = M − Q²/(2r)
    （標準の RN 質量関数）。du m = −Q²Ω/(2r²)、dv m = +Q²Ω/(2r²)。
  - Q = 0 で両残差は 0、m = M となり 9-1 に帰着。

  正直な留保：ここで検証したのは計量レベルの二重ヌル明示解である。
  RN を「解」として完全に Lean 化するには、くさび系に
  Einstein–Maxwell のソース項を入れる（Abelian 射影）必要があり、
  それはこのモジュールの範囲外。したがってこのモジュールが入っても
  12-7.6 は「解の明示」の部分が埋まるだけで、状態は **部分** のまま。
  地平線 r± = M ± √(M² − Q²) の扱い（Ω = 0）は範囲外（Om ≠ 0 を仮定）。
  くさび EYM 系の W 場側への埋め込みも未検証で別の引数が必要。
-/
import CFT.Spherical.WedgeConstraintPropagation
import CFT.Spherical.WedgeMisnerSharpMass
import CFT.Spherical.SchwarzschildVacuumSolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.ReissnerNordstrom

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]

variable (du dv : Derivation ℤ S S) (r Om M Q : S)

/-- RN 場の特徴づけ（トータス関係）。
    s = v − u に対するトータス ODE dρ/ds = f(ρ)/2
    （f(ρ) = 1 − 2M/ρ + Q²/ρ²）の導分代数版：
    Ω = (1 − 2M/r + Q²/r²)/2、r_u = −Ω、r_v = +Ω。
    M は質量パラメータ、Q は電荷パラメータ（ともに定数）。 -/
def ReissnerNordstromField : Prop :=
  2 * Om = 1 - 2 * M / r + Q ^ 2 / r ^ 2 ∧ du r = -Om ∧ dv r = Om
    ∧ du M = 0 ∧ dv M = 0 ∧ du Q = 0 ∧ dv Q = 0

set_option linter.unusedSectionVars false in
/-- 分母を払った形：2 Ω r² = r² − 2Mr + Q²。 -/
theorem rn_Om_mul (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0) :
    2 * Om * r ^ 2 = r ^ 2 - 2 * M * r + Q ^ 2 := by
  have hOm := h.1
  have h1 : (2 * Om) * r ^ 2 = (1 - 2 * M / r + Q ^ 2 / r ^ 2) * r ^ 2 :=
    congrArg (· * r ^ 2) hOm
  have h2 : (1 - 2 * M / r + Q ^ 2 / r ^ 2) * r ^ 2
      = r ^ 2 - 2 * M * r + Q ^ 2 := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- Ω の u 微分：du Ω = −MΩ/r² + Q²Ω/r³（トータス関係の微分）。 -/
theorem rn_du_Om (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0) :
    du Om = -M * Om / r ^ 2 + Q ^ 2 * Om / r ^ 3 := by
  have htorus : 2 * Om = 1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2 := by
    have ht := h.1
    simp only [div_eq_mul_inv, ← inv_pow] at ht
    exact ht
  have hru := h.2.1
  have hMu := h.2.2.2.1
  have hQu := h.2.2.2.2.2.1
  have h1 : du (2 * Om) = du (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) := by rw [htorus]
  simp only [map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr,
    CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hru, hMu, hQu, zero_sub,
    CFT.WedgePropagation.deriv_ofNat du 2, nsmul_eq_mul, Nat.cast_ofNat,
    pow_one] at h1
  simp only [div_eq_mul_inv]
  linear_combination h1 / 2

/-- Ω の v 微分：dv Ω = +MΩ/r² − Q²Ω/r³。 -/
theorem rn_dv_Om (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0) :
    dv Om = M * Om / r ^ 2 - Q ^ 2 * Om / r ^ 3 := by
  have htorus : 2 * Om = 1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2 := by
    have ht := h.1
    simp only [div_eq_mul_inv, ← inv_pow] at ht
    exact ht
  have hrv := h.2.2.1
  have hMv := h.2.2.2.2
  have hQv := h.2.2.2.2.2.2
  have h1 : dv (2 * Om) = dv (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) := by rw [htorus]
  simp only [map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr,
    CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hrv, hMv, hQv, zero_sub,
    CFT.WedgePropagation.deriv_ofNat dv 2, nsmul_eq_mul, Nat.cast_ofNat,
    pow_one] at h1
  simp only [div_eq_mul_inv]
  linear_combination h1 / 2

/-- r 方程式の残差形：r_uv = −Ω/(2r) − r_u r_v/r + Q²Ω/(2r³)。
    Q = 0 で真空の r 方程式（9-1）に帰着。 -/
theorem rn_r_eq (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0) :
    du (dv r) = -Om / (2 * r) - du r * dv r / r + Q ^ 2 * Om / (2 * r ^ 3) := by
  have hru := h.2.1
  have hrv := h.2.2.1
  have hOm' := rn_Om_mul du dv r Om M Q h hr
  have hdu := rn_du_Om du dv r Om M Q h hr
  rw [hrv, hdu, hru]
  field_simp
  linear_combination (-2 * Om * r ^ 7) * hOm'

/-- Ω 方程式の残差形：
    Ω_uv = Ω_u Ω_v/Ω − 2Ω r_uv/r − Q²Ω²/r⁴。
    Q = 0 で真空の Ω 方程式（9-1）に帰着。 -/
theorem rn_Om_eq (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (dv Om) = du Om * dv Om / Om - 2 * Om * du (dv r) / r
      - Q ^ 2 * Om ^ 2 / r ^ 4 := by
  have hru := h.2.1
  have hrv := h.2.2.1
  have hMu := h.2.2.2.1
  have hQu := h.2.2.2.2.2.1
  have hdu := rn_du_Om du dv r Om M Q h hr
  have hdv := rn_dv_Om du dv r Om M Q h hr
  have hdu' : du Om = -M * Om * (r⁻¹) ^ 2 + Q ^ 2 * Om * (r⁻¹) ^ 3 := by
    simp only [div_eq_mul_inv, ← inv_pow] at hdu
    exact hdu
  have hdv' : dv Om = M * Om * (r⁻¹) ^ 2 - Q ^ 2 * Om * (r⁻¹) ^ 3 := by
    simp only [div_eq_mul_inv, ← inv_pow] at hdv
    exact hdv
  have hOmInv : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hOm0
  simp only [hdv', hdu', hrv]
  simp only [div_eq_mul_inv, ← inv_pow]
  simp only [map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ hr,
    CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hdu', hru, hMu, hQu,
    CFT.WedgePropagation.deriv_ofNat du 2, nsmul_eq_mul, Nat.cast_ofNat,
    pow_one]
  linear_combination (-Om * ((-M * (r⁻¹) ^ 2 + Q ^ 2 * (r⁻¹) ^ 3)
      * (M * (r⁻¹) ^ 2 - Q ^ 2 * (r⁻¹) ^ 3))) * hOmInv

/-- 拘束 C_u：r_uu − (Ω_u/Ω) r_u = 0。 -/
theorem rn_constraint_u (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (du r) - du Om / Om * du r = 0 := by
  have hru := h.2.1
  have hdu := rn_du_Om du dv r Om M Q h hr
  simp only [hru, map_neg, hdu]
  field_simp
  ring

/-- 拘束 C_v：r_vv − (Ω_v/Ω) r_v = 0。 -/
theorem rn_constraint_v (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    dv (dv r) - dv Om / Om * dv r = 0 := by
  have hrv := h.2.2.1
  have hdv := rn_dv_Om du dv r Om M Q h hr
  simp only [hrv, map_neg, hdv]
  field_simp
  ring

/-- ミスナー–シャープ質量は M − Q²/(2r)（標準の RN 質量関数）。
    Q = 0 で m = M（9-1）に帰着。 -/
theorem rn_mass (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    CFT.WedgeMass.misnerSharpMass du dv r Om = M - Q ^ 2 / (2 * r) := by
  have hru := h.2.1
  have hrv := h.2.2.1
  have hOm' := rn_Om_mul du dv r Om M Q h hr
  rw [CFT.WedgeMass.mass_alt, hru, hrv]
  field_simp
  linear_combination (-2 * Om) * hOm'

/-- 質量の u 微分：du m = −Q²Ω/(2r²)（質量は定数ではない）。 -/
theorem rn_mass_u (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (CFT.WedgeMass.misnerSharpMass du dv r Om) = -Q ^ 2 * Om / (2 * r ^ 2) := by
  have hru := h.2.1
  have hMu := h.2.2.2.1
  have hQu := h.2.2.2.2.2.1
  have hm := rn_mass du dv r Om M Q h hr hOm0
  rw [hm]
  simp only [div_eq_mul_inv, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ (mul_ne_zero (by norm_num : (2 : S) ≠ 0) hr),
    CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hMu, hQu, hru,
    CFT.WedgePropagation.deriv_ofNat du 2, nsmul_eq_mul, Nat.cast_ofNat,
    pow_one]
  field_simp
  ring

/-- 質量の v 微分：dv m = +Q²Ω/(2r²)。 -/
theorem rn_mass_v (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    dv (CFT.WedgeMass.misnerSharpMass du dv r Om) = Q ^ 2 * Om / (2 * r ^ 2) := by
  have hrv := h.2.2.1
  have hMv := h.2.2.2.2
  have hQv := h.2.2.2.2.2.2
  have hm := rn_mass du dv r Om M Q h hr hOm0
  rw [hm]
  simp only [div_eq_mul_inv, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul,
    CFT.WedgePropagation.deriv_inv _ _ (mul_ne_zero (by norm_num : (2 : S) ≠ 0) hr),
    CFT.WedgePropagation.deriv_ofNat,
    Derivation.map_one_eq_zero, hMv, hQv, hrv,
    CFT.WedgePropagation.deriv_ofNat dv 2, nsmul_eq_mul, Nat.cast_ofNat,
    pow_one]
  field_simp
  ring

/-- まとめ：RN 場は真空方程式を残差 Q² 項つきで満たし、拘束は 0、
    質量は M − Q²/(2r)。 -/
theorem rn_electrovacuum (h : ReissnerNordstromField du dv r Om M Q) (hr : r ≠ 0)
    (hOm0 : Om ≠ 0) :
    du (dv r) = -Om / (2 * r) - du r * dv r / r + Q ^ 2 * Om / (2 * r ^ 3)
      ∧ du (dv Om) = du Om * dv Om / Om - 2 * Om * du (dv r) / r
          - Q ^ 2 * Om ^ 2 / r ^ 4
      ∧ du (du r) - du Om / Om * du r = 0
      ∧ dv (dv r) - dv Om / Om * dv r = 0
      ∧ CFT.WedgeMass.misnerSharpMass du dv r Om = M - Q ^ 2 / (2 * r) :=
  ⟨rn_r_eq du dv r Om M Q h hr,
   rn_Om_eq du dv r Om M Q h hr hOm0,
   rn_constraint_u du dv r Om M Q h hr hOm0,
   rn_constraint_v du dv r Om M Q h hr hOm0,
   rn_mass du dv r Om M Q h hr hOm0⟩

set_option linter.unusedSectionVars false in
/-- Q = 0 での帰着：RN 場はシュワルツシルト場になる（9-1）。 -/
theorem rn_to_schwarzschild (h : ReissnerNordstromField du dv r Om M Q)
    (hQ : Q = 0) :
    CFT.Schwarzschild.SchwarzschildField du dv r Om M := by
  obtain ⟨ht, hru, hrv, hMu, hMv, -, -⟩ := h
  refine ⟨?_, hru, hrv, hMu, hMv⟩
  rw [hQ] at ht
  simpa using ht

end CFT.ReissnerNordstrom
