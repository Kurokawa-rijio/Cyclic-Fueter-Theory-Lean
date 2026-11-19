import Mathlib.Tactic

/-
# The BPS monopole profile and the Langevin function

Z(x) = sinh x / x, W = x/sinh x = 1/Z, h = coth x − 1/x = (ln Z)′ (the Langevin function), and
W, h satisfy the Bogomolny equations W′ = −hW, h′ = (1 − W²)/x² (`bogomolny_W`, `bogomolny_h`).
All statements are for x ≠ 0 (at x = 0 Lean's convention a/0 = 0 gives Z 0 = W 0 = 0).
-/

open Real

namespace FieldEquations.MonopoleLangevin

noncomputable def Z (x : ℝ) : ℝ := sinh x / x

noncomputable def W (x : ℝ) : ℝ := x / sinh x

noncomputable def h (x : ℝ) : ℝ := cosh x / sinh x - 1 / x

theorem sinh_ne (x : ℝ) (hx : x ≠ 0) : sinh x ≠ 0 := fun h0 => hx (Real.sinh_eq_zero.mp h0)

theorem W_eq_inv_Z (x : ℝ) : W x = 1 / Z x := by
  unfold W Z
  rw [one_div_div]

theorem Z_integral (x : ℝ) (hx : x ≠ 0) :
    (1 / 2 : ℝ) * ∫ u in (-1 : ℝ)..1, Real.exp (x * u) = Z x := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hx, integral_exp]
  unfold Z
  rw [Real.sinh_eq]
  simp only [smul_eq_mul, mul_one, mul_neg]
  field_simp

theorem hasDerivAt_Z (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Z ((x * cosh x - sinh x) / x ^ 2) x := by
  have h1 := (Real.hasDerivAt_sinh x).div (hasDerivAt_id' x) hx
  exact h1.congr_deriv (by ring)

theorem hasDerivAt_logZ (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => Real.log (Z y)) (h x) x := by
  have hs := sinh_ne x hx
  have hZ : Z x ≠ 0 := div_ne_zero hs hx
  have h1 := (hasDerivAt_Z x hx).log hZ
  refine h1.congr_deriv ?_
  unfold Z h
  field_simp
  ring

/-- W′ = −hW. -/
theorem bogomolny_W (x : ℝ) (hx : x ≠ 0) : HasDerivAt W (-(h x * W x)) x := by
  have hs := sinh_ne x hx
  have h1 := (hasDerivAt_id' x).div (Real.hasDerivAt_sinh x) hs
  refine h1.congr_deriv ?_
  unfold h W
  field_simp
  ring

/-- h′ = (1 − W²)/x². -/
theorem bogomolny_h (x : ℝ) (hx : x ≠ 0) : HasDerivAt h ((1 - W x ^ 2) / x ^ 2) x := by
  have hs := sinh_ne x hx
  have h1 := (Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs
  have h2 := (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id' x) hx
  have e : sinh x * sinh x - cosh x * cosh x = -1 := by nlinarith [Real.cosh_sq x]
  refine (h1.sub h2).congr_deriv ?_
  rw [e]
  unfold W
  field_simp
  ring

end FieldEquations.MonopoleLangevin
