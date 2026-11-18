/-
  BPS 単極子(Prasad–Sommerfield 解)と Langevin の常磁性体(2026-11-14、命題 Q9)

  球面上で向きを変える一本の古典スピン(磁場 x)の分配関数は Z(x) = ½∫_{-1}^{1} e^{xu} du = sinh x / x。
  Prasad–Sommerfield 解は W = x / sinh x、h = coth x − 1/x。
  * `Z_integral`:½∫_{-1}^{1} e^{xu} du = sinh x / x。
  * `W_eq_inv_Z`:W = 1/Z。
  * `hasDerivAt_logZ`:(ln Z)′ = h(h は平均の向き ⟨u⟩、Langevin 関数)。
  * `bogomolny_W`:W′ = −h W(Bogomolny 方程式の 1 本目)。
  * `bogomolny_h`:h′ = (1 − W²)/x²(Bogomolny 方程式の 2 本目)。
    h′ = (ln Z)″ は向きのゆらぎの分散 ⟨u²⟩ − ⟨u⟩² なので、この式は「感受率 = 分散」(揺動応答の関係)と同じ式。
  ここで示すのは Z の積分表示と (ln Z)′、(ln Z)″ の式まで。⟨u⟩、⟨u²⟩ を積分で書いて微分と積分を入れ替える部分は示していない。
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open Real

namespace CFT.MonopoleLangevin

/-- 分配関数 -/
noncomputable def Z (x : ℝ) : ℝ := sinh x / x

/-- ゲージ場の動径関数 -/
noncomputable def W (x : ℝ) : ℝ := x / sinh x

/-- Higgs 場の動径関数(Langevin 関数) -/
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

theorem bogomolny_W (x : ℝ) (hx : x ≠ 0) : HasDerivAt W (-(h x * W x)) x := by
  have hs := sinh_ne x hx
  have h1 := (hasDerivAt_id' x).div (Real.hasDerivAt_sinh x) hs
  refine h1.congr_deriv ?_
  unfold h W
  field_simp
  ring

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

end CFT.MonopoleLangevin
