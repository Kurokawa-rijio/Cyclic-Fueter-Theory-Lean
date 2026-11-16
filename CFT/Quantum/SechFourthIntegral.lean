/-
  α-VI.8 の一部:インスタントンの作用に現れる積分 ∫_ℝ 2 sech⁴ x dx = 8/3

  原始関数 F = tanh − tanh³/3 を使う。
  * tanh′ = sech²(`hasDerivAt_th`)
  * F′ = sech²(1 − tanh²) = sech⁴(`hasDerivAt_F`)
  * tanh → ±1(x → ±∞)なので F → ±2/3(`F_top`、`F_bot`)
  * sech⁴ ≥ 0 で、[−n, n] 上の積分 F(n) − F(−n) が 4/3 に収束するので可積分(`integrable_sech4`)
  * ∫ sech⁴ = 2/3 − (−2/3) = 4/3、したがって ∫ 2 sech⁴ = 8/3(`integral_two_sech4`)
  これで AlphaVI の `instanton_action`(3π² · 8/3 = 8π²)の 8/3 が積分として証明される。
-/
import Mathlib

namespace CFT.VISech

open Real MeasureTheory Filter Topology intervalIntegral

/-- tanh x = sinh x / cosh x -/
noncomputable def th (x : ℝ) : ℝ := sinh x / cosh x

/-- 原始関数 F = tanh − tanh³/3 -/
noncomputable def F (x : ℝ) : ℝ := th x - th x ^ 3 / 3

theorem cosh_ne (x : ℝ) : cosh x ≠ 0 := (cosh_pos x).ne'

theorem sinh_sq (x : ℝ) : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [cosh_sq x]; ring

/-- tanh′ = sech² -/
theorem hasDerivAt_th (x : ℝ) : HasDerivAt th ((cosh x)⁻¹ ^ 2) x := by
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_ne x)
  have h1 : cosh x * cosh x - sinh x * sinh x = 1 := by
    have := sinh_sq x
    nlinarith [this]
  show HasDerivAt (fun y => sinh y / cosh y) _ x
  exact h.congr_deriv (by rw [h1, inv_pow, one_div])

/-- tanh² = 1 − sech² -/
theorem th_sq (x : ℝ) : th x ^ 2 = 1 - (cosh x)⁻¹ ^ 2 := by
  have hc := cosh_ne x
  rw [th, div_pow, sinh_sq x, sub_div, div_self (pow_ne_zero 2 hc), inv_pow, one_div]

/-- F′ = sech⁴ -/
theorem hasDerivAt_F (x : ℝ) : HasDerivAt F ((cosh x)⁻¹ ^ 4) x := by
  have h := (hasDerivAt_th x).sub (((hasDerivAt_th x).pow 3).div_const 3)
  have e2 : th x ^ (3 - 1) = 1 - (cosh x)⁻¹ ^ 2 := th_sq x
  show HasDerivAt (fun y => th y - th y ^ 3 / 3) _ x
  refine h.congr_deriv ?_
  rw [e2]
  push_cast
  ring

/-- tanh x = (1 − e^{−2x})/(1 + e^{−2x}) の形 -/
theorem th_eq (x : ℝ) : th x = (1 - exp (-x) ^ 2) / (1 + exp (-x) ^ 2) := by
  have h1 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
  have hden : (1 + exp (-x) ^ 2) ≠ 0 := by positivity
  rw [th, div_eq_div_iff (cosh_ne x) hden, sinh_eq, cosh_eq]
  linear_combination (exp (-x)) * h1

theorem th_top : Tendsto th atTop (𝓝 1) := by
  have hu := tendsto_exp_neg_atTop_nhds_zero
  have h : Tendsto (fun x => (1 - exp (-x) ^ 2) / (1 + exp (-x) ^ 2)) atTop
      (𝓝 ((1 - 0 ^ 2) / (1 + 0 ^ 2))) :=
    ((tendsto_const_nhds.sub (hu.pow 2)).div (tendsto_const_nhds.add (hu.pow 2)) (by norm_num))
  norm_num at h
  exact Tendsto.congr (fun x => (th_eq x).symm) h

theorem th_neg (x : ℝ) : th (-x) = -th x := by
  simp only [th, sinh_neg, cosh_neg, neg_div]

theorem th_bot : Tendsto th atBot (𝓝 (-1)) := by
  have h := (th_top.comp tendsto_neg_atBot_atTop).neg
  refine Tendsto.congr (fun x => ?_) h
  simp only [Function.comp_apply, th_neg, neg_neg]

theorem F_top : Tendsto F atTop (𝓝 (1 - 1 ^ 3 / 3)) :=
  th_top.sub ((th_top.pow 3).div_const 3)

theorem F_bot : Tendsto F atBot (𝓝 (-1 - (-1) ^ 3 / 3)) :=
  th_bot.sub ((th_bot.pow 3).div_const 3)

theorem sech4_cont : Continuous fun x : ℝ => (cosh x)⁻¹ ^ 4 :=
  (continuous_cosh.inv₀ cosh_ne).pow 4

/-- sech⁴ は ℝ 上で可積分 -/
theorem integrable_sech4 : Integrable (fun x : ℝ => (cosh x)⁻¹ ^ 4) := by
  have hint : ∀ n : ℕ, ∫ x in (-(n : ℝ))..(n : ℝ), ‖(cosh x)⁻¹ ^ 4‖ = F n - F (-(n : ℝ)) := by
    intro n
    have : ∀ x, ‖(cosh x)⁻¹ ^ 4‖ = (cosh x)⁻¹ ^ 4 := fun x =>
      Real.norm_of_nonneg (by positivity)
    simp_rw [this]
    exact integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_F x)
      (sech4_cont.intervalIntegrable _ _)
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  refine integrable_of_intervalIntegral_norm_tendsto
    (a := fun n : ℕ => -(n : ℝ)) (b := fun n : ℕ => (n : ℝ))
    ((1 - 1 ^ 3 / 3) - (-1 - (-1) ^ 3 / 3))
    (fun n => (sech4_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
    hneg tendsto_natCast_atTop_atTop ?_
  simp_rw [hint]
  exact (F_top.comp tendsto_natCast_atTop_atTop).sub (F_bot.comp hneg)

/-- ∫_ℝ sech⁴ = 4/3 -/
theorem integral_sech4 : ∫ x : ℝ, (cosh x)⁻¹ ^ 4 = 4 / 3 := by
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_F integrable_sech4 F_bot F_top]
  norm_num

/-- 【α-VI.8】∫_ℝ 2 sech⁴ x dx = 8/3 -/
theorem integral_two_sech4 : ∫ x : ℝ, 2 * (cosh x)⁻¹ ^ 4 = 8 / 3 := by
  rw [integral_mul_left, integral_sech4]
  norm_num

/-- 【α-VI.8】インスタントンの作用:3π² · ∫ 2 sech⁴ = 8π² -/
theorem instanton_action_integral : 3 * π ^ 2 * (∫ x : ℝ, 2 * (cosh x)⁻¹ ^ 4) = 8 * π ^ 2 := by
  rw [integral_two_sech4]; ring

end CFT.VISech
