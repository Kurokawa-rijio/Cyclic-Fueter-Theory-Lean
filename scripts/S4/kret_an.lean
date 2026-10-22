section Analysis
open Real Filter Topology Set

/-- 固有時 τ = ℓ sin η で a = ℓ cos η は a² = ℓ² − τ² -/
theorem cap_cosmic (l η : ℝ) : (l * cos η) ^ 2 = l ^ 2 - (l * sin η) ^ 2 := by
  have := sin_sq_add_cos_sq η; nlinarith

/-- η → π/2⁻ で K = 24ℓ⁴/(ℓ cos η)⁸ → ∞ -/
theorem kret_blowup (l : ℝ) (hl : 0 < l) :
    Tendsto (fun η => 24 * l ^ 4 * ((l * cos η)⁻¹) ^ 8) (𝓝[<] (π / 2)) atTop := by
  have h1 : Tendsto (fun η => l * cos η) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    have hc := tendsto_cos_pi_div_two
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (tendsto_nhdsWithin_iff.mp hc).1
      simpa using this.const_mul l
    · filter_upwards [(tendsto_nhdsWithin_iff.mp hc).2] with η hη
      exact Set.mem_Ioi.mpr (mul_pos hl (Set.mem_Ioi.mp hη))
  have h2 : Tendsto (fun η => (l * cos η) ^ 8) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_nhdsWithin_iff.mp h1).1.pow 8
    · filter_upwards [(tendsto_nhdsWithin_iff.mp h1).2] with η hη
      exact Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp hη) 8)
  have h3 := (tendsto_inv_nhdsGT_zero.comp h2).const_mul_atTop (by positivity : (0 : ℝ) < 24 * l ^ 4)
  refine h3.congr' ?_
  filter_upwards with η
  simp only [Function.comp, inv_pow]

/-- K と ρ̂ は χ によらない(空間的に一様)ので、極座標の中心 χ → 0⁺ でも同じ値をとる -/
theorem center_limit (v : ℝ) (f : ℝ → ℝ) (hf : ∀ χ ∈ Ioo 0 π, f χ = v) :
    Tendsto f (𝓝[>] 0) (𝓝 v) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with χ hχ
  exact (hf χ hχ).symm

theorem density_center (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun χ => CFT.S4J.Rho (a * sin χ) (cos χ) 0 (-(sin χ) / a)) (𝓝[>] 0) (𝓝 (3 / (2 * a ^ 4))) :=
  center_limit _ _ fun χ hχ => cap_density a (sin χ) (cos χ) ha (sin_pos_of_pos_of_lt_pi hχ.1 hχ.2).ne'
    (sin_sq_add_cos_sq χ)

/-- 共形計量 a²(−dη² + dχ²) の曲線 η ↦ (η, χ(η)) がヌル ⇔ χ′² = 1 -/
theorem front_null (a χ' : ℝ) (ha : a ≠ 0) : -a ^ 2 + a ^ 2 * χ' ^ 2 = 0 ↔ χ' ^ 2 = 1 := by
  constructor
  · intro h
    have : a ^ 2 * (χ' ^ 2 - 1) = 0 := by linear_combination h
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 ha); linarith
  · intro h; rw [h]; ring

/-- 連続な χ′ が至る所 χ′² = 1 で χ′(0) = −1 なら至る所 χ′ = −1(内向きの波面は向きを変えない) -/
theorem front_sign (χ' : ℝ → ℝ) (hc : Continuous χ') (h : ∀ η, χ' η ^ 2 = 1) (h0 : χ' 0 = -1) :
    ∀ η, χ' η = -1 := by
  intro η
  have hv : χ' η = 1 ∨ χ' η = -1 := by
    have := h η
    have : (χ' η - 1) * (χ' η + 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  rcases hv with h1 | h1
  · exfalso
    have hne : ∀ x, χ' x ≠ 0 := fun x hx => by have := h x; rw [hx] at this; norm_num at this
    rcases le_total 0 η with hle | hle
    · obtain ⟨x, -, hx⟩ := intermediate_value_Icc hle hc.continuousOn
        (show (0 : ℝ) ∈ Icc (χ' 0) (χ' η) by rw [h0, h1]; norm_num)
      exact hne x hx
    · obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hle hc.continuousOn
        (show (0 : ℝ) ∈ Icc (χ' 0) (χ' η) by rw [h0, h1]; norm_num)
      exact hne x hx
  · exact h1

/-- 接合 χ(0) = π/2 から内向きのヌルな波面は χ(η) = π/2 − η -/
theorem front_inward (χ χ' : ℝ → ℝ) (hd : ∀ η, HasDerivAt χ (χ' η) η) (hc : Continuous χ')
    (hnull : ∀ η, χ' η ^ 2 = 1) (h0' : χ' 0 = -1) (h0 : χ 0 = π / 2) : ∀ η, χ η = π / 2 - η := by
  have hs := front_sign χ' hc hnull h0'
  have hD : ∀ η, HasDerivAt (fun η => χ η + η) 0 η := by
    intro η
    have := (hd η).add (hasDerivAt_id η)
    simpa [hs η] using this
  intro η
  have := is_const_of_deriv_eq_zero (fun z => (hD z).differentiableAt) (fun z => (hD z).deriv) η 0
  simp only [h0, add_zero] at this
  linarith

/-- 波面が中心 χ = 0 に着くのは η = π/2(崩壊の瞬間)だけ。それ以前の中心は波面の外(帽子の依存領域) -/
theorem front_hits_center (η : ℝ) : π / 2 - η = 0 ↔ η = π / 2 := by
  constructor <;> intro h <;> linarith

end Analysis

end CFT.S5K
