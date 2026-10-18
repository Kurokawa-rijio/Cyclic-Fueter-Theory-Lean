/-
  α-VII.7 の比較補題:単極子ゼロモードが L² になる条件

  u(θ) = tan(θ/2)^m sin(θ)^q(AlphaCompleteD.zero_mode の厳密解)について
    u ∈ L²(0, π/2) ⇔ m + q > −1/2、  u ∈ L²(π/2, π) ⇔ q − m > −1/2。
  証明の流れ
  1. べきの比較:0 < aθ ≤ X ≤ bθ なら min(a^m, b^m) θ^m ≤ X^m ≤ max(a^m, b^m) θ^m
  2. 0 < θ < π/2 で θ/2 ≤ tan(θ/2) ≤ θ、(2/π)θ ≤ sin θ ≤ θ
  3. よって u² は定数倍の範囲で θ^{2(m+q)} に挟まれる
  4. θ^s が (0, T) で可積分 ⇔ s > −1(Mathlib の intervalIntegral.integrableOn_Ioo_rpow_iff)
  5. θ = π − φ と置くと tan(θ/2) = 1/tan(φ/2)、sin θ = sin φ なので π 側は m → −m の場合
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real MeasureTheory Set

namespace CFT.ZeroModeL2

/-! ### 1. べきの比較 -/

theorem rpow_between {a b θ X m : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ : 0 < θ)
    (h1 : a * θ ≤ X) (h2 : X ≤ b * θ) :
    min (a ^ m) (b ^ m) * θ ^ m ≤ X ^ m ∧ X ^ m ≤ max (a ^ m) (b ^ m) * θ ^ m := by
  have hX : 0 < X := lt_of_lt_of_le (mul_pos ha hθ) h1
  have hA : (a * θ) ^ m = a ^ m * θ ^ m := Real.mul_rpow ha.le hθ.le
  have hB : (b * θ) ^ m = b ^ m * θ ^ m := Real.mul_rpow (ha.le.trans hab) hθ.le
  have hθm : 0 < θ ^ m := Real.rpow_pos_of_pos hθ m
  rcases le_total 0 m with hm | hm
  · have l : (a * θ) ^ m ≤ X ^ m := Real.rpow_le_rpow (by positivity) h1 hm
    have u : X ^ m ≤ (b * θ) ^ m := Real.rpow_le_rpow hX.le h2 hm
    rw [hA] at l; rw [hB] at u
    constructor
    · calc min (a ^ m) (b ^ m) * θ ^ m ≤ a ^ m * θ ^ m :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hθm.le
        _ ≤ X ^ m := l
    · calc X ^ m ≤ b ^ m * θ ^ m := u
        _ ≤ max (a ^ m) (b ^ m) * θ ^ m := mul_le_mul_of_nonneg_right (le_max_right _ _) hθm.le
  · have l : (b * θ) ^ m ≤ X ^ m := Real.rpow_le_rpow_of_exponent_nonpos hX h2 hm
    have u : X ^ m ≤ (a * θ) ^ m := Real.rpow_le_rpow_of_exponent_nonpos (by positivity) h1 hm
    rw [hB] at l; rw [hA] at u
    constructor
    · calc min (a ^ m) (b ^ m) * θ ^ m ≤ b ^ m * θ ^ m :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hθm.le
        _ ≤ X ^ m := l
    · calc X ^ m ≤ a ^ m * θ ^ m := u
        _ ≤ max (a ^ m) (b ^ m) * θ ^ m := mul_le_mul_of_nonneg_right (le_max_left _ _) hθm.le

/-! ### 2. 三角関数の評価 -/

theorem tan_half_bounds {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    (1 / 2) * θ ≤ tan (θ / 2) ∧ tan (θ / 2) ≤ 1 * θ := by
  have hh0 : 0 < θ / 2 := by linarith
  have hh1 : θ / 2 < π / 2 := by linarith [pi_pos]
  constructor
  · have := Real.lt_tan hh0 hh1; linarith
  · -- tan(θ/2) = sin(θ/2)/cos(θ/2) ≤ (θ/2)/cos(π/4) ≤ θ
    have hc : cos (π / 4) ≤ cos (θ / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hh0.le (by linarith [pi_pos]) (by linarith)
    have hc4 : (1 / 2 : ℝ) ≤ cos (π / 4) := by
      rw [cos_pi_div_four]
      have : (1 : ℝ) ≤ √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    have hcpos : 0 < cos (θ / 2) := by linarith
    have hs : sin (θ / 2) ≤ θ / 2 := (Real.sin_lt hh0).le
    rw [tan_eq_sin_div_cos, div_le_iff hcpos]
    have hs0 : 0 ≤ sin (θ / 2) := (sin_pos_of_pos_of_lt_pi hh0 (by linarith [pi_pos])).le
    nlinarith

theorem sin_bounds {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    (2 / π) * θ ≤ sin θ ∧ sin θ ≤ 1 * θ := by
  constructor
  · exact Real.mul_le_sin h0.le h1.le
  · have := Real.sin_lt h0; linarith

/-! ### 3. u² の評価 -/

/-- u(θ)² は (0, π/2) で定数倍の範囲で θ^{2(m+q)} に挟まれる -/
theorem u_sq_bounds (m q : ℝ) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      c1 * θ ^ (2 * (m + q)) ≤ (tan (θ / 2) ^ m * sin θ ^ q) ^ 2 ∧
      (tan (θ / 2) ^ m * sin θ ^ q) ^ 2 ≤ c2 * θ ^ (2 * (m + q)) := by
  have hπ : 0 < 2 / π := by positivity
  have h2π : 2 / π ≤ 1 := by rw [div_le_one pi_pos]; linarith [Real.two_le_pi]
  set L1 := min ((1 / 2 : ℝ) ^ m) ((1 : ℝ) ^ m)
  set U1 := max ((1 / 2 : ℝ) ^ m) ((1 : ℝ) ^ m)
  set L2 := min ((2 / π) ^ q) ((1 : ℝ) ^ q)
  set U2 := max ((2 / π) ^ q) ((1 : ℝ) ^ q)
  have hL1 : 0 < L1 := lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos one_pos _)
  have hL2 : 0 < L2 := lt_min (Real.rpow_pos_of_pos hπ _) (Real.rpow_pos_of_pos one_pos _)
  refine ⟨(L1 * L2) ^ 2, (U1 * U2) ^ 2, by positivity, ?_⟩
  intro θ hθ
  obtain ⟨h0, h1⟩ := hθ
  obtain ⟨t1, t2⟩ := tan_half_bounds h0 h1
  obtain ⟨s1, s2⟩ := sin_bounds h0 h1
  obtain ⟨a1, a2⟩ := rpow_between (m := m) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) h0 t1 t2
  obtain ⟨b1, b2⟩ := rpow_between (m := q) hπ h2π h0 s1 s2
  have hθm := Real.rpow_pos_of_pos h0 m
  have hθq := Real.rpow_pos_of_pos h0 q
  have hmq : θ ^ (2 * (m + q)) = (θ ^ m * θ ^ q) ^ 2 := by
    rw [← Real.rpow_add h0, mul_comm, Real.rpow_mul h0.le, Real.rpow_two]
  rw [hmq]
  have hlow : L1 * L2 * (θ ^ m * θ ^ q) ≤ tan (θ / 2) ^ m * sin θ ^ q := by
    calc L1 * L2 * (θ ^ m * θ ^ q) = (L1 * θ ^ m) * (L2 * θ ^ q) := by ring
      _ ≤ tan (θ / 2) ^ m * sin θ ^ q := by
        apply mul_le_mul a1 b1 (by positivity)
        exact (Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) t1) m).le
  have hup : tan (θ / 2) ^ m * sin θ ^ q ≤ U1 * U2 * (θ ^ m * θ ^ q) := by
    calc tan (θ / 2) ^ m * sin θ ^ q ≤ (U1 * θ ^ m) * (U2 * θ ^ q) := by
          apply mul_le_mul a2 b2
          · exact (Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) s1) q).le
          · exact (Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) t1) m).le.trans a2
      _ = U1 * U2 * (θ ^ m * θ ^ q) := by ring
  have hpos : 0 ≤ L1 * L2 * (θ ^ m * θ ^ q) := by positivity
  constructor
  · calc (L1 * L2) ^ 2 * (θ ^ m * θ ^ q) ^ 2 = (L1 * L2 * (θ ^ m * θ ^ q)) ^ 2 := by ring
      _ ≤ (tan (θ / 2) ^ m * sin θ ^ q) ^ 2 := pow_le_pow_left₀ hpos hlow 2
  · calc (tan (θ / 2) ^ m * sin θ ^ q) ^ 2 ≤ (U1 * U2 * (θ ^ m * θ ^ q)) ^ 2 :=
          pow_le_pow_left₀ (le_trans hpos hlow) hup 2
      _ = (U1 * U2) ^ 2 * (θ ^ m * θ ^ q) ^ 2 := by ring

/-! ### 4. 比較による可積分性の判定 -/

theorem integrable_iff_of_bounds {f : ℝ → ℝ} {e c1 c2 T : ℝ} (hT : 0 < T) (hc1 : 0 < c1)
    (hf : ContinuousOn f (Ioo 0 T))
    (hb : ∀ θ ∈ Ioo (0 : ℝ) T, c1 * θ ^ e ≤ f θ ∧ f θ ≤ c2 * θ ^ e) :
    IntegrableOn f (Ioo 0 T) ↔ -1 < e := by
  have hmeas := hf.aestronglyMeasurable (μ := volume) measurableSet_Ioo
  constructor
  · intro hI
    rw [← intervalIntegral.integrableOn_Ioo_rpow_iff hT]
    refine Integrable.mono' (hI.const_mul (1 / c1)) ?_ ?_
    · exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable
        (μ := volume) measurableSet_Ioo
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall ?_)
      intro θ hθ
      have h1 := (hb θ hθ).1
      have hθe : 0 ≤ θ ^ e := (Real.rpow_pos_of_pos hθ.1 e).le
      rw [Real.norm_eq_abs, abs_of_nonneg hθe]
      calc θ ^ e = 1 / c1 * (c1 * θ ^ e) := by field_simp
        _ ≤ 1 / c1 * f θ := mul_le_mul_of_nonneg_left h1 (by positivity)
  · intro he
    have hg : IntegrableOn (fun θ => c2 * θ ^ e) (Ioo 0 T) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 he).const_mul c2
    refine Integrable.mono' hg hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall ?_)
    intro θ hθ
    obtain ⟨h1, h2⟩ := hb θ hθ
    have hf0 : 0 ≤ f θ := le_trans (by have := Real.rpow_pos_of_pos hθ.1 e; positivity) h1
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    exact h2

/-! ### 5. ゼロモードの L² 条件 -/

/-- θ = 0 側:u ∈ L²(0, π/2) ⇔ m + q > −1/2 -/
theorem zero_side (m q : ℝ) :
    IntegrableOn (fun θ => (tan (θ / 2) ^ m * sin θ ^ q) ^ 2) (Ioo 0 (π / 2)) ↔ -(1 / 2) < m + q := by
  obtain ⟨c1, c2, hc1, hb⟩ := u_sq_bounds m q
  have hcont : ContinuousOn (fun θ => (tan (θ / 2) ^ m * sin θ ^ q) ^ 2) (Ioo 0 (π / 2)) := by
    intro θ hθ
    have h0 := hθ.1; have h1 := hθ.2
    have hc : cos (θ / 2) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩).ne'
    have ht : 0 < tan (θ / 2) := by
      rw [tan_eq_sin_div_cos]
      exact div_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos]))
        (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩)
    have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.pow
    apply ContinuousAt.mul
    · have hct : ContinuousAt (fun θ : ℝ => tan (θ / 2)) θ :=
        ContinuousAt.comp (f := fun θ : ℝ => θ / 2) (Real.continuousAt_tan.2 hc)
          ((continuous_id.div_const (2 : ℝ)).continuousAt)
      exact hct.rpow_const (Or.inl ht.ne')
    · exact continuous_sin.continuousAt.rpow_const (Or.inl hs.ne')
  rw [integrable_iff_of_bounds (by positivity) hc1 hcont hb]
  constructor <;> intro h <;> linarith

/-- θ = π 側(θ = π − φ と置く):u(π − φ) = tan(φ/2)^{−m} sin(φ)^q -/
theorem reflect (m q φ : ℝ) (h0 : 0 < φ) (h1 : φ < π / 2) :
    (tan ((π - φ) / 2) ^ m * sin (π - φ) ^ q) ^ 2 = (tan (φ / 2) ^ (-m) * sin φ ^ q) ^ 2 := by
  have e1 : (π - φ) / 2 = π / 2 - φ / 2 := by ring
  rw [e1, tan_pi_div_two_sub, sin_pi_sub]
  have ht : 0 < tan (φ / 2) := by
    rw [tan_eq_sin_div_cos]
    exact div_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos]))
      (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩)
  rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le]

theorem pi_side (m q : ℝ) :
    IntegrableOn (fun φ => (tan ((π - φ) / 2) ^ m * sin (π - φ) ^ q) ^ 2) (Ioo 0 (π / 2))
      ↔ -(1 / 2) < q - m := by
  rw [integrableOn_congr_fun (fun φ hφ => reflect m q φ hφ.1 hφ.2) measurableSet_Ioo,
    zero_side (-m) q]
  constructor <;> intro h <;> linarith

/-- まとめ:両端で L² ⇔ |m| < q + 1/2(AlphaCompleteD.exponent_condition と同じ条件) -/
theorem zero_mode_L2 (m q : ℝ) :
    (IntegrableOn (fun θ => (tan (θ / 2) ^ m * sin θ ^ q) ^ 2) (Ioo 0 (π / 2)) ∧
      IntegrableOn (fun φ => (tan ((π - φ) / 2) ^ m * sin (π - φ) ^ q) ^ 2) (Ioo 0 (π / 2)))
      ↔ |m| < q + 1 / 2 := by
  rw [zero_side, pi_side, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end CFT.ZeroModeL2
