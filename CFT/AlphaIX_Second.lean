/-
  α-IX.31〜IX.34、XI.3:第二法則・エルゴード性・相転移・位相欠陥・捕捉面

  * IX.31 焦点を結ぶ定理:Raychaudhuri の式とヌルエネルギー条件から θ′ ≤ −θ²/2(外部:幾何の恒等式)。
      θ(0) < 0 で区間 [0, Λ] の上で θ < 0 なら Λ < −2/θ(0)(`focusing`):有限のアフィン助変数で θ → −∞。
      大域的な面積定理(Hawking 1971)は外部。
  * IX.32 エルゴード性:Euclid の首は曲率 −1/ℓ² の H²(IX.22)。種数 g ≥ 2 の閉曲面 H²/Γ の面積は
      Gauss–Bonnet で 4π(g − 1)ℓ²(`hyperbolic_area`)。測地流がエルゴード的(Hopf 1936)、コンパクトな
      商が存在すること:外部。
  * IX.33 相転移:W の Landau の自由エネルギー F(W) = (1 − W²)²/2(首の磁気のエネルギー、AlphaII_EYM の ρ)は
      W = 0 で極大(F″(0) = −2)、W = ±1 で最小 0 < F(0) = 1/2(`landau`):凝縮した相の方が低い。
      Hawking–Page 型:AdS の Schwarzschild の自由エネルギー F = (r₊/4)(1 − r₊²/L²) は r₊ > L で負(`hawking_page`)
      (Euclid 作用の評価は外部)。
  * IX.34 秩序変数の空間 G/H = SU(2)/U(1) = S²:はりねずみの写像の次数 = 磁束/4π = 1(`hedgehog_charge`、
      帽子の赤道で AlphaII_EYM `flux_cap` の 4π sin²x = 4π)。π₂(S²) = ℤ と次数による分類は外部。
  * XI.3 捕捉面:閉じた FRW a(η)²(−dη² + dχ² + sin²χ dΩ²)の球 χ の面積半径 R = a sin χ、ヌルの膨張率
      θ± ∝ a′/a ± cot χ。帽子 a = ℓ cos η で θ₊ ∝ cot χ − tan η = cos(χ + η)/(sin χ cos η)(`expansion_cap`)。
      帽子の厳密な領域 χ < π/2 − η(波面の内側)では θ₊ > 0、θ₋ < 0:捕捉面はない(`no_trapped_in_cap`)。
      θ₊ = 0 となるのはちょうど波面 χ = π/2 − η の上(`marginal_on_front`)。捕捉面ができるかどうかは
      波面の外(首の影響が届く領域)の解で決まり、帽子だけでは判定できない(部分)。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace CFT.Second

open Real Set

/-! ### IX.31 焦点 -/

/-- 【α-IX.31】θ′ ≤ −θ²/2、[0, Λ] で θ < 0 なら Λ < −2/θ(0) -/
theorem focusing (θ θd : ℝ → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hθ : ∀ s ∈ Icc 0 Λ, HasDerivAt θ (θd s) s) (hneg : ∀ s ∈ Icc 0 Λ, θ s < 0)
    (hray : ∀ s ∈ Icc 0 Λ, θd s ≤ -(θ s ^ 2 / 2)) : Λ < -2 / θ 0 := by
  have h0 : (0 : ℝ) ∈ Icc 0 Λ := ⟨le_refl _, hΛ⟩
  have hΛm : Λ ∈ Icc 0 Λ := ⟨hΛ, le_refl _⟩
  have hd : ∀ s ∈ Icc 0 Λ,
      HasDerivAt (fun x => (θ x)⁻¹ - x / 2) (-(θd s) / θ s ^ 2 - 1 / 2) s := by
    intro s hs
    exact ((hθ s hs).inv (hneg s hs).ne).sub ((hasDerivAt_id' s).div_const 2)
  have hmono : MonotoneOn (fun x => (θ x)⁻¹ - x / 2) (Icc 0 Λ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 Λ)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' := Ioo_subset_Icc_self hs
      rw [(hd s hs').deriv]
      have hpos : 0 < θ s ^ 2 := by have := hneg s hs'; positivity
      have h1 : θ s ^ 2 / 2 ≤ -(θd s) := by linarith [hray s hs']
      have h2 : 1 / 2 ≤ -(θd s) / θ s ^ 2 := by
        rw [le_div_iff₀ hpos]; linarith
      linarith
  have hle : (θ 0)⁻¹ - 0 / 2 ≤ (θ Λ)⁻¹ - Λ / 2 := hmono h0 hΛm hΛ
  have hΛneg : (θ Λ)⁻¹ < 0 := inv_lt_zero.mpr (hneg Λ hΛm)
  have h00 := hneg 0 h0
  have : (θ 0)⁻¹ + Λ / 2 < 0 := by linarith
  have e : -2 / θ 0 = -2 * (θ 0)⁻¹ := by ring
  rw [e]; linarith

/-! ### IX.32 双曲面の面積 -/

/-- 【α-IX.32】Gauss–Bonnet:(−1/ℓ²)A = 2π(2 − 2g) ⇔ A = 4π(g − 1)ℓ² -/
theorem hyperbolic_area (l A g : ℝ) (hl : l ≠ 0) :
    -1 / l ^ 2 * A = 2 * π * (2 - 2 * g) ↔ A = 4 * π * (g - 1) * l ^ 2 := by
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  constructor
  · intro h; field_simp at h; linarith
  · intro h; rw [h]; field_simp <;> ring

/-! ### IX.33 相転移 -/

/-- 【α-IX.33】F(W) = (1 − W²)²/2:F′(0) = 0、F″(0) = −2、F(±1) = 0 < F(0) = 1/2 -/
theorem landau :
    HasDerivAt (fun W : ℝ => (1 - W ^ 2) ^ 2 / 2) 0 0 ∧
    HasDerivAt (fun W : ℝ => -2 * W * (1 - W ^ 2)) (-2) 0 ∧
    (fun W : ℝ => (1 - W ^ 2) ^ 2 / 2) 1 = 0 ∧ (fun W : ℝ => (1 - W ^ 2) ^ 2 / 2) (-1) = 0 ∧
    (0 : ℝ) < (fun W : ℝ => (1 - W ^ 2) ^ 2 / 2) 0 := by
  refine ⟨?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · have h := (((hasDerivAt_pow 2 (0 : ℝ)).const_sub 1).pow 2).div_const 2
    convert h using 1; simp
  · have h := ((hasDerivAt_id' (0 : ℝ)).const_mul (-2)).mul ((hasDerivAt_pow 2 (0 : ℝ)).const_sub 1)
    convert h using 1; simp

/-- 【α-IX.33】Hawking–Page 型:F = (r₊/4)(1 − r₊²/L²) < 0 ⇔ r₊ > L(r₊, L > 0) -/
theorem hawking_page (rp L : ℝ) (hr : 0 < rp) (hL : 0 < L) :
    rp / 4 * (1 - rp ^ 2 / L ^ 2) < 0 ↔ L < rp := by
  have hL2 : 0 < L ^ 2 := by positivity
  constructor
  · intro h
    have h1 : 1 - rp ^ 2 / L ^ 2 < 0 := by
      by_contra hc; push_neg at hc; have : 0 ≤ rp / 4 * (1 - rp ^ 2 / L ^ 2) := by positivity
      linarith
    rw [sub_neg, one_lt_div hL2] at h1
    nlinarith
  · intro h
    have h1 : 1 - rp ^ 2 / L ^ 2 < 0 := by
      rw [sub_neg, one_lt_div hL2]; nlinarith
    have : 0 < rp / 4 := by positivity
    nlinarith

/-! ### IX.34 はりねずみの次数 -/

/-- 【α-IX.34】帽子の赤道で磁束 4π sin²(π/2) = 4π、次数 = 磁束/4π = 1 -/
theorem hedgehog_charge : 4 * π * sin (π / 2) ^ 2 / (4 * π) = 1 := by
  rw [sin_pi_div_two]; have := pi_ne_zero; field_simp

/-! ### XI.3 捕捉面 -/

/-- 【α-XI.3】a = ℓ cos η:(a′ sin χ + a cos χ)/(a sin χ) = cot χ − tan η = cos(χ + η)/(sin χ cos η) -/
theorem expansion_cap (l χ η : ℝ) (hl : l ≠ 0) (hs : sin χ ≠ 0) (hc : cos η ≠ 0) :
    (-(l * sin η) * sin χ + l * cos η * cos χ) / (l * cos η * sin χ)
      = cos χ / sin χ - sin η / cos η ∧
    cos χ / sin χ - sin η / cos η = cos (χ + η) / (sin χ * cos η) := by
  constructor
  · field_simp <;> ring
  · rw [cos_add]; field_simp <;> ring

/-- 【α-XI.3】帽子の厳密な領域(0 < χ、0 ≤ η、χ + η < π/2)では θ₊ ∝ cot χ − tan η > 0、θ₋ ∝ −cot χ − tan η < 0 -/
theorem no_trapped_in_cap (χ η : ℝ) (hχ : 0 < χ) (hη : 0 ≤ η) (hfront : χ + η < π / 2) :
    0 < cos χ / sin χ - sin η / cos η ∧ -(cos χ / sin χ) - sin η / cos η < 0 := by
  have hχ2 : χ < π / 2 := by linarith
  have hη2 : η < π / 2 := by linarith
  have hsχ : 0 < sin χ := sin_pos_of_pos_of_lt_pi hχ (by linarith [pi_pos])
  have hcχ : 0 < cos χ := cos_pos_of_mem_Ioo ⟨by linarith, hχ2⟩
  have hcη : 0 < cos η := cos_pos_of_mem_Ioo ⟨by linarith, hη2⟩
  have hsη : 0 ≤ sin η := sin_nonneg_of_nonneg_of_le_pi hη (by linarith [pi_pos])
  have hcs : 0 < cos (χ + η) := cos_pos_of_mem_Ioo ⟨by linarith, hfront⟩
  constructor
  · rw [(expansion_cap 1 χ η one_ne_zero hsχ.ne' hcη.ne').2]
    positivity
  · have : 0 < cos χ / sin χ := div_pos hcχ hsχ
    have : 0 ≤ sin η / cos η := div_nonneg hsη hcη.le
    linarith

/-- 【α-XI.3】波面 χ = π/2 − η の上で θ₊ = 0(周辺的に捕捉された球) -/
theorem marginal_on_front (η : ℝ) (hη : 0 < η) (hη2 : η < π / 2) :
    cos (π / 2 - η) / sin (π / 2 - η) - sin η / cos η = 0 := by
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub]; ring

end CFT.Second
