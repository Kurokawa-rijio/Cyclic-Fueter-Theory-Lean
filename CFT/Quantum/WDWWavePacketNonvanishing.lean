/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅。

  物理的状態は波束 Ψ_f = ∫ g(C) Ψ_C dC（C > 8c²ℓ に台を持つ g）である。
  核関数版は `WDWBoundaryConditions.lean` で閉じており、Ψ₊(0,b) = 1/σ_C(b) ≠ 0
  だが、波束への波及には C 積分の下限評価が要る（`GAP_5-8_prep.md` §5、OPEN-中）。

  このモジュールはその第一段として、具体的な波束（T₀ = 0、g = 𝟙_[C₁,C₂]、
  首 b = ℓ）について境界値の閉形式と正の明示下限を証明する。
  首では Q c l C l = ℓ(C − 8c²ℓ) なので、被積分関数は 1/√(ℓ(C − 8c²ℓ)) で、
  原始関数は 2√(ℓ(C − 8c²ℓ))/ℓ。FTC-2 により

    Ψ_f(0, ℓ) = ∫_{C₁}^{C₂} dC/√(ℓ(C − 8c²ℓ))
               = 2(√(ℓ(C₂ − 8c²ℓ)) − √(ℓ(C₁ − 8c²ℓ)))/ℓ > 0

  （C₁ < C₂、8c²ℓ < C₁）。具体例 c = ℓ = 1、C ∈ [9, 10] では値は
  2(√2 − 1) ≈ 0.828（sympy で照合済み）。

  残り：一般の g（滑らかな台を持つ重み）に対する下限評価。位相 e^{−iCT₀/ħ} が
  入る場合（T₀ ≠ 0）の評価も含めて OPEN のまま。
-/
import CFT.Quantum.WDWBoundaryConditions

namespace CFT.WDWWavePacket

open CFT.WKB CFT.WDWBoundary MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 首 b = ℓ での Q：Q c l C l = ℓ * (C − 8c²ℓ) -/
theorem Q_neck (C : ℝ) : Q c l C l = l * (C - 8 * c ^ 2 * l) := by
  unfold Q
  ring

/-- 物理的枝 C > 8c²ℓ では首での Q > 0 -/
theorem Q_neck_pos {C : ℝ} (hC : 8 * c ^ 2 * l < C) (hl : 0 < l) :
    0 < Q c l C l := by
  rw [Q_neck]
  exact mul_pos hl (sub_pos.mpr hC)

/-- 原始関数 F(C) = 2√(Q c l C l)/ℓ の微分は 1/√(Q c l C l) -/
theorem hasDerivAt_packetAntideriv {x : ℝ} (hx : 8 * c ^ 2 * l < x) (hl : 0 < l) :
    HasDerivAt (fun C => 2 * Real.sqrt (Q c l C l) / l)
      (1 / Real.sqrt (Q c l x l)) x := by
  have hQ : 0 < Q c l x l := Q_neck_pos c l hx hl
  have hQne : Q c l x l ≠ 0 := hQ.ne'
  have hsqrt : Real.sqrt (Q c l x l) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hlne : l ≠ 0 := hl.ne'
  have hinner : HasDerivAt (fun C => Q c l C l) l x := by
    have hfun : (fun C => Q c l C l) = fun C => l * C - 8 * c ^ 2 * l ^ 2 := by
      funext C
      rw [Q_neck]
      ring
    rw [hfun]
    have h1 : HasDerivAt (fun C => l * C) (l * 1) x := (hasDerivAt_id x).const_mul l
    have h2 := h1.sub_const (8 * c ^ 2 * l ^ 2)
    simpa using h2
  have hcomp := (Real.hasDerivAt_sqrt hQne).comp x hinner
  have hmul := hcomp.const_mul 2
  have hdiv := hmul.div_const l
  convert hdiv using 1
  field_simp
  ring

/-- 波束の境界値（T₀ = 0、g = 𝟙_[C₁,C₂]、首 b = ℓ）の閉形式 -/
theorem packetZero_eq {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hle : C₁ ≤ C₂)
    (hl : 0 < l) :
    ∫ C in C₁..C₂, 1 / Real.sqrt (Q c l C l)
      = 2 * (Real.sqrt (Q c l C₂ l) - Real.sqrt (Q c l C₁ l)) / l := by
  have hderiv : ∀ x ∈ Set.uIcc C₁ C₂,
      HasDerivAt (fun C => 2 * Real.sqrt (Q c l C l) / l)
        (1 / Real.sqrt (Q c l x l)) x := by
    intro x hx
    have hx1 : 8 * c ^ 2 * l < x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · exact lt_of_lt_of_le hC₁ h.1
      · exact lt_of_lt_of_le hC₁ (le_trans hle h.1)
    exact hasDerivAt_packetAntideriv c l hx1 hl
  have hint : IntervalIntegrable (fun C => 1 / Real.sqrt (Q c l C l)) volume C₁ C₂ := by
    have hQcont : Continuous (fun C => Q c l C l) := by
      have heq : (fun C => Q c l C l) = fun C => l * (C - 8 * c ^ 2 * l) := by
        funext C
        exact Q_neck c l C
      rw [heq]
      fun_prop
    have hcont : ContinuousOn (fun C => 1 / Real.sqrt (Q c l C l))
        (Set.uIcc C₁ C₂) := by
      apply ContinuousOn.div continuousOn_const
      · exact (Real.continuous_sqrt.comp hQcont).continuousOn
      · intro x hx
        have hx1 : 8 * c ^ 2 * l < x := by
          rcases Set.mem_uIcc.mp hx with h | h
          · exact lt_of_lt_of_le hC₁ h.1
          · exact lt_of_lt_of_le hC₁ (le_trans hle h.1)
        exact (Real.sqrt_pos.mpr (Q_neck_pos c l hx1 hl)).ne'
    exact hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- 波束の境界値は正：DeWitt 不適合はこの波束でも成り立つ -/
theorem packetZero_pos {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂)
    (hl : 0 < l) :
    0 < ∫ C in C₁..C₂, 1 / Real.sqrt (Q c l C l) := by
  rw [packetZero_eq c l hC₁ hlt.le hl]
  have hQlt : Q c l C₁ l < Q c l C₂ l := by
    rw [Q_neck, Q_neck]
    apply mul_lt_mul_of_pos_left _ hl
    linarith
  have hsqrt : Real.sqrt (Q c l C₁ l) < Real.sqrt (Q c l C₂ l) :=
    Real.sqrt_lt_sqrt (Q_neck_pos c l hC₁ hl).le hQlt
  apply div_pos _ hl
  linarith

/-- 複素表示：波束 Ψ_f(0, ℓ)（T₀ = 0、g = 𝟙_[C₁,C₂]）は 0 でない -/
theorem packetZero_ne {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂)
    (hl : 0 < l) (κ : ℝ) :
    (∫ C in C₁..C₂, PsiPlus c l κ C 0 l) ≠ 0 := by
  have h1 : (∫ C in C₁..C₂, PsiPlus c l κ C 0 l)
      = ∫ C in C₁..C₂, ((1 / Real.sqrt (Q c l C l) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro C _
    show PsiPlus c l κ C 0 l = ((1 / Real.sqrt (Q c l C l) : ℝ) : ℂ)
    rw [psiPlus_zero]
  rw [h1, intervalIntegral.integral_ofReal, ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (packetZero_pos c l hC₁ hlt hl)

/-- 具体例：c = ℓ = 1、C ∈ [9, 10] の波束の境界値は 2(√2 − 1) -/
theorem packetZero_example :
    ∫ C in (9 : ℝ)..10, 1 / Real.sqrt (Q 1 1 C 1) = 2 * (Real.sqrt 2 - 1) := by
  have h := packetZero_eq 1 1 (by norm_num : 8 * (1 : ℝ) ^ 2 * 1 < 9)
    (by norm_num : (9 : ℝ) ≤ 10) (by norm_num : (0 : ℝ) < 1)
  rw [h]
  have h10 : Q (1 : ℝ) 1 10 1 = 2 := by
    rw [Q_neck]
    norm_num
  have h9 : Q (1 : ℝ) 1 9 1 = 1 := by
    rw [Q_neck]
    norm_num
  rw [h10, h9, Real.sqrt_one]
  ring

end

end CFT.WDWWavePacket
