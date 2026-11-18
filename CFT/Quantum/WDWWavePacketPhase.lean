/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  位相 e^{−iCT₀/hbar} が入る場合（T₀ ≠ 0）の評価（第三段）。

  第一・第二段では T₀ = 0 の波束の境界値 Ψ_f(0, ℓ) = ∫ g(C)/√(Q c l C l) dC > 0
  が示されている。ここでは |T₀| が小さい範囲で非消滅が保たれることを示す：
  |e^{−iθ} − 1| ≤ |θ|（平均値定理。t ↦ e^{−it} の導関数のノルムは 1）から、
  位相つき波束と T₀ = 0 の波束の差は |T₀|/hbar × (明示定数) で抑えられ、
  T₀ = 0 での正値の半分より小さければ逆三角不等式により Ψ_f(T₀) ≠ 0。

  残り：大きな |T₀| に対する評価。位相の振動が積分を打ち消さないことの
  評価（振動積分の相殺の制御）が要り、別段として残る。
-/
import CFT.Quantum.WDWWavePacketGeneral

namespace CFT.WDWWavePacketPhase

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- |e^{−iθ} − 1| ≤ |θ|（平均値定理：t ↦ e^{−it} の導関数のノルムは 1）。-/
theorem norm_exp_neg_I_mul_sub_one_le (θ : ℝ) :
    ‖Complex.exp (-Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (s : ℂ)))
      (-Complex.I * Complex.exp (-Complex.I * (t : ℂ))) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-Complex.I * z))
        (Complex.exp (-Complex.I * (t : ℂ)) * (-Complex.I)) (t : ℂ) := by
      have h2 : HasDerivAt (fun z : ℂ => -Complex.I * z) (-Complex.I) (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)
      exact (Complex.hasDerivAt_exp _).comp (t : ℂ) h2
    have h3 := h1.comp_ofReal (z := t)
    convert h3 using 1
    ring
  have hbound : ∀ t : ℝ, ‖-Complex.I * Complex.exp (-Complex.I * (t : ℂ))‖ ≤ 1 := by
    intro t
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_eq_abs]
    have hrew : -Complex.I * (t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrew]
    exact (Complex.abs_exp_ofReal_mul_I _).le
  rcases le_or_lt 0 θ with hθ | hθ
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s : ℝ => Complex.exp (-Complex.I * (s : ℂ)))
      (f' := fun s : ℝ => -Complex.I * Complex.exp (-Complex.I * (s : ℂ)))
      (a := 0) (b := θ) (C := 1)
      (fun x _ => (hderiv x).hasDerivWithinAt)
      (fun x _ => hbound x) θ ⟨hθ, le_refl θ⟩
    rw [abs_of_nonneg hθ]
    simpa using h
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s : ℝ => Complex.exp (-Complex.I * (s : ℂ)))
      (f' := fun s : ℝ => -Complex.I * Complex.exp (-Complex.I * (s : ℂ)))
      (a := θ) (b := 0) (C := 1)
      (fun x _ => (hderiv x).hasDerivWithinAt)
      (fun x _ => hbound x) 0 ⟨hθ.le, le_refl 0⟩
    rw [norm_sub_rev] at h
    rw [abs_of_neg hθ]
    simpa using h

/-- 位相つき波束の境界値：Ψ_f(T₀, ℓ) = ∫ g(C) e^{−iCT₀/hbar} / √Q dC（複素積分）。-/
def packetPhase (C₁ C₂ T₀ hbar : ℝ) (g : ℝ → ℝ) : ℂ :=
  ∫ C in C₁..C₂, ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
    Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))

/-- T₀ = 0 の位相つき波束は、第二段の実積分に一致する。-/
theorem packetPhase_zero (C₁ C₂ hbar : ℝ) (g : ℝ → ℝ) :
    packetPhase c l C₁ C₂ 0 hbar g
      = ((∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) := by
  unfold packetPhase
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro C _
  simp

/-- 位相つき波束と T₀ = 0 の波束の差の評価（明示定数つき）。-/
theorem packetPhase_sub_norm_le {C₁ C₂ T₀ hbar : ℝ} (hhbar : 0 < hbar)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂))
    (hg_nonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C)
    {G : ℝ} (hG : ∀ C ∈ Set.Icc C₁ C₂, g C ≤ G) :
    ‖packetPhase c l C₁ C₂ T₀ hbar g - packetPhase c l C₁ C₂ 0 hbar g‖
      ≤ |T₀| / hbar * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) := by
  have hC₁pos : 0 < C₁ := by
    have hnn : 0 ≤ 8 * c ^ 2 * l := by positivity
    linarith
  have hGnn : 0 ≤ G :=
    le_trans (hg_nonneg C₁ (Set.left_mem_Icc.mpr hlt.le)) (hG C₁ (Set.left_mem_Icc.mpr hlt.le))
  have hs : 0 < Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) :=
    Real.sqrt_pos.mpr (mul_pos hl (sub_pos.mpr hC₁))
  have hs0 : Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) ≠ 0 := hs.ne'
  have hhbar0 : hbar ≠ 0 := hhbar.ne'
  -- 被積分関数の連続性（任意の T₀ について）
  have hcont : ∀ T : ℝ, ContinuousOn (fun C => ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (C : ℂ) * (T : ℂ) / (hbar : ℂ))) (Set.uIcc C₁ C₂) := by
    intro T
    apply ContinuousOn.mul
    · exact (Complex.continuous_ofReal.continuousOn.comp
        (packetIntegrand_continuousOn c l hC₁ hlt hl hg_cont) (Set.mapsTo_univ _ _))
    · exact (Complex.continuous_exp.continuousOn.comp
        ((((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).div_const _).continuousOn)
        (Set.mapsTo_univ _ _))
  have hInt : ∀ T : ℝ, IntervalIntegrable (fun C => ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (C : ℂ) * (T : ℂ) / (hbar : ℂ))) volume C₁ C₂ :=
    fun T => (hcont T).intervalIntegrable
  -- 差を一つの積分にまとめる
  have hdiff : packetPhase c l C₁ C₂ T₀ hbar g - packetPhase c l C₁ C₂ 0 hbar g
      = ∫ C in C₁..C₂, ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ)) - 1) := by
    unfold packetPhase
    rw [← intervalIntegral.integral_sub (hInt T₀) (hInt 0)]
    apply intervalIntegral.integral_congr
    intro C _
    have hexp0 : Complex.exp (-Complex.I * (C : ℂ) * ((0 : ℝ) : ℂ) / (hbar : ℂ)) = 1 := by simp
    show ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))
        - ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (C : ℂ) * ((0 : ℝ) : ℂ) / (hbar : ℂ))
        = ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ)) - 1)
    rw [hexp0, mul_sub, mul_one]
  -- 点ごとのノルム評価
  have hpt : ∀ C ∈ Set.uIoc C₁ C₂,
      ‖((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ)) - 1)‖
        ≤ (|T₀| / hbar) * (G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) := by
    intro C hC
    have hCmem : C ∈ Set.Icc C₁ C₂ := by
      rw [Set.uIoc_of_le hlt.le] at hC
      exact Set.Ioc_subset_Icc_self hC
    have hC1 : C₁ ≤ C := hCmem.1
    have hC2 : C ≤ C₂ := hCmem.2
    have hCpos : 0 < C := lt_of_lt_of_le hC₁pos hC1
    have hQpos : 0 < Q c l C l := Q_neck_pos c l (lt_of_lt_of_le hC₁ hC1) hl
    have hQmin : l * (C₁ - 8 * c ^ 2 * l) ≤ Q c l C l := by
      rw [Q_neck]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hC1 _) hl.le
    have hsqrt_le : Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) ≤ Real.sqrt (Q c l C l) :=
      Real.sqrt_le_sqrt hQmin
    have hexp : Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))
        = Complex.exp (-Complex.I * ((C * T₀ / hbar : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    have hnorm1 : ‖((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ)‖
        = g C / Real.sqrt (Q c l C l) := by
      rw [Complex.norm_eq_abs, Complex.abs_ofReal]
      exact abs_of_nonneg (div_nonneg (hg_nonneg C hCmem) (Real.sqrt_nonneg _))
    have hCabs : |C * T₀ / hbar| = C * |T₀| / hbar := by
      rw [abs_div, abs_mul, abs_of_pos hCpos, abs_of_pos hhbar]
    have hgQ : g C / Real.sqrt (Q c l C l)
        ≤ G / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) := by
      calc g C / Real.sqrt (Q c l C l)
          ≤ G / Real.sqrt (Q c l C l) :=
            (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hQpos)).mpr (hG C hCmem)
        _ ≤ G / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) :=
            div_le_div_of_nonneg_left hGnn hs hsqrt_le
    calc ‖((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ)) - 1)‖
        = (g C / Real.sqrt (Q c l C l)) *
          ‖Complex.exp (-Complex.I * ((C * T₀ / hbar : ℝ) : ℂ)) - 1‖ := by
          rw [hexp, norm_mul, hnorm1]
      _ ≤ (g C / Real.sqrt (Q c l C l)) * |C * T₀ / hbar| :=
          mul_le_mul_of_nonneg_left (norm_exp_neg_I_mul_sub_one_le _)
            (div_nonneg (hg_nonneg C hCmem) (Real.sqrt_nonneg _))
      _ = (g C / Real.sqrt (Q c l C l)) * (C * |T₀| / hbar) := by rw [hCabs]
      _ ≤ (G / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) * (C₂ * |T₀| / hbar) :=
          mul_le_mul hgQ
            ((div_le_div_iff_of_pos_right hhbar).mpr (mul_le_mul_of_nonneg_right hC2 (abs_nonneg _)))
            (div_nonneg (mul_nonneg hCpos.le (abs_nonneg _)) hhbar.le)
            (div_nonneg hGnn hs.le)
      _ = (|T₀| / hbar) * (G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) := by
          field_simp
          ring
  calc ‖packetPhase c l C₁ C₂ T₀ hbar g - packetPhase c l C₁ C₂ 0 hbar g‖
      = ‖∫ C in C₁..C₂, ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ)) - 1)‖ := by
        rw [hdiff]
    _ ≤ ((|T₀| / hbar) * (G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)))) * |C₂ - C₁| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ = |T₀| / hbar * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) := by
        rw [abs_of_pos (sub_pos.mpr hlt)]
        field_simp
        ring

/-- 位相つき波束の非消滅：|T₀| が十分小さい範囲で。-/
theorem packetPhase_ne_of_small {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁)
    (hlt : C₁ < C₂) (hl : 0 < l) {hbar : ℝ} (hhbar : 0 < hbar)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂))
    (hg_nonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo C₁ C₂) (hgpos : 0 < g x₀)
    {G : ℝ} (hG : ∀ C ∈ Set.Icc C₁ C₂, g C ≤ G) :
    ∃ δ > 0, ∀ T₀ : ℝ, |T₀| < δ →
      packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  have hP₀pos : 0 < ∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l) :=
    packetGen_pos c l hC₁ hlt hl hg_cont hg_nonneg hx₀ hgpos
  have hC₁pos : 0 < C₁ := by
    have hnn : 0 ≤ 8 * c ^ 2 * l := by positivity
    linarith
  have hC₂pos : 0 < C₂ := lt_trans hC₁pos hlt
  have hGpos : 0 < G := lt_of_lt_of_le hgpos (hG x₀ ⟨hx₀.1.le, hx₀.2.le⟩)
  have hs : 0 < Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) :=
    Real.sqrt_pos.mpr (mul_pos hl (sub_pos.mpr hC₁))
  have hB : 0 < (C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)) :=
    div_pos (mul_pos (mul_pos (sub_pos.mpr hlt) hGpos) hC₂pos) hs
  refine ⟨hbar * (∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l)) /
    (2 * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)))),
    div_pos (mul_pos hhbar hP₀pos) (mul_pos two_pos hB), ?_⟩
  intro T₀ hT₀
  have hdiff : ‖packetPhase c l C₁ C₂ T₀ hbar g - packetPhase c l C₁ C₂ 0 hbar g‖
      ≤ |T₀| / hbar * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) :=
    packetPhase_sub_norm_le c l hhbar hC₁ hlt hl hg_cont hg_nonneg hG
  have hsmall : ‖packetPhase c l C₁ C₂ T₀ hbar g - packetPhase c l C₁ C₂ 0 hbar g‖
      < (∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l)) / 2 := by
    have h1 : |T₀| / hbar * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)))
        < (∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l)) / 2 := by
      rw [div_mul_eq_mul_div,
        div_lt_div_iff₀ hhbar (by norm_num : (0 : ℝ) < 2)]
      have hB2 : (0 : ℝ) < 2 * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) :=
        mul_pos two_pos hB
      have h2 : |T₀| * (2 * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))))
          < (∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l)) * hbar := by
        rw [← lt_div_iff₀ hB2]
        have h3 : (∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l)) * hbar /
            (2 * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))))
            = hbar * (∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l)) /
            (2 * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)))) := by
          ring
        rw [h3]
        exact hT₀
      have h4 : |T₀| * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l))) * 2
          = |T₀| * (2 * ((C₂ - C₁) * G * C₂ / Real.sqrt (l * (C₁ - 8 * c ^ 2 * l)))) := by
        ring
      rw [h4]
      exact h2
    exact lt_of_le_of_lt hdiff h1
  have hzero : packetPhase c l C₁ C₂ 0 hbar g
      = ((∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) :=
    packetPhase_zero c l C₁ C₂ hbar g
  have hnorm0 : ‖packetPhase c l C₁ C₂ 0 hbar g‖
      = ∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l) := by
    rw [hzero, Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_pos hP₀pos]
  have htri : ‖packetPhase c l C₁ C₂ 0 hbar g‖
      ≤ ‖packetPhase c l C₁ C₂ T₀ hbar g‖ +
        ‖packetPhase c l C₁ C₂ T₀ hbar g - packetPhase c l C₁ C₂ 0 hbar g‖ := by
    conv_lhs => rw [← sub_sub_self (packetPhase c l C₁ C₂ T₀ hbar g)
      (packetPhase c l C₁ C₂ 0 hbar g)]
    exact norm_sub_le _ _
  intro hcon
  have hnormT : ‖packetPhase c l C₁ C₂ T₀ hbar g‖ = 0 := by
    rw [hcon]
    simp
  have hpos : 0 < ‖packetPhase c l C₁ C₂ T₀ hbar g‖ := by
    rw [hnorm0] at htri
    linarith
  rw [hnormT] at hpos
  exact lt_irrefl 0 hpos

/-- 具体例：c = ℓ = 1、g(C) = C − 8、C ∈ [9, 10] の波束は、|T₀| が十分
    小さい範囲で 0 でない。-/
theorem packetPhase_example :
    ∃ δ > 0, ∀ T₀ : ℝ, |T₀| < δ →
      packetPhase 1 1 9 10 T₀ 1 (fun C => C - 8) ≠ 0 := by
  exact packetPhase_ne_of_small (c := 1) (l := 1) (hbar := 1) (G := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (continuous_id.sub continuous_const).continuousOn
    (fun C hC => by linarith [hC.1])
    (show (9.5 : ℝ) ∈ Set.Ioo (9 : ℝ) 10 by norm_num)
    (by norm_num)
    (fun C hC => by linarith [hC.2])

end

end CFT.WDWWavePacketPhase
