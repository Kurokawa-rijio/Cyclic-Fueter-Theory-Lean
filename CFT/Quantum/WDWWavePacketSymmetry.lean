/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第四段：T₀ の符号対称性）。

  第三段では |T₀| が小さい範囲で非消滅が示されている。ここでは位相つき波束の
  T₀ → −T₀ 対称性を示す：g が実関数なら Ψ_f(−T₀) = conj (Ψ_f(T₀))、よって
  ‖Ψ_f(−T₀)‖ = ‖Ψ_f(T₀)‖ で、非消滅の範囲は T₀ の符号によらない。
  すなわち大きな |T₀| の評価は T₀ ≥ 0 に帰着する。対称性そのものは g の連続性や
  Q の正値性を要しない（区間積分と共役の交換による）。

  残り：大きな |T₀|（T₀ ≥ 0）に対する評価。位相の振動が積分を打ち消さないことの
  評価（振動積分の相殺の制御）が要り、別段として残る。
-/
import CFT.Quantum.WDWWavePacketPhase

namespace CFT.WDWWavePacketSymm

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 位相つき波束の被積分関数は区間上で連続（第三段の `hcont` と同じ議論。
    後の段の評価で使うため、対称性の証明そのものとは別に置く）。-/
theorem packetPhase_integrand_continuousOn {C₁ C₂ T₀ hbar : ℝ}
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂)) :
    ContinuousOn (fun C => ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))) (Set.uIcc C₁ C₂) := by
  apply ContinuousOn.mul
  · exact (Complex.continuous_ofReal.continuousOn.comp
      (packetIntegrand_continuousOn c l hC₁ hlt hl hg_cont) (Set.mapsTo_univ _ _))
  · exact (Complex.continuous_exp.continuousOn.comp
      ((((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).div_const _).continuousOn)
      (Set.mapsTo_univ _ _))

/-- 区間積分と複素共役は交換する。-/
theorem intervalIntegral_conj {C₁ C₂ : ℝ} (hlt : C₁ < C₂) {f : ℝ → ℂ} :
    (∫ C in C₁..C₂, starRingEnd ℂ (f C)) = starRingEnd ℂ (∫ C in C₁..C₂, f C) := by
  rw [intervalIntegral.integral_of_le hlt.le, intervalIntegral.integral_of_le hlt.le]
  exact integral_conj

/-- 被積分関数の T₀ → −T₀ は共役に対応する（点ごと）。-/
theorem packetPhase_integrand_neg_conj (C T₀ hbar : ℝ) (g : ℝ → ℝ) :
    ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (C : ℂ) * ((-T₀ : ℝ) : ℂ) / (hbar : ℂ))
      = starRingEnd ℂ (((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))) := by
  have hexp : -Complex.I * (C : ℂ) * ((-T₀ : ℝ) : ℂ) / (hbar : ℂ)
      = starRingEnd ℂ (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ)) := by
    have h1 : starRingEnd ℂ (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))
        = Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ) := by
      simp [map_div₀, Complex.conj_I]
    rw [h1]
    push_cast
    ring
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hexp]

/-- 位相つき波束の T₀ → −T₀ 対称性：Ψ_f(−T₀) = conj (Ψ_f(T₀))（g は実関数）。-/
theorem packetPhase_neg_conj {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    {g : ℝ → ℝ} :
    packetPhase c l C₁ C₂ (-T₀) hbar g
      = starRingEnd ℂ (packetPhase c l C₁ C₂ T₀ hbar g) := by
  unfold packetPhase
  rw [← intervalIntegral_conj hlt]
  apply intervalIntegral.integral_congr
  intro C _
  exact packetPhase_integrand_neg_conj c l C T₀ hbar g

/-- 対称性のノルム版：‖Ψ_f(−T₀)‖ = ‖Ψ_f(T₀)‖。-/
theorem packetPhase_neg_norm {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    {g : ℝ → ℝ} :
    ‖packetPhase c l C₁ C₂ (-T₀) hbar g‖ = ‖packetPhase c l C₁ C₂ T₀ hbar g‖ := by
  rw [packetPhase_neg_conj c l hlt]
  exact RCLike.norm_conj _

/-- 非消滅の範囲は T₀ の符号によらない。-/
theorem packetPhase_ne_iff_neg {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    {g : ℝ → ℝ} :
    packetPhase c l C₁ C₂ (-T₀) hbar g ≠ 0 ↔
      packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  rw [packetPhase_neg_conj c l hlt]
  simp only [ne_eq, starRingEnd_apply, star_eq_zero]

/-- 大きな |T₀| の非消滅は T₀ ≥ 0 の場合に帰着する：T₀ での非消滅は −T₀ でも成り立つ。-/
theorem packetPhase_ne_neg_of_ne {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    {g : ℝ → ℝ} (h : packetPhase c l C₁ C₂ T₀ hbar g ≠ 0) :
    packetPhase c l C₁ C₂ (-T₀) hbar g ≠ 0 :=
  (packetPhase_ne_iff_neg c l hlt).mpr h

/-- 実部は T₀ の符号によらない。-/
theorem packetPhase_neg_re {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    {g : ℝ → ℝ} :
    (packetPhase c l C₁ C₂ (-T₀) hbar g).re
      = (packetPhase c l C₁ C₂ T₀ hbar g).re := by
  rw [packetPhase_neg_conj c l hlt]
  exact Complex.conj_re _

/-- 虚部は T₀ の符号で反転する。-/
theorem packetPhase_neg_im {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    {g : ℝ → ℝ} :
    (packetPhase c l C₁ C₂ (-T₀) hbar g).im
      = -(packetPhase c l C₁ C₂ T₀ hbar g).im := by
  rw [packetPhase_neg_conj c l hlt]
  exact Complex.conj_im _

/-- 具体例：c = ℓ = 1、g(C) = C − 8、C ∈ [9, 10] の波束の対称性。-/
theorem packetPhase_example_neg_conj (T₀ : ℝ) :
    packetPhase 1 1 9 10 (-T₀) 1 (fun C => C - 8)
      = starRingEnd ℂ (packetPhase 1 1 9 10 T₀ 1 (fun C => C - 8)) := by
  exact packetPhase_neg_conj (c := 1) (l := 1) (by norm_num)

end

end CFT.WDWWavePacketSymm
