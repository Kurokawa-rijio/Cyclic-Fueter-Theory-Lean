/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第十八段）。

  第十七段では多項式重みに対する因数分解を等比数列の和で与えた。ここでは一般の
  C¹ 重み w に対する因数分解を証明する：差商の因子
  u(C) = (w(C) − w(C₁+C₂−C)) / (2(C − m))（m = (C₁+C₂)/2）は、中点では
  deriv w m を値として取ることで連続関数に拡張できる。鍵は平均値定理で、
  C ≠ m なら u(C) = deriv w ξ となる ξ が C とその鏡像 2m−C の間に取れ、
  |ξ − m| < |C − m| であること（したがって deriv w の連続性から u の中点での
  連続性が従う）。単調な重みでは u ≥ 0、区間上で狭義単調な重みでは u は中点以外
  の点で正になる。第十六段と組み合わせると、全体で単調・区間上で狭義単調な
  C¹ 重みでは小さな θ > 0 でサイン積分が正になり、位相つき波束は 0 にならない。
  具体例として w(C) = exp C を与える。
  なお第十六段の仮定 hu_nonneg は全体で課されているため、ここでは単調性を
  全体で仮定している。区間上のみの単調性への拡張は、第十六段の局所化（区間上
  のみの仮定への書き換え）とあわせて次の段に残る。

  残り：区間上のみ単調な重みへの拡張（第十六段の局所化）、およびサイン積分の
  零点の具体的な構造（大きな θ での符号変化、零点の列挙など）。
-/
import CFT.Quantum.WDWWavePacketSineZero

namespace CFT.WDWWavePacketC1Weight

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketDecayExplicit CFT.WDWWavePacketSymmW CFT.WDWWavePacketAsymW
  CFT.WDWWavePacketSineZero
  MeasureTheory intervalIntegral

open scoped Topology

noncomputable section

variable (c l : ℝ)

/-- 差商の因子：C¹ 重み w に対し、反対称部分を (C − m)·u(C) と書く因子。
    中点 m = (C₁+C₂)/2 では微分係数を値として取る（平均値定理による
    連続拡張）。-/
noncomputable def antiQuot (w : ℝ → ℝ) (C₁ C₂ : ℝ) : ℝ → ℝ := fun C =>
  if C = (C₁ + C₂) / 2 then deriv w ((C₁ + C₂) / 2)
  else (w C - w (C₁ + C₂ - C)) / (2 * (C - (C₁ + C₂) / 2))

/-- 中点での値は微分係数である（定義）。-/
theorem antiQuot_mid (w : ℝ → ℝ) (C₁ C₂ : ℝ) :
    antiQuot w C₁ C₂ ((C₁ + C₂) / 2) = deriv w ((C₁ + C₂) / 2) := by
  show (if (C₁ + C₂) / 2 = (C₁ + C₂) / 2 then deriv w ((C₁ + C₂) / 2)
      else (w ((C₁ + C₂) / 2) - w (C₁ + C₂ - (C₁ + C₂) / 2))
        / (2 * ((C₁ + C₂) / 2 - (C₁ + C₂) / 2)))
    = deriv w ((C₁ + C₂) / 2)
  rw [if_pos rfl]

/-- 中点以外での値は差商の形である（定義）。-/
theorem antiQuot_eq_of_ne {w : ℝ → ℝ} {C₁ C₂ C : ℝ}
    (hCm : C ≠ (C₁ + C₂) / 2) :
    antiQuot w C₁ C₂ C
      = (w C - w (C₁ + C₂ - C)) / (2 * (C - (C₁ + C₂) / 2)) := by
  show (if C = (C₁ + C₂) / 2 then deriv w ((C₁ + C₂) / 2)
      else (w C - w (C₁ + C₂ - C)) / (2 * (C - (C₁ + C₂) / 2)))
    = (w C - w (C₁ + C₂ - C)) / (2 * (C - (C₁ + C₂) / 2))
  rw [if_neg hCm]

/-- 反対称部分は (C − m)·antiQuot と因数分解できる。-/
theorem antiPart_eq_mul_antiQuot (w : ℝ → ℝ) (C₁ C₂ C : ℝ) :
    antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * antiQuot w C₁ C₂ C := by
  by_cases hCm : C = (C₁ + C₂) / 2
  · subst hCm
    have h1 : C₁ + C₂ - (C₁ + C₂) / 2 = (C₁ + C₂) / 2 := by ring
    show (w ((C₁ + C₂) / 2) - w (C₁ + C₂ - (C₁ + C₂) / 2)) / 2
        = ((C₁ + C₂) / 2 - (C₁ + C₂) / 2) * antiQuot w C₁ C₂ ((C₁ + C₂) / 2)
    rw [h1]
    simp
  · show (w C - w (C₁ + C₂ - C)) / 2
        = (C - (C₁ + C₂) / 2) * antiQuot w C₁ C₂ C
    rw [antiQuot_eq_of_ne hCm, mul_div_assoc',
      show (2:ℝ) * (C - (C₁ + C₂) / 2) = (C - (C₁ + C₂) / 2) * 2 by ring,
      mul_div_mul_left _ _ (sub_ne_zero.mpr hCm)]

/-- 平均値定理：C ≠ m なら、u(C) = deriv w ξ となる ξ が C とその鏡像の
    間に取れ、ξ は m により近い。-/
theorem exists_deriv_eq_antiQuot {w : ℝ → ℝ} (hdiff : Differentiable ℝ w)
    {C₁ C₂ C : ℝ} (hCm : C ≠ (C₁ + C₂) / 2) :
    ∃ ξ, |ξ - (C₁ + C₂) / 2| < |C - (C₁ + C₂) / 2|
      ∧ antiQuot w C₁ C₂ C = deriv w ξ := by
  have hcont : Continuous w := hdiff.continuous
  rcases lt_or_gt_of_ne hCm with hlt | hgt
  · have hab : C < C₁ + C₂ - C := by linarith
    obtain ⟨ξ, hξmem, hξeq⟩ := exists_deriv_eq_slope w hab
      hcont.continuousOn hdiff.differentiableOn
    obtain ⟨hξ1, hξ2⟩ := hξmem
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_neg (show C - (C₁ + C₂) / 2 < 0 by linarith), abs_lt]
      constructor <;> linarith
    · rw [antiQuot_eq_of_ne hCm, hξeq, div_eq_div_iff
        (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hCm))
        (show C₁ + C₂ - C - C ≠ 0 by
          have h2 : C₁ + C₂ - C - C = 2 * ((C₁ + C₂) / 2 - C) := by ring
          rw [h2]
          exact mul_ne_zero (by norm_num) (by linarith))]
      ring
  · have hab : C₁ + C₂ - C < C := by linarith
    obtain ⟨ξ, hξmem, hξeq⟩ := exists_deriv_eq_slope w hab
      hcont.continuousOn hdiff.differentiableOn
    obtain ⟨hξ1, hξ2⟩ := hξmem
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_pos (show (0:ℝ) < C - (C₁ + C₂) / 2 by linarith), abs_lt]
      constructor <;> linarith
    · rw [antiQuot_eq_of_ne hCm, hξeq, div_eq_div_iff
        (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hCm))
        (show C - (C₁ + C₂ - C) ≠ 0 by
          have h2 : C - (C₁ + C₂ - C) = 2 * (C - (C₁ + C₂) / 2) := by ring
          rw [h2]
          exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hCm))]
      ring

/-- 差商の因子は中点で連続である（平均値定理と deriv の連続性による）。-/
theorem continuousAt_antiQuot_mid {w : ℝ → ℝ} (hdiff : Differentiable ℝ w)
    (hderiv : Continuous (deriv w)) (C₁ C₂ : ℝ) :
    ContinuousAt (antiQuot w C₁ C₂) ((C₁ + C₂) / 2) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hcont : ContinuousAt (deriv w) ((C₁ + C₂) / 2) := hderiv.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδball⟩ := hcont ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hxeq : x = (C₁ + C₂) / 2
  · subst hxeq
    rw [dist_self]
    exact hε
  · obtain ⟨ξ, hξbound, hξeq⟩ := exists_deriv_eq_antiQuot hdiff hxeq
    have hξδ : dist ξ ((C₁ + C₂) / 2) < δ := by
      rw [Real.dist_eq] at hx ⊢
      exact lt_trans hξbound hx
    have hε' := hδball hξδ
    rw [Real.dist_eq] at hε' ⊢
    rw [hξeq, antiQuot_mid]
    exact hε'

/-- 差商の因子は中点以外でも連続である（連続関数の商）。-/
theorem continuousAt_antiQuot_of_ne {w : ℝ → ℝ} (hdiff : Differentiable ℝ w)
    {C₁ C₂ C : ℝ} (hCm : C ≠ (C₁ + C₂) / 2) :
    ContinuousAt (antiQuot w C₁ C₂) C := by
  have hw : Continuous w := hdiff.continuous
  have hnum : ContinuousAt (fun x => w x - w (C₁ + C₂ - x)) C :=
    hw.continuousAt.sub
      (hw.continuousAt.comp ((continuous_const.sub continuous_id).continuousAt))
  have hden : ContinuousAt (fun x => (2:ℝ) * (x - (C₁ + C₂) / 2)) C :=
    (continuous_const.mul (continuous_id.sub continuous_const)).continuousAt
  have hden_ne : (2:ℝ) * (C - (C₁ + C₂) / 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hCm)
  have hquot : ContinuousAt
      (fun x => (w x - w (C₁ + C₂ - x)) / (2 * (x - (C₁ + C₂) / 2))) C :=
    hnum.div hden hden_ne
  apply hquot.congr
  filter_upwards [eventually_ne_nhds hCm] with x hx
  rw [antiQuot_eq_of_ne hx]

/-- 差商の因子は区間上で連続である。-/
theorem continuousOn_antiQuot {w : ℝ → ℝ} (hdiff : Differentiable ℝ w)
    (hderiv : Continuous (deriv w)) (C₁ C₂ : ℝ) :
    ContinuousOn (antiQuot w C₁ C₂) (Set.uIcc C₁ C₂) := by
  intro C hC
  by_cases hCm : C = (C₁ + C₂) / 2
  · subst hCm
    exact (continuousAt_antiQuot_mid hdiff hderiv C₁ C₂).continuousWithinAt
  · exact (continuousAt_antiQuot_of_ne hdiff hCm).continuousWithinAt

/-- 鏡像 C ↦ C₁+C₂−C は区間を保つ。-/
theorem mem_uIcc_reflect {C₁ C₂ C : ℝ} (hC : C ∈ Set.uIcc C₁ C₂) :
    C₁ + C₂ - C ∈ Set.uIcc C₁ C₂ := by
  rw [Set.mem_uIcc] at hC ⊢
  rcases hC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- 単調な重みでは、中点以外での差商の因子は非負である。-/
theorem antiQuot_nonneg_of_ne {w : ℝ → ℝ} {C₁ C₂ C : ℝ}
    (hmono : Monotone w) (hCm : C ≠ (C₁ + C₂) / 2) :
    0 ≤ antiQuot w C₁ C₂ C := by
  rw [antiQuot_eq_of_ne hCm]
  rcases lt_or_gt_of_ne hCm with hlt | hgt
  · have hle : w C ≤ w (C₁ + C₂ - C) := hmono (by linarith)
    rw [← neg_div_neg_eq]
    exact div_nonneg (by linarith) (by linarith)
  · have hle : w (C₁ + C₂ - C) ≤ w C := hmono (by linarith)
    exact div_nonneg (by linarith) (by linarith)

/-- 単調な C¹ 重みでは、差商の因子は全体で非負である（中点では連続性による極限）。-/
theorem antiQuot_nonneg_of_monotone {w : ℝ → ℝ} {C₁ C₂ : ℝ} (hlt : C₁ < C₂)
    (hdiff : Differentiable ℝ w) (hderiv : Continuous (deriv w))
    (hmono : Monotone w) (C : ℝ) : 0 ≤ antiQuot w C₁ C₂ C := by
  by_cases hCm : C = (C₁ + C₂) / 2
  · subst hCm
    have hcont : ContinuousAt (antiQuot w C₁ C₂) ((C₁ + C₂) / 2) :=
      continuousAt_antiQuot_mid hdiff hderiv C₁ C₂
    have htend : Filter.Tendsto (antiQuot w C₁ C₂) (𝓝[≠] ((C₁ + C₂) / 2))
        (𝓝 (antiQuot w C₁ C₂ ((C₁ + C₂) / 2))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ x in 𝓝[≠] ((C₁ + C₂) / 2), 0 ≤ antiQuot w C₁ C₂ x := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioo_mem_nhds (show C₁ < (C₁ + C₂) / 2 by linarith)
        (show (C₁ + C₂) / 2 < C₂ by linarith)] with x _ hxne
      have hxne' : x ≠ (C₁ + C₂) / 2 := hxne
      exact antiQuot_nonneg_of_ne hmono hxne'
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
  · exact antiQuot_nonneg_of_ne hmono hCm

/-- 区間上で狭義単調な重みでは、中点以外の点での差商の因子は正である。-/
theorem antiQuot_pos_of_strictMonoOn {w : ℝ → ℝ} {C₁ C₂ C : ℝ}
    (hmono : StrictMonoOn w (Set.uIcc C₁ C₂)) (hC : C ∈ Set.uIcc C₁ C₂)
    (hCm : C ≠ (C₁ + C₂) / 2) : 0 < antiQuot w C₁ C₂ C := by
  have hC' := mem_uIcc_reflect hC
  rw [antiQuot_eq_of_ne hCm]
  rcases lt_or_gt_of_ne hCm with hlt | hgt
  · have hlt' : w C < w (C₁ + C₂ - C) := hmono hC hC' (by linarith)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · have hlt' : w (C₁ + C₂ - C) < w C := hmono hC' hC (by linarith)
    exact div_pos (by linarith) (by linarith)

/-- 全体で単調・区間上で狭義単調な C¹ 重みでは、小さな θ > 0 でサイン積分は正である。-/
theorem integral_sin_antiQuot_pos {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (w : ℝ → ℝ)
    (hdiff : Differentiable ℝ w) (hderiv : Continuous (deriv w))
    (hmono : Monotone w) (hstrict : StrictMonoOn w (Set.uIcc C₁ C₂)) :
    0 < ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  apply integral_sin_antiPart_pos hlt hθ0 hθ w hdiff.continuous.continuousOn
    (u := antiQuot w C₁ C₂)
    (hu_cont := continuousOn_antiQuot hdiff hderiv C₁ C₂)
    (hu_nonneg := fun C => antiQuot_nonneg_of_monotone hlt hdiff hderiv hmono C)
    (hfact := fun C => antiPart_eq_mul_antiQuot w C₁ C₂ C)
    (c₀ := (C₁ + 3 * C₂) / 4)
    (hc₀ := ⟨by linarith, by linarith⟩)
    (hu0 := antiQuot_pos_of_strictMonoOn hstrict
      (by rw [Set.uIcc_of_le hlt.le]; constructor <;> linarith)
      (by intro h; linarith))

/-- 全体で単調・区間上で狭義単調な C¹ 重みでは、0 < T₀ < 2πħ/(C₂−C₁) の範囲で
    位相つき波束は 0 にならない。-/
theorem packetPhase_ne_of_small_pos_of_monotone {C₁ C₂ T₀ hbar : ℝ}
    (hhbar : 0 < hbar) (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hdiff : Differentiable ℝ w) (hderiv : Continuous (deriv w))
    (hmono : Monotone w) (hstrict : StrictMonoOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi * hbar / (C₂ - C₁)) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  apply packetPhase_ne_of_small_pos (c := c) (l := l) hhbar hC₁ hlt hl
    (w := w) (hw_cont := hdiff.continuous.continuousOn) (g := g) (hg := hg)
    (u := antiQuot w C₁ C₂)
    (hu_cont := continuousOn_antiQuot hdiff hderiv C₁ C₂)
    (hu_nonneg := fun C => antiQuot_nonneg_of_monotone hlt hdiff hderiv hmono C)
    (hfact := fun C => antiPart_eq_mul_antiQuot w C₁ C₂ C)
    (c₀ := (C₁ + 3 * C₂) / 4)
    (hc₀ := ⟨by linarith, by linarith⟩)
    (hu0 := antiQuot_pos_of_strictMonoOn hstrict
      (by rw [Set.uIcc_of_le hlt.le]; constructor <;> linarith)
      (by intro h; linarith))
    hT0 hT

/-- 具体例：c = ℓ = 1、C ∈ [9, 10]、指数重み g(C) = e^C·√Q では、0 < T₀ < 2π の
    範囲で位相つき波束は 0 にならない。-/
theorem packetPhase_ne_exp_example {T₀ : ℝ} (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi) :
    packetPhase 1 1 9 10 T₀ 1 (fun C => Real.exp C * Real.sqrt (Q 1 1 C 1)) ≠ 0 := by
  refine packetPhase_ne_of_small_pos_of_monotone (c := 1) (l := 1) one_pos (by norm_num)
    (by norm_num) one_pos (w := Real.exp) (hdiff := Real.differentiable_exp)
    (hderiv := ?_) (hmono := Real.exp_strictMono.monotone)
    (hstrict := Real.exp_strictMono.strictMonoOn _)
    (g := fun C => Real.exp C * Real.sqrt (Q 1 1 C 1)) (hg := fun C _ => rfl)
    hT0 ?_
  · rw [Real.deriv_exp]
    exact Real.continuous_exp
  · have heq : (2 : ℝ) * Real.pi * (1 : ℝ) / ((10 : ℝ) - 9) = 2 * Real.pi := by
      rw [show ((10 : ℝ) - 9) = 1 by norm_num, div_one, mul_one]
    rw [heq]
    exact hT

end

end CFT.WDWWavePacketC1Weight
