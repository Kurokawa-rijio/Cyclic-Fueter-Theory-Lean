/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第十九段）。

  第十六段では反対称部分の因数分解 w_anti(C) = (C − m)·u(C) に対する
  サイン積分の正値性を、u の非負性と因数分解を全体（すべての C）で仮定して
  示した。第十八段では C¹ 重みの全体での単調性から u = antiQuot の非負性を
  導いた。ここでは第十六段を区間上に局所化する：u ≥ 0 と因数分解を区間
  [C₁, C₂] 上でのみ仮定すれば十分であり、対応する波束の非消滅も区間上の
  仮定だけで得られる。したがって C¹ 重みが区間上で単調（全体では単調で
  なくてよい）・区間上で狭義単調なら、小さな T₀ > 0 で位相つき波束は 0 に
  ならない。具体例として、区間 [9, 10] 上では増加するが全体では単調でない
  二次重み w(C) = −(C − 10)² を与える。

  残り：サイン積分の零点の具体的な構造（大きな θ での符号変化、零点の列挙など）。
-/
import CFT.Quantum.WDWWavePacketC1Weight

namespace CFT.WDWWavePacketIntervalMono

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketDecayExplicit CFT.WDWWavePacketSymmW CFT.WDWWavePacketAsymW
  CFT.WDWWavePacketSineZero CFT.WDWWavePacketC1Weight
  MeasureTheory intervalIntegral

open scoped Topology

noncomputable section

variable (c l : ℝ)

/-- 区間上で単調な重みでは、中点以外での差商の因子は区間上で非負である。-/
theorem antiQuot_nonneg_of_ne_of_monotoneOn {w : ℝ → ℝ} {C₁ C₂ C : ℝ}
    (hmono : MonotoneOn w (Set.uIcc C₁ C₂)) (hC : C ∈ Set.uIcc C₁ C₂)
    (hCm : C ≠ (C₁ + C₂) / 2) :
    0 ≤ antiQuot w C₁ C₂ C := by
  have hC' : C₁ + C₂ - C ∈ Set.uIcc C₁ C₂ := mem_uIcc_reflect hC
  rw [antiQuot_eq_of_ne hCm]
  rcases lt_or_gt_of_ne hCm with hlt | hgt
  · have hle : w C ≤ w (C₁ + C₂ - C) := hmono hC hC' (by linarith)
    rw [← neg_div_neg_eq]
    exact div_nonneg (by linarith) (by linarith)
  · have hle : w (C₁ + C₂ - C) ≤ w C := hmono hC' hC (by linarith)
    exact div_nonneg (by linarith) (by linarith)

/-- 区間上で単調な C¹ 重みでは、差商の因子は区間上で非負である
    （中点では連続性による極限）。-/
theorem antiQuot_nonneg_of_monotoneOn {w : ℝ → ℝ} {C₁ C₂ : ℝ} (hlt : C₁ < C₂)
    (hdiff : Differentiable ℝ w) (hderiv : Continuous (deriv w))
    (hmono : MonotoneOn w (Set.uIcc C₁ C₂)) (C : ℝ) (hC : C ∈ Set.uIcc C₁ C₂) :
    0 ≤ antiQuot w C₁ C₂ C := by
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
        (show (C₁ + C₂) / 2 < C₂ by linarith)] with x hxmem hxne
      exact antiQuot_nonneg_of_ne_of_monotoneOn hmono
        (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hxmem)) hxne
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
  · exact antiQuot_nonneg_of_ne_of_monotoneOn hmono hC hCm

/-- 第十六段の局所化：反対称部分が (C−m)·u(C)（u は区間上で連続・非負で、
    区間内のどこかで正）と書ける場合、小さな θ > 0 ではサイン積分は正である。
    u ≥ 0 と因数分解は区間上でのみ仮定する。-/
theorem integral_sin_antiPart_pos_of_nonnegOn {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂)
    (hθ0 : 0 < θ) (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonneg : ∀ C ∈ Set.uIcc C₁ C₂, 0 ≤ u C)
    (hfact : ∀ C ∈ Set.uIcc C₁ C₂,
      antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : 0 < u c₀) :
    0 < ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  obtain ⟨c₁, hc₁, hcm, hu1⟩ := exists_pos_point_ne_mid hlt hu_cont hc₀ hu0
  apply integral_pos_of_continuous_nonneg _ _ hc₁ _
  · exact (antiPart_continuousOn hw_cont).mul ((Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)
  · intro C hC
    rw [hfact C (Set.Icc_subset_uIcc hC)]
    have hmul := mul_sin_nonneg hlt hθ0 hθ.le (Set.Icc_subset_uIcc hC)
    have h1 : (C - (C₁ + C₂) / 2) * u C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
        = u C * ((C - (C₁ + C₂) / 2) * Real.sin ((C - (C₁ + C₂) / 2) * θ)) := by ring
    rw [h1]
    exact mul_nonneg (hu_nonneg C (Set.Icc_subset_uIcc hC)) hmul
  · rw [hfact c₁ (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hc₁))]
    have hmul := mul_sin_pos hlt hθ0 hθ hc₁ hcm
    have h1 : (c₁ - (C₁ + C₂) / 2) * u c₁ * Real.sin ((c₁ - (C₁ + C₂) / 2) * θ)
        = u c₁ * ((c₁ - (C₁ + C₂) / 2) * Real.sin ((c₁ - (C₁ + C₂) / 2) * θ)) := by ring
    rw [h1]
    exact mul_pos hu1 hmul

/-- 第十六段の局所化（符号反転版）：u が区間上で非正で、区間内のどこかで負なら、
    小さな θ > 0 でサイン積分は負である。-/
theorem integral_sin_antiPart_neg_of_nonposOn {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂)
    (hθ0 : 0 < θ) (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonpos : ∀ C ∈ Set.uIcc C₁ C₂, u C ≤ 0)
    (hfact : ∀ C ∈ Set.uIcc C₁ C₂,
      antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : u c₀ < 0) :
    ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) < 0 := by
  have hpos : 0 < ∫ C in C₁..C₂,
      antiPart (-w) C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) :=
    integral_sin_antiPart_pos_of_nonnegOn hlt hθ0 hθ (-w) hw_cont.neg
      (hu_cont := hu_cont.neg)
      (hu_nonneg := fun C hC => neg_nonneg.mpr (hu_nonpos C hC))
      (hfact := fun C hC => by
        simp only [antiPart_neg, hfact C hC, Pi.neg_apply]
        ring)
      (hc₀ := hc₀) (hu0 := neg_pos.mpr hu0)
  have hneg : ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
      = -∫ C in C₁..C₂, antiPart (-w) C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro C _
    show antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
        = -(antiPart (-w) C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ))
    rw [antiPart_neg]
    ring
  rw [hneg]
  exact neg_neg_of_pos hpos

/-- 区間上の仮定だけで、反対称部分が (C−m)·u(C)（u ≥ 0）の形の重みでは、
    0 < T₀ < 2πħ/(C₂−C₁) の範囲で位相つき波束は 0 にならない。-/
theorem packetPhase_ne_of_small_pos_of_nonnegOn {C₁ C₂ T₀ hbar : ℝ}
    (hhbar : 0 < hbar) (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonneg : ∀ C ∈ Set.uIcc C₁ C₂, 0 ≤ u C)
    (hfact : ∀ C ∈ Set.uIcc C₁ C₂,
      antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : 0 < u c₀)
    (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi * hbar / (C₂ - C₁)) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  have hL : 0 < C₂ - C₁ := sub_pos.mpr hlt
  have hT' : T₀ * (C₂ - C₁) < 2 * Real.pi * hbar := (lt_div_iff₀ hL).mp hT
  have hθ0 : 0 < T₀ / hbar := div_pos hT0 hhbar
  have hθ : T₀ / hbar < 2 * Real.pi / (C₂ - C₁) := by
    rw [div_lt_iff₀ hhbar, div_mul_eq_mul_div, lt_div_iff₀ hL]
    exact hT'
  have hsin := integral_sin_antiPart_pos_of_nonnegOn hlt hθ0 hθ w hw_cont hu_cont
    hu_nonneg hfact hc₀ hu0
  exact packetPhase_ne_of_sin_integral_ne c l hhbar.ne' hC₁ hlt hl hw_cont g hg hsin.ne'

/-- 区間上の仮定だけで、反対称部分が (C−m)·u(C)（u ≤ 0）の形の重みでは、
    0 < T₀ < 2πħ/(C₂−C₁) の範囲で位相つき波束は 0 にならない。-/
theorem packetPhase_ne_of_small_neg_of_nonposOn {C₁ C₂ T₀ hbar : ℝ}
    (hhbar : 0 < hbar) (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonpos : ∀ C ∈ Set.uIcc C₁ C₂, u C ≤ 0)
    (hfact : ∀ C ∈ Set.uIcc C₁ C₂,
      antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : u c₀ < 0)
    (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi * hbar / (C₂ - C₁)) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  have hL : 0 < C₂ - C₁ := sub_pos.mpr hlt
  have hT' : T₀ * (C₂ - C₁) < 2 * Real.pi * hbar := (lt_div_iff₀ hL).mp hT
  have hθ0 : 0 < T₀ / hbar := div_pos hT0 hhbar
  have hθ : T₀ / hbar < 2 * Real.pi / (C₂ - C₁) := by
    rw [div_lt_iff₀ hhbar, div_mul_eq_mul_div, lt_div_iff₀ hL]
    exact hT'
  have hsin := integral_sin_antiPart_neg_of_nonposOn hlt hθ0 hθ w hw_cont hu_cont
    hu_nonpos hfact hc₀ hu0
  exact packetPhase_ne_of_sin_integral_ne c l hhbar.ne' hC₁ hlt hl hw_cont g hg hsin.ne

/-- 区間上で単調・区間上で狭義単調な C¹ 重みでは、小さな θ > 0 でサイン積分は正である。-/
theorem integral_sin_antiQuot_pos_of_monotoneOn {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂)
    (hθ0 : 0 < θ) (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (w : ℝ → ℝ)
    (hdiff : Differentiable ℝ w) (hderiv : Continuous (deriv w))
    (hmono : MonotoneOn w (Set.uIcc C₁ C₂)) (hstrict : StrictMonoOn w (Set.uIcc C₁ C₂)) :
    0 < ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  apply integral_sin_antiPart_pos_of_nonnegOn hlt hθ0 hθ w hdiff.continuous.continuousOn
    (u := antiQuot w C₁ C₂)
    (hu_cont := continuousOn_antiQuot hdiff hderiv C₁ C₂)
    (hu_nonneg := fun C hC => antiQuot_nonneg_of_monotoneOn hlt hdiff hderiv hmono C hC)
    (hfact := fun C _ => antiPart_eq_mul_antiQuot w C₁ C₂ C)
    (c₀ := (C₁ + 3 * C₂) / 4)
    (hc₀ := ⟨by linarith, by linarith⟩)
    (hu0 := antiQuot_pos_of_strictMonoOn hstrict
      (by rw [Set.uIcc_of_le hlt.le]; constructor <;> linarith)
      (by intro h; linarith))

/-- 区間上で単調・区間上で狭義単調な C¹ 重みでは、0 < T₀ < 2πħ/(C₂−C₁) の範囲で
    位相つき波束は 0 にならない。全体での単調性は要らない。-/
theorem packetPhase_ne_of_small_pos_of_monotoneOn {C₁ C₂ T₀ hbar : ℝ}
    (hhbar : 0 < hbar) (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hdiff : Differentiable ℝ w) (hderiv : Continuous (deriv w))
    (hmono : MonotoneOn w (Set.uIcc C₁ C₂)) (hstrict : StrictMonoOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi * hbar / (C₂ - C₁)) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  apply packetPhase_ne_of_small_pos_of_nonnegOn (c := c) (l := l) hhbar hC₁ hlt hl
    (w := w) (hw_cont := hdiff.continuous.continuousOn) (g := g) (hg := hg)
    (u := antiQuot w C₁ C₂)
    (hu_cont := continuousOn_antiQuot hdiff hderiv C₁ C₂)
    (hu_nonneg := fun C hC => antiQuot_nonneg_of_monotoneOn hlt hdiff hderiv hmono C hC)
    (hfact := fun C _ => antiPart_eq_mul_antiQuot w C₁ C₂ C)
    (c₀ := (C₁ + 3 * C₂) / 4)
    (hc₀ := ⟨by linarith, by linarith⟩)
    (hu0 := antiQuot_pos_of_strictMonoOn hstrict
      (by rw [Set.uIcc_of_le hlt.le]; constructor <;> linarith)
      (by intro h; linarith))
    hT0 hT

/-- 二次重み w(C) = −(C − 10)² は区間 [9, 10] 上で狭義単調増加である
    （全体では単調でない：C > 10 では減少する）。-/
theorem quad_strictMonoOn : StrictMonoOn (fun C : ℝ => -(C - 10) ^ 2) (Set.uIcc 9 10) := by
  intro x hx y hy hxy
  rw [Set.uIcc_of_le (by norm_num : (9:ℝ) ≤ 10)] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  show -(x - 10) ^ 2 < -(y - 10) ^ 2
  have key : (y - 10) ^ 2 < (x - 10) ^ 2 := by
    have h := pow_lt_pow_left₀ (show (10:ℝ) - y < 10 - x by linarith)
      (show (0:ℝ) ≤ 10 - y by linarith) (show (2:ℕ) ≠ 0 by norm_num)
    rwa [show ((10:ℝ) - y) ^ 2 = (y - 10) ^ 2 by ring,
      show ((10:ℝ) - x) ^ 2 = (x - 10) ^ 2 by ring] at h
  exact neg_lt_neg key

/-- 二次重み w(C) = −(C − 10)² は区間 [9, 10] 上で単調である。-/
theorem quad_monotoneOn : MonotoneOn (fun C : ℝ => -(C - 10) ^ 2) (Set.uIcc 9 10) :=
  quad_strictMonoOn.monotoneOn

/-- 具体例：c = ℓ = 1、C ∈ [9, 10]、区間上でのみ単調な二次重み
    g(C) = −(C − 10)²·√Q では、0 < T₀ < 2π の範囲で位相つき波束は 0 にならない。-/
theorem packetPhase_ne_quad_example {T₀ : ℝ} (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi) :
    packetPhase 1 1 9 10 T₀ 1
      (fun C => (-(C - 10) ^ 2) * Real.sqrt (Q 1 1 C 1)) ≠ 0 := by
  refine packetPhase_ne_of_small_pos_of_monotoneOn (c := 1) (l := 1) one_pos (by norm_num)
    (by norm_num) one_pos (w := fun C => -(C - 10) ^ 2) (hdiff := by fun_prop)
    (hderiv := ?_) (hmono := quad_monotoneOn) (hstrict := quad_strictMonoOn)
    (g := fun C => (-(C - 10) ^ 2) * Real.sqrt (Q 1 1 C 1)) (hg := fun C _ => rfl)
    hT0 ?_
  · have hcd : ContDiff ℝ 1 (fun C : ℝ => -(C - 10) ^ 2) := by fun_prop
    exact hcd.continuous_deriv (le_refl 1)
  · have heq : (2 : ℝ) * Real.pi * (1 : ℝ) / ((10 : ℝ) - 9) = 2 * Real.pi := by
      rw [show ((10 : ℝ) - 9) = 1 by norm_num, div_one, mul_one]
    rw [heq]
    exact hT

end

end CFT.WDWWavePacketIntervalMono
