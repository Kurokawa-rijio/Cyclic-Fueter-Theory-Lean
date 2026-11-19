/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第十六段）。

  第十五段で、一般の重みの波束が 0 になる条件は二つの実数の方程式
  （対称部分のコサイン積分 = 0 かつ反対称部分のサイン積分 = 0）に帰着した。
  ここではサイン積分 ∫ w_anti(C) sin((C − m)θ) dC の零点を解析する第一歩として、
  反対称部分が中点からのずれに比例する形
  w_anti(C) = (C − m)·u(C)（u は連続・非負で、区間内のどこかで正）に書ける場合に、
  小さな θ > 0 ではサイン積分が正の符号を持つことを示す。鍵は、|(C−m)θ| ≤ π の
  範囲では (C−m) と sin((C−m)θ) が同符号になること（すなわち
  (C−m)·sin((C−m)θ) ≥ 0）で、θ < 2π/(C₂−C₁) なら区間全体でこの範囲に入る。
  したがってこの形の重みでは、0 < T₀ < 2πħ/(C₂−C₁) の範囲で波束は 0 にならない。
  符号が逆の場合（u ≤ 0）も同様にサイン積分は負になる。
  仮定の意味：u ≥ 0 は、反対称部分が中点の左右で (C−m) と同符号であること、
  すなわち重みが中点を境に単調に増加する方向の非対称性を持つことに対応する
  （例：w(C) = C では u = 1）。単調な重みからこの因数分解を導くこと
  （差商の連続性）は次の段に残る。

  残り：サイン積分の零点の具体的な構造（大きな θ での符号変化、零点の列挙など）。
-/
import CFT.Quantum.WDWWavePacketAsymmetricWeight

namespace CFT.WDWWavePacketSineZero

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketDecayExplicit CFT.WDWWavePacketSymmW CFT.WDWWavePacketAsymW
  MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 反対称部分は重みの符号反転で符号が反転する。-/
theorem antiPart_neg (w : ℝ → ℝ) (C₁ C₂ C : ℝ) :
    antiPart (-w) C₁ C₂ C = -antiPart w C₁ C₂ C := by
  unfold antiPart
  simp only [Pi.neg_apply]
  ring

/-- 0 < θ ≤ 2π/(C₂−C₁) なら、区間内の点では (C−m)·sin((C−m)θ) ≥ 0
    （(C−m) と sin((C−m)θ) が同符号）。-/
theorem mul_sin_nonneg {C₁ C₂ θ C : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ ≤ 2 * Real.pi / (C₂ - C₁)) (hC : C ∈ Set.uIcc C₁ C₂) :
    0 ≤ (C - (C₁ + C₂) / 2) * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  have hL : 0 < C₂ - C₁ := sub_pos.mpr hlt
  have hLne : C₂ - C₁ ≠ 0 := hL.ne'
  rw [Set.uIcc_of_le hlt.le] at hC
  have hbound : |C - (C₁ + C₂) / 2| ≤ (C₂ - C₁) / 2 := by
    obtain ⟨hC1, hC2⟩ := hC
    rw [abs_le]
    constructor <;> linarith
  have hpi : (C₂ - C₁) / 2 * (2 * Real.pi / (C₂ - C₁)) = Real.pi := by
    field_simp
    ring
  have hprod : |(C - (C₁ + C₂) / 2) * θ| ≤ Real.pi := by
    calc |(C - (C₁ + C₂) / 2) * θ| = |C - (C₁ + C₂) / 2| * |θ| := abs_mul _ _
      _ = |C - (C₁ + C₂) / 2| * θ := by rw [abs_of_pos hθ0]
      _ ≤ (C₂ - C₁) / 2 * (2 * Real.pi / (C₂ - C₁)) :=
          mul_le_mul hbound hθ (le_of_lt hθ0) (by linarith)
      _ = Real.pi := hpi
  rcases le_or_lt 0 (C - (C₁ + C₂) / 2) with hx | hx
  · have h1 : 0 ≤ (C - (C₁ + C₂) / 2) * θ := mul_nonneg hx hθ0.le
    have h2 : (C - (C₁ + C₂) / 2) * θ ≤ Real.pi := by
      have h := hprod
      rw [abs_of_nonneg h1] at h
      exact h
    exact mul_nonneg hx (Real.sin_nonneg_of_mem_Icc ⟨h1, h2⟩)
  · have h1 : (C - (C₁ + C₂) / 2) * θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx.le hθ0.le
    have h2 : -Real.pi ≤ (C - (C₁ + C₂) / 2) * θ := by
      have h := hprod
      rw [abs_of_nonpos h1] at h
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hx.le
      (Real.sin_nonpos_of_nonnpos_of_neg_pi_le h1 h2)

/-- 0 < θ < 2π/(C₂−C₁) なら、区間内の点 C ≠ m では (C−m)·sin((C−m)θ) > 0。-/
theorem mul_sin_pos {C₁ C₂ θ C : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (hC : C ∈ Set.Ioo C₁ C₂)
    (hm : C ≠ (C₁ + C₂) / 2) :
    0 < (C - (C₁ + C₂) / 2) * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  have hL : 0 < C₂ - C₁ := sub_pos.mpr hlt
  have hLne : C₂ - C₁ ≠ 0 := hL.ne'
  have hbound : |C - (C₁ + C₂) / 2| < (C₂ - C₁) / 2 := by
    obtain ⟨hC1, hC2⟩ := hC
    rw [abs_lt]
    constructor <;> linarith
  have hpi : (C₂ - C₁) / 2 * (2 * Real.pi / (C₂ - C₁)) = Real.pi := by
    field_simp
    ring
  have hprod : |(C - (C₁ + C₂) / 2) * θ| < Real.pi := by
    calc |(C - (C₁ + C₂) / 2) * θ| = |C - (C₁ + C₂) / 2| * |θ| := abs_mul _ _
      _ = |C - (C₁ + C₂) / 2| * θ := by rw [abs_of_pos hθ0]
      _ < (C₂ - C₁) / 2 * (2 * Real.pi / (C₂ - C₁)) :=
          mul_lt_mul hbound hθ.le hθ0 (by linarith)
      _ = Real.pi := hpi
  rcases lt_or_gt_of_ne hm with hx | hx
  · have h1 : (C - (C₁ + C₂) / 2) * θ < 0 := mul_neg_of_neg_of_pos (by linarith) hθ0
    have h2 : -Real.pi < (C - (C₁ + C₂) / 2) * θ := by
      have h := hprod
      rw [abs_of_neg h1] at h
      linarith
    exact mul_pos_of_neg_of_neg (by linarith)
      (Real.sin_neg_of_neg_of_neg_pi_lt h1 h2)
  · have h1 : 0 < (C - (C₁ + C₂) / 2) * θ := mul_pos (by linarith) hθ0
    have h2 : (C - (C₁ + C₂) / 2) * θ < Real.pi := by
      have h := hprod
      rw [abs_of_pos h1] at h
      exact h
    exact mul_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-- u が区間内の点 c₀ で正なら、中点と異なる点でも正になる点が取れる
    （c₀ が中点そのものの場合、連続性から近傍の点を取る）。-/
theorem exists_pos_point_ne_mid {C₁ C₂ : ℝ} (hlt : C₁ < C₂)
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : 0 < u c₀) :
    ∃ c₁ ∈ Set.Ioo C₁ C₂, c₁ ≠ (C₁ + C₂) / 2 ∧ 0 < u c₁ := by
  have hnhds : Set.uIcc C₁ C₂ ∈ nhds c₀ :=
    Filter.mem_of_superset (Ioo_mem_nhds hc₀.1 hc₀.2)
      (Set.Ioo_subset_Icc_self.trans Set.Icc_subset_uIcc)
  have hu_at : ContinuousAt u c₀ := hu_cont.continuousAt hnhds
  have hev : ∀ᶠ C in nhds c₀, 0 < u C := hu_at.eventually (Ioi_mem_nhds hu0)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  by_cases hm : c₀ = (C₁ + C₂) / 2
  · -- c₀ が中点の場合：c₁ = c₀ + min (δ/2) ((C₂−C₁)/4) を取る
    have hε : 0 < min (δ / 2) ((C₂ - C₁) / 4) :=
      lt_min (by linarith) (by linarith)
    refine ⟨c₀ + min (δ / 2) ((C₂ - C₁) / 4), ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith
    · have hmin : min (δ / 2) ((C₂ - C₁) / 4) ≤ (C₂ - C₁) / 4 := min_le_right _ _
      rw [hm]
      linarith
    · rw [← hm]
      exact ne_of_gt (by linarith)
    · apply hball
      rw [Real.dist_eq]
      have heq : c₀ + min (δ / 2) ((C₂ - C₁) / 4) - c₀
          = min (δ / 2) ((C₂ - C₁) / 4) := by ring
      rw [heq, abs_of_pos hε]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · exact ⟨c₀, hc₀, hm, hu0⟩

/-- 反対称部分が (C−m)·u(C)（u は連続・非負で、区間内のどこかで正）と書ける場合、
    小さな θ > 0 ではサイン積分は正である。-/
theorem integral_sin_antiPart_pos {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonneg : ∀ C, 0 ≤ u C)
    (hfact : ∀ C, antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : 0 < u c₀) :
    0 < ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  obtain ⟨c₁, hc₁, hcm, hu1⟩ := exists_pos_point_ne_mid hlt hu_cont hc₀ hu0
  apply integral_pos_of_continuous_nonneg _ _ hc₁ _
  · exact (antiPart_continuousOn hw_cont).mul ((Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)
  · intro C hC
    rw [hfact C]
    have hmul := mul_sin_nonneg hlt hθ0 hθ.le (Set.Icc_subset_uIcc hC)
    have h1 : (C - (C₁ + C₂) / 2) * u C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
        = u C * ((C - (C₁ + C₂) / 2) * Real.sin ((C - (C₁ + C₂) / 2) * θ)) := by ring
    rw [h1]
    exact mul_nonneg (hu_nonneg C) hmul
  · rw [hfact c₁]
    have hmul := mul_sin_pos hlt hθ0 hθ hc₁ hcm
    have h1 : (c₁ - (C₁ + C₂) / 2) * u c₁ * Real.sin ((c₁ - (C₁ + C₂) / 2) * θ)
        = u c₁ * ((c₁ - (C₁ + C₂) / 2) * Real.sin ((c₁ - (C₁ + C₂) / 2) * θ)) := by ring
    rw [h1]
    exact mul_pos hu1 hmul

/-- 反対称部分が (C−m)·u(C)（u は連続・非正で、区間内のどこかで負）と書ける場合、
    小さな θ > 0 ではサイン積分は負である。-/
theorem integral_sin_antiPart_neg {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonpos : ∀ C, u C ≤ 0)
    (hfact : ∀ C, antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : u c₀ < 0) :
    ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) < 0 := by
  have hpos : 0 < ∫ C in C₁..C₂,
      antiPart (-w) C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) :=
    integral_sin_antiPart_pos hlt hθ0 hθ (-w) hw_cont.neg
      (hu_cont := hu_cont.neg)
      (hu_nonneg := fun C => neg_nonneg.mpr (hu_nonpos C))
      (hfact := fun C => by
        simp only [antiPart_neg, hfact C, Pi.neg_apply]
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

/-- サイン積分が 0 でなければ、位相つき波束は 0 にならない（第十五段の iff の片側）。-/
theorem packetPhase_ne_of_sin_integral_ne {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    (hsin : ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) ≠ 0) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  intro hzero
  exact hsin ((packetPhase_decomp_eq_zero_iff c l hhbar hC₁ hlt hl hw_cont g hg).mp hzero).2

/-- 反対称部分が (C−m)·u(C)（u ≥ 0）の形の重みでは、0 < T₀ < 2πħ/(C₂−C₁) の範囲で
    位相つき波束は 0 にならない。-/
theorem packetPhase_ne_of_small_pos {C₁ C₂ T₀ hbar : ℝ}
    (hhbar : 0 < hbar) (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonneg : ∀ C, 0 ≤ u C)
    (hfact : ∀ C, antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : 0 < u c₀)
    (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi * hbar / (C₂ - C₁)) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  have hL : 0 < C₂ - C₁ := sub_pos.mpr hlt
  have hT' : T₀ * (C₂ - C₁) < 2 * Real.pi * hbar := (lt_div_iff₀ hL).mp hT
  have hθ0 : 0 < T₀ / hbar := div_pos hT0 hhbar
  have hθ : T₀ / hbar < 2 * Real.pi / (C₂ - C₁) := by
    rw [div_lt_iff₀ hhbar, div_mul_eq_mul_div, lt_div_iff₀ hL]
    exact hT'
  have hsin := integral_sin_antiPart_pos hlt hθ0 hθ w hw_cont hu_cont hu_nonneg hfact hc₀ hu0
  exact packetPhase_ne_of_sin_integral_ne c l hhbar.ne' hC₁ hlt hl hw_cont g hg hsin.ne'

/-- 反対称部分が (C−m)·u(C)（u ≤ 0）の形の重みでは、0 < T₀ < 2πħ/(C₂−C₁) の範囲で
    位相つき波束は 0 にならない。-/
theorem packetPhase_ne_of_small_neg {C₁ C₂ T₀ hbar : ℝ}
    (hhbar : 0 < hbar) (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    {u : ℝ → ℝ} (hu_cont : ContinuousOn u (Set.uIcc C₁ C₂))
    (hu_nonpos : ∀ C, u C ≤ 0)
    (hfact : ∀ C, antiPart w C₁ C₂ C = (C - (C₁ + C₂) / 2) * u C)
    {c₀ : ℝ} (hc₀ : c₀ ∈ Set.Ioo C₁ C₂) (hu0 : u c₀ < 0)
    (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi * hbar / (C₂ - C₁)) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  have hL : 0 < C₂ - C₁ := sub_pos.mpr hlt
  have hT' : T₀ * (C₂ - C₁) < 2 * Real.pi * hbar := (lt_div_iff₀ hL).mp hT
  have hθ0 : 0 < T₀ / hbar := div_pos hT0 hhbar
  have hθ : T₀ / hbar < 2 * Real.pi / (C₂ - C₁) := by
    rw [div_lt_iff₀ hhbar, div_mul_eq_mul_div, lt_div_iff₀ hL]
    exact hT'
  have hsin := integral_sin_antiPart_neg hlt hθ0 hθ w hw_cont hu_cont hu_nonpos hfact hc₀ hu0
  exact packetPhase_ne_of_sin_integral_ne c l hhbar.ne' hC₁ hlt hl hw_cont g hg hsin.ne

/-- 線形重み w(C) = C では反対称部分はちょうど C − m であり、u = 1 が取れる。-/
theorem antiPart_linear_eq (C₁ C₂ C : ℝ) :
    antiPart (fun C => C) C₁ C₂ C = C - (C₁ + C₂) / 2 := by
  unfold antiPart
  show (C - (C₁ + C₂ - C)) / 2 = C - (C₁ + C₂) / 2
  ring

/-- 線形重みでは、小さな θ > 0 でサイン積分は正である。-/
theorem integral_sin_linear_pos {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) :
    0 < ∫ C in C₁..C₂, (C - (C₁ + C₂) / 2) * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  have h : 0 < ∫ C in C₁..C₂,
      antiPart (fun C => C) C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
    apply integral_sin_antiPart_pos hlt hθ0 hθ (fun C => C) (by fun_prop)
      (u := fun _ => (1 : ℝ)) (hu_cont := continuousOn_const)
      (hu_nonneg := fun _ => zero_le_one)
      (hfact := fun C => by rw [antiPart_linear_eq]; simp)
      (c₀ := (C₁ + C₂) / 2) (hc₀ := ⟨by linarith, by linarith⟩) (hu0 := one_pos)
  have hcongr : ∫ C in C₁..C₂,
        antiPart (fun C => C) C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
      = ∫ C in C₁..C₂, (C - (C₁ + C₂) / 2) * Real.sin ((C - (C₁ + C₂) / 2) * θ) :=
    intervalIntegral.integral_congr (fun C _ => by rw [antiPart_linear_eq])
  rw [hcongr] at h
  exact h

/-- 具体例：c = ℓ = 1、C ∈ [9, 10]、線形重み g(C) = C·√Q では、0 < T₀ < 2π の範囲で
    位相つき波束は 0 にならない。-/
theorem packetPhase_ne_linear_example {T₀ : ℝ} (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi) :
    packetPhase 1 1 9 10 T₀ 1 (fun C => C * Real.sqrt (Q 1 1 C 1)) ≠ 0 := by
  refine packetPhase_ne_of_small_pos (c := 1) (l := 1) one_pos (by norm_num) (by norm_num)
    one_pos (w := fun C => C) (hw_cont := by fun_prop)
    (g := fun C => C * Real.sqrt (Q 1 1 C 1)) (hg := fun C _ => rfl)
    (u := fun _ => (1 : ℝ)) (hu_cont := continuousOn_const)
    (hu_nonneg := fun _ => zero_le_one)
    (hfact := fun C => by rw [antiPart_linear_eq]; simp)
    (c₀ := (9 + 10 : ℝ) / 2) (hc₀ := ⟨by norm_num, by norm_num⟩) (hu0 := one_pos)
    hT0 ?_
  have heq : (2 : ℝ) * Real.pi * (1 : ℝ) / ((10 : ℝ) - 9) = 2 * Real.pi := by
    rw [show ((10 : ℝ) - 9) = 1 by norm_num, div_one, mul_one]
  rw [heq]
  exact hT

end

end CFT.WDWWavePacketSineZero
