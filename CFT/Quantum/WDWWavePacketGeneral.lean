/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第二段）。

  第一弾 `WDWWavePacketNonvanishing.lean` では、具体的な波束（T₀ = 0、
  g = 𝟙_[C₁,C₂]、首 b = ℓ）について境界値の閉形式と正の明示下限を証明した。
  ここでは重みを一般化する：g が [C₁, C₂] 上で連続・非負で、ある内点で正なら、
  波束の境界値 Ψ_f(0, ℓ) = ∫_{C₁}^{C₂} g(C)/√(Q c l C l) dC は正である。

  証明の核は実解析の一般補題：連続・非負で、ある内点で正の関数の区間積分は
  正である（正の点の近傍で関数が正の定数以上になることと、部分区間への
  単調性 `intervalIntegral.integral_mono_interval` による）。
  さらに定量的な下限（δ * m ≤ ∫）も同時に得る。これが `GAP_5-8_prep.md` §5
  のいう「C 積分の下限評価」の一般の g に対する形である。

  残り：位相 e^{−iCT₀/ħ} が入る場合（T₀ ≠ 0）の評価。
-/
import CFT.Quantum.WDWWavePacketNonvanishing

namespace CFT.WDWWavePacketGen

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 連続・非負で、ある内点で正の関数の区間積分の定量的な下限。-/
theorem integral_lower_of_continuous_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf_cont : ContinuousOn f (Set.uIcc a b))
    (hf_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b) (hfpos : 0 < f x₀) :
    ∃ δ > 0, ∃ m > 0, δ * m ≤ ∫ x in a..b, f x := by
  have hcat : ContinuousAt f x₀ :=
    hf_cont.continuousAt (Filter.mem_of_superset (Ioo_mem_nhds hx₀.1 hx₀.2)
      (fun x hx => Set.mem_uIcc.mpr (Or.inl ⟨hx.1.le, hx.2.le⟩)))
  obtain ⟨δ, hδ, hδspec⟩ := (Metric.continuousAt_iff.mp hcat) (f x₀ / 2) (half_pos hfpos)
  obtain ⟨δ', hδ'pos, hδ'δ, hδ'a, hδ'b⟩ :
      ∃ δ', 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ x₀ - a ∧ δ' ≤ b - x₀ :=
    ⟨min δ (min (x₀ - a) (b - x₀)),
      lt_min hδ (lt_min (sub_pos.mpr hx₀.1) (sub_pos.mpr hx₀.2)),
      min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hhalf : δ' / 2 ≤ δ' := half_le_self hδ'pos.le
  have hau : a ≤ x₀ - δ' / 2 := by linarith
  have hvb : x₀ + δ' / 2 ≤ b := by linarith
  have huv : x₀ - δ' / 2 < x₀ + δ' / 2 := by linarith
  -- [x₀ - δ'/2, x₀ + δ'/2] 上では f ≥ f x₀ / 2
  have hlower : ∀ x ∈ Set.Icc (x₀ - δ' / 2) (x₀ + δ' / 2), f x₀ / 2 ≤ f x := by
    intro x hx
    have hdist : dist x x₀ < δ := by
      rw [Real.dist_eq]
      have habs : |x - x₀| ≤ δ' / 2 := by
        rw [abs_le]
        obtain ⟨hx1, hx2⟩ := hx
        constructor <;> linarith
      linarith
    have h := hδspec hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith
  -- 可積分性
  have hf_int_ab : IntervalIntegrable f volume a b := hf_cont.intervalIntegrable
  have hf_int_uv : IntervalIntegrable f volume (x₀ - δ' / 2) (x₀ + δ' / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply hf_cont.mono
    apply Set.uIcc_subset_uIcc
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hau, huv.le.trans hvb⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hau.trans huv.le, hvb⟩)
  -- 中間区間の積分 ≥ (v - u) * (f x₀ / 2)
  have hmid : (x₀ + δ' / 2 - (x₀ - δ' / 2)) * (f x₀ / 2)
      ≤ ∫ x in (x₀ - δ' / 2)..(x₀ + δ' / 2), f x := by
    have h1 : ∫ x in (x₀ - δ' / 2)..(x₀ + δ' / 2), (f x₀ / 2)
        ≤ ∫ x in (x₀ - δ' / 2)..(x₀ + δ' / 2), f x := by
      apply intervalIntegral.integral_mono_on huv.le intervalIntegrable_const hf_int_uv
      intro x hx
      exact hlower x hx
    rw [intervalIntegral.integral_const] at h1
    rwa [smul_eq_mul] at h1
  -- 中間区間の積分 ≤ 全区間の積分（非負性より）
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), 0 ≤ f x := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact hf_nonneg x (Set.Ioc_subset_Icc_self hx)
  have hmono : ∫ x in (x₀ - δ' / 2)..(x₀ + δ' / 2), f x ≤ ∫ x in a..b, f x :=
    intervalIntegral.integral_mono_interval hau huv.le hvb hnn hf_int_ab
  refine ⟨δ', hδ'pos, f x₀ / 2, half_pos hfpos, ?_⟩
  have hlen : x₀ + δ' / 2 - (x₀ - δ' / 2) = δ' := by ring
  rw [hlen] at hmid
  exact le_trans hmid hmono

/-- 連続・非負で、ある内点で正の関数の区間積分は正である。-/
theorem integral_pos_of_continuous_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf_cont : ContinuousOn f (Set.uIcc a b))
    (hf_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b) (hfpos : 0 < f x₀) :
    0 < ∫ x in a..b, f x := by
  obtain ⟨δ, hδ, m, hm, hle⟩ :=
    integral_lower_of_continuous_nonneg hf_cont hf_nonneg hx₀ hfpos
  exact lt_of_lt_of_le (mul_pos hδ hm) hle

/-- 被積分関数 g(C)/√(Q c l C l) の連続性（分母は [C₁, C₂] 上で 0 にならない）。-/
theorem packetIntegrand_continuousOn {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁)
    (hlt : C₁ < C₂) (hl : 0 < l) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂)) :
    ContinuousOn (fun C => g C / Real.sqrt (Q c l C l)) (Set.uIcc C₁ C₂) := by
  have hQcont : Continuous (fun C => Q c l C l) := by
    have heq : (fun C => Q c l C l) = fun C => l * (C - 8 * c ^ 2 * l) := by
      funext C
      exact Q_neck c l C
    rw [heq]
    fun_prop
  apply ContinuousOn.div hg_cont
  · exact (Real.continuous_sqrt.comp hQcont).continuousOn
  · intro x hx
    have hx1 : 8 * c ^ 2 * l < x := by
      rw [Set.uIcc_of_le hlt.le] at hx
      exact lt_of_lt_of_le hC₁ hx.1
    exact (Real.sqrt_pos.mpr (Q_neck_pos c l hx1 hl)).ne'

/-- 波束の境界値の正値性：一般の重み g について（T₀ = 0、首 b = ℓ）。-/
theorem packetGen_pos {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂)
    (hl : 0 < l) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂))
    (hg_nonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo C₁ C₂) (hgpos : 0 < g x₀) :
    0 < ∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l) := by
  have hcont := packetIntegrand_continuousOn c l hC₁ hlt hl hg_cont
  have hnonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C / Real.sqrt (Q c l C l) := by
    intro C hC
    exact div_nonneg (hg_nonneg C hC) (Real.sqrt_nonneg _)
  have hpos : 0 < g x₀ / Real.sqrt (Q c l x₀ l) := by
    have hx1 : 8 * c ^ 2 * l < x₀ := lt_of_lt_of_le hC₁ hx₀.1.le
    exact div_pos hgpos (Real.sqrt_pos.mpr (Q_neck_pos c l hx1 hl))
  exact integral_pos_of_continuous_nonneg hcont hnonneg hx₀ hpos

/-- 波束の境界値の定量的な下限：一般の重み g について。-/
theorem packetGen_lower {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂)
    (hl : 0 < l) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂))
    (hg_nonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo C₁ C₂) (hgpos : 0 < g x₀) :
    ∃ δ > 0, ∃ m > 0, δ * m ≤ ∫ C in C₁..C₂, g C / Real.sqrt (Q c l C l) := by
  have hcont := packetIntegrand_continuousOn c l hC₁ hlt hl hg_cont
  have hnonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C / Real.sqrt (Q c l C l) := by
    intro C hC
    exact div_nonneg (hg_nonneg C hC) (Real.sqrt_nonneg _)
  have hpos : 0 < g x₀ / Real.sqrt (Q c l x₀ l) := by
    have hx1 : 8 * c ^ 2 * l < x₀ := lt_of_lt_of_le hC₁ hx₀.1.le
    exact div_pos hgpos (Real.sqrt_pos.mpr (Q_neck_pos c l hx1 hl))
  exact integral_lower_of_continuous_nonneg hcont hnonneg hx₀ hpos

/-- 複素表示：一般の重み g の波束 Ψ_f(0, ℓ) は 0 でない。-/
theorem packetGen_ne {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂)
    (hl : 0 < l) (κ : ℝ) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.uIcc C₁ C₂))
    (hg_nonneg : ∀ C ∈ Set.Icc C₁ C₂, 0 ≤ g C)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo C₁ C₂) (hgpos : 0 < g x₀) :
    (∫ C in C₁..C₂, g C • PsiPlus c l κ C 0 l) ≠ 0 := by
  have h1 : (∫ C in C₁..C₂, g C • PsiPlus c l κ C 0 l)
      = ∫ C in C₁..C₂, ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro C _
    show g C • PsiPlus c l κ C 0 l = ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ)
    rw [psiPlus_zero, Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    rw [mul_one_div]
  rw [h1, intervalIntegral.integral_ofReal, ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (packetGen_pos c l hC₁ hlt hl hg_cont hg_nonneg hx₀ hgpos)

/-- 具体例：c = ℓ = 1、g(C) = C − 8、C ∈ [9, 10] の波束の境界値は正。-/
theorem packetGen_example :
    0 < ∫ C in (9 : ℝ)..10, (C - 8) / Real.sqrt (Q 1 1 C 1) := by
  exact packetGen_pos 1 1 (by norm_num) (by norm_num) (by norm_num)
    (continuous_id.sub continuous_const).continuousOn
    (fun C hC => by linarith [hC.1])
    (show (9.5 : ℝ) ∈ Set.Ioo (9 : ℝ) 10 by norm_num)
    (by norm_num)

end

end CFT.WDWWavePacketGen
