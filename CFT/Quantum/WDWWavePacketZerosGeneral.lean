/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の区間への拡張（第十二段）。

  第七段〜第十一段では、bump 波束を c = ℓ = 1、C ∈ [9, 10]（L = C₂ − C₁ = 1）、
  ħ = 1 の場合に固定して解析した：閉形式、位相条件、零点の存在・一意性・
  可算性、零点の間隔。ここでは区間を一般の [C₁, C₂] に広げる。

  鍵は、位相関数が L によるスケールでそのまま移ること：位相条件
  e^{−iLθ} = (2 − iθL)/(2 + iθL) は、x = Lθ と置けば第九段の位相方程式
  phaseFun x = 2πn（phaseFun x = x − 2 arctan(x/2)）そのものになる
  （`phase_condition_general_iff`）。したがって零点は θ = phaseZero n / L
  に並び、T₀ = ħ·phaseZero n / L に並ぶ（`packetPhase_bump_zero_set_eq_general`）。
  T₀ = 0 での値は Ψ_f(0) = (C₂ − C₁)³/(6√ℓ) ≠ 0
  （`packetPhase_bump_zero_value_general`、FTC による）で、零点集合は可算・
  測度 0、ほとんどすべての T₀ で波束は 0 でない
  （`packetPhase_bump_ae_ne_zero_general`）。すなわち第十段の
  「ほとんどすべての T₀ での非消滅」が、任意の区間 [C₁, C₂] の bump 波束
  について成り立つ。

  残り：一般の重み g への拡張（bump 以外の重みでは閉形式が変わるため、
  位相関数の形そのものから見直す必要がある）と、零点の間隔の一般区間版
  （間隔は 2π/L に収束するはずで、第十一段のスケール版）。
-/
import CFT.Quantum.WDWWavePacketZeros

namespace CFT.WDWWavePacketZerosGen

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay CFT.WDWWavePacketDecayExplicit
  CFT.WDWWavePacketClosedForm CFT.WDWWavePacketZero CFT.WDWWavePacketZeroUnique
  CFT.WDWWavePacketZeros MeasureTheory intervalIntegral

variable (c l : ℝ)

/-- 一般区間の位相関数：h_L(θ) = h(Lθ)。-/
theorem phaseFun_scaled (L θ : ℝ) :
    phaseFun (L * θ) = L * θ - 2 * Real.arctan (L * θ / 2) :=
  rfl

/-- 位相条件の二つの書き方：L と θ を分けた形と、積 Lθ の形。-/
theorem phase_condition_general_iff (L θ : ℝ) :
    Complex.exp (-Complex.I * (L : ℂ) * (θ : ℂ))
      = (2 - Complex.I * (θ : ℂ) * (L : ℂ))
        / (2 + Complex.I * (θ : ℂ) * (L : ℂ))
    ↔ Complex.exp (-Complex.I * ((L * θ : ℝ) : ℂ))
      = (2 - Complex.I * ((L * θ : ℝ) : ℂ))
        / (2 + Complex.I * ((L * θ : ℝ) : ℂ)) := by
  have e1 : (-Complex.I * (L : ℂ) * (θ : ℂ))
      = (-Complex.I * ((L * θ : ℝ) : ℂ)) := by push_cast; ring
  have e2 : (2 - Complex.I * (θ : ℂ) * (L : ℂ))
      / (2 + Complex.I * (θ : ℂ) * (L : ℂ))
      = (2 - Complex.I * ((L * θ : ℝ) : ℂ))
        / (2 + Complex.I * ((L * θ : ℝ) : ℂ)) := by
    congr 1 <;> push_cast <;> ring
  rw [e1, e2]

/-- 一般区間の bump 波束が 0 になる条件：ちょうど位相条件のとき
    （θ = T₀/ħ、L = C₂ − C₁）。-/
theorem packetPhase_bump_zero_iff_phase_general {C₁ C₂ T₀ hbar : ℝ}
    (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l)
    (hT₀ : T₀ ≠ 0) (hhbar : hbar ≠ 0) :
    packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0
      ↔ Complex.exp (-Complex.I * ((C₂ - C₁ : ℝ) : ℂ) * ((T₀ / hbar : ℝ) : ℂ))
        = (2 - Complex.I * ((T₀ / hbar : ℝ) : ℂ) * ((C₂ - C₁ : ℝ) : ℂ))
          / (2 + Complex.I * ((T₀ / hbar : ℝ) : ℂ) * ((C₂ - C₁ : ℝ) : ℂ)) := by
  have hθ : (T₀ / hbar : ℝ) ≠ 0 := div_ne_zero hT₀ hhbar
  have hcf := packetPhase_bump_closed_form (c := c) (l := l) hlt hC₁ hl hT₀ hhbar
  have hif := bumpPoly_integral_closed_form (C₁ := C₁) (C₂ := C₂) (θ := T₀ / hbar) hθ
  have hsqrt : ((Real.sqrt l : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hl).ne'
  have hEq : packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)
      = (∫ C in C₁..C₂, ((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))
          * Complex.exp (-Complex.I * (C : ℂ) * ((T₀ / hbar : ℝ) : ℂ)))
        / (Real.sqrt l : ℂ) := by
    rw [hcf, ← hif]
  rw [hEq, div_eq_zero_iff, or_iff_left hsqrt]
  exact bumpPoly_integral_eq_zero_iff hθ

/-- T₀ = 0 での bump 波束の値：一般区間では (C₂ − C₁)³/(6√ℓ)。-/
theorem packetPhase_bump_zero_value_general {C₁ C₂ hbar : ℝ} (hlt : C₁ < C₂)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) :
    packetPhase c l C₁ C₂ 0 hbar (bumpG c l C₁ C₂)
      = (((C₂ - C₁) ^ 3 / (6 * Real.sqrt l) : ℝ) : ℂ) := by
  rw [packetPhase_zero (c := c) (l := l) (C₁ := C₁) (C₂ := C₂) (hbar := hbar)
    (g := bumpG c l C₁ C₂)]
  have hInt : (∫ C in C₁..C₂, bumpG c l C₁ C₂ C / Real.sqrt (Q c l C l))
      = (C₂ - C₁) ^ 3 / (6 * Real.sqrt l) := by
    have hcong : ∀ C ∈ Set.uIcc C₁ C₂,
        bumpG c l C₁ C₂ C / Real.sqrt (Q c l C l)
          = (C - C₁) * (C₂ - C) / Real.sqrt l := by
      intro C hC
      have hCa : 8 * c ^ 2 * l < C := by
        rw [Set.uIcc_of_le hlt.le] at hC
        exact lt_of_lt_of_le hC₁ hC.1
      exact bumpG_div_sqrt_eq c l hCa hl
    rw [intervalIntegral.integral_congr hcong]
    have hF : ∀ x : ℝ, HasDerivAt
        (fun y : ℝ => (-y ^ 3 / 3 + (C₁ + C₂) * y ^ 2 / 2 - C₁ * C₂ * y) / Real.sqrt l)
        (((x - C₁) * (C₂ - x)) / Real.sqrt l) x := by
      intro x
      have h := (((hasDerivAt_pow 3 x).const_mul (-1 / 3 : ℝ)).add
        (((hasDerivAt_pow 2 x).const_mul ((C₁ + C₂) / 2 : ℝ)).add
          ((hasDerivAt_id x).const_mul (-(C₁ * C₂) : ℝ)))).div_const (Real.sqrt l)
      convert h using 1
      · ext y; simp only [id_eq]; ring
      · push_cast; ring
    have hint : IntervalIntegrable (fun x : ℝ => (x - C₁) * (C₂ - x) / Real.sqrt l)
        volume C₁ C₂ := by
      apply Continuous.intervalIntegrable
      continuity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (-y ^ 3 / 3 + (C₁ + C₂) * y ^ 2 / 2 - C₁ * C₂ * y) / Real.sqrt l)
      (f' := fun x : ℝ => (x - C₁) * (C₂ - x) / Real.sqrt l) (fun x _ => hF x) hint]
    have hG : (-C₂ ^ 3 / 3 + (C₁ + C₂) * C₂ ^ 2 / 2 - C₁ * C₂ * C₂)
        - (-C₁ ^ 3 / 3 + (C₁ + C₂) * C₁ ^ 2 / 2 - C₁ * C₂ * C₁)
        = (C₂ - C₁) ^ 3 / 6 := by ring
    rw [← sub_div, hG, div_div]
  rw [hInt]

/-- T₀ = 0 で bump 波束は 0 でない（一般区間）。-/
theorem packetPhase_bump_ne_zero_at_zero_general {C₁ C₂ hbar : ℝ} (hlt : C₁ < C₂)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) :
    packetPhase c l C₁ C₂ 0 hbar (bumpG c l C₁ C₂) ≠ 0 := by
  rw [packetPhase_bump_zero_value_general (c := c) (l := l) hlt hC₁ hl]
  have hL : (0:ℝ) < C₂ - C₁ := sub_pos.mpr hlt
  have hsqrt : (0:ℝ) < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hpos : (0:ℝ) < (C₂ - C₁) ^ 3 / (6 * Real.sqrt l) :=
    div_pos (pow_pos hL 3) (mul_pos (by norm_num) hsqrt)
  exact_mod_cast ne_of_gt hpos

/-- 一般区間の bump 波束が 0 になるのはちょうど、ある n ≠ 0 に対して
    phaseFun ((C₂ − C₁)·(T₀/ħ)) = 2πn のとき。-/
theorem packetPhase_bump_zero_iff_exists_int_general {C₁ C₂ T₀ hbar : ℝ}
    (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : hbar ≠ 0) :
    packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0
      ↔ ∃ n : ℤ, n ≠ 0 ∧ phaseFun ((C₂ - C₁) * (T₀ / hbar)) = (n : ℝ) * (2 * Real.pi) := by
  have hL : (0:ℝ) < C₂ - C₁ := sub_pos.mpr hlt
  have hLne : (C₂ - C₁ : ℝ) ≠ 0 := hL.ne'
  have hphase_eq := phase_condition_general_iff (C₂ - C₁) (T₀ / hbar)
  constructor
  · intro h
    by_cases hT₀ : T₀ = 0
    · rw [hT₀] at h
      exact absurd h (packetPhase_bump_ne_zero_at_zero_general (c := c) (l := l) hlt hC₁ hl)
    · have hphase := (packetPhase_bump_zero_iff_phase_general (c := c) (l := l) hlt hC₁ hl hT₀ hhbar).mp h
      have hphase' := hphase_eq.mp hphase
      obtain ⟨n, hn⟩ := phase_condition_iff_exists_int.mp hphase'
      refine ⟨n, ?_, hn⟩
      intro hn0
      subst hn0
      simp only [Int.cast_zero, zero_mul] at hn
      have hT : (C₂ - C₁) * (T₀ / hbar) = 0 :=
        phaseFun_injective (by rw [hn, phaseFun_zero])
      have hθ : (T₀ / hbar) = 0 := by
        rcases mul_eq_zero.mp hT with h | h
        · exact absurd h hLne
        · exact h
      exact hT₀ ((div_eq_zero_iff.mp hθ).resolve_right hhbar)
  · rintro ⟨n, hn0, hfn⟩
    have hT₀ : T₀ ≠ 0 := by
      intro hT
      rw [hT] at hfn
      simp only [zero_div, mul_zero, phaseFun_zero] at hfn
      have hpi : (2 * Real.pi) ≠ 0 := by
        have hpi' := Real.pi_pos
        positivity
      have hnR : (n : ℝ) = 0 := by
        rcases mul_eq_zero.mp hfn.symm with h | h
        · exact h
        · exact absurd h hpi
      exact hn0 (by exact_mod_cast hnR)
    apply (packetPhase_bump_zero_iff_phase_general (c := c) (l := l) hlt hC₁ hl hT₀ hhbar).mpr
    rw [hphase_eq]
    exact phase_condition_iff_exists_int.mpr ⟨n, hfn⟩

/-- 一般区間の bump 波束の零点集合は、第 n 零点を ħ/L 倍したものの像に一致する。-/
theorem packetPhase_bump_zero_set_eq_general {C₁ C₂ hbar : ℝ}
    (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : 0 < hbar) :
    {T₀ | packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0}
      = (fun n : ℤ => hbar * phaseZero n / (C₂ - C₁)) '' {n : ℤ | n ≠ 0} := by
  have hL : (0:ℝ) < C₂ - C₁ := sub_pos.mpr hlt
  have hLne : (C₂ - C₁ : ℝ) ≠ 0 := hL.ne'
  have hhn : (hbar : ℝ) ≠ 0 := hhbar.ne'
  ext T₀
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨n, hn0, hfn⟩ :=
      (packetPhase_bump_zero_iff_exists_int_general (c := c) (l := l) hlt hC₁ hl hhn).mp h
    refine ⟨n, hn0, ?_⟩
    have hx : (C₂ - C₁) * (T₀ / hbar) = phaseZero n := by
      apply phaseFun_injective
      rw [phaseZero_spec, hfn]
    have hT : T₀ = hbar * phaseZero n / (C₂ - C₁) := by
      rw [eq_div_iff hLne]
      have h2 : (C₂ - C₁) * (T₀ / hbar) = phaseZero n := hx
      rw [mul_div_assoc'] at h2
      rw [div_eq_iff hhn] at h2
      rw [mul_comm T₀ (C₂ - C₁), mul_comm hbar (phaseZero n)]
      exact h2
    exact hT.symm
  · rintro ⟨n, hn0, rfl⟩
    apply (packetPhase_bump_zero_iff_exists_int_general (c := c) (l := l) hlt hC₁ hl hhn).mpr
    refine ⟨n, hn0, ?_⟩
    have hx : (C₂ - C₁) * ((hbar * phaseZero n / (C₂ - C₁)) / hbar) = phaseZero n := by
      rw [← mul_div_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hLne,
        mul_div_cancel_left₀ _ hhn]
    rw [hx, phaseZero_spec]

/-- 一般区間の bump 波束の零点集合は可算である。-/
theorem packetPhase_bump_zero_set_countable_general {C₁ C₂ hbar : ℝ}
    (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : 0 < hbar) :
    Set.Countable {T₀ | packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0} := by
  rw [packetPhase_bump_zero_set_eq_general (c := c) (l := l) hlt hC₁ hl hhbar]
  exact (Set.to_countable _).image _

/-- 一般区間の bump 波束の零点集合は測度 0 である。-/
theorem packetPhase_bump_zero_set_measure_zero_general {C₁ C₂ hbar : ℝ}
    (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : 0 < hbar) :
    volume {T₀ : ℝ | packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0} = 0 :=
  (packetPhase_bump_zero_set_countable_general (c := c) (l := l) hlt hC₁ hl hhbar).measure_zero volume

/-- ほとんどすべての T₀ で、一般区間の bump 波束は 0 でない。-/
theorem packetPhase_bump_ae_ne_zero_general {C₁ C₂ hbar : ℝ}
    (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : 0 < hbar) :
    ∀ᵐ T₀ ∂(volume : MeasureTheory.Measure ℝ),
      packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) ≠ 0 := by
  have h := (packetPhase_bump_zero_set_countable_general (c := c) (l := l) hlt hC₁ hl hhbar).ae_not_mem volume
  filter_upwards [h] with T₀ hT₀
  exact hT₀

/-- 具体例：c = ℓ = 1、C ∈ [9, 11]（L = 2）、ħ = 1 では零点は
    phaseFun (2T₀) = 2πn のとき。-/
theorem packetPhase_bump_zero_iff_general_example {T₀ : ℝ} :
    packetPhase 1 1 9 11 T₀ 1 (bumpG 1 1 9 11) = 0
      ↔ ∃ n : ℤ, n ≠ 0 ∧ phaseFun (2 * T₀) = (n : ℝ) * (2 * Real.pi) := by
  have h := packetPhase_bump_zero_iff_exists_int_general (c := 1) (l := 1) (T₀ := T₀)
    (by norm_num : (9 : ℝ) < 11) (by norm_num : 8 * (1 : ℝ) ^ 2 * 1 < 9)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≠ 0)
  have h2 : ((11 : ℝ) - 9) * (T₀ / 1) = 2 * T₀ := by norm_num
  rw [h2] at h
  exact h

end CFT.WDWWavePacketZerosGen
