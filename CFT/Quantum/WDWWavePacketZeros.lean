/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第十段：各 n に対する零点の存在と零点集合の可算性）。

  第九段までで、bump 波束（c = ℓ = 1、C ∈ [9, 10]、ħ = 1）の零点は
  (2π, 10) 内にちょうど一つあり、それが位相方程式 h(x) = 2π（h(x) = x − 2 arctan(x/2)）
  の解であることが示された。ここでは h が ℝ 全体で狭義単調であること
  （`strictMono_phaseFun`、奇性と [0, ∞) 上の単調性から）を示し、中間値の定理により
  各 n : ℤ に対して h(x) = 2πn なる x が一意に存在すること
  （`existsUnique_phaseFun_eq`）を証明する。n ≥ 1 の零点は区間
  (2πn, 2πn + 2π) 内にある（`phaseZero_mem_Ioo_of_one_le`）。
  零点の列挙 `phaseZero : ℤ → ℝ` を置き、bump 波束の零点集合が
  phaseZero '' {n | n ≠ 0} に一致すること（`packetPhase_bump_zero_set_eq`）から、
  零点集合は可算で測度 0 であり（`packetPhase_bump_zero_set_countable`・
  `packetPhase_bump_zero_set_measure_zero`）、ほとんどすべての T₀ で波束は
  0 でないこと（`packetPhase_bump_ae_ne_zero`）を証明する。すなわち「すべての
  大きな |T₀| に対する非消滅」は反証されたが、「ほとんどすべての T₀ での非消滅」
  は成り立つ、という組み替えが完成する。
  残り：零点の密度・間隔の定量評価（x_{n+1} − x_n → 2π など）と、一般の重み g・
  一般の区間への拡張。
-/
import CFT.Quantum.WDWWavePacketZeroUnique

namespace CFT.WDWWavePacketZeros

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay CFT.WDWWavePacketDecayExplicit
  CFT.WDWWavePacketClosedForm CFT.WDWWavePacketZero CFT.WDWWavePacketZeroUnique
  MeasureTheory intervalIntegral

/-- 位相関数は連続。-/
theorem phaseFun_continuous : Continuous phaseFun := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hasDerivAt_phaseFun x).continuousAt

/-- 位相関数は 0 で 0。-/
theorem phaseFun_zero : phaseFun 0 = 0 := by
  simp [phaseFun]

/-- 位相関数は奇関数。-/
theorem phaseFun_neg (x : ℝ) : phaseFun (-x) = -phaseFun x := by
  simp only [phaseFun]
  rw [show (-x) / 2 = -(x / 2) by ring, Real.arctan_neg]
  ring

/-- 位相関数は [0, ∞) 上で狭義単調（端点 0 を含む）。-/
theorem strictMonoOn_phaseFun_Ici : StrictMonoOn phaseFun (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x _
    exact (hasDerivAt_phaseFun x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact deriv_phaseFun_pos hx

/-- x > 0 では h(x) > 0。-/
theorem phaseFun_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < phaseFun x := by
  have h := strictMonoOn_phaseFun_Ici (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hx.le) hx
  rwa [phaseFun_zero] at h

/-- 位相関数は ℝ 全体で狭義単調。-/
theorem strictMono_phaseFun : StrictMono phaseFun := by
  intro x y hxy
  rcases le_or_lt 0 x with hx0 | hxneg
  · exact strictMonoOn_phaseFun_Ici (Set.mem_Ici.mpr hx0)
      (Set.mem_Ici.mpr (hx0.trans_lt hxy).le) hxy
  · rcases le_or_lt 0 y with hy0 | hyneg
    · have hxp : phaseFun x < 0 := by
        have h1 : 0 < phaseFun (-x) := phaseFun_pos_of_pos (by linarith)
        rw [phaseFun_neg] at h1
        linarith
      have hyp : 0 ≤ phaseFun y := by
        rcases eq_or_lt_of_le hy0 with hy | hy
        · rw [← hy, phaseFun_zero]
        · exact (phaseFun_pos_of_pos hy).le
      linarith
    · have h1 : phaseFun (-y) < phaseFun (-x) :=
        strictMonoOn_phaseFun_Ici (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ -y))
          (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ -x)) (by linarith : -y < -x)
      rw [phaseFun_neg, phaseFun_neg] at h1
      linarith

/-- 位相関数は単射。-/
theorem phaseFun_injective : Function.Injective phaseFun :=
  strictMono_phaseFun.injective

/-- n ≥ 1 なら、位相方程式 h(x) = 2πn の解は区間 (2πn, 2πn + 2π) 内に存在する。-/
theorem exists_phaseFun_eq_of_one_le {n : ℤ} (hn : 1 ≤ n) :
    ∃ x ∈ Set.Ioo ((n : ℝ) * (2 * Real.pi)) ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi),
      phaseFun x = (n : ℝ) * (2 * Real.pi) := by
  have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpi := Real.pi_pos
  set a : ℝ := (n : ℝ) * (2 * Real.pi) with ha_def
  have ha_pos : 0 < a := mul_pos hnRpos (by linarith)
  have hfa : phaseFun a < a := by
    have harg : (0 : ℝ) < Real.arctan (a / 2) := by
      have h := Real.arctan_strictMono (show (0 : ℝ) < a / 2 by linarith)
      rwa [Real.arctan_zero] at h
    simp only [phaseFun]
    linarith
  have hfb : a < phaseFun (a + 2 * Real.pi) := by
    have hlt : Real.arctan ((a + 2 * Real.pi) / 2) < Real.pi / 2 :=
      Real.arctan_lt_pi_div_two _
    simp only [phaseFun]
    linarith
  have hmem : a ∈ Set.Ioo (phaseFun a) (phaseFun (a + 2 * Real.pi)) := ⟨hfa, hfb⟩
  have hIVT := intermediate_value_Ioo (a := a) (b := a + 2 * Real.pi)
    (by linarith) phaseFun_continuous.continuousOn hmem
  obtain ⟨x, hxmem, hx⟩ := hIVT
  exact ⟨x, hxmem, hx⟩

/-- 各 n : ℤ に対して、位相方程式 h(x) = 2πn の解が存在する。-/
theorem exists_phaseFun_eq (n : ℤ) :
    ∃ x, phaseFun x = (n : ℝ) * (2 * Real.pi) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · obtain ⟨x, hxmem, hx⟩ := exists_phaseFun_eq_of_one_le (show 1 ≤ -n by omega)
    refine ⟨-x, ?_⟩
    rw [phaseFun_neg, hx]
    push_cast
    ring
  · subst hn
    refine ⟨0, ?_⟩
    simp [phaseFun]
  · obtain ⟨x, hxmem, hx⟩ := exists_phaseFun_eq_of_one_le (show 1 ≤ n by omega)
    exact ⟨x, hx⟩

/-- 各 n : ℤ に対して、位相方程式 h(x) = 2πn の解は一意に存在する。-/
theorem existsUnique_phaseFun_eq (n : ℤ) :
    ∃! x, phaseFun x = (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨x, hx⟩ := exists_phaseFun_eq n
  exact ⟨x, hx, fun y hy => phaseFun_injective (by rw [hx, hy])⟩

/-- 第 n 零点：h(x) = 2πn の一意な解。-/
noncomputable def phaseZero (n : ℤ) : ℝ := Classical.choose (exists_phaseFun_eq n)

/-- 第 n 零点は位相方程式を満たす。-/
theorem phaseZero_spec (n : ℤ) :
    phaseFun (phaseZero n) = (n : ℝ) * (2 * Real.pi) :=
  Classical.choose_spec (exists_phaseFun_eq n)

/-- 零点の列挙は単射。-/
theorem phaseZero_injective : Function.Injective phaseZero := by
  intro m n hmn
  have h := congrArg phaseFun hmn
  rw [phaseZero_spec, phaseZero_spec] at h
  have hpi : (2 * Real.pi) ≠ 0 := by
    have hpi' := Real.pi_pos
    positivity
  have h2 : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ hpi h
  exact_mod_cast h2

/-- n ≥ 1 の第 n 零点は区間 (2πn, 2πn + 2π) 内にある。-/
theorem phaseZero_mem_Ioo_of_one_le {n : ℤ} (hn : 1 ≤ n) :
    phaseZero n ∈ Set.Ioo ((n : ℝ) * (2 * Real.pi))
      ((n : ℝ) * (2 * Real.pi) + 2 * Real.pi) := by
  obtain ⟨x, hxmem, hx⟩ := exists_phaseFun_eq_of_one_le hn
  have hEq : phaseZero n = x := phaseFun_injective (by rw [phaseZero_spec, hx])
  rwa [hEq]

/-- T₀ = 0 での bump 波束の値：∫₉¹⁰ (C − 9)(10 − C) dC = 1/6。-/
theorem packetPhase_bump_zero_value :
    packetPhase 1 1 9 10 0 1 (bumpG 1 1 9 10) = (1 / 6 : ℂ) := by
  rw [packetPhase_zero (c := 1) (l := 1) (C₁ := 9) (C₂ := 10) (hbar := 1)
    (g := bumpG 1 1 9 10)]
  have hInt : (∫ C in (9 : ℝ)..10, bumpG 1 1 9 10 C / Real.sqrt (Q 1 1 C 1))
      = 1 / 6 := by
    have hcong : ∀ C ∈ Set.uIcc (9 : ℝ) 10,
        bumpG 1 1 9 10 C / Real.sqrt (Q 1 1 C 1) = (C - 9) * (10 - C) := by
      intro C hC
      have h9 : (9 : ℝ) ≤ C := by
        rw [Set.uIcc_of_le (by norm_num : (9 : ℝ) ≤ 10)] at hC
        exact hC.1
      have hC8 : (8 : ℝ) * (1 : ℝ) ^ 2 * 1 < C := by
        calc (8 : ℝ) * (1 : ℝ) ^ 2 * 1 = 8 := by norm_num
        _ < 9 := by norm_num
        _ ≤ C := h9
      rw [bumpG_div_sqrt_eq (c := 1) (l := 1) (C₁ := 9) (C₂ := 10) hC8
        (by norm_num : (0 : ℝ) < 1)]
      simp
    rw [intervalIntegral.integral_congr hcong]
    have hF : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -y ^ 3 / 3 + 19 * y ^ 2 / 2 - 90 * y)
        ((x - 9) * (10 - x)) x := by
      intro x
      have h := ((hasDerivAt_pow 3 x).const_mul (-1 / 3 : ℝ)).add
        (((hasDerivAt_pow 2 x).const_mul (19 / 2 : ℝ)).add
          ((hasDerivAt_id x).const_mul (-90 : ℝ)))
      convert h using 1
      · ext y; simp only [id_eq]; ring
      · push_cast; ring
    have hint : IntervalIntegrable (fun x : ℝ => (x - 9) * (10 - x)) volume (9 : ℝ) 10 := by
      apply Continuous.intervalIntegrable
      continuity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => -y ^ 3 / 3 + 19 * y ^ 2 / 2 - 90 * y)
      (f' := fun x : ℝ => (x - 9) * (10 - x)) (fun x _ => hF x) hint]
    norm_num
  rw [hInt]
  norm_num

/-- T₀ = 0 で bump 波束は 0 でない。-/
theorem packetPhase_bump_ne_zero_at_zero :
    packetPhase 1 1 9 10 0 1 (bumpG 1 1 9 10) ≠ 0 := by
  rw [packetPhase_bump_zero_value]
  norm_num

/-- bump 波束が 0 になるのはちょうど、ある n ≠ 0 に対して h(T₀) = 2πn のとき。-/
theorem packetPhase_bump_zero_iff_exists_int {T₀ : ℝ} :
    packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0
      ↔ ∃ n : ℤ, n ≠ 0 ∧ phaseFun T₀ = (n : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    by_cases hT₀ : T₀ = 0
    · rw [hT₀] at h
      exact absurd h packetPhase_bump_ne_zero_at_zero
    · obtain ⟨n, hn⟩ := phase_condition_iff_exists_int.mp
        ((packetPhase_bump_zero_iff_phase hT₀).mp h)
      refine ⟨n, ?_, hn⟩
      intro hn0
      subst hn0
      simp only [Int.cast_zero, zero_mul] at hn
      have hT : T₀ = 0 := phaseFun_injective (by rw [hn, phaseFun_zero])
      exact hT₀ hT
  · rintro ⟨n, hn0, hfn⟩
    have hT₀ : T₀ ≠ 0 := by
      intro hT
      rw [hT, phaseFun_zero] at hfn
      have hpi : (2 * Real.pi) ≠ 0 := by
        have hpi' := Real.pi_pos
        positivity
      have hnR : (n : ℝ) = 0 := by
        rcases mul_eq_zero.mp hfn.symm with h | h
        · exact h
        · exact absurd h hpi
      exact hn0 (by exact_mod_cast hnR)
    exact (packetPhase_bump_zero_iff_phase hT₀).mpr
      (phase_condition_iff_exists_int.mpr ⟨n, hfn⟩)

/-- bump 波束の零点集合は、第 n 零点（n ≠ 0）の像に一致する。-/
theorem packetPhase_bump_zero_set_eq :
    {T₀ | packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0}
      = phaseZero '' {n : ℤ | n ≠ 0} := by
  ext T₀
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨n, hn0, hfn⟩ := packetPhase_bump_zero_iff_exists_int.mp h
    refine ⟨n, hn0, ?_⟩
    exact (phaseFun_injective (by rw [phaseZero_spec, hfn])).symm
  · rintro ⟨n, hn0, rfl⟩
    exact packetPhase_bump_zero_iff_exists_int.mpr ⟨n, hn0, phaseZero_spec n⟩

/-- bump 波束の零点集合は可算である。-/
theorem packetPhase_bump_zero_set_countable :
    Set.Countable {T₀ | packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0} := by
  rw [packetPhase_bump_zero_set_eq]
  exact (Set.to_countable _).image _

/-- bump 波束の零点集合は測度 0 である。-/
theorem packetPhase_bump_zero_set_measure_zero :
    volume {T₀ : ℝ | packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0} = 0 :=
  packetPhase_bump_zero_set_countable.measure_zero volume

/-- ほとんどすべての T₀ で bump 波束は 0 でない。-/
theorem packetPhase_bump_ae_ne_zero :
    ∀ᵐ T₀ ∂(volume : MeasureTheory.Measure ℝ),
      packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) ≠ 0 := by
  have h := packetPhase_bump_zero_set_countable.ae_not_mem volume
  filter_upwards [h] with T₀ hT₀
  exact hT₀

end CFT.WDWWavePacketZeros
