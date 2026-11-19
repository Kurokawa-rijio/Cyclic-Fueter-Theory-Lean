/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第九段：位相条件の解の一意性）。

  第八段で h(x) = x − 2 arctan(x/2) − 2π の符号変化から、(2π, 10) 内に
  x* − 2 arctan(x*/2) = 2π なる点の存在を示し、c = ℓ = 1、C ∈ [9, 10] の bump
  波束が T₀* = x* で Ψ_f = 0 になることを証明した。ここでは位相関数
  h(x) = x − 2 arctan(x/2) の導関数 h′(x) = 1 − 1/(1 + (x/2)²) > 0（x > 0）
  から h が (0, ∞) 上で狭義単調であることを示し（`strictMonoOn_phaseFun`）、
  位相条件 e^{−ix} = (2 − ix)/(2 + ix) が h(x) = 2πn（n : ℤ）と同値であること
  （`phase_condition_iff_exists_int`）と合わせて、(2π, 10) 内の bump 波束の
  零点がちょうど一つであること（∃!、 `existsUnique_packetPhase_bump_zero`）を
  証明する。零点集合の離散性・可算性への第一歩であり、「ほとんどすべての T₀
  での非消滅」への組み替えの土台になる。
  残り：各 n に対する零点の存在（可算無限個の零点の列挙）と、零点集合が
  可算であることの定式化。
-/
import CFT.Quantum.WDWWavePacketZero

namespace CFT.WDWWavePacketZeroUnique

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay CFT.WDWWavePacketDecayExplicit
  CFT.WDWWavePacketClosedForm CFT.WDWWavePacketZero
  MeasureTheory intervalIntegral

/-- 位相関数 h(x) = x − 2 arctan(x/2)。-/
noncomputable def phaseFun (x : ℝ) : ℝ := x - 2 * Real.arctan (x / 2)

/-- 位相関数の微分：h′(x) = 1 − 1/(1 + (x/2)²)。-/
theorem hasDerivAt_phaseFun (x : ℝ) :
    HasDerivAt phaseFun (1 - 1 / (1 + (x / 2) ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.arctan (y / 2))
      (1 / (1 + (x / 2) ^ 2) * (1 / 2)) x := by
    have h := (Real.hasDerivAt_arctan (x / 2)).comp x ((hasDerivAt_id x).div_const 2)
    convert h using 1
  have h2 : HasDerivAt (fun y : ℝ => 2 * Real.arctan (y / 2))
      (2 * (1 / (1 + (x / 2) ^ 2) * (1 / 2))) x := h1.const_mul 2
  have h3 : HasDerivAt (fun y : ℝ => y - 2 * Real.arctan (y / 2))
      (1 - 2 * (1 / (1 + (x / 2) ^ 2) * (1 / 2))) x :=
    (hasDerivAt_id x).sub h2
  have hder : (1 : ℝ) - 2 * (1 / (1 + (x / 2) ^ 2) * (1 / 2))
      = 1 - 1 / (1 + (x / 2) ^ 2) := by
    have hD : (1 : ℝ) + (x / 2) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hder] at h3
  exact h3

/-- 位相関数の導関数の明示形。-/
theorem deriv_phaseFun (x : ℝ) : deriv phaseFun x = 1 - 1 / (1 + (x / 2) ^ 2) :=
  (hasDerivAt_phaseFun x).deriv

/-- x > 0 では h′(x) > 0。-/
theorem deriv_phaseFun_pos {x : ℝ} (hx : 0 < x) : 0 < deriv phaseFun x := by
  rw [deriv_phaseFun]
  have hsq : (0 : ℝ) < (x / 2) ^ 2 := pow_pos (by linarith) 2
  have h1 : (1 : ℝ) / (1 + (x / 2) ^ 2) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

/-- 位相関数は (0, ∞) 上で狭義単調。-/
theorem strictMonoOn_phaseFun : StrictMonoOn phaseFun (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x _
    exact (hasDerivAt_phaseFun x).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Ioi] at hx
    exact deriv_phaseFun_pos hx

/-- 位相関数は (0, ∞) 上で単射。-/
theorem phaseFun_injOn : Set.InjOn phaseFun (Set.Ioi 0) :=
  strictMonoOn_phaseFun.injOn

/-- 位相方程式 h(x) = 2π の解は (2π, 10) 内にちょうど一つ存在する。-/
theorem existsUnique_arctan_phase :
    ∃! x ∈ Set.Ioo (2 * Real.pi) 10, x - 2 * Real.arctan (x / 2) = 2 * Real.pi := by
  obtain ⟨x₀, hx₀mem, hx₀⟩ := exists_arctan_phase
  refine ⟨x₀, ⟨hx₀mem, hx₀⟩, ?_⟩
  intro y ⟨hymem, hy⟩
  have hIoi₀ : x₀ ∈ Set.Ioi (0 : ℝ) := by
    show (0 : ℝ) < x₀
    have hpi := Real.pi_pos
    linarith [hx₀mem.1]
  have hIoi_y : y ∈ Set.Ioi (0 : ℝ) := by
    show (0 : ℝ) < y
    have hpi := Real.pi_pos
    linarith [hymem.1]
  have hEq : phaseFun x₀ = phaseFun y := by
    simp only [phaseFun]
    linarith [hx₀, hy]
  exact (phaseFun_injOn hIoi₀ hIoi_y hEq).symm

/-- 位相条件は h(x) = 2πn（n : ℤ）と同値。-/
theorem phase_condition_iff_exists_int {x : ℝ} :
    Complex.exp (-Complex.I * (x : ℂ)) = (2 - Complex.I * (x : ℂ)) / (2 + Complex.I * (x : ℂ))
      ↔ ∃ n : ℤ, phaseFun x = n * (2 * Real.pi) := by
  have h2 : (2 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hkey := exp_two_mul_I_arctan_mul x
  have hmul : Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
        * Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ)) = 1 := by
    rw [← Complex.exp_add,
      show (-2 : ℂ) * Complex.I * (Real.arctan (x / 2) : ℂ)
        + 2 * Complex.I * (Real.arctan (x / 2) : ℂ) = 0 by ring,
      Complex.exp_zero]
  have hdiv : (2 - Complex.I * (x : ℂ)) / (2 + Complex.I * (x : ℂ))
      = Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ)) := by
    rw [div_eq_iff h2]
    calc (2 - Complex.I * (x : ℂ))
        = (Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
          * Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ)))
          * (2 - Complex.I * (x : ℂ)) := by rw [hmul, one_mul]
      _ = Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
          * (Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ))
            * (2 - Complex.I * (x : ℂ))) := by rw [mul_assoc]
      _ = Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
          * (2 + Complex.I * (x : ℂ)) := by rw [hkey]
  constructor
  · intro hphase
    rw [hdiv] at hphase
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hphase
    refine ⟨-n, ?_⟩
    -- hn の両辺は (実数 : ℂ) * I の形なので、I で割って実数の等式を得る。
    have hI : ((-x : ℝ) : ℂ) * Complex.I
        = ((-2 * Real.arctan (x / 2) + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
          * Complex.I := by
      have h := hn
      push_cast at h ⊢
      linear_combination h
    have key : (-x : ℝ) = -2 * Real.arctan (x / 2) + (n : ℝ) * (2 * Real.pi) :=
      Complex.ofReal_inj.mp (mul_right_cancel₀ Complex.I_ne_zero hI)
    simp only [phaseFun]
    push_cast at key ⊢
    linarith [key]
  · rintro ⟨n, hn⟩
    rw [hdiv]
    have hxeq : (x : ℂ)
        = 2 * (Real.arctan (x / 2) : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      have hxr : x = 2 * Real.arctan (x / 2) + (n : ℝ) * (2 * Real.pi) := by
        have h := hn
        simp only [phaseFun] at h
        push_cast at h ⊢
        linarith [h]
      have hxc : (x : ℂ)
          = ((2 * Real.arctan (x / 2) + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
        exact_mod_cast hxr
      rw [hxc]
      push_cast
      ring
    have harg : (-Complex.I * (x : ℂ))
        = (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
          + ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hxeq]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- x ∈ (2π, 10) なら h(x) ∈ (π, 10 − π/2)。-/
theorem phaseFun_mem_Ioo_of_mem {x : ℝ} (hx : x ∈ Set.Ioo (2 * Real.pi) 10) :
    Real.pi < phaseFun x ∧ phaseFun x < 10 - Real.pi / 2 := by
  have h1 : Real.arctan (x / 2) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have h2 : Real.pi / 4 < Real.arctan (x / 2) := by
    have hlt : (1 : ℝ) < x / 2 := by
      have hpi : (2 : ℝ) < 2 * Real.pi := by
        have h1 := Real.pi_gt_three
        linarith
      linarith [hx.1]
    have h := Real.arctan_strictMono hlt
    rwa [Real.arctan_one] at h
  simp only [phaseFun]
  constructor <;> linarith [hx.1, hx.2, h1, h2]

/-- x ∈ (2π, 10) で位相条件を満たすなら h(x) = 2π（n = 1 のみが範囲に入る）。-/
theorem phaseFun_eq_two_pi_of_phase {x : ℝ} (hx : x ∈ Set.Ioo (2 * Real.pi) 10)
    (hphase : Complex.exp (-Complex.I * (x : ℂ))
      = (2 - Complex.I * (x : ℂ)) / (2 + Complex.I * (x : ℂ))) :
    phaseFun x = 2 * Real.pi := by
  obtain ⟨n, hn⟩ := phase_condition_iff_exists_int.mp hphase
  obtain ⟨hlo, hhi⟩ := phaseFun_mem_Ioo_of_mem hx
  have hpi1 : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi2 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hn1 : (1 : ℤ) ≤ n := by
    by_contra hlt
    push_neg at hlt
    have hnle : (n : ℝ) ≤ 0 := by exact_mod_cast (by omega : n ≤ 0)
    have hle : (n : ℝ) * (2 * Real.pi) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnle (by linarith [Real.pi_pos])
    rw [← hn] at hle
    linarith [hlo, Real.pi_pos]
  have hn2 : n ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hnge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    have hge : 4 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
      have h := mul_le_mul_of_nonneg_right hnge
        (show (0 : ℝ) ≤ 2 * Real.pi by linarith [Real.pi_pos])
      linarith [h]
    rw [← hn] at hge
    linarith [hhi, hpi1]
  have hn_eq : n = 1 := by omega
  rw [hn_eq] at hn
  push_cast at hn
  simpa using hn

/-- bump 波束が 0 になるのはちょうど位相条件のとき。-/
theorem packetPhase_bump_zero_iff_phase {T₀ : ℝ} (hT₀ : T₀ ≠ 0) :
    packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0
      ↔ Complex.exp (-Complex.I * (T₀ : ℂ))
        = (2 - Complex.I * (T₀ : ℂ)) / (2 + Complex.I * (T₀ : ℂ)) := by
  have hEq : packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10)
      = ∫ C in (9 : ℝ)..10, ((C : ℂ) - ((9 : ℝ) : ℂ)) * (((10 : ℝ) : ℂ) - (C : ℂ))
          * Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ)) := by
    have h := packetPhase_bump_closed_form (c := 1) (l := 1)
      (by norm_num : (9 : ℝ) < 10) (by norm_num : 8 * (1 : ℝ) ^ 2 * 1 < 9)
      (by norm_num : (0 : ℝ) < 1) hT₀ (by norm_num : (1 : ℝ) ≠ 0)
    have h2 := bumpPoly_integral_closed_form (C₁ := (9 : ℝ)) (C₂ := (10 : ℝ)) (θ := T₀) hT₀
    rw [h, h2]
    simp
  have hL : ((10 : ℝ) - 9) = 1 := by norm_num
  rw [hEq, bumpPoly_integral_eq_zero_iff hT₀, hL]
  norm_num

/-- bump 波束の零点は (2π, 10) 内にちょうど一つ存在する。-/
theorem existsUnique_packetPhase_bump_zero :
    ∃! T₀ ∈ Set.Ioo (2 * Real.pi) 10,
      packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0 := by
  obtain ⟨x₀, hx₀mem, hx₀⟩ := exists_packetPhase_bump_zero
  refine ⟨x₀, ⟨hx₀mem, hx₀⟩, ?_⟩
  intro y ⟨hymem, hy⟩
  have hx₀0 : x₀ ≠ 0 := by
    have hpi := Real.pi_pos
    linarith [hx₀mem.1]
  have hy0 : y ≠ 0 := by
    have hpi := Real.pi_pos
    linarith [hymem.1]
  have hfx₀ : phaseFun x₀ = 2 * Real.pi :=
    phaseFun_eq_two_pi_of_phase hx₀mem ((packetPhase_bump_zero_iff_phase hx₀0).mp hx₀)
  have hfy : phaseFun y = 2 * Real.pi :=
    phaseFun_eq_two_pi_of_phase hymem ((packetPhase_bump_zero_iff_phase hy0).mp hy)
  have hIoi₀ : x₀ ∈ Set.Ioi (0 : ℝ) := by
    show (0 : ℝ) < x₀
    have hpi := Real.pi_pos
    linarith [hx₀mem.1]
  have hIoi_y : y ∈ Set.Ioi (0 : ℝ) := by
    show (0 : ℝ) < y
    have hpi := Real.pi_pos
    linarith [hymem.1]
  exact (phaseFun_injOn hIoi₀ hIoi_y (by rw [hfx₀, hfy])).symm

end CFT.WDWWavePacketZeroUnique
