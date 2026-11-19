/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第八段：零点の存在の中間値の定理による証明）。

  第七段で bump 波束の積分が 0 になる条件がちょうど位相条件
    e^{−iLθ} = (2 − iθL)/(2 + iθL)
  であることを示した（`bumpPoly_integral_eq_zero_iff`）。L = 1 の場合、この条件は
  x − 2 arctan(x/2) = 2π（x = θ）に帰着する。ここでは
  h(x) = x − 2 arctan(x/2) − 2π の符号変化（h(2π) = −2 arctan π < 0、h(10) > 0）
  から中間値の定理で x* ∈ (2π, 10) で h(x*) = 0 なる点の存在を示し、位相条件を経て
  c = ℓ = 1、C ∈ [9, 10] の bump 波束が T₀* = x*（ħ = 1）で Ψ_f = 0 になることを
  証明する（`exists_packetPhase_bump_zero`）。すなわち「すべての大きな |T₀| に対する
  非消滅」はこの bump 重みでは Lean でも反証された（第七段では数値診断のみだった）。
  残り：非消滅の主張の組み替え（「ほとんどすべての T₀ での非消滅」や
  「零点の列挙・密度」へ）。
-/
import CFT.Quantum.WDWWavePacketClosedForm

namespace CFT.WDWWavePacketZero

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay CFT.WDWWavePacketDecayExplicit
  CFT.WDWWavePacketClosedForm
  MeasureTheory intervalIntegral

/-- arctan の倍角の余弦。-/
theorem cos_two_mul_arctan (x : ℝ) :
    Real.cos (2 * Real.arctan (x / 2)) = (1 - (x / 2) ^ 2) / (1 + (x / 2) ^ 2) := by
  have hs : (0 : ℝ) < Real.sqrt (1 + (x / 2) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (Real.sqrt (1 + (x / 2) ^ 2)) ^ 2 = 1 + (x / 2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hD : (1 : ℝ) + (x / 2) ^ 2 ≠ 0 := by positivity
  rw [Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow]
  field_simp [hs.ne', hD]
  ring

/-- arctan の倍角の正弦。-/
theorem sin_two_mul_arctan (x : ℝ) :
    Real.sin (2 * Real.arctan (x / 2)) = x / (1 + (x / 2) ^ 2) := by
  have hs : (0 : ℝ) < Real.sqrt (1 + (x / 2) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (Real.sqrt (1 + (x / 2) ^ 2)) ^ 2 = 1 + (x / 2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hD : (1 : ℝ) + (x / 2) ^ 2 ≠ 0 := by positivity
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp [hs.ne', hD]
  ring

/-- 鍵となる恒等式：e^{2iφ}·(2 − ix) = 2 + ix（φ = arctan(x/2)）。-/
theorem exp_two_mul_I_arctan_mul (x : ℝ) :
    Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ))
      * (2 - Complex.I * (x : ℂ)) = 2 + Complex.I * (x : ℂ) := by
  have hD : (1 : ℝ) + (x / 2) ^ 2 ≠ 0 := by positivity
  have hDc : ((1 + (x / 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD
  have hexp : Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ))
      = (Real.cos (2 * Real.arctan (x / 2)) : ℂ)
        + (Real.sin (2 * Real.arctan (x / 2)) : ℂ) * Complex.I := by
    rw [show (2 : ℂ) * Complex.I * (Real.arctan (x / 2) : ℂ)
        = ((2 * Real.arctan (x / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp, cos_two_mul_arctan, sin_two_mul_arctan,
    Complex.ofReal_div, Complex.ofReal_div,
    div_mul_eq_mul_div, ← add_div, div_mul_eq_mul_div, div_eq_iff hDc]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- 位相条件の arctan 表示：x = 2π + 2 arctan(x/2) なら
    e^{−ix} = (2 − ix)/(2 + ix)。-/
theorem exp_neg_I_mul_eq_div_of_arctan {x : ℝ}
    (hx : x = 2 * Real.pi + 2 * Real.arctan (x / 2)) :
    Complex.exp (-Complex.I * (x : ℂ))
      = (2 - Complex.I * (x : ℂ)) / (2 + Complex.I * (x : ℂ)) := by
  have h2 : (2 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hkey := exp_two_mul_I_arctan_mul x
  have h2pi : Complex.exp (-2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [show (-2 : ℂ) * (Real.pi : ℂ) * Complex.I = -(2 * (Real.pi : ℂ) * Complex.I)
        by ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hexp : Complex.exp (-Complex.I * (x : ℂ))
      = Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ)) := by
    have harg : (-Complex.I * (x : ℂ))
        = -2 * (Real.pi : ℂ) * Complex.I
          + -2 * Complex.I * (Real.arctan (x / 2) : ℂ) := by
      conv_lhs => rw [hx]
      push_cast
      ring
    rw [harg, Complex.exp_add, h2pi, one_mul]
  have hmul : Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
      * Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ)) = 1 := by
    rw [← Complex.exp_add,
      show (-2 : ℂ) * Complex.I * (Real.arctan (x / 2) : ℂ)
        + 2 * Complex.I * (Real.arctan (x / 2) : ℂ) = 0 by ring,
      Complex.exp_zero]
  rw [hexp, eq_div_iff h2]
  calc Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
        * (2 + Complex.I * (x : ℂ))
      = Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
        * (Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ))
          * (2 - Complex.I * (x : ℂ))) := by rw [hkey]
    _ = (Complex.exp (-2 * Complex.I * (Real.arctan (x / 2) : ℂ))
        * Complex.exp (2 * Complex.I * (Real.arctan (x / 2) : ℂ)))
        * (2 - Complex.I * (x : ℂ)) := (mul_assoc _ _ _).symm
    _ = 2 - Complex.I * (x : ℂ) := by rw [hmul, one_mul]

/-- 中間値の定理：h(x) = x − 2 arctan(x/2) − 2π は (2π, 10) 内に零点を持つ。-/
theorem exists_arctan_phase :
    ∃ x ∈ Set.Ioo (2 * Real.pi) 10, x - 2 * Real.arctan (x / 2) = 2 * Real.pi := by
  have hcont : Continuous (fun x : ℝ => x - 2 * Real.arctan (x / 2) - 2 * Real.pi) := by
    apply Continuous.sub
    · apply Continuous.sub
      · exact continuous_id'
      · exact continuous_const.mul (Real.continuous_arctan.comp (continuous_id.div_const 2))
    · exact continuous_const
  have h2pi : (2 * Real.pi) - 2 * Real.arctan ((2 * Real.pi) / 2) - 2 * Real.pi
      = -2 * Real.arctan Real.pi := by
    rw [show (2 * Real.pi) / 2 = Real.pi by ring]
    ring
  have h2pi_neg : (2 * Real.pi) - 2 * Real.arctan ((2 * Real.pi) / 2) - 2 * Real.pi
      < 0 := by
    rw [h2pi]
    have hpos : 0 < Real.arctan Real.pi := by
      have h := Real.arctan_strictMono Real.pi_pos
      rwa [Real.arctan_zero] at h
    linarith
  have h10 : 0 < (10 : ℝ) - 2 * Real.arctan (10 / 2) - 2 * Real.pi := by
    have harctan5 : Real.arctan 5 < Real.pi / 2 := Real.arctan_lt_pi_div_two 5
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    have h105 : (10 : ℝ) / 2 = 5 := by norm_num
    rw [h105]
    linarith
  have hmem : (0 : ℝ) ∈ Set.Ioo
      ((2 * Real.pi) - 2 * Real.arctan ((2 * Real.pi) / 2) - 2 * Real.pi)
      ((10 : ℝ) - 2 * Real.arctan (10 / 2) - 2 * Real.pi) := ⟨h2pi_neg, h10⟩
  have hIVT := intermediate_value_Ioo (a := 2 * Real.pi) (b := 10)
    (by have hpi := Real.pi_lt_d4; linarith) hcont.continuousOn hmem
  obtain ⟨x, hxmem, hx0⟩ := hIVT
  have hx0' : x - 2 * Real.arctan (x / 2) - 2 * Real.pi = 0 := hx0
  exact ⟨x, hxmem, by linarith⟩

/-- 位相条件を満たす x では bump 波束の多項式積分は 0 になる。-/
theorem bumpPoly_integral_eq_zero_of_arctan_phase {x : ℝ} (hx0 : x ≠ 0)
    (hx : x = 2 * Real.pi + 2 * Real.arctan (x / 2)) :
    (∫ C in (9 : ℝ)..10, ((C : ℂ) - ((9 : ℝ) : ℂ)) * (((10 : ℝ) : ℂ) - (C : ℂ))
        * Complex.exp (-Complex.I * (C : ℂ) * (x : ℂ))) = 0 := by
  rw [bumpPoly_integral_eq_zero_iff hx0]
  have hphase := exp_neg_I_mul_eq_div_of_arctan hx
  have hL : ((10 : ℝ) - 9) = 1 := by norm_num
  rw [hL]
  push_cast
  simp only [mul_one]
  exact hphase

/-- 零点の存在：c = ℓ = 1、C ∈ [9, 10] の bump 波束は、ある T₀* ∈ (2π, 10)
    （ħ = 1）で Ψ_f(T₀*) = 0 になる。-/
theorem exists_packetPhase_bump_zero :
    ∃ T₀ ∈ Set.Ioo (2 * Real.pi) 10,
      packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10) = 0 := by
  obtain ⟨x, hxmem, hxeq⟩ := exists_arctan_phase
  refine ⟨x, hxmem, ?_⟩
  have hx0 : x ≠ 0 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith [hxmem.1]
  have hphase := exp_neg_I_mul_eq_div_of_arctan
    (show x = 2 * Real.pi + 2 * Real.arctan (x / 2) by linarith)
  have h2 : (2 : ℂ) + Complex.I * (x : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hNum : (Complex.I * (x : ℂ) - 2) * Complex.exp (-Complex.I * 9 * (x : ℂ))
      + (Complex.I * (x : ℂ) + 2) * Complex.exp (-Complex.I * 10 * (x : ℂ)) = 0 := by
    have he10 : Complex.exp (-Complex.I * 10 * (x : ℂ))
        = Complex.exp (-Complex.I * 9 * (x : ℂ))
          * Complex.exp (-Complex.I * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc (Complex.I * (x : ℂ) - 2) * Complex.exp (-Complex.I * 9 * (x : ℂ))
          + (Complex.I * (x : ℂ) + 2) * Complex.exp (-Complex.I * 10 * (x : ℂ))
        = Complex.exp (-Complex.I * 9 * (x : ℂ))
          * ((Complex.I * (x : ℂ) - 2)
            + (Complex.I * (x : ℂ) + 2) * Complex.exp (-Complex.I * (x : ℂ))) := by
          rw [he10]; ring
      _ = Complex.exp (-Complex.I * 9 * (x : ℂ))
          * ((Complex.I * (x : ℂ) - 2)
            + (Complex.I * (x : ℂ) + 2)
              * ((2 - Complex.I * (x : ℂ)) / (2 + Complex.I * (x : ℂ)))) := by
          rw [hphase]
      _ = 0 := by
          rw [show (Complex.I * (x : ℂ) + 2) = (2 + Complex.I * (x : ℂ)) by ring,
            mul_div_assoc', mul_div_cancel_left₀ _ h2]
          ring
  rw [packetPhase_bump_example_closed_form hx0 (by norm_num : (1 : ℝ) ≠ 0)]
  simp only [div_one]
  rw [hNum]
  simp

end CFT.WDWWavePacketZero
