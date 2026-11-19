/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第七段：bump 波束の積分の閉形式と、零点の条件）。

  第五段・第六段で bump 重み g(C) = (C − C₁)(C₂ − C)·√(C − 8c²ℓ) に対する
  減衰評価 ‖Ψ_f(T₀)‖ ≤ (C₂ − C₁)²·|ħ|/(√ℓ·|T₀|) を得た。ここでは被積分関数が
  多項式 f(C) = (C − C₁)(C₂ − C)/√ℓ になることを使い、積分そのものの閉形式

    ∫_{C₁}^{C₂} (C − C₁)(C₂ − C) e^{−iCθ} dC
      = ((iθL − 2) e^{−iC₁θ} + (iθL + 2) e^{−iC₂θ}) / (−iθ³),  L = C₂ − C₁,

  を原始関数による FTC で証明する（`bumpPoly_integral_closed_form`）。さらに
  積分が 0 になる条件がちょうど位相条件

    e^{−iLθ} = (2 − iθL)/(2 + iθL)

  であること（`bumpPoly_integral_eq_zero_iff`）を示す。

  数値診断（証明ではない）：L = 1 の場合、この位相条件は x − 2 arctan(x/2) = 2π
  （x = θL）に帰着し、θ* ≈ 8.9868189158 が最初の解（mpmath で確認。直接積分も
  ~10⁻³⁸ で 0）。すなわち c = ℓ = 1、C ∈ [9, 10] の bump 波束は
  T₀* ≈ 8.987·ħ で Ψ_f = 0 になる。したがって「すべての大きな |T₀| に対する
  非消滅」はこの bump 重みでは成り立たない（反証）。残る問いは「ほとんどすべての
  T₀ での非消滅」や「零点の列挙・密度」への組み替えである。零点の存在の Lean に
  よる証明（中間値の定理による）は次の段に残る。
-/
import CFT.Quantum.WDWWavePacketDecayExplicit

namespace CFT.WDWWavePacketClosedForm

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay CFT.WDWWavePacketDecayExplicit
  MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 原始関数の多項式部分 P(C)。
    P′(C) − iθ·P(C) = −iθ³·(C − C₁)(C₂ − C) を満たすように選んだ二次式。-/
def bumpAntiderivPoly (C₁ C₂ θ C : ℝ) : ℂ :=
  (-((θ : ℂ) * (θ : ℂ))) * ((C : ℂ) * (C : ℂ))
    + (((θ : ℂ) * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2 * Complex.I * (θ : ℂ)) * (C : ℂ))
    + (-((θ : ℂ) * (θ : ℂ) * (C₁ : ℂ) * (C₂ : ℂ)) - Complex.I * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2)

/-- 多項式部分の微分。-/
theorem hasDerivAt_bumpAntiderivPoly (C₁ C₂ θ C : ℝ) :
    HasDerivAt (fun C : ℝ => bumpAntiderivPoly C₁ C₂ θ C)
      (2 * (-((θ : ℂ) * (θ : ℂ))) * (C : ℂ)
        + ((θ : ℂ) * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2 * Complex.I * (θ : ℂ))) C := by
  have hC : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 C := (hasDerivAt_id (C : ℂ)).comp_ofReal
  have hC2 : HasDerivAt (fun x : ℝ => (x : ℂ) * (x : ℂ)) (1 * (C : ℂ) + (C : ℂ) * 1) C :=
    hC.mul hC
  have h1 := hC2.const_mul (-((θ : ℂ) * (θ : ℂ)))
  have h2 := hC.const_mul
    ((θ : ℂ) * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2 * Complex.I * (θ : ℂ))
  have h3 := hasDerivAt_const C
    (-((θ : ℂ) * (θ : ℂ) * (C₁ : ℂ) * (C₂ : ℂ)) - Complex.I * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2)
  have h := (h1.add h2).add h3
  convert h using 1
  ring

/-- 原始関数の鍵となる代数恒等式：P′(C) − iθ·P(C) = −iθ³·(C − C₁)(C₂ − C)。-/
theorem bumpAntiderivPoly_key (C₁ C₂ θ C : ℝ) :
    (2 * (-((θ : ℂ) * (θ : ℂ))) * (C : ℂ)
        + ((θ : ℂ) * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2 * Complex.I * (θ : ℂ)))
      - Complex.I * (θ : ℂ) * bumpAntiderivPoly C₁ C₂ θ C
      = (((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3) := by
  simp only [bumpAntiderivPoly]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- 閉形式の原始関数：G(C) = e^{−iCθ}·P(C)。微分は
    G′(C) = e^{−iCθ}·(C − C₁)(C₂ − C)·(−iθ³) になる（分母を払った形）。-/
def bumpAntideriv (C₁ C₂ θ C : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) * bumpAntiderivPoly C₁ C₂ θ C

/-- 原始関数の微分は被積分関数に (−iθ³) を掛けたもの。-/
theorem hasDerivAt_bumpAntideriv (C₁ C₂ θ C : ℝ) :
    HasDerivAt (fun C : ℝ => bumpAntideriv C₁ C₂ θ C)
      (Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
        * ((((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3))) C := by
  have hP := hasDerivAt_bumpAntiderivPoly C₁ C₂ θ C
  have hG := (hasDerivAt_exp_neg_I_mul θ C).mul hP
  convert hG using 1
  have hkey := bumpAntiderivPoly_key C₁ C₂ θ C
  calc Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
        * ((((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3))
      = Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
        * ((2 * (-((θ : ℂ) * (θ : ℂ))) * (C : ℂ)
          + ((θ : ℂ) * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2 * Complex.I * (θ : ℂ)))
          - Complex.I * (θ : ℂ) * bumpAntiderivPoly C₁ C₂ θ C) := by rw [hkey]
    _ = (-Complex.I * (θ : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)))
        * bumpAntiderivPoly C₁ C₂ θ C
        + Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
          * (2 * (-((θ : ℂ) * (θ : ℂ))) * (C : ℂ)
            + ((θ : ℂ) * (θ : ℂ) * ((C₁ : ℂ) + (C₂ : ℂ)) + 2 * Complex.I * (θ : ℂ))) := by
        ring

/-- bump 波束の積分の閉形式：多項式 × 振動因子の区間積分は端点の指数関数の
    一次結合を −iθ³ で割ったものになる。-/
theorem bumpPoly_integral_closed_form {C₁ C₂ θ : ℝ} (hθ : θ ≠ 0) :
    (∫ C in C₁..C₂, ((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))
        * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)))
      = ((Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) - 2)
          * Complex.exp (-Complex.I * (C₁ : ℂ) * (θ : ℂ))
        + (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
          * Complex.exp (-Complex.I * (C₂ : ℂ) * (θ : ℂ)))
        / (-Complex.I * (θ : ℂ) ^ 3) := by
  have hne : (-Complex.I * (θ : ℂ) ^ 3) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (pow_ne_zero 3 (by exact_mod_cast hθ))
  have hderiv : ∀ C ∈ Set.uIcc C₁ C₂, HasDerivAt (fun C : ℝ => bumpAntideriv C₁ C₂ θ C)
      (Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
        * ((((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3))) C :=
    fun C _ => hasDerivAt_bumpAntideriv C₁ C₂ θ C
  have hint : IntervalIntegrable
      (fun C : ℝ => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
        * ((((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3)))
      volume C₁ C₂ := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hInt : (∫ C in C₁..C₂, Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
        * ((((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3)))
      = (∫ C in C₁..C₂, ((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))
          * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3) := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro C _
    ring
  have hP1 : bumpAntiderivPoly C₁ C₂ θ C₁
      = 2 - Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) := by
    simp only [bumpAntiderivPoly]
    push_cast
    ring
  have hP2 : bumpAntiderivPoly C₁ C₂ θ C₂
      = 2 + Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) := by
    simp only [bumpAntiderivPoly]
    push_cast
    ring
  have hmul : (∫ C in C₁..C₂, ((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))
        * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) * (-Complex.I * (θ : ℂ) ^ 3)
      = (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) - 2)
          * Complex.exp (-Complex.I * (C₁ : ℂ) * (θ : ℂ))
        + (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
          * Complex.exp (-Complex.I * (C₂ : ℂ) * (θ : ℂ)) := by
    rw [← hInt, hFTC]
    simp only [bumpAntideriv, hP1, hP2]
    ring
  rw [eq_div_iff hne]
  exact hmul

/-- bump 波束の積分が 0 になる条件：ちょうど位相条件
    e^{−iLθ} = (2 − iθL)/(2 + iθL)（L = C₂ − C₁）のとき。-/
theorem bumpPoly_integral_eq_zero_iff {C₁ C₂ θ : ℝ} (hθ : θ ≠ 0) :
    (∫ C in C₁..C₂, ((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))
        * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) = 0
      ↔ Complex.exp (-Complex.I * ((C₂ - C₁ : ℝ) : ℂ) * (θ : ℂ))
        = (2 - Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ))
          / (2 + Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ)) := by
  have hne : (-Complex.I * (θ : ℂ) ^ 3) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (pow_ne_zero 3 (by exact_mod_cast hθ))
  have h2 : (2 : ℂ) + Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have he2 : Complex.exp (-Complex.I * (C₂ : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * (C₁ : ℂ) * (θ : ℂ))
        * Complex.exp (-Complex.I * ((C₂ - C₁ : ℝ) : ℂ) * (θ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [bumpPoly_integral_closed_form hθ, div_eq_zero_iff, or_iff_left hne]
  have hN : (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) - 2)
        * Complex.exp (-Complex.I * (C₁ : ℂ) * (θ : ℂ))
        + (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
          * Complex.exp (-Complex.I * (C₂ : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * (C₁ : ℂ) * (θ : ℂ))
        * ((Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) - 2)
          + (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
            * Complex.exp (-Complex.I * ((C₂ - C₁ : ℝ) : ℂ) * (θ : ℂ))) := by
    rw [he2]
    ring
  rw [hN, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
  constructor
  · intro hb
    rw [eq_div_iff h2]
    linear_combination hb
  · intro hz
    rw [hz]
    have hcan : (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
          * ((2 - Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ))
            / (2 + Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ)))
        = 2 - Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) := by
      rw [show (Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
          = (2 + Complex.I * (θ : ℂ) * ((C₂ - C₁ : ℝ) : ℂ)) by ring,
        mul_div_assoc', mul_div_cancel_left₀ _ h2]
    rw [hcan]
    ring

/-- 位相つき bump 波束の閉形式：θ = T₀/ħ として上の閉形式を √ℓ で割ったもの。-/
theorem packetPhase_bump_closed_form {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hT₀ : T₀ ≠ 0) (hhbar : hbar ≠ 0) :
    packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)
      = (((Complex.I * ((T₀ / hbar : ℝ) : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) - 2)
          * Complex.exp (-Complex.I * (C₁ : ℂ) * ((T₀ / hbar : ℝ) : ℂ))
        + (Complex.I * ((T₀ / hbar : ℝ) : ℂ) * ((C₂ - C₁ : ℝ) : ℂ) + 2)
          * Complex.exp (-Complex.I * (C₂ : ℂ) * ((T₀ / hbar : ℝ) : ℂ)))
        / (-Complex.I * ((T₀ / hbar : ℝ) : ℂ) ^ 3)) / (Real.sqrt l : ℂ) := by
  have hθ : (T₀ / hbar : ℝ) ≠ 0 := div_ne_zero hT₀ hhbar
  have hsqrt : (Real.sqrt l : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hl).ne'
  have hEq : packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)
      = (∫ C in C₁..C₂, ((C : ℂ) - (C₁ : ℂ)) * ((C₂ : ℂ) - (C : ℂ))
          * Complex.exp (-Complex.I * (C : ℂ) * ((T₀ / hbar : ℝ) : ℂ)))
        / (Real.sqrt l : ℂ) := by
    unfold packetPhase
    rw [div_eq_mul_inv, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro C hC
    have hCa : 8 * c ^ 2 * l < C := by
      rcases Set.mem_uIcc.mp hC with h | h
      · exact lt_of_lt_of_le hC₁ h.1
      · exact lt_of_lt_of_le hC₁ (le_trans hlt.le h.1)
    have hdiv : bumpG c l C₁ C₂ C / Real.sqrt (Q c l C l)
        = (C - C₁) * (C₂ - C) / Real.sqrt l := bumpG_div_sqrt_eq c l hCa hl
    dsimp only
    rw [hdiv]
    have hexp : Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))
        = Complex.exp (-Complex.I * (C : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) := by
      congr 1
      rw [Complex.ofReal_div, mul_div_assoc]
    rw [hexp]
    push_cast
    rw [div_mul_eq_mul_div, ← div_eq_mul_inv]
  rw [hEq, bumpPoly_integral_closed_form hθ]

/-- 具体例：c = ℓ = 1、C ∈ [9, 10] の bump 波束の閉形式。-/
theorem packetPhase_bump_example_closed_form {T₀ hbar : ℝ} (hT₀ : T₀ ≠ 0) (hhbar : hbar ≠ 0) :
    packetPhase 1 1 9 10 T₀ hbar (bumpG 1 1 9 10)
      = ((Complex.I * ((T₀ / hbar : ℝ) : ℂ) - 2)
          * Complex.exp (-Complex.I * (9 : ℂ) * ((T₀ / hbar : ℝ) : ℂ))
        + (Complex.I * ((T₀ / hbar : ℝ) : ℂ) + 2)
          * Complex.exp (-Complex.I * (10 : ℂ) * ((T₀ / hbar : ℝ) : ℂ)))
        / (-Complex.I * ((T₀ / hbar : ℝ) : ℂ) ^ 3) := by
  have h := packetPhase_bump_closed_form (c := 1) (l := 1)
    (by norm_num : (9 : ℝ) < 10)
    (by norm_num : 8 * (1 : ℝ) ^ 2 * 1 < 9)
    (by norm_num : (0 : ℝ) < 1) hT₀ hhbar
  rw [show ((10 : ℝ) - 9) = 1 by norm_num, Real.sqrt_one] at h
  simpa using h

end

end CFT.WDWWavePacketClosedForm
