/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第十四段）。

  第十二・十三段では bump 波束について、零点集合が可算・測度 0 で、零点の間隔が
  2πħ/L に収束することを示した。そこでは bump 重みの閉形式（第七段）が鍵だった。
  ここでは閉形式を使わない、対称な重み一般に対する構造定理を示す：重み w が
  区間 [C₁, C₂] の中点 m = (C₁ + C₂)/2 について対称なら、位相つき波束は
  Ψ_f(T₀) = e^{−imT₀/ħ} ×（実数のコサイン積分）となり、零点の条件は実数の
  方程式 ∫ w(C) cos((C − m)T₀/ħ) dC = 0 に帰着する。すなわち対称な重みでは
  位相は e^{−imθ} の因子に分離し、残りは実数である。bump 重み
  w(C) = (C − C₁)(C₂ − C)/√ℓ は対称なので、この定理の例になっている
  （第七段の閉形式とも整合する）。

  残り：非対称な一般の重み g に対する零点の構造（位相関数の形そのものから
  見直す必要がある）。
-/
import CFT.Quantum.WDWWavePacketDecayExplicit

namespace CFT.WDWWavePacketSymmW

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketDecayExplicit MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 中点について対称な重みのサイン積分は消える（反射による置換）。-/
theorem integral_sin_symm_eq_zero {C₁ C₂ θ : ℝ} (w : ℝ → ℝ)
    (hw_symm : ∀ C, w (C₁ + C₂ - C) = w C) :
    ∫ C in C₁..C₂, w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) = 0 := by
  have hsub : ∫ C in C₁..C₂,
        w (C₁ + C₂ - C) * Real.sin (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
      = ∫ C in C₁..C₂, w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun C => w C * Real.sin ((C - (C₁ + C₂) / 2) * θ)) (C₁ + C₂) (a := C₁) (b := C₂)
    rw [show C₁ + C₂ - C₂ = C₁ by ring, show C₁ + C₂ - C₁ = C₂ by ring] at h
    exact h
  have hpt : ∀ C ∈ Set.uIcc C₁ C₂,
      w (C₁ + C₂ - C) * Real.sin (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
        = -(w C * Real.sin ((C - (C₁ + C₂) / 2) * θ)) := by
    intro C _
    rw [hw_symm C]
    have hsin : Real.sin (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
        = -Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
      have heq : (C₁ + C₂ - C) - (C₁ + C₂) / 2 = -(C - (C₁ + C₂) / 2) := by ring
      rw [heq, neg_mul, Real.sin_neg]
    rw [hsin]
    ring
  have hneg : ∫ C in C₁..C₂,
        w (C₁ + C₂ - C) * Real.sin (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
      = -∫ C in C₁..C₂, w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr hpt
  rw [hsub] at hneg
  linarith

/-- 対称な重みの振動積分は、中点の位相因子と実数のコサイン積分に分離する。-/
theorem integral_exp_symm_eq {C₁ C₂ θ : ℝ} (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (hw_symm : ∀ C, w (C₁ + C₂ - C) = w C) :
    ∫ C in C₁..C₂, ((w C : ℝ) : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
        ((∫ C in C₁..C₂, w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) := by
  -- exp(−iCθ) = exp(−imθ) · exp(−i(C−m)θ)
  have hexp : ∀ C : ℝ, Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
        Complex.exp (-Complex.I * ((C - (C₁ + C₂) / 2 : ℝ) : ℂ) * (θ : ℂ)) := by
    intro C
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- exp(−i(C−m)θ) = cos((C−m)θ) − i sin((C−m)θ)
  have hexp2 : ∀ C : ℝ,
      Complex.exp (-Complex.I * ((C - (C₁ + C₂) / 2 : ℝ) : ℂ) * (θ : ℂ))
        = ((Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
          - ((Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) * Complex.I := by
    intro C
    have h : -Complex.I * ((C - (C₁ + C₂) / 2 : ℝ) : ℂ) * (θ : ℂ)
        = ((-((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  -- 被積分関数の点ごとの表示
  have hpt : ∀ C : ℝ, ((w C : ℝ) : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
        (((w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
          - ((w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) * Complex.I) := by
    intro C
    rw [hexp C, hexp2 C]
    push_cast
    ring
  -- 連続性（可積分性）
  have hcos_cont : ContinuousOn (fun C => w C * Real.cos ((C - (C₁ + C₂) / 2) * θ))
      (Set.uIcc C₁ C₂) :=
    hw_cont.mul ((Real.continuous_cos.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)
  have hsin_cont : ContinuousOn (fun C => w C * Real.sin ((C - (C₁ + C₂) / 2) * θ))
      (Set.uIcc C₁ C₂) :=
    hw_cont.mul ((Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)
  have hcos_int : IntervalIntegrable
      (fun C => ((w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)) volume C₁ C₂ :=
    (Complex.continuous_ofReal.continuousOn.comp hcos_cont (Set.mapsTo_univ _ _)).intervalIntegrable
  have hsin_int : IntervalIntegrable
      (fun C => ((w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) * Complex.I) volume C₁ C₂ :=
    ((Complex.continuous_ofReal.continuousOn.comp hsin_cont (Set.mapsTo_univ _ _)).mul
      continuousOn_const).intervalIntegrable
  calc ∫ C in C₁..C₂, ((w C : ℝ) : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
      = ∫ C in C₁..C₂, Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
          (((w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
            - ((w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) * Complex.I) :=
        intervalIntegral.integral_congr (fun C _ => hpt C)
    _ = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
          ∫ C in C₁..C₂, (((w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
            - ((w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) * Complex.I) :=
        intervalIntegral.integral_const_mul _ _
    _ = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
          ((∫ C in C₁..C₂, w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ) := by
        congr 1
        rw [intervalIntegral.integral_sub hcos_int hsin_int,
          intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_ofReal, integral_sin_symm_eq_zero w hw_symm]
        simp

/-- 対称な重みでは、位相つき波束は中点の位相因子と実数のコサイン積分に分離する。-/
theorem packetPhase_symm_eq {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (hw_symm : ∀ C, w (C₁ + C₂ - C) = w C)
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l)) :
    packetPhase c l C₁ C₂ T₀ hbar g
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) *
        ((∫ C in C₁..C₂, w C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ) := by
  have hQpos : ∀ C ∈ Set.uIcc C₁ C₂, 0 < Q c l C l := by
    intro C hC
    rw [Set.uIcc_of_le hlt.le] at hC
    rw [Q_neck]
    exact mul_pos hl (sub_pos.mpr (lt_of_lt_of_le hC₁ hC.1))
  -- 位相の書き換え：−i·C·T₀/ħ = −i·C·(T₀/ħ)
  have hexp : ∀ C : ℝ, Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))
      = Complex.exp (-Complex.I * (C : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) := by
    intro C
    congr 1
    rw [Complex.ofReal_div, mul_div_assoc]
  -- 被積分関数の一致
  have hpt : ∀ C ∈ Set.uIcc C₁ C₂,
      ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (C : ℂ) * (T₀ : ℂ) / (hbar : ℂ))
      = ((w C : ℝ) : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) := by
    intro C hC
    have hQne : Real.sqrt (Q c l C l) ≠ 0 := (Real.sqrt_pos.mpr (hQpos C hC)).ne'
    rw [hexp C, hg C hC, mul_div_cancel_right₀ _ hQne]
  unfold packetPhase
  rw [intervalIntegral.integral_congr hpt]
  exact integral_exp_symm_eq w hw_cont hw_symm

/-- 対称な重みでは、波束が 0 になるのはちょうど実数のコサイン積分が 0 になるとき。-/
theorem packetPhase_symm_eq_zero_iff {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (hw_symm : ∀ C, w (C₁ + C₂ - C) = w C)
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l)) :
    packetPhase c l C₁ C₂ T₀ hbar g = 0 ↔
      ∫ C in C₁..C₂, w C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0 := by
  rw [packetPhase_symm_eq c l hhbar hC₁ hlt hl hw_cont hw_symm g hg]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (Complex.exp_ne_zero _)
    · exact Complex.ofReal_eq_zero.mp h1
  · intro h
    rw [h]
    simp

/-- bump 重み w(C) = (C − C₁)(C₂ − C)/√ℓ（第六段の被積分関数）。-/
def bumpW (c l : ℝ) (C₁ C₂ : ℝ) (C : ℝ) : ℝ := (C - C₁) * (C₂ - C) / Real.sqrt l

/-- bump 重みは区間の中点について対称である。-/
theorem bumpW_symm (C₁ C₂ : ℝ) (C : ℝ) :
    bumpW c l C₁ C₂ (C₁ + C₂ - C) = bumpW c l C₁ C₂ C := by
  unfold bumpW
  have h1 : C₁ + C₂ - C - C₁ = C₂ - C := by ring
  have h2 : C₂ - (C₁ + C₂ - C) = C - C₁ := by ring
  rw [h1, h2]
  ring

/-- bump 重みは連続である。-/
theorem bumpW_cont (C₁ C₂ : ℝ) :
    ContinuousOn (bumpW c l C₁ C₂) (Set.uIcc C₁ C₂) := by
  unfold bumpW
  exact (((continuous_id.sub continuous_const).mul
    (continuous_const.sub continuous_id)).div_const _).continuousOn

/-- 第六段の bump 重みは、区間上では bumpW × √Q に等しい。-/
theorem bumpG_eq_bumpW_mul_sqrt {C₁ C₂ : ℝ} (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂)
    (hl : 0 < l) {C : ℝ} (hC : C ∈ Set.uIcc C₁ C₂) :
    bumpG c l C₁ C₂ C = bumpW c l C₁ C₂ C * Real.sqrt (Q c l C l) := by
  rw [Set.uIcc_of_le hlt.le] at hC
  have hCa : 8 * c ^ 2 * l < C := lt_of_lt_of_le hC₁ hC.1
  have hQne : Real.sqrt (Q c l C l) ≠ 0 :=
    (Real.sqrt_pos.mpr (Q_neck_pos c l hCa hl)).ne'
  have h := bumpG_div_sqrt_eq (C₁ := C₁) (C₂ := C₂) c l hCa hl
  rw [div_eq_iff hQne] at h
  unfold bumpW
  rw [h]

/-- bump 波束は中点の位相因子と実数のコサイン積分に分離する（第六・七段の一般化）。-/
theorem packetPhase_bump_symm_eq {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l) :
    packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) *
        ((∫ C in C₁..C₂, bumpW c l C₁ C₂ C *
          Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ) := by
  apply packetPhase_symm_eq c l hhbar hC₁ hlt hl (bumpW_cont c l C₁ C₂)
    (bumpW_symm c l C₁ C₂) (bumpG c l C₁ C₂)
  intro C hC
  exact bumpG_eq_bumpW_mul_sqrt c l hC₁ hlt hl hC

/-- bump 波束が 0 になるのは、ちょうど実数のコサイン積分が 0 になるとき。-/
theorem packetPhase_bump_symm_eq_zero_iff {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l) :
    packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0 ↔
      ∫ C in C₁..C₂, bumpW c l C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0 :=
  packetPhase_symm_eq_zero_iff c l hhbar hC₁ hlt hl
    (bumpW_cont c l C₁ C₂) (bumpW_symm c l C₁ C₂) (bumpG c l C₁ C₂)
    (fun C hC => bumpG_eq_bumpW_mul_sqrt c l hC₁ hlt hl hC)

/-- 具体例：c = ℓ = 1、C ∈ [9, 10] の bump 波束は e^{−19iT₀/2} ×（実積分）。-/
theorem packetPhase_bump_symm_example (T₀ : ℝ) :
    packetPhase 1 1 9 10 T₀ 1 (bumpG 1 1 9 10)
      = Complex.exp (-Complex.I * (((9 : ℝ) + 10) / 2 : ℂ) * ((T₀ / 1 : ℝ) : ℂ)) *
        ((∫ C in (9 : ℝ)..10, bumpW 1 1 9 10 C *
          Real.cos ((C - ((9 : ℝ) + 10) / 2) * (T₀ / 1)) : ℝ) : ℂ) :=
  packetPhase_bump_symm_eq 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end

end CFT.WDWWavePacketSymmW
