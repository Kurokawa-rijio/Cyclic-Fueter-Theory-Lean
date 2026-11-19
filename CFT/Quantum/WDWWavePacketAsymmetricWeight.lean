/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第十五段）。

  第十四段では対称な重みについて、位相つき波束が e^{−imθ} ×（実数のコサイン積分）
  に分離することを示した。ここでは重みに対称性を仮定せず、重みを中点
  m = (C₁ + C₂)/2 について対称な部分と反対称な部分に分解する：
  w_sym(C) = (w(C) + w(C₁ + C₂ − C))/2、w_anti(C) = (w(C) − w(C₁ + C₂ − C))/2。
  反対称部分のコサイン積分は反射で消え、対称部分のサイン積分は第十四段の補題で
  消えるため、振動積分は
  ∫ w(C)e^{−iCθ} dC = e^{−imθ}·(∫ w_sym cos − i·∫ w_anti sin)
  と分離する。零点の条件は二つの実数の方程式
  （コサイン積分 = 0 かつサイン積分 = 0）に帰着する。特に反対称部分が小さければ
  サイン積分は小さく、対称部分のコサイン積分が 0 でなければ波束は 0 にならない
  （非対称性の摂動に対する安定性）。bump 重みは対称なので反対称部分は 0 であり、
  第十四段の分離を回収する。

  残り：非対称な一般の重みに対する零点の具体的な構造（サイン積分の零点の解析など）。
-/
import CFT.Quantum.WDWWavePacketSymmetricWeight

namespace CFT.WDWWavePacketAsymW

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketDecayExplicit CFT.WDWWavePacketSymmW MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 反射 C ↦ C₁ + C₂ − C は区間 [C₁, C₂] を保つ。-/
theorem mapsTo_reflect {C₁ C₂ : ℝ} :
    Set.MapsTo (fun C => C₁ + C₂ - C) (Set.uIcc C₁ C₂) (Set.uIcc C₁ C₂) := by
  intro C hC
  rw [Set.mem_uIcc] at hC ⊢
  rcases hC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨by show C₁ ≤ C₁ + C₂ - C; linarith, by show C₁ + C₂ - C ≤ C₂; linarith⟩
  · right
    exact ⟨by show C₂ ≤ C₁ + C₂ - C; linarith, by show C₁ + C₂ - C ≤ C₁; linarith⟩

/-- 中点 m = (C₁ + C₂)/2 についての重みの対称部分。-/
def symPart (w : ℝ → ℝ) (C₁ C₂ : ℝ) (C : ℝ) : ℝ := (w C + w (C₁ + C₂ - C)) / 2

/-- 中点 m = (C₁ + C₂)/2 についての重みの反対称部分。-/
def antiPart (w : ℝ → ℝ) (C₁ C₂ : ℝ) (C : ℝ) : ℝ := (w C - w (C₁ + C₂ - C)) / 2

/-- 対称部分は反射で不変である。-/
theorem symPart_symm (w : ℝ → ℝ) (C₁ C₂ C : ℝ) :
    symPart w C₁ C₂ (C₁ + C₂ - C) = symPart w C₁ C₂ C := by
  unfold symPart
  have h : C₁ + C₂ - (C₁ + C₂ - C) = C := by ring
  rw [h]
  ring

/-- 反対称部分は反射で符号が反転する。-/
theorem antiPart_antisymm (w : ℝ → ℝ) (C₁ C₂ C : ℝ) :
    antiPart w C₁ C₂ (C₁ + C₂ - C) = -antiPart w C₁ C₂ C := by
  unfold antiPart
  have h : C₁ + C₂ - (C₁ + C₂ - C) = C := by ring
  rw [h]
  ring

/-- 重みは対称部分と反対称部分の和に分解する。-/
theorem symPart_add_antiPart (w : ℝ → ℝ) (C₁ C₂ C : ℝ) :
    symPart w C₁ C₂ C + antiPart w C₁ C₂ C = w C := by
  unfold symPart antiPart
  ring

/-- 対称部分は連続性を保つ。-/
theorem symPart_continuousOn {w : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hw : ContinuousOn w (Set.uIcc C₁ C₂)) :
    ContinuousOn (symPart w C₁ C₂) (Set.uIcc C₁ C₂) := by
  have href : ContinuousOn (fun C => w (C₁ + C₂ - C)) (Set.uIcc C₁ C₂) :=
    hw.comp ((continuous_const.sub continuous_id).continuousOn) mapsTo_reflect
  unfold symPart
  exact (hw.add href).div_const 2

/-- 反対称部分は連続性を保つ。-/
theorem antiPart_continuousOn {w : ℝ → ℝ} {C₁ C₂ : ℝ}
    (hw : ContinuousOn w (Set.uIcc C₁ C₂)) :
    ContinuousOn (antiPart w C₁ C₂) (Set.uIcc C₁ C₂) := by
  have href : ContinuousOn (fun C => w (C₁ + C₂ - C)) (Set.uIcc C₁ C₂) :=
    hw.comp ((continuous_const.sub continuous_id).continuousOn) mapsTo_reflect
  unfold antiPart
  exact (hw.sub href).div_const 2

/-- 反対称部分のコサイン積分は消える（反射で被積分関数が符号反転する）。-/
theorem integral_cos_antiPart_eq_zero {C₁ C₂ θ : ℝ} (w : ℝ → ℝ) :
    ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) = 0 := by
  have hsub : ∫ C in C₁..C₂,
        antiPart w C₁ C₂ (C₁ + C₂ - C) * Real.cos (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
      = ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun C => antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ)) (C₁ + C₂)
      (a := C₁) (b := C₂)
    rw [show C₁ + C₂ - C₂ = C₁ by ring, show C₁ + C₂ - C₁ = C₂ by ring] at h
    exact h
  have hpt : ∀ C ∈ Set.uIcc C₁ C₂,
      antiPart w C₁ C₂ (C₁ + C₂ - C) * Real.cos (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
        = -(antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ)) := by
    intro C _
    rw [antiPart_antisymm w C₁ C₂ C]
    have hcos : Real.cos (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
        = Real.cos ((C - (C₁ + C₂) / 2) * θ) := by
      have heq : (C₁ + C₂ - C) - (C₁ + C₂) / 2 = -(C - (C₁ + C₂) / 2) := by ring
      rw [heq, neg_mul, Real.cos_neg]
    rw [hcos]
    ring
  have hneg : ∫ C in C₁..C₂,
        antiPart w C₁ C₂ (C₁ + C₂ - C) * Real.cos (((C₁ + C₂ - C) - (C₁ + C₂) / 2) * θ)
      = -∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr hpt
  rw [hsub] at hneg
  linarith

/-- 対称部分のサイン積分は消える（第十四段の補題を対称部分に適用）。-/
theorem integral_sin_symPart_eq_zero {C₁ C₂ θ : ℝ} (w : ℝ → ℝ) :
    ∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) = 0 :=
  integral_sin_symm_eq_zero (symPart w C₁ C₂) (symPart_symm w C₁ C₂)

/-- コサイン積分は対称部分だけに依存する。-/
theorem integral_cos_eq_symPart {C₁ C₂ θ : ℝ} (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂)) :
    ∫ C in C₁..C₂, w C * Real.cos ((C - (C₁ + C₂) / 2) * θ)
      = ∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) := by
  have hcos_sym : IntervalIntegrable
      (fun C => symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ)) volume C₁ C₂ :=
    ((symPart_continuousOn hw_cont).mul ((Real.continuous_cos.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)).intervalIntegrable
  have hcos_anti : IntervalIntegrable
      (fun C => antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ)) volume C₁ C₂ :=
    ((antiPart_continuousOn hw_cont).mul ((Real.continuous_cos.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)).intervalIntegrable
  have hpt : ∀ C : ℝ, w C * Real.cos ((C - (C₁ + C₂) / 2) * θ)
      = symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ)
        + antiPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) := by
    intro C
    rw [← add_mul, symPart_add_antiPart w C₁ C₂ C]
  rw [intervalIntegral.integral_congr (fun C _ => hpt C),
    intervalIntegral.integral_add hcos_sym hcos_anti, integral_cos_antiPart_eq_zero w,
    add_zero]

/-- サイン積分は反対称部分だけに依存する。-/
theorem integral_sin_eq_antiPart {C₁ C₂ θ : ℝ} (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂)) :
    ∫ C in C₁..C₂, w C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
      = ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  have hsin_sym : IntervalIntegrable
      (fun C => symPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)) volume C₁ C₂ :=
    ((symPart_continuousOn hw_cont).mul ((Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)).intervalIntegrable
  have hsin_anti : IntervalIntegrable
      (fun C => antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)) volume C₁ C₂ :=
    ((antiPart_continuousOn hw_cont).mul ((Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).mul continuous_const)).continuousOn)).intervalIntegrable
  have hpt : ∀ C : ℝ, w C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
      = symPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)
        + antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
    intro C
    rw [← add_mul, symPart_add_antiPart w C₁ C₂ C]
  rw [intervalIntegral.integral_congr (fun C _ => hpt C),
    intervalIntegral.integral_add hsin_sym hsin_anti, integral_sin_symPart_eq_zero w,
    zero_add]

/-- 一般の重みの振動積分は、中点の位相因子と、対称部分のコサイン積分・反対称部分の
    サイン積分に分離する。-/
theorem integral_exp_decomp_eq {C₁ C₂ θ : ℝ} (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂)) :
    ∫ C in C₁..C₂, ((w C : ℝ) : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
        (((∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
          - ((∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
            * Complex.I) := by
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
          (((∫ C in C₁..C₂, w C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
            - ((∫ C in C₁..C₂, w C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
              * Complex.I) := by
        congr 1
        rw [intervalIntegral.integral_sub hcos_int hsin_int,
          intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_ofReal]
    _ = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * (θ : ℂ)) *
          (((∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
            - ((∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ) : ℝ) : ℂ)
              * Complex.I) := by
        rw [integral_cos_eq_symPart w hw_cont, integral_sin_eq_antiPart w hw_cont]

/-- 一般の重みでは、位相つき波束は中点の位相因子と、対称部分のコサイン積分・
    反対称部分のサイン積分に分離する。-/
theorem packetPhase_decomp_eq {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l)) :
    packetPhase c l C₁ C₂ T₀ hbar g
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) *
        (((∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ)
          - ((∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ)
            * Complex.I) := by
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
  exact integral_exp_decomp_eq w hw_cont

/-- 一般の重みでは、波束が 0 になるのはちょうど、対称部分のコサイン積分と
    反対称部分のサイン積分がともに 0 になるとき。-/
theorem packetPhase_decomp_eq_zero_iff {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l)) :
    packetPhase c l C₁ C₂ T₀ hbar g = 0 ↔
      (∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0 ∧
       ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0) := by
  rw [packetPhase_decomp_eq c l hhbar hC₁ hlt hl hw_cont g hg]
  constructor
  · intro h
    have h0 : ((∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ)
          - ((∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ)
            * Complex.I = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (Complex.exp_ne_zero _)
      · exact h1
    have hre : ∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0 := by
      have hcon := congrArg Complex.re h0
      simpa using hcon
    have him : ∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0 := by
      have hcon := congrArg Complex.im h0
      simpa using hcon
    exact ⟨hre, him⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

/-- 対称部分のコサイン積分が 0 でなければ、反対称部分のいかんにかかわらず
    波束は 0 にならない（非対称性の摂動に対する安定性）。-/
theorem packetPhase_ne_of_cos_integral_ne {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l)
    {w : ℝ → ℝ} (hw_cont : ContinuousOn w (Set.uIcc C₁ C₂))
    (g : ℝ → ℝ) (hg : ∀ C ∈ Set.uIcc C₁ C₂, g C = w C * Real.sqrt (Q c l C l))
    (hcos : ∫ C in C₁..C₂, symPart w C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) ≠ 0) :
    packetPhase c l C₁ C₂ T₀ hbar g ≠ 0 := by
  intro hzero
  exact hcos ((packetPhase_decomp_eq_zero_iff c l hhbar hC₁ hlt hl hw_cont g hg).mp hzero).1

/-- 反対称部分が ε で抑えられれば、サイン積分は区間長 × ε で抑えられる
    （小さな非対称成分の影響の定量評価）。-/
theorem norm_integral_sin_antiPart_le {C₁ C₂ θ ε : ℝ} (hC : C₁ ≤ C₂) (hε : 0 ≤ ε)
    (w : ℝ → ℝ)
    (hanti : ∀ C ∈ Set.uIcc C₁ C₂, |antiPart w C₁ C₂ C| ≤ ε) :
    |∫ C in C₁..C₂, antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)|
      ≤ (C₂ - C₁) * ε := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := C₁) (b := C₂)
    (f := fun C => antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ))
    (fun C hC => by
      calc ‖antiPart w C₁ C₂ C * Real.sin ((C - (C₁ + C₂) / 2) * θ)‖
          = |antiPart w C₁ C₂ C| * |Real.sin ((C - (C₁ + C₂) / 2) * θ)| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ ε * 1 :=
            mul_le_mul (hanti C (Set.uIoc_subset_uIcc hC)) (Real.abs_sin_le_one _)
              (abs_nonneg _) hε
        _ = ε := mul_one ε)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hC), mul_comm ε (C₂ - C₁)] at h
  exact h

/-- bump 重みは対称なので、その対称部分は bump 重みそのものである。-/
theorem symPart_bumpW_eq (C₁ C₂ C : ℝ) :
    symPart (bumpW c l C₁ C₂) C₁ C₂ C = bumpW c l C₁ C₂ C := by
  unfold symPart
  rw [bumpW_symm c l C₁ C₂ C]
  ring

/-- bump 重みは対称なので、その反対称部分は 0 である。-/
theorem antiPart_bumpW_eq_zero (C₁ C₂ C : ℝ) :
    antiPart (bumpW c l C₁ C₂) C₁ C₂ C = 0 := by
  unfold antiPart
  rw [bumpW_symm c l C₁ C₂ C]
  ring

/-- bump 波束では反対称部分が 0 なので、第十五段の分離は第十四段の分離を回収する。-/
theorem packetPhase_bump_decomp_eq {C₁ C₂ T₀ hbar : ℝ} (hhbar : hbar ≠ 0)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hlt : C₁ < C₂) (hl : 0 < l) :
    packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) *
        ((∫ C in C₁..C₂, bumpW c l C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ) := by
  have h : packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)
      = Complex.exp (-Complex.I * ((C₁ + C₂) / 2 : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) *
        (((∫ C in C₁..C₂, symPart (bumpW c l C₁ C₂) C₁ C₂ C *
            Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ)
          - ((∫ C in C₁..C₂, antiPart (bumpW c l C₁ C₂) C₁ C₂ C *
            Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) : ℝ) : ℂ)
            * Complex.I) :=
    packetPhase_decomp_eq c l hhbar hC₁ hlt hl (bumpW_cont c l C₁ C₂)
      (bumpG c l C₁ C₂) (fun C hC => bumpG_eq_bumpW_mul_sqrt c l hC₁ hlt hl hC)
  rw [h]
  have hcos : ∫ C in C₁..C₂, symPart (bumpW c l C₁ C₂) C₁ C₂ C *
        Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar))
      = ∫ C in C₁..C₂, bumpW c l C₁ C₂ C * Real.cos ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) :=
    intervalIntegral.integral_congr (fun C _ => by rw [symPart_bumpW_eq c l C₁ C₂ C])
  have hsin : ∫ C in C₁..C₂, antiPart (bumpW c l C₁ C₂) C₁ C₂ C *
        Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar)) = 0 := by
    calc ∫ C in C₁..C₂, antiPart (bumpW c l C₁ C₂) C₁ C₂ C *
            Real.sin ((C - (C₁ + C₂) / 2) * (T₀ / hbar))
        = ∫ C in C₁..C₂, (0 : ℝ) :=
          intervalIntegral.integral_congr
            (fun C _ => by rw [antiPart_bumpW_eq_zero c l C₁ C₂ C]; simp)
      _ = 0 := by simp
  congr 1
  rw [hcos, hsin]
  simp

end

end CFT.WDWWavePacketAsymW
