/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第五段：部分積分による減衰評価）。

  第四段までで、大きな |T₀| の評価は T₀ ≥ 0 に帰着した。ここでは台が区間
  (C₁, C₂) の内側にある重み g に対する部分積分の形を固定する：
  f(C) = g(C)/√Q が端点で消えれば、振動因子 e^{−iCθ} の部分積分で境界項が消え、
  ∫ f(C) e^{−iCθ} dC = (−i/θ) ∫ f′(C) e^{−iCθ} dC となり、
  ‖Ψ_f(T₀)‖ ≤ (C₂ − C₁)·M·|ħ|/|T₀|（M は ‖f′‖ の上界）の減衰評価が得られる。

  この段では f′ を仮定として置く（抽象形）。具体的な g に対する f′ の計算と
  明示定数の評価は次の段に残る。
-/
import CFT.Quantum.WDWWavePacketSymmetry

namespace CFT.WDWWavePacketDecay

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 振動因子の微分：C ↦ e^{−iCθ} の導関数は −iθ·e^{−iCθ}。-/
theorem hasDerivAt_exp_neg_I_mul (θ C : ℝ) :
    HasDerivAt (fun C : ℝ => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)))
      (-Complex.I * (θ : ℂ) * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) C := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-Complex.I * z * (θ : ℂ)))
      (Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) * (-Complex.I * (θ : ℂ))) (C : ℂ) := by
    have h2 : HasDerivAt (fun z : ℂ => -Complex.I * z * (θ : ℂ))
        (-Complex.I * (θ : ℂ)) (C : ℂ) := by
      have h := ((hasDerivAt_id (C : ℂ)).const_mul (-Complex.I)).mul_const (θ : ℂ)
      simpa using h
    exact (Complex.hasDerivAt_exp _).comp (C : ℂ) h2
  have h3 := h1.comp_ofReal (z := C)
  convert h3 using 1
  ring

/-- 振動因子はノルム 1：‖e^{−iCθ}‖ = 1。-/
theorem norm_exp_neg_I_mul (θ C : ℝ) :
    ‖Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))‖ = 1 := by
  have h : -Complex.I * (C : ℂ) * (θ : ℂ) = (((-C * θ : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_eq_abs, Complex.abs_exp_ofReal_mul_I]

/-- 部分積分の恒等式：端点で消える C¹ 関数 f に対して
    ∫ f(C) e^{−iCθ} dC = (−i/θ) ∫ f′(C) e^{−iCθ} dC。-/
theorem integral_exp_mul_eq_of_vanish {C₁ C₂ θ : ℝ} (hθ : θ ≠ 0)
    {f f' : ℝ → ℂ}
    (hf : ∀ C ∈ Set.uIcc C₁ C₂, HasDerivAt f (f' C) C)
    (hf' : ContinuousOn f' (Set.uIcc C₁ C₂))
    (hf1 : f C₁ = 0) (hf2 : f C₂ = 0) :
    (∫ C in C₁..C₂, f C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)))
      = (-Complex.I / (θ : ℂ)) *
        ∫ C in C₁..C₂, f' C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) := by
  have hθℂ : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  have hIθ : (-Complex.I * (θ : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hθℂ
  have hφcont : Continuous
      (fun C : ℝ => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) :=
    Complex.continuous_exp.comp
      (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
  -- v(C) = e^{−iCθ}/(−iθ) は e^{−iCθ} の原始関数。
  have hv : ∀ C ∈ Set.uIcc C₁ C₂,
      HasDerivAt (fun C : ℝ => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) /
          (-Complex.I * (θ : ℂ)))
        (Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) C := by
    intro C _
    have h := (hasDerivAt_exp_neg_I_mul θ C).div_const (-Complex.I * (θ : ℂ))
    convert h using 1
    rw [eq_div_iff hIθ]
    ring
  have hf'int : IntervalIntegrable f' volume C₁ C₂ := hf'.intervalIntegrable
  have hφint : IntervalIntegrable
      (fun C => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) volume C₁ C₂ :=
    (hφcont.continuousOn.mono (Set.subset_univ _)).intervalIntegrable
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := f)
    (v := fun C => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) /
      (-Complex.I * (θ : ℂ)))
    (u' := f')
    (v' := fun C => Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)))
    hf hv hf'int hφint
  rw [hf1, hf2] at hIBP
  simp only [zero_mul, sub_zero, zero_sub] at hIBP
  -- ∫ f′·v = (∫ f′·e^{−iCθ})·(−iθ)⁻¹
  have hIntv : (∫ C in C₁..C₂, f' C * (Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) /
        (-Complex.I * (θ : ℂ))))
      = (∫ C in C₁..C₂, f' C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) *
        (-Complex.I * (θ : ℂ))⁻¹ := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro C _
    show f' C * (Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) / (-Complex.I * (θ : ℂ)))
        = f' C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ)) * (-Complex.I * (θ : ℂ))⁻¹
    rw [div_eq_mul_inv]
    ring
  have hInv : (-Complex.I * (θ : ℂ))⁻¹ = Complex.I * (θ : ℂ)⁻¹ := by
    rw [mul_inv, inv_neg, Complex.inv_I, neg_neg]
  rw [hIBP, hIntv, hInv, div_eq_mul_inv]
  ring

/-- 減衰評価（抽象形）：‖∫ f(C) e^{−iCθ} dC‖ ≤ (C₂ − C₁)·M/|θ|。-/
theorem norm_integral_exp_mul_le_of_vanish {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ : θ ≠ 0)
    {f f' : ℝ → ℂ}
    (hf : ∀ C ∈ Set.uIcc C₁ C₂, HasDerivAt f (f' C) C)
    (hf' : ContinuousOn f' (Set.uIcc C₁ C₂))
    (hf1 : f C₁ = 0) (hf2 : f C₂ = 0)
    {M : ℝ} (hM : ∀ C ∈ Set.uIoc C₁ C₂, ‖f' C‖ ≤ M) :
    ‖∫ C in C₁..C₂, f C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))‖
      ≤ (C₂ - C₁) * M / |θ| := by
  rw [integral_exp_mul_eq_of_vanish hθ hf hf' hf1 hf2]
  have hnorm : ‖∫ C in C₁..C₂, f' C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))‖
      ≤ M * (C₂ - C₁) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := C₁) (b := C₂)
      (f := fun C => f' C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))) (C := M)
      (fun C hC => by
        rw [norm_mul, norm_exp_neg_I_mul, mul_one]
        exact hM C hC)
    rwa [abs_of_pos (sub_pos.mpr hlt)] at h
  have hcoef : ‖(-Complex.I / (θ : ℂ))‖ = 1 / |θ| := by
    rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hθpos : (0 : ℝ) < |θ| := abs_pos.mpr hθ
  have hθne : |θ| ≠ 0 := hθpos.ne'
  rw [norm_mul, hcoef]
  calc (1 / |θ|) * ‖∫ C in C₁..C₂, f' C * Complex.exp (-Complex.I * (C : ℂ) * (θ : ℂ))‖
      ≤ (1 / |θ|) * (M * (C₂ - C₁)) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg zero_le_one (abs_nonneg _))
    _ = (C₂ - C₁) * M / |θ| := by
        field_simp
        ring

/-- 位相つき波束への適用：g が端点で消え、被積分関数 f(C) = g(C)/√Q が
    [C₁, C₂] 上で導関数 f′（上界 M つき）を持てば、
    ‖Ψ_f(T₀)‖ ≤ (C₂ − C₁)·M·|ħ|/|T₀|（T₀ ≠ 0）。-/
theorem packetPhase_norm_le_of_vanish {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    (hT₀ : T₀ ≠ 0) (hhbar : hbar ≠ 0)
    {g : ℝ → ℝ} {f' : ℝ → ℂ}
    (hf : ∀ C ∈ Set.uIcc C₁ C₂,
      HasDerivAt (fun C => ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ)) (f' C) C)
    (hf' : ContinuousOn f' (Set.uIcc C₁ C₂))
    (hg1 : g C₁ = 0) (hg2 : g C₂ = 0)
    {M : ℝ} (hM : ∀ C ∈ Set.uIoc C₁ C₂, ‖f' C‖ ≤ M) :
    ‖packetPhase c l C₁ C₂ T₀ hbar g‖ ≤ (C₂ - C₁) * M * |hbar| / |T₀| := by
  have hθ : (T₀ / hbar : ℝ) ≠ 0 := div_ne_zero hT₀ hhbar
  have hf1 : ((g C₁ / Real.sqrt (Q c l C₁ l) : ℝ) : ℂ) = 0 := by simp [hg1]
  have hf2 : ((g C₂ / Real.sqrt (Q c l C₂ l) : ℝ) : ℂ) = 0 := by simp [hg2]
  have hEq : packetPhase c l C₁ C₂ T₀ hbar g
      = ∫ C in C₁..C₂, ((g C / Real.sqrt (Q c l C l) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (C : ℂ) * ((T₀ / hbar : ℝ) : ℂ)) := by
    unfold packetPhase
    apply intervalIntegral.integral_congr
    intro C _
    push_cast
    ring
  rw [hEq]
  have hbound := norm_integral_exp_mul_le_of_vanish hlt hθ hf hf' hf1 hf2 hM
  have hT₀pos : (0 : ℝ) < |T₀| := abs_pos.mpr hT₀
  have hHbarpos : (0 : ℝ) < |hbar| := abs_pos.mpr hhbar
  have hT₀ne : |T₀| ≠ 0 := hT₀pos.ne'
  have hHbarne : |hbar| ≠ 0 := hHbarpos.ne'
  rw [abs_div] at hbound
  have heq : (C₂ - C₁) * M / (|T₀| / |hbar|) = (C₂ - C₁) * M * |hbar| / |T₀| := by
    field_simp
  rwa [heq] at hbound

end

end CFT.WDWWavePacketDecay
