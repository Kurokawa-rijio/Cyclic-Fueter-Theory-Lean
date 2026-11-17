import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 5-1（作用素の対称性）の本体への適用（混合項）。

  ウィーラー–ドウィット作用素は `CFT.WKB.wdwOp`（`WDWExactWKB.lean`）で
    Ĥ Ψ = (1/4c)(−ħ² a Ψ_aa + 2ħ² b Ψ_ab) − c a (b² − ℓ²) Ψ
  と定義されている。a-部分は `WDWSymmetry.lean` で重み 1/a の内積に関して
  対称であることが証明済み。ここでは混合項 2ħ²b ∂_a∂_b を扱う。

  主結果は二つある。

  1. 純粋な混合微分 ∂_a∂_b は、矩形上の平坦な測度に関して対称である
     （`mixedDeriv_symm`）。証明は a 方向・b 方向の 1 次元部分積分と、
     積分順序の交換（フビニ）の組み立てである。
     Clairaut（混合偏微分の交換）は使わない：混合偏微分 fab は
     ∂_a(f_b) = ∂_b(f_a) = fab を満たす一つの関数として仮定する。

  2. 実際の WDW 混合項 b·∂_a∂_b は、重み 1/a の内積に関しては
     対称ではない。その随伴は 1 階の補正項を持つ
     （`wdw_mixed_adjoint`、`wdw_mixed_adjoint_weighted`）：
       ⟨f, b ∂_a∂_b g⟩ = ⟨b ∂_a∂_b f + ∂_a f − (b/a) ∂_b f − f/a, g⟩
     （重み 1/a の内積、矩形上のディリクレ境界のもと）。
     すなわち混合項をそのまま対称だとして使うことはできない。
     対称な形にするには 1 階の項を補う順序づけ（ラプラス–ベルトラーミ型）
     が必要である。補正が 0 でない具体例は sympy による数値確認
     （`/tmp/check51mix.py`）：f = sin(π(a−1))·sin(πb)、
     g = sin(π(a−1))·sin(2πb)、a ∈ [1,2]、b ∈ [0,1] で
     ⟨f, b g_ab⟩ − ⟨b f_ab, g⟩ = −2π(−Si(2π)+Si(4π))/3 ≠ 0。
     （数値確認は証明ではない。Lean で証明されているのは随伴公式そのものである。
     具体的なテスト関数による非対称性の Lean 証明は別葉として残る。）
-/

namespace CFT.WDWMix

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- 区間積分の順序交換（フビニ）。`MeasureTheory.integral_integral_swap` の区間版。 -/
theorem intervalIntegral_swap {F : ℝ → ℝ → ℝ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D)))) :
    ∫ x in A..B, ∫ y in C..D, F x y = ∫ y in C..D, ∫ x in A..B, F x y := by
  simp only [intervalIntegral.integral_of_le hAB, intervalIntegral.integral_of_le hCD]
  exact MeasureTheory.integral_integral_swap hF

/-- 矩形上で連続な関数は、区間の積に対する制限測度の積に関して可積分である。 -/
theorem integrable_prod_restrict_of_continuousOn {F : ℝ → ℝ → ℝ} {A B C D : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc A B ×ˢ Set.Icc C D)) :
    Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) := by
  have h1 : IntegrableOn (Function.uncurry F) (Set.Icc A B ×ˢ Set.Icc C D)
      (volume : Measure (ℝ × ℝ)) :=
    hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h2 : IntegrableOn (Function.uncurry F) (Set.Ioc A B ×ˢ Set.Ioc C D)
      (volume : Measure (ℝ × ℝ)) :=
    h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  rw [MeasureTheory.Measure.prod_restrict]
  exact h2

/-- a 方向の部分積分（b を固定）：∫ fab·g = −∫ fb·ga。 -/
theorem ibp_a {fb fab g ga : ℝ → ℝ → ℝ} {A B : ℝ} (b : ℝ)
    (hfb : ∀ a, HasDerivAt (fun a' => fb a' b) (fab a b) a)
    (hg : ∀ a, HasDerivAt (fun a' => g a' b) (ga a b) a)
    (hfab' : IntervalIntegrable (fun a => fab a b) volume A B)
    (hga' : IntervalIntegrable (fun a => ga a b) volume A B)
    (hfab_int : IntervalIntegrable (fun a => fab a b * g a b) volume A B)
    (hfbga_int : IntervalIntegrable (fun a => fb a b * ga a b) volume A B)
    (hgA : g A b = 0) (hgB : g B b = 0) :
    ∫ x in A..B, fab x b * g x b = -∫ x in A..B, fb x b * ga x b := by
  have h := intervalIntegral.integral_deriv_mul_eq_sub (u := fun a => fb a b)
    (v := fun a => g a b) (u' := fun a => fab a b) (v' := fun a => ga a b)
    (fun x _ => hfb x) (fun x _ => hg x) hfab' hga'
  rw [intervalIntegral.integral_add hfab_int hfbga_int] at h
  dsimp only at h
  rw [hgB, hgA, mul_zero, mul_zero, sub_zero] at h
  linarith

/-- b 方向の部分積分（a を固定）：∫ f·gab = −∫ fb·ga。 -/
theorem ibp_b {f fb ga gab : ℝ → ℝ → ℝ} {C D : ℝ} (a : ℝ)
    (hf : ∀ b, HasDerivAt (fun b' => f a b') (fb a b) b)
    (hga : ∀ b, HasDerivAt (fun b' => ga a b') (gab a b) b)
    (hfb' : IntervalIntegrable (fun b => fb a b) volume C D)
    (hgab' : IntervalIntegrable (fun b => gab a b) volume C D)
    (hfbga_int : IntervalIntegrable (fun b => fb a b * ga a b) volume C D)
    (hfgab_int : IntervalIntegrable (fun b => f a b * gab a b) volume C D)
    (hfC : f a C = 0) (hfD : f a D = 0) :
    ∫ y in C..D, f a y * gab a y = -∫ y in C..D, fb a y * ga a y := by
  have h := intervalIntegral.integral_deriv_mul_eq_sub (u := fun b => f a b)
    (v := fun b => ga a b) (u' := fun b => fb a b) (v' := fun b => gab a b)
    (fun y _ => hf y) (fun y _ => hga y) hfb' hgab'
  rw [intervalIntegral.integral_add hfbga_int hfgab_int] at h
  dsimp only at h
  rw [hfD, hfC, zero_mul, zero_mul, sub_zero] at h
  linarith

/-- 【5-1】純粋な混合微分 ∂_a∂_b は、矩形上の平坦な測度に関して対称である
  （両変数にディリクレ境界）。 -/
theorem mixedDeriv_symm {f g fb fab ga gab : ℝ → ℝ → ℝ} {A B C D : ℝ}
    (hAB : A ≤ B) (hCD : C ≤ D)
    (hfb_a : ∀ a b, HasDerivAt (fun a' => fb a' b) (fab a b) a)
    (hga_a : ∀ a b, HasDerivAt (fun a' => g a' b) (ga a b) a)
    (hgab_b : ∀ a b, HasDerivAt (fun b' => ga a b') (gab a b) b)
    (hfb_b : ∀ a b, HasDerivAt (fun b' => f a b') (fb a b) b)
    (hgA : ∀ b, g A b = 0) (hgB : ∀ b, g B b = 0)
    (hfC : ∀ a, f a C = 0) (hfD : ∀ a, f a D = 0)
    (hfab_c : Continuous (Function.uncurry fab)) (hg_c : Continuous (Function.uncurry g))
    (hfb_c : Continuous (Function.uncurry fb)) (hga_c : Continuous (Function.uncurry ga))
    (hf_c : Continuous (Function.uncurry f)) (hgab_c : Continuous (Function.uncurry gab)) :
    ∫ x in A..B, ∫ y in C..D, fab x y * g x y
      = ∫ x in A..B, ∫ y in C..D, f x y * gab x y := by
  have cont_a : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ b : ℝ,
      Continuous fun a => F a b := by
    intro F hF b
    exact hF.comp (continuous_id.prod_mk continuous_const)
  have cont_b : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ a : ℝ,
      Continuous fun b => F a b := by
    intro F hF a
    exact hF.comp (continuous_const.prod_mk continuous_id)
  have ifab' : ∀ b, IntervalIntegrable (fun a => fab a b) volume A B := fun b =>
    (cont_a fab hfab_c b).intervalIntegrable A B
  have iga' : ∀ b, IntervalIntegrable (fun a => ga a b) volume A B := fun b =>
    (cont_a ga hga_c b).intervalIntegrable A B
  have ifab : ∀ b, IntervalIntegrable (fun a => fab a b * g a b) volume A B := fun b =>
    ((cont_a fab hfab_c b).mul (cont_a g hg_c b)).intervalIntegrable A B
  have ifbga_a : ∀ b, IntervalIntegrable (fun a => fb a b * ga a b) volume A B := fun b =>
    ((cont_a fb hfb_c b).mul (cont_a ga hga_c b)).intervalIntegrable A B
  have ifb' : ∀ a, IntervalIntegrable (fun b => fb a b) volume C D := fun a =>
    (cont_b fb hfb_c a).intervalIntegrable C D
  have igab' : ∀ a, IntervalIntegrable (fun b => gab a b) volume C D := fun a =>
    (cont_b gab hgab_c a).intervalIntegrable C D
  have ifgab : ∀ a, IntervalIntegrable (fun b => f a b * gab a b) volume C D := fun a =>
    ((cont_b f hf_c a).mul (cont_b gab hgab_c a)).intervalIntegrable C D
  have ifbga_b : ∀ a, IntervalIntegrable (fun b => fb a b * ga a b) volume C D := fun a =>
    ((cont_b fb hfb_c a).mul (cont_b ga hga_c a)).intervalIntegrable C D
  have hswap1 : Integrable (Function.uncurry fun x y => fab x y * g x y)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) :=
    integrable_prod_restrict_of_continuousOn ((hfab_c.mul hg_c).continuousOn)
  have hswap2 : Integrable (Function.uncurry fun x y => fb x y * ga x y)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) :=
    integrable_prod_restrict_of_continuousOn ((hfb_c.mul hga_c).continuousOn)
  have e1 : ∫ x in A..B, ∫ y in C..D, fab x y * g x y
      = ∫ y in C..D, ∫ x in A..B, fab x y * g x y :=
    intervalIntegral_swap hAB hCD hswap1
  have e2 : ∫ y in C..D, ∫ x in A..B, fab x y * g x y
      = -∫ y in C..D, ∫ x in A..B, fb x y * ga x y := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    exact ibp_a y (fun a => hfb_a a y) (fun a => hga_a a y) (ifab' y) (iga' y) (ifab y)
      (ifbga_a y) (hgA y) (hgB y)
  have e3 : ∫ y in C..D, ∫ x in A..B, fb x y * ga x y
      = ∫ x in A..B, ∫ y in C..D, fb x y * ga x y :=
    (intervalIntegral_swap hAB hCD hswap2).symm
  have e4 : ∫ x in A..B, ∫ y in C..D, f x y * gab x y
      = -∫ x in A..B, ∫ y in C..D, fb x y * ga x y := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact ibp_b x (fun b => hfb_b x b) (fun b => hgab_b x b) (ifb' x) (igab' x) (ifbga_b x)
      (ifgab x) (hfC x) (hfD x)
  rw [e1, e2, e3, e4]

/-- a 方向の部分積分（重みつき、b を固定）。v = f·b/a の a 微分は
  b·fa/a − b·f/a² である。 -/
theorem ibp_a_weighted {f fa gb gab : ℝ → ℝ → ℝ} {A B : ℝ} (b : ℝ) (hAB : A ≤ B)
    (hA : 0 < A)
    (hgb : ∀ a, HasDerivAt (fun a' => gb a' b) (gab a b) a)
    (hfa : ∀ a, HasDerivAt (fun a' => f a' b) (fa a b) a)
    (hgb_int : IntervalIntegrable (fun a => gab a b) volume A B)
    (hv'_int : IntervalIntegrable (fun a => b * fa a b / a - b * f a b / a ^ 2) volume A B)
    (hprod1 : IntervalIntegrable (fun a => gab a b * (f a b * b / a)) volume A B)
    (hprod2 : IntervalIntegrable
      (fun a => gb a b * (b * fa a b / a - b * f a b / a ^ 2)) volume A B)
    (hfA : f A b = 0) (hfB : f B b = 0) :
    ∫ x in A..B, f x b * b / x * gab x b
      = -∫ x in A..B, gb x b * (b * fa x b / x - b * f x b / x ^ 2) := by
  have hderiv : ∀ a ∈ [[A, B]], HasDerivAt (fun a' => f a' b * b / a')
      (b * fa a b / a - b * f a b / a ^ 2) a := by
    intro a ha
    have ha0 : a ≠ 0 := by
      have hmem : A ≤ a := by
        rw [Set.uIcc_of_le hAB] at ha
        exact ha.1
      exact ne_of_gt (lt_of_lt_of_le hA hmem)
    have h1 : HasDerivAt (fun a' => f a' b * b) (fa a b * b) a := (hfa a).mul_const b
    have h2 := h1.div (hasDerivAt_id' a) ha0
    convert h2 using 1
    field_simp
    ring
  have h := intervalIntegral.integral_deriv_mul_eq_sub (u := fun a => gb a b)
    (v := fun a => f a b * b / a) (u' := fun a => gab a b)
    (v' := fun a => b * fa a b / a - b * f a b / a ^ 2)
    (fun x _ => hgb x) hderiv hgb_int hv'_int
  rw [intervalIntegral.integral_add hprod1 hprod2] at h
  dsimp only at h
  have e : ∫ x in A..B, gab x b * (f x b * b / x)
      = ∫ x in A..B, f x b * b / x * gab x b := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [e, hfB, hfA] at h
  simp only [mul_zero, zero_mul, zero_div, sub_zero] at h
  linarith

/-- b 方向の部分積分（重みつき、a を固定）。W = y·fa/a − y·f/a² の b 微分は
  (fa/a − f/a²) + y·(fab/a − fb/a²) である。 -/
theorem ibp_b_weighted {f fa fb fab g gb : ℝ → ℝ → ℝ} {C D : ℝ} (a : ℝ)
    (hg : ∀ b, HasDerivAt (fun b' => g a b') (gb a b) b)
    (hfa : ∀ b, HasDerivAt (fun b' => fa a b') (fab a b) b)
    (hfb : ∀ b, HasDerivAt (fun b' => f a b') (fb a b) b)
    (hgb_int : IntervalIntegrable (fun b => gb a b) volume C D)
    (hW'_int : IntervalIntegrable
      (fun b => (fa a b / a - f a b / a ^ 2) + b * (fab a b / a - fb a b / a ^ 2))
      volume C D)
    (hprod1 : IntervalIntegrable (fun b => gb a b * (b * fa a b / a - b * f a b / a ^ 2))
      volume C D)
    (hprod2 : IntervalIntegrable
      (fun b => g a b * ((fa a b / a - f a b / a ^ 2) + b * (fab a b / a - fb a b / a ^ 2)))
      volume C D)
    (hgC : g a C = 0) (hgD : g a D = 0) :
    ∫ y in C..D, gb a y * (y * fa a y / a - y * f a y / a ^ 2)
      = -∫ y in C..D,
          g a y * ((fa a y / a - f a y / a ^ 2) + y * (fab a y / a - fb a y / a ^ 2)) := by
  have hderiv : ∀ b, HasDerivAt (fun b' => b' * fa a b' / a - b' * f a b' / a ^ 2)
      ((fa a b / a - f a b / a ^ 2) + b * (fab a b / a - fb a b / a ^ 2)) b := by
    intro b
    have h1 : HasDerivAt (fun b' => b' * fa a b') (fa a b + b * fab a b) b := by
      have h := (hasDerivAt_id' b).mul (hfa b)
      convert h using 1
      ring
    have h2 : HasDerivAt (fun b' => b' * f a b') (f a b + b * fb a b) b := by
      have h := (hasDerivAt_id' b).mul (hfb b)
      convert h using 1
      ring
    have h3 := (h1.div_const a).sub (h2.div_const (a ^ 2))
    convert h3 using 1
    ring
  have h := intervalIntegral.integral_deriv_mul_eq_sub (u := fun b => g a b)
    (v := fun b => b * fa a b / a - b * f a b / a ^ 2) (u' := fun b => gb a b)
    (v' := fun b => (fa a b / a - f a b / a ^ 2) + b * (fab a b / a - fb a b / a ^ 2))
    (fun y _ => hg y) (fun y _ => hderiv y) hgb_int hW'_int
  rw [intervalIntegral.integral_add hprod1 hprod2] at h
  dsimp only at h
  rw [hgD, hgC] at h
  simp only [mul_zero, zero_mul, sub_zero] at h
  linarith

/-- 【5-1】WDW 混合項 b·∂_a∂_b の随伴公式（密度形）。重み 1/a の内積では
  混合項は対称ではなく、随伴は 1 階の補正項を持つ。 -/
theorem wdw_mixed_adjoint {f g fa fb fab gb gab : ℝ → ℝ → ℝ} {A B C D : ℝ}
    (hAB : A ≤ B) (hCD : C ≤ D) (hA : 0 < A)
    (hfa_a : ∀ a b, HasDerivAt (fun a' => f a' b) (fa a b) a)
    (hfa_b : ∀ a b, HasDerivAt (fun b' => fa a b') (fab a b) b)
    (hfb_b : ∀ a b, HasDerivAt (fun b' => f a b') (fb a b) b)
    (hgb_a : ∀ a b, HasDerivAt (fun a' => gb a' b) (gab a b) a)
    (hgb_b : ∀ a b, HasDerivAt (fun b' => g a b') (gb a b) b)
    (hfA : ∀ b, f A b = 0) (hfB : ∀ b, f B b = 0)
    (hgC : ∀ a, g a C = 0) (hgD : ∀ a, g a D = 0)
    (hf_c : Continuous (Function.uncurry f)) (hfa_c : Continuous (Function.uncurry fa))
    (hfb_c : Continuous (Function.uncurry fb)) (hfab_c : Continuous (Function.uncurry fab))
    (hg_c : Continuous (Function.uncurry g)) (hgb_c : Continuous (Function.uncurry gb))
    (hgab_c : Continuous (Function.uncurry gab)) :
    ∫ x in A..B, ∫ y in C..D, f x y * y / x * gab x y
      = ∫ x in A..B, ∫ y in C..D,
          ((fa x y / x - f x y / x ^ 2) + y * (fab x y / x - fb x y / x ^ 2)) * g x y := by
  have cont_a : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ b : ℝ,
      Continuous fun a => F a b := by
    intro F hF b
    exact hF.comp (continuous_id.prod_mk continuous_const)
  have cont_b : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ a : ℝ,
      Continuous fun b => F a b := by
    intro F hF a
    exact hF.comp (continuous_const.prod_mk continuous_id)
  have hne_a : ∀ a ∈ [[A, B]], a ≠ 0 := by
    intro a ha
    rw [Set.uIcc_of_le hAB] at ha
    exact ne_of_gt (lt_of_lt_of_le hA ha.1)
  have hne_rect : ∀ p ∈ Set.Icc A B ×ˢ Set.Icc C D, p.1 ≠ 0 := by
    intro p hp
    exact ne_of_gt (lt_of_lt_of_le hA hp.1.1)
  have u1 : ∀ y, ContinuousOn (fun a => y * fa a y / a) [[A, B]] := by
    intro y
    exact ((continuous_const.mul (cont_a fa hfa_c y)).continuousOn.div
      continuous_id.continuousOn hne_a)
  have u2 : ∀ y, ContinuousOn (fun a => y * f a y / a ^ 2) [[A, B]] := by
    intro y
    exact ((continuous_const.mul (cont_a f hf_c y)).continuousOn.div
      (continuous_id.continuousOn.pow 2) (fun a ha => pow_ne_zero 2 (hne_a a ha)))
  have w1 : ∀ x, ContinuousOn (fun b => fa x b / x - f x b / x ^ 2) [[C, D]] := by
    intro x
    exact (((cont_b fa hfa_c x).continuousOn.div_const x).sub
      ((cont_b f hf_c x).continuousOn.div_const (x ^ 2)))
  have w2 : ∀ x, ContinuousOn (fun b => b * (fab x b / x - fb x b / x ^ 2)) [[C, D]] := by
    intro x
    exact continuous_id.continuousOn.mul
      (((cont_b fab hfab_c x).continuousOn.div_const x).sub
        ((cont_b fb hfb_c x).continuousOn.div_const (x ^ 2)))
  have w4 : ∀ x, ContinuousOn (fun b => b * fa x b / x - b * f x b / x ^ 2) [[C, D]] := by
    intro x
    exact ((continuous_id.continuousOn.mul (cont_b fa hfa_c x).continuousOn).div_const
      x).sub
      ((continuous_id.continuousOn.mul (cont_b f hf_c x).continuousOn).div_const (x ^ 2))
  have igb_a : ∀ y, IntervalIntegrable (fun a => gab a y) volume A B := fun y =>
    ((cont_a gab hgab_c y).continuousOn).intervalIntegrable
  have iW'_a : ∀ y, IntervalIntegrable (fun a => y * fa a y / a - y * f a y / a ^ 2)
      volume A B := fun y => ((u1 y).sub (u2 y)).intervalIntegrable
  have iprod1_a : ∀ y, IntervalIntegrable (fun a => gab a y * (f a y * y / a))
      volume A B := by
    intro y
    have v : ContinuousOn (fun a => f a y * y / a) [[A, B]] :=
      (((cont_a f hf_c y).mul continuous_const).continuousOn.div
        continuous_id.continuousOn hne_a)
    exact ((cont_a gab hgab_c y).continuousOn.mul v).intervalIntegrable
  have iprod2_a : ∀ y, IntervalIntegrable
      (fun a => gb a y * (y * fa a y / a - y * f a y / a ^ 2)) volume A B := fun y =>
    ((cont_a gb hgb_c y).continuousOn.mul ((u1 y).sub (u2 y))).intervalIntegrable
  have igb_b : ∀ x, IntervalIntegrable (fun b => gb x b) volume C D := fun x =>
    ((cont_b gb hgb_c x).continuousOn).intervalIntegrable
  have iW'_b : ∀ x, IntervalIntegrable
      (fun b => (fa x b / x - f x b / x ^ 2) + b * (fab x b / x - fb x b / x ^ 2))
      volume C D := fun x => ((w1 x).add (w2 x)).intervalIntegrable
  have iprod1_b : ∀ x, IntervalIntegrable
      (fun b => gb x b * (b * fa x b / x - b * f x b / x ^ 2)) volume C D := fun x =>
    ((cont_b gb hgb_c x).continuousOn.mul (w4 x)).intervalIntegrable
  have iprod2_b : ∀ x, IntervalIntegrable
      (fun b => g x b * ((fa x b / x - f x b / x ^ 2) + b * (fab x b / x - fb x b / x ^ 2)))
      volume C D := fun x =>
    ((cont_b g hg_c x).continuousOn.mul ((w1 x).add (w2 x))).intervalIntegrable
  have hswapL : Integrable (Function.uncurry fun x y => f x y * y / x * gab x y)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) := by
    apply integrable_prod_restrict_of_continuousOn
    show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * p.2 / p.1 * gab p.1 p.2)
      (Set.Icc A B ×ˢ Set.Icc C D)
    exact (((hf_c.continuousOn.mul continuous_snd.continuousOn).div
      continuous_fst.continuousOn hne_rect).mul hgab_c.continuousOn)
  have hswapM : Integrable
      (Function.uncurry fun x y => gb x y * (y * fa x y / x - y * f x y / x ^ 2))
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) := by
    apply integrable_prod_restrict_of_continuousOn
    show ContinuousOn
      (fun p : ℝ × ℝ => gb p.1 p.2 * (p.2 * fa p.1 p.2 / p.1 - p.2 * f p.1 p.2 / p.1 ^ 2))
      (Set.Icc A B ×ˢ Set.Icc C D)
    have t1 : ContinuousOn (fun p : ℝ × ℝ => p.2 * fa p.1 p.2 / p.1)
        (Set.Icc A B ×ˢ Set.Icc C D) :=
      (continuous_snd.continuousOn.mul hfa_c.continuousOn).div
        continuous_fst.continuousOn hne_rect
    have t2 : ContinuousOn (fun p : ℝ × ℝ => p.2 * f p.1 p.2 / p.1 ^ 2)
        (Set.Icc A B ×ˢ Set.Icc C D) :=
      (continuous_snd.continuousOn.mul hf_c.continuousOn).div
        (continuous_fst.continuousOn.pow 2) (fun p hp => pow_ne_zero 2 (hne_rect p hp))
    exact hgb_c.continuousOn.mul (t1.sub t2)
  have e1 : ∫ x in A..B, ∫ y in C..D, f x y * y / x * gab x y
      = ∫ y in C..D, ∫ x in A..B, f x y * y / x * gab x y :=
    intervalIntegral_swap hAB hCD hswapL
  have e2 : ∫ y in C..D, ∫ x in A..B, f x y * y / x * gab x y
      = -∫ y in C..D, ∫ x in A..B, gb x y * (y * fa x y / x - y * f x y / x ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    exact ibp_a_weighted y hAB hA (fun a => hgb_a a y) (fun a => hfa_a a y)
      (igb_a y) (iW'_a y) (iprod1_a y) (iprod2_a y) (hfA y) (hfB y)
  have e3 : ∫ y in C..D, ∫ x in A..B, gb x y * (y * fa x y / x - y * f x y / x ^ 2)
      = ∫ x in A..B, ∫ y in C..D, gb x y * (y * fa x y / x - y * f x y / x ^ 2) :=
    (intervalIntegral_swap hAB hCD hswapM).symm
  have e4 : ∫ x in A..B, ∫ y in C..D, gb x y * (y * fa x y / x - y * f x y / x ^ 2)
      = -∫ x in A..B, ∫ y in C..D,
          g x y * ((fa x y / x - f x y / x ^ 2) + y * (fab x y / x - fb x y / x ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact ibp_b_weighted x (fun b => hgb_b x b) (fun b => hfa_b x b) (fun b => hfb_b x b)
      (igb_b x) (iW'_b x) (iprod1_b x) (iprod2_b x) (hgC x) (hgD x)
  have e5 : ∫ x in A..B, ∫ y in C..D,
        g x y * ((fa x y / x - f x y / x ^ 2) + y * (fab x y / x - fb x y / x ^ 2))
      = ∫ x in A..B, ∫ y in C..D,
          ((fa x y / x - f x y / x ^ 2) + y * (fab x y / x - fb x y / x ^ 2)) * g x y := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    exact mul_comm _ _
  rw [e1, e2, e3, e4, neg_neg]
  exact e5

/-- 【5-1】WDW 混合項 b·∂_a∂_b の随伴公式（重み 1/a の内積形）。
  随伴は b·∂_a∂_b + ∂_a − (b/a)·∂_b − 1/a である。 -/
theorem wdw_mixed_adjoint_weighted {f g fa fb fab gb gab : ℝ → ℝ → ℝ} {A B C D : ℝ}
    (hAB : A ≤ B) (hCD : C ≤ D) (hA : 0 < A)
    (hfa_a : ∀ a b, HasDerivAt (fun a' => f a' b) (fa a b) a)
    (hfa_b : ∀ a b, HasDerivAt (fun b' => fa a b') (fab a b) b)
    (hfb_b : ∀ a b, HasDerivAt (fun b' => f a b') (fb a b) b)
    (hgb_a : ∀ a b, HasDerivAt (fun a' => gb a' b) (gab a b) a)
    (hgb_b : ∀ a b, HasDerivAt (fun b' => g a b') (gb a b) b)
    (hfA : ∀ b, f A b = 0) (hfB : ∀ b, f B b = 0)
    (hgC : ∀ a, g a C = 0) (hgD : ∀ a, g a D = 0)
    (hf_c : Continuous (Function.uncurry f)) (hfa_c : Continuous (Function.uncurry fa))
    (hfb_c : Continuous (Function.uncurry fb)) (hfab_c : Continuous (Function.uncurry fab))
    (hg_c : Continuous (Function.uncurry g)) (hgb_c : Continuous (Function.uncurry gb))
    (hgab_c : Continuous (Function.uncurry gab)) :
    ∫ x in A..B, ∫ y in C..D, f x y * (y * gab x y) * (1 / x)
      = ∫ x in A..B, ∫ y in C..D,
          (y * fab x y + fa x y - f x y / x - (y / x) * fb x y) * g x y * (1 / x) := by
  have h := wdw_mixed_adjoint hAB hCD hA hfa_a hfa_b hfb_b hgb_a hgb_b
    hfA hfB hgC hgD hf_c hfa_c hfb_c hfab_c hg_c hgb_c hgab_c
  have eL : ∫ x in A..B, ∫ y in C..D, f x y * (y * gab x y) * (1 / x)
      = ∫ x in A..B, ∫ y in C..D, f x y * y / x * gab x y := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y _
    have hx0 : x ≠ 0 := by
      have hmem : A ≤ x := by
        rw [Set.uIcc_of_le hAB] at hx
        exact hx.1
      exact ne_of_gt (lt_of_lt_of_le hA hmem)
    field_simp
    ring
  have eR : ∫ x in A..B, ∫ y in C..D,
        (y * fab x y + fa x y - f x y / x - (y / x) * fb x y) * g x y * (1 / x)
      = ∫ x in A..B, ∫ y in C..D,
          ((fa x y / x - f x y / x ^ 2) + y * (fab x y / x - fb x y / x ^ 2)) * g x y := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y _
    have hx0 : x ≠ 0 := by
      have hmem : A ≤ x := by
        rw [Set.uIcc_of_le hAB] at hx
        exact hx.1
      exact ne_of_gt (lt_of_lt_of_le hA hmem)
    field_simp
    ring
  rw [eL, eR]
  exact h

end

end CFT.WDWMix
