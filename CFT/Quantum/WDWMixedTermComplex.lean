import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 5-1（作用素の対称性）の本体への適用（混合項の複素版）。

  実関数版の随伴公式は `CFT.WDWMix`（`WDWMixedTerm.lean`）で証明済み：
  重み 1/a の内積では WDW 混合項 b·∂_a∂_b は対称ではなく、随伴は
    b·∂_a∂_b + ∂_a − (b/a)·∂_b − 1/a
  である。ここではその共役つき版を示す。共役つきの重み 1/a の内積
  ⟨f, g⟩ = ∫∫ f̄ g (dx dy / a)（矩形上、ディリクレ境界、0 < A）に対し、
  随伴は実随伴式の共役に等しい（`wdw_mixed_adjoint_weighted_complex`、
  `wdw_mixed_adjoint_expr_star`）：
    ⟨f, b ∂_a∂_b g⟩ = ⟨b ∂_a∂_b f + ∂_a f − (b/a) ∂_b f − f/a, g⟩
  （右辺の随伴は f 側に共役をつけた形で読む）。証明は実関数版の証明を
  ℂ 値関数に持ち上げたものである：f 側を共役にした重みつき部分積分
  （`ibp_a_weighted_complex`、`ibp_b_weighted_complex`）と、複素版の
  積分順序交換（フビニ）を組み立てる。`HasDerivAt.star` により共役は
  微分を通り抜け、実係数のため共役は随伴式の係数を通り抜ける。
  ℂ 上では `linarith` が使えないため、部分積分の最後の組み立ては
  `linear_combination` で行う（`WDWComplexSymmetry.lean` と同じ流儀）。
  純粋な混合微分 ∂_a∂_b の複素版の対称性（平坦な測度）は別葉として残る。
-/

namespace CFT.WDWMixComplex

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- 区間積分の順序交換（フビニ、複素値版）。 -/
theorem intervalIntegral_swap {F : ℝ → ℝ → ℂ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D)))) :
    ∫ x in A..B, ∫ y in C..D, F x y = ∫ y in C..D, ∫ x in A..B, F x y := by
  simp only [intervalIntegral.integral_of_le hAB, intervalIntegral.integral_of_le hCD]
  exact MeasureTheory.integral_integral_swap hF

/-- 矩形上で連続な複素値関数は、区間の積に対する制限測度の積に関して可積分である。 -/
theorem integrable_prod_restrict_of_continuousOn {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
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

/-- a 方向の部分積分（重みつき、b を固定、複素版）。f 側は共役をつけた形で現れる：
  ∫ f̄·(b/a)·gab = −∫ gb·(b·f̄_a/a − b·f̄/a²)。 -/
theorem ibp_a_weighted_complex {f fa gb gab : ℝ → ℝ → ℂ} {A B : ℝ} (b : ℝ) (hAB : A ≤ B)
    (hA : 0 < A)
    (hgb : ∀ a, HasDerivAt (fun a' => gb a' b) (gab a b) a)
    (hfa : ∀ a, HasDerivAt (fun a' => star (f a' b)) (star (fa a b)) a)
    (hgb_int : IntervalIntegrable (fun a => gab a b) volume A B)
    (hv'_int : IntervalIntegrable
      (fun a => (b : ℂ) * star (fa a b) / (a : ℂ) - (b : ℂ) * star (f a b) / (a : ℂ) ^ 2)
      volume A B)
    (hprod1 : IntervalIntegrable (fun a => gab a b * (star (f a b) * (b : ℂ) / (a : ℂ)))
      volume A B)
    (hprod2 : IntervalIntegrable
      (fun a => gb a b * ((b : ℂ) * star (fa a b) / (a : ℂ)
        - (b : ℂ) * star (f a b) / (a : ℂ) ^ 2)) volume A B)
    (hfA : f A b = 0) (hfB : f B b = 0) :
    ∫ x in A..B, star (f x b) * (b : ℂ) / (x : ℂ) * gab x b
      = -∫ x in A..B, gb x b * ((b : ℂ) * star (fa x b) / (x : ℂ)
        - (b : ℂ) * star (f x b) / (x : ℂ) ^ 2) := by
  have hderiv : ∀ a ∈ [[A, B]], HasDerivAt (fun a' => star (f a' b) * (b : ℂ) / (a' : ℂ))
      ((b : ℂ) * star (fa a b) / (a : ℂ) - (b : ℂ) * star (f a b) / (a : ℂ) ^ 2) a := by
    intro a ha
    have ha0 : (a : ℂ) ≠ 0 := by
      have hmem : A ≤ a := by
        rw [Set.uIcc_of_le hAB] at ha
        exact ha.1
      exact_mod_cast (lt_of_lt_of_le hA hmem).ne'
    have h1 : HasDerivAt (fun a' => star (f a' b) * (b : ℂ)) (star (fa a b) * (b : ℂ)) a :=
      (hfa a).mul_const (b : ℂ)
    have h2 := h1.div (hasDerivAt_id' a).ofReal_comp ha0
    convert h2 using 1
    field_simp
    ring
  have h := intervalIntegral.integral_deriv_mul_eq_sub (u := fun a => gb a b)
    (v := fun a => star (f a b) * (b : ℂ) / (a : ℂ)) (u' := fun a => gab a b)
    (v' := fun a => (b : ℂ) * star (fa a b) / (a : ℂ)
      - (b : ℂ) * star (f a b) / (a : ℂ) ^ 2)
    (fun x _ => hgb x) hderiv hgb_int hv'_int
  rw [intervalIntegral.integral_add hprod1 hprod2] at h
  dsimp only at h
  have e : ∫ x in A..B, gab x b * (star (f x b) * (b : ℂ) / (x : ℂ))
      = ∫ x in A..B, star (f x b) * (b : ℂ) / (x : ℂ) * gab x b := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [e, hfB, hfA] at h
  simp only [star_zero, mul_zero, zero_mul, zero_div, sub_zero] at h
  linear_combination h

/-- b 方向の部分積分（重みつき、a を固定、複素版）。W = b·f̄_a/a − b·f̄/a² の b 微分は
  (f̄_a/a − f̄/a²) + b·(f̄_ab/a − f̄_b/a²) である。 -/
theorem ibp_b_weighted_complex {f fa fb fab g gb : ℝ → ℝ → ℂ} {C D : ℝ} (a : ℝ)
    (hg : ∀ b, HasDerivAt (fun b' => g a b') (gb a b) b)
    (hfa : ∀ b, HasDerivAt (fun b' => star (fa a b')) (star (fab a b)) b)
    (hfb : ∀ b, HasDerivAt (fun b' => star (f a b')) (star (fb a b)) b)
    (hgb_int : IntervalIntegrable (fun b => gb a b) volume C D)
    (hW'_int : IntervalIntegrable
      (fun b => (star (fa a b) / (a : ℂ) - star (f a b) / (a : ℂ) ^ 2)
        + (b : ℂ) * (star (fab a b) / (a : ℂ) - star (fb a b) / (a : ℂ) ^ 2))
      volume C D)
    (hprod1 : IntervalIntegrable
      (fun b => gb a b * ((b : ℂ) * star (fa a b) / (a : ℂ)
        - (b : ℂ) * star (f a b) / (a : ℂ) ^ 2)) volume C D)
    (hprod2 : IntervalIntegrable
      (fun b => g a b * ((star (fa a b) / (a : ℂ) - star (f a b) / (a : ℂ) ^ 2)
        + (b : ℂ) * (star (fab a b) / (a : ℂ) - star (fb a b) / (a : ℂ) ^ 2)))
      volume C D)
    (hgC : g a C = 0) (hgD : g a D = 0) :
    ∫ y in C..D, gb a y * ((y : ℂ) * star (fa a y) / (a : ℂ)
        - (y : ℂ) * star (f a y) / (a : ℂ) ^ 2)
      = -∫ y in C..D,
          g a y * ((star (fa a y) / (a : ℂ) - star (f a y) / (a : ℂ) ^ 2)
            + (y : ℂ) * (star (fab a y) / (a : ℂ) - star (fb a y) / (a : ℂ) ^ 2)) := by
  have hderiv : ∀ (b : ℝ), HasDerivAt
      (fun (b' : ℝ) => (b' : ℂ) * star (fa a b') / (a : ℂ) - (b' : ℂ) * star (f a b') / (a : ℂ) ^ 2)
      ((star (fa a b) / (a : ℂ) - star (f a b) / (a : ℂ) ^ 2)
        + (b : ℂ) * (star (fab a b) / (a : ℂ) - star (fb a b) / (a : ℂ) ^ 2)) b := by
    intro b
    have h1 : HasDerivAt (fun (b' : ℝ) => (b' : ℂ) * star (fa a b'))
        (star (fa a b) + (b : ℂ) * star (fab a b)) b := by
      have h := (hasDerivAt_id' b).ofReal_comp.mul (hfa b)
      simpa using h
    have h2 : HasDerivAt (fun (b' : ℝ) => (b' : ℂ) * star (f a b'))
        (star (f a b) + (b : ℂ) * star (fb a b)) b := by
      have h := (hasDerivAt_id' b).ofReal_comp.mul (hfb b)
      simpa using h
    have h3 := (h1.div_const (a : ℂ)).sub (h2.div_const ((a : ℂ) ^ 2))
    convert h3 using 1
    ring
  have h := intervalIntegral.integral_deriv_mul_eq_sub (u := fun b => g a b)
    (v := fun b => (b : ℂ) * star (fa a b) / (a : ℂ) - (b : ℂ) * star (f a b) / (a : ℂ) ^ 2)
    (u' := fun b => gb a b)
    (v' := fun b => (star (fa a b) / (a : ℂ) - star (f a b) / (a : ℂ) ^ 2)
      + (b : ℂ) * (star (fab a b) / (a : ℂ) - star (fb a b) / (a : ℂ) ^ 2))
    (fun y _ => hg y) (fun y _ => hderiv y) hgb_int hW'_int
  rw [intervalIntegral.integral_add hprod1 hprod2] at h
  dsimp only at h
  rw [hgD, hgC] at h
  simp only [mul_zero, zero_mul, sub_zero] at h
  linear_combination h

/-- 【5-1】WDW 混合項 b·∂_a∂_b の随伴公式（密度形、複素版）。重み 1/a の内積では
  混合項は対称ではなく、随伴は 1 階の補正項を持つ（f 側は共役つき）。 -/
theorem wdw_mixed_adjoint_complex {f g fa fb fab gb gab : ℝ → ℝ → ℂ} {A B C D : ℝ}
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
    ∫ x in A..B, ∫ y in C..D, star (f x y) * (y : ℂ) / (x : ℂ) * gab x y
      = ∫ x in A..B, ∫ y in C..D,
          ((star (fa x y) / (x : ℂ) - star (f x y) / (x : ℂ) ^ 2)
            + (y : ℂ) * (star (fab x y) / (x : ℂ) - star (fb x y) / (x : ℂ) ^ 2)) * g x y := by
  have cont_a : ∀ (F : ℝ → ℝ → ℂ), Continuous (Function.uncurry F) → ∀ b : ℝ,
      Continuous fun a => F a b := by
    intro F hF b
    exact hF.comp (continuous_id.prod_mk continuous_const)
  have cont_b : ∀ (F : ℝ → ℝ → ℂ), Continuous (Function.uncurry F) → ∀ a : ℝ,
      Continuous fun b => F a b := by
    intro F hF a
    exact hF.comp (continuous_const.prod_mk continuous_id)
  have hne_a : ∀ a ∈ [[A, B]], (a : ℂ) ≠ 0 := by
    intro a ha
    rw [Set.uIcc_of_le hAB] at ha
    exact_mod_cast (lt_of_lt_of_le hA ha.1).ne'
  have hne_rect : ∀ p ∈ Set.Icc A B ×ˢ Set.Icc C D, (p.1 : ℂ) ≠ 0 := by
    intro p hp
    exact_mod_cast (lt_of_lt_of_le hA hp.1.1).ne'
  have u1 : ∀ (y : ℝ), ContinuousOn (fun a => (y : ℂ) * star (fa a y) / (a : ℂ)) [[A, B]] := by
    intro y
    exact ((continuous_const.mul (cont_a fa hfa_c y).star).continuousOn.div
      Complex.continuous_ofReal.continuousOn hne_a)
  have u2 : ∀ (y : ℝ), ContinuousOn (fun a => (y : ℂ) * star (f a y) / (a : ℂ) ^ 2) [[A, B]] := by
    intro y
    exact ((continuous_const.mul (cont_a f hf_c y).star).continuousOn.div
      (Complex.continuous_ofReal.continuousOn.pow 2) (fun a ha => pow_ne_zero 2 (hne_a a ha)))
  have w1 : ∀ x, ContinuousOn
      (fun b => star (fa x b) / (x : ℂ) - star (f x b) / (x : ℂ) ^ 2) [[C, D]] := by
    intro x
    exact (((cont_b fa hfa_c x).star.continuousOn.div_const (x : ℂ)).sub
      ((cont_b f hf_c x).star.continuousOn.div_const ((x : ℂ) ^ 2)))
  have w2 : ∀ x, ContinuousOn
      (fun (b : ℝ) => (b : ℂ) * (star (fab x b) / (x : ℂ) - star (fb x b) / (x : ℂ) ^ 2))
      [[C, D]] := by
    intro x
    exact Complex.continuous_ofReal.continuousOn.mul
      (((cont_b fab hfab_c x).star.continuousOn.div_const (x : ℂ)).sub
        ((cont_b fb hfb_c x).star.continuousOn.div_const ((x : ℂ) ^ 2)))
  have w4 : ∀ x, ContinuousOn
      (fun (b : ℝ) => (b : ℂ) * star (fa x b) / (x : ℂ) - (b : ℂ) * star (f x b) / (x : ℂ) ^ 2)
      [[C, D]] := by
    intro x
    exact ((Complex.continuous_ofReal.continuousOn.mul
      (cont_b fa hfa_c x).star.continuousOn).div_const (x : ℂ)).sub
      ((Complex.continuous_ofReal.continuousOn.mul
        (cont_b f hf_c x).star.continuousOn).div_const ((x : ℂ) ^ 2))
  have igb_a : ∀ y, IntervalIntegrable (fun a => gab a y) volume A B := fun y =>
    ((cont_a gab hgab_c y).continuousOn).intervalIntegrable
  have iW'_a : ∀ (y : ℝ), IntervalIntegrable
      (fun a => (y : ℂ) * star (fa a y) / (a : ℂ) - (y : ℂ) * star (f a y) / (a : ℂ) ^ 2)
      volume A B := fun y => ((u1 y).sub (u2 y)).intervalIntegrable
  have iprod1_a : ∀ y, IntervalIntegrable
      (fun a => gab a y * (star (f a y) * (y : ℂ) / (a : ℂ))) volume A B := by
    intro y
    have v : ContinuousOn (fun a => star (f a y) * (y : ℂ) / (a : ℂ)) [[A, B]] :=
      (((cont_a f hf_c y).star.mul continuous_const).continuousOn.div
        Complex.continuous_ofReal.continuousOn hne_a)
    exact ((cont_a gab hgab_c y).continuousOn.mul v).intervalIntegrable
  have iprod2_a : ∀ y, IntervalIntegrable
      (fun a => gb a y * ((y : ℂ) * star (fa a y) / (a : ℂ)
        - (y : ℂ) * star (f a y) / (a : ℂ) ^ 2)) volume A B := fun y =>
    ((cont_a gb hgb_c y).continuousOn.mul ((u1 y).sub (u2 y))).intervalIntegrable
  have igb_b : ∀ x, IntervalIntegrable (fun b => gb x b) volume C D := fun x =>
    ((cont_b gb hgb_c x).continuousOn).intervalIntegrable
  have iW'_b : ∀ x, IntervalIntegrable
      (fun b => (star (fa x b) / (x : ℂ) - star (f x b) / (x : ℂ) ^ 2)
        + (b : ℂ) * (star (fab x b) / (x : ℂ) - star (fb x b) / (x : ℂ) ^ 2))
      volume C D := fun x => ((w1 x).add (w2 x)).intervalIntegrable
  have iprod1_b : ∀ x, IntervalIntegrable
      (fun b => gb x b * ((b : ℂ) * star (fa x b) / (x : ℂ)
        - (b : ℂ) * star (f x b) / (x : ℂ) ^ 2)) volume C D := fun x =>
    ((cont_b gb hgb_c x).continuousOn.mul (w4 x)).intervalIntegrable
  have iprod2_b : ∀ x, IntervalIntegrable
      (fun b => g x b * ((star (fa x b) / (x : ℂ) - star (f x b) / (x : ℂ) ^ 2)
        + (b : ℂ) * (star (fab x b) / (x : ℂ) - star (fb x b) / (x : ℂ) ^ 2)))
      volume C D := fun x =>
    ((cont_b g hg_c x).continuousOn.mul ((w1 x).add (w2 x))).intervalIntegrable
  have hswapL : Integrable
      (Function.uncurry fun x y => star (f x y) * (y : ℂ) / (x : ℂ) * gab x y)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) := by
    apply integrable_prod_restrict_of_continuousOn
    show ContinuousOn
      (fun p : ℝ × ℝ => star (f p.1 p.2) * (p.2 : ℂ) / (p.1 : ℂ) * gab p.1 p.2)
      (Set.Icc A B ×ˢ Set.Icc C D)
    exact (((hf_c.continuousOn.star.mul
      (Complex.continuous_ofReal.comp continuous_snd).continuousOn).div
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn hne_rect).mul
      hgab_c.continuousOn)
  have hswapM : Integrable
      (Function.uncurry fun x y => gb x y * ((y : ℂ) * star (fa x y) / (x : ℂ)
        - (y : ℂ) * star (f x y) / (x : ℂ) ^ 2))
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) := by
    apply integrable_prod_restrict_of_continuousOn
    show ContinuousOn
      (fun p : ℝ × ℝ => gb p.1 p.2 * ((p.2 : ℂ) * star (fa p.1 p.2) / (p.1 : ℂ)
        - (p.2 : ℂ) * star (f p.1 p.2) / (p.1 : ℂ) ^ 2))
      (Set.Icc A B ×ˢ Set.Icc C D)
    have t1 : ContinuousOn
        (fun p : ℝ × ℝ => (p.2 : ℂ) * star (fa p.1 p.2) / (p.1 : ℂ))
        (Set.Icc A B ×ˢ Set.Icc C D) :=
      ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
        hfa_c.continuousOn.star).div
        (Complex.continuous_ofReal.comp continuous_fst).continuousOn hne_rect
    have t2 : ContinuousOn
        (fun p : ℝ × ℝ => (p.2 : ℂ) * star (f p.1 p.2) / (p.1 : ℂ) ^ 2)
        (Set.Icc A B ×ˢ Set.Icc C D) :=
      ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
        hf_c.continuousOn.star).div
        ((Complex.continuous_ofReal.comp continuous_fst).continuousOn.pow 2)
        (fun p hp => pow_ne_zero 2 (hne_rect p hp))
    exact hgb_c.continuousOn.mul (t1.sub t2)
  have e1 : ∫ x in A..B, ∫ y in C..D, star (f x y) * (y : ℂ) / (x : ℂ) * gab x y
      = ∫ y in C..D, ∫ x in A..B, star (f x y) * (y : ℂ) / (x : ℂ) * gab x y :=
    intervalIntegral_swap hAB hCD hswapL
  have e2 : ∫ y in C..D, ∫ x in A..B, star (f x y) * (y : ℂ) / (x : ℂ) * gab x y
      = -∫ y in C..D, ∫ x in A..B, gb x y * ((y : ℂ) * star (fa x y) / (x : ℂ)
          - (y : ℂ) * star (f x y) / (x : ℂ) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    exact ibp_a_weighted_complex y hAB hA (fun a => hgb_a a y) (fun a => (hfa_a a y).star)
      (igb_a y) (iW'_a y) (iprod1_a y) (iprod2_a y) (hfA y) (hfB y)
  have e3 : ∫ y in C..D, ∫ x in A..B, gb x y * ((y : ℂ) * star (fa x y) / (x : ℂ)
        - (y : ℂ) * star (f x y) / (x : ℂ) ^ 2)
      = ∫ x in A..B, ∫ y in C..D, gb x y * ((y : ℂ) * star (fa x y) / (x : ℂ)
          - (y : ℂ) * star (f x y) / (x : ℂ) ^ 2) :=
    (intervalIntegral_swap hAB hCD hswapM).symm
  have e4 : ∫ x in A..B, ∫ y in C..D, gb x y * ((y : ℂ) * star (fa x y) / (x : ℂ)
        - (y : ℂ) * star (f x y) / (x : ℂ) ^ 2)
      = -∫ x in A..B, ∫ y in C..D,
          g x y * ((star (fa x y) / (x : ℂ) - star (f x y) / (x : ℂ) ^ 2)
            + (y : ℂ) * (star (fab x y) / (x : ℂ) - star (fb x y) / (x : ℂ) ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact ibp_b_weighted_complex x (fun b => hgb_b x b) (fun b => (hfa_b x b).star)
      (fun b => (hfb_b x b).star) (igb_b x) (iW'_b x) (iprod1_b x) (iprod2_b x)
      (hgC x) (hgD x)
  have e5 : ∫ x in A..B, ∫ y in C..D,
        g x y * ((star (fa x y) / (x : ℂ) - star (f x y) / (x : ℂ) ^ 2)
          + (y : ℂ) * (star (fab x y) / (x : ℂ) - star (fb x y) / (x : ℂ) ^ 2))
      = ∫ x in A..B, ∫ y in C..D,
          ((star (fa x y) / (x : ℂ) - star (f x y) / (x : ℂ) ^ 2)
            + (y : ℂ) * (star (fab x y) / (x : ℂ) - star (fb x y) / (x : ℂ) ^ 2)) * g x y := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    exact mul_comm _ _
  rw [e1, e2, e3, e4, neg_neg]
  exact e5

/-- 【5-1】WDW 混合項 b·∂_a∂_b の随伴公式（重み 1/a の内積形、複素版）。
  随伴は b·∂_a∂_b + ∂_a − (b/a)·∂_b − 1/a で、f 側に共役がついた形で現れる。 -/
theorem wdw_mixed_adjoint_weighted_complex {f g fa fb fab gb gab : ℝ → ℝ → ℂ} {A B C D : ℝ}
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
    ∫ x in A..B, ∫ y in C..D, star (f x y) * ((y : ℂ) * gab x y) * (1 / (x : ℂ))
      = ∫ x in A..B, ∫ y in C..D,
          ((y : ℂ) * star (fab x y) + star (fa x y) - star (f x y) / (x : ℂ)
            - ((y : ℂ) / (x : ℂ)) * star (fb x y)) * g x y * (1 / (x : ℂ)) := by
  have h := wdw_mixed_adjoint_complex hAB hCD hA hfa_a hfa_b hfb_b hgb_a hgb_b
    hfA hfB hgC hgD hf_c hfa_c hfb_c hfab_c hg_c hgb_c hgab_c
  have eL : ∫ x in A..B, ∫ y in C..D, star (f x y) * ((y : ℂ) * gab x y) * (1 / (x : ℂ))
      = ∫ x in A..B, ∫ y in C..D, star (f x y) * (y : ℂ) / (x : ℂ) * gab x y := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y _
    have hx0 : (x : ℂ) ≠ 0 := by
      have hmem : A ≤ x := by
        rw [Set.uIcc_of_le hAB] at hx
        exact hx.1
      exact_mod_cast (lt_of_lt_of_le hA hmem).ne'
    field_simp
    ring
  have eR : ∫ x in A..B, ∫ y in C..D,
        ((y : ℂ) * star (fab x y) + star (fa x y) - star (f x y) / (x : ℂ)
          - ((y : ℂ) / (x : ℂ)) * star (fb x y)) * g x y * (1 / (x : ℂ))
      = ∫ x in A..B, ∫ y in C..D,
          ((star (fa x y) / (x : ℂ) - star (f x y) / (x : ℂ) ^ 2)
            + (y : ℂ) * (star (fab x y) / (x : ℂ) - star (fb x y) / (x : ℂ) ^ 2)) * g x y := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y _
    have hx0 : (x : ℂ) ≠ 0 := by
      have hmem : A ≤ x := by
        rw [Set.uIcc_of_le hAB] at hx
        exact hx.1
      exact_mod_cast (lt_of_lt_of_le hA hmem).ne'
    field_simp
    ring
  rw [eL, eR]
  exact h

/-- 随伴の表示は、実随伴式の共役に等しい（係数が実のため共役は係数を通り抜ける）。 -/
theorem wdw_mixed_adjoint_expr_star (f fa fb fab : ℝ → ℝ → ℂ) (x y : ℝ) :
    (y : ℂ) * star (fab x y) + star (fa x y) - star (f x y) / (x : ℂ)
        - ((y : ℂ) / (x : ℂ)) * star (fb x y)
      = star ((y : ℂ) * fab x y + fa x y - f x y / (x : ℂ)
        - ((y : ℂ) / (x : ℂ)) * fb x y) := by
  simp

end

end CFT.WDWMixComplex
