import Mathlib
import CFT.Foundations.PeriodicIntegrationByParts
import CFT.Quantum.WDWExactWKB
import CFT.Quantum.WDWSymmetry

/-!
  命題集 `LEAN_GAP_TREES.md` 5-1（作用素の対称性）の複素版。

  実関数版は `CFT.WDWSymm`（`WDWSymmetry.lean`）で、混合項の随伴公式は
  `CFT.WDWMix`（`WDWMixedTerm.lean`）で証明済み。ここでは a-部分の対称性を
  共役つきの内積 ⟨f, g⟩ = ∫_A^B f̄ g (dx/x)（0 < A）に対して示す
  （`wdw_a_symm_complex`）。核は複素値関数のディリクレ境界での
  −d²/dx² の対称性（`integral_secondDeriv_symm_dirichlet_complex_AB`）で、
  共役をつけた側の部分積分（`HasDerivAt.star`）と、共役をつけない側の
  部分積分を組み合わせる。実係数の作用素なので共役は係数を通り抜ける
  （`star_wdwAPartC`）。混合項の複素版は別葉。
  `wdwAPartC_eq_wdwOp` で複素 a-部分が実際の `wdwOp` の Ψ_ab = 0 の
  場合であることを確認してある。
-/

namespace CFT.WDWComplex

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- WDW 作用素の a-部分（複素値版、実係数）。`wdwAPart` の複素値への持ち上げ。 -/
def wdwAPartC (c l hb b a : ℝ) (Ψ Ψaa : ℂ) : ℂ :=
  (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (a : ℂ) * Ψaa
    - (((c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (a : ℂ) * Ψ

/-- `wdwAPartC` は `wdwOp` の Ψ_ab = 0 の場合。 -/
theorem wdwAPartC_eq_wdwOp (c l hb b a : ℝ) (Ψ Ψaa : ℂ) :
    wdwAPartC c l hb b a Ψ Ψaa = CFT.WKB.wdwOp c l hb a b Ψ Ψaa 0 := by
  simp only [wdwAPartC, CFT.WKB.wdwOp]
  push_cast
  ring

/-- 実関数に適用した `wdwAPartC` は実の `wdwAPart` のキャストに一致する。 -/
theorem wdwAPartC_eq_ofReal (c l hb b a : ℝ) (Ψ Ψaa : ℝ) :
    wdwAPartC c l hb b a (Ψ : ℂ) (Ψaa : ℂ) = (CFT.WDWSymm.wdwAPart c l hb b a Ψ Ψaa : ℂ) := by
  simp only [wdwAPartC, CFT.WDWSymm.wdwAPart]
  push_cast
  ring

/-- 実係数のため、共役は `wdwAPartC` を通り抜ける。 -/
theorem star_wdwAPartC (c l hb b a : ℝ) (Ψ Ψaa : ℂ) :
    star (wdwAPartC c l hb b a Ψ Ψaa) = wdwAPartC c l hb b a (star Ψ) (star Ψaa) := by
  simp only [wdwAPartC]
  simp

/-- 複素値関数のディリクレ境界での −d²/dx² の対称性：両端で消える f, g に対し
  ∫ f̄₂ g = ∫ f̄ g₂（区間 [A, B] 版）。 -/
theorem integral_secondDeriv_symm_dirichlet_complex_AB {f g f₁ f₂ g₁ g₂ : ℝ → ℂ} {A B : ℝ}
    (hf₁ : ∀ x, HasDerivAt f (f₁ x) x) (hf₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hg₁ : ∀ x, HasDerivAt g (g₁ x) x) (hg₂ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hg₁' : IntervalIntegrable g₁ volume A B) (hg₂' : IntervalIntegrable g₂ volume A B)
    (hf₁s' : IntervalIntegrable (fun x => star (f₁ x)) volume A B)
    (hf₂s' : IntervalIntegrable (fun x => star (f₂ x)) volume A B)
    (hfg : IntervalIntegrable (fun x => star (f₂ x) * g x) volume A B)
    (hf₁g₁ : IntervalIntegrable (fun x => star (f₁ x) * g₁ x) volume A B)
    (hg₂fs : IntervalIntegrable (fun x => g₂ x * star (f x)) volume A B)
    (hg₁f₁s : IntervalIntegrable (fun x => g₁ x * star (f₁ x)) volume A B)
    (hfA : f A = 0) (hfB : f B = 0) (hgA : g A = 0) (hgB : g B = 0) :
    ∫ x in A..B, star (f₂ x) * g x = ∫ x in A..B, star (f x) * g₂ x := by
  have hA := integral_deriv_mul_eq_sub (u := fun x => star (f₁ x)) (v := g)
    (u' := fun x => star (f₂ x)) (v' := g₁)
    (fun x _ => (hf₂ x).star) (fun x _ => hg₁ x) hf₂s' hg₁'
  rw [integral_add hfg hf₁g₁] at hA
  simp only [hgB, hgA, mul_zero, sub_zero] at hA
  have hB := integral_deriv_mul_eq_sub (u := g₁) (v := fun x => star (f x))
    (u' := g₂) (v' := fun x => star (f₁ x))
    (fun x _ => hg₂ x) (fun x _ => (hf₁ x).star) hg₂' hf₁s'
  rw [integral_add hg₂fs hg₁f₁s] at hB
  simp only [hfB, hfA, star_zero, mul_zero, sub_zero] at hB
  have e1 : (fun x => g₂ x * star (f x)) = (fun x => star (f x) * g₂ x) :=
    funext fun x => mul_comm _ _
  have e2 : (fun x => g₁ x * star (f₁ x)) = (fun x => star (f₁ x) * g₁ x) :=
    funext fun x => mul_comm _ _
  rw [e1, e2] at hB
  linear_combination hA - hB

/-- 【5-1】WDW 作用素の a-部分は、共役つきの重み 1/a の内積に関して対称
  （b を固定、ディリクレ境界、区間 [A, B] ⊂ (0, ∞)、複素値関数版）。 -/
theorem wdw_a_symm_complex {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (c l hb b : ℝ)
    {f g f₁ f₂ g₁ g₂ : ℝ → ℂ}
    (hf₁ : ∀ x, HasDerivAt f (f₁ x) x) (hf₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hg₁ : ∀ x, HasDerivAt g (g₁ x) x) (hg₂ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hg₁' : IntervalIntegrable g₁ volume A B) (hg₂' : IntervalIntegrable g₂ volume A B)
    (hf₁s' : IntervalIntegrable (fun x => star (f₁ x)) volume A B)
    (hf₂s' : IntervalIntegrable (fun x => star (f₂ x)) volume A B)
    (hfg₂ : IntervalIntegrable (fun x => star (f x) * g₂ x) volume A B)
    (hf₂g : IntervalIntegrable (fun x => star (f₂ x) * g x) volume A B)
    (hfg : IntervalIntegrable (fun x => star (f x) * g x) volume A B)
    (hf₁g₁ : IntervalIntegrable (fun x => star (f₁ x) * g₁ x) volume A B)
    (hg₂fs : IntervalIntegrable (fun x => g₂ x * star (f x)) volume A B)
    (hg₁f₁s : IntervalIntegrable (fun x => g₁ x * star (f₁ x)) volume A B)
    (hfA : f A = 0) (hfB : f B = 0) (hgA : g A = 0) (hgB : g B = 0) :
    ∫ x in A..B, star (f x) * wdwAPartC c l hb b x (g x) (g₂ x) * (1 / (x : ℂ))
      = ∫ x in A..B, star (wdwAPartC c l hb b x (f x) (f₂ x)) * g x * (1 / (x : ℂ)) := by
  have hmem : ∀ x ∈ [[A, B]], (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact lt_of_lt_of_le hA hx.1
  have eL : Set.EqOn (fun x => star (f x) * wdwAPartC c l hb b x (g x) (g₂ x) * (1 / (x : ℂ)))
      (fun x => (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f x) * g₂ x)
        + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x)) [[A, B]] := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hmem x hx).ne'
    have key : (x : ℂ) * (1 / (x : ℂ)) = 1 := mul_one_div_cancel hx0
    calc star (f x) * wdwAPartC c l hb b x (g x) (g₂ x) * (1 / (x : ℂ))
        = ((((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f x) * g₂ x)
            + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x))
            * ((x : ℂ) * (1 / (x : ℂ))) := by
          simp only [wdwAPartC]; push_cast; ring
      _ = _ := by rw [key, mul_one]
  have eR : Set.EqOn (fun x => star (wdwAPartC c l hb b x (f x) (f₂ x)) * g x * (1 / (x : ℂ)))
      (fun x => (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f₂ x) * g x)
        + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x)) [[A, B]] := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hmem x hx).ne'
    have key : (x : ℂ) * (1 / (x : ℂ)) = 1 := mul_one_div_cancel hx0
    simp only [star_wdwAPartC]
    calc wdwAPartC c l hb b x (star (f x)) (star (f₂ x)) * g x * (1 / (x : ℂ))
        = ((((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f₂ x) * g x)
            + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x))
            * ((x : ℂ) * (1 / (x : ℂ))) := by
          simp only [wdwAPartC]; push_cast; ring
      _ = _ := by rw [key, mul_one]
  have hsym := integral_secondDeriv_symm_dirichlet_complex_AB hf₁ hf₂ hg₁ hg₂ hg₁' hg₂'
    hf₁s' hf₂s' hf₂g hf₁g₁ hg₂fs hg₁f₁s hfA hfB hgA hgB
  have hkin : ∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f x) * g₂ x)
      = ∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f₂ x) * g x) := by
    rw [integral_const_mul, integral_const_mul, hsym]
  have eL' : ∫ x in A..B, star (f x) * wdwAPartC c l hb b x (g x) (g₂ x) * (1 / (x : ℂ))
      = ∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f x) * g₂ x)
          + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x) :=
    integral_congr eL
  have eR' : ∫ x in A..B, star (wdwAPartC c l hb b x (f x) (f₂ x)) * g x * (1 / (x : ℂ))
      = ∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f₂ x) * g x)
          + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x) :=
    integral_congr eR
  have haddL : ∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f x) * g₂ x)
        + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x)
      = (∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f x) * g₂ x))
        + ∫ x in A..B, (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x) :=
    integral_add (hfg₂.const_mul _) (hfg.const_mul _)
  have haddR : ∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f₂ x) * g x)
        + (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x)
      = (∫ x in A..B, (((1 / (4 * c)) * (-hb ^ 2) : ℝ) : ℂ) * (star (f₂ x) * g x))
        + ∫ x in A..B, (((-c * (b ^ 2 - l ^ 2) : ℝ)) : ℂ) * (star (f x) * g x) :=
    integral_add (hf₂g.const_mul _) (hfg.const_mul _)
  rw [eL', eR', haddL, haddR, hkin]

end

end CFT.WDWComplex
