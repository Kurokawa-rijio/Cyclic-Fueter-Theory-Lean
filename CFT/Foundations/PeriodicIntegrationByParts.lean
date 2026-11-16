import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 3-3（境界項なしの部分積分）の機構部：
  周期境界では ∫ f' g = −∫ f g'、ディリクレ境界では −d²/dx² が対称になる
  （∫ f'' g = ∫ f g''）。同じ機構が 5-1（WDW 作用素の対称性）の1次元モデルでもある。
  本体は Mathlib の `intervalIntegral.integral_deriv_mul_eq_sub`（積の微分の FTC）。
-/

namespace CFT.PeriodicIBP

open MeasureTheory intervalIntegral

/-- 周期境界での部分積分：境界項 f(T)g(T) = f(0)g(0) が相殺すれば ∫ f' g = −∫ f g'。 -/
theorem integral_deriv_mul_periodic {f g f' g' : ℝ → ℝ} {T : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hf' : IntervalIntegrable f' volume 0 T) (hg' : IntervalIntegrable g' volume 0 T)
    (hfg : IntervalIntegrable (fun x => f' x * g x) volume 0 T)
    (hgf : IntervalIntegrable (fun x => f x * g' x) volume 0 T)
    (hper : f T * g T = f 0 * g 0) :
    ∫ x in (0:ℝ)..T, f' x * g x = -∫ x in (0:ℝ)..T, f x * g' x := by
  have h := integral_deriv_mul_eq_sub (u := f) (v := g) (u' := f') (v' := g')
    (fun x _ => hf x) (fun x _ => hg x) hf' hg'
  rw [integral_add hfg hgf, hper] at h
  simp only [sub_self] at h
  linarith

/-- ディリクレ境界での −d²/dx² の対称性：両端で消える f, g に対し ∫ f'' g = ∫ f g''。 -/
theorem integral_secondDeriv_symm_dirichlet {f g f₁ f₂ g₁ g₂ : ℝ → ℝ} {T : ℝ}
    (hf₁ : ∀ x, HasDerivAt f (f₁ x) x) (hf₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hg₁ : ∀ x, HasDerivAt g (g₁ x) x) (hg₂ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hf₁' : IntervalIntegrable f₁ volume 0 T) (hf₂' : IntervalIntegrable f₂ volume 0 T)
    (hg₁' : IntervalIntegrable g₁ volume 0 T) (hg₂' : IntervalIntegrable g₂ volume 0 T)
    (hfg : IntervalIntegrable (fun x => f₂ x * g x) volume 0 T)
    (hf₁g₁ : IntervalIntegrable (fun x => f₁ x * g₁ x) volume 0 T)
    (hg₂f : IntervalIntegrable (fun x => g₂ x * f x) volume 0 T)
    (hg₁f₁ : IntervalIntegrable (fun x => g₁ x * f₁ x) volume 0 T)
    (hf0 : f 0 = 0) (hfT : f T = 0) (hg0 : g 0 = 0) (hgT : g T = 0) :
    ∫ x in (0:ℝ)..T, f₂ x * g x = ∫ x in (0:ℝ)..T, f x * g₂ x := by
  have hA := integral_deriv_mul_eq_sub (u := f₁) (v := g) (u' := f₂) (v' := g₁)
    (fun x _ => hf₂ x) (fun x _ => hg₁ x) hf₂' hg₁'
  rw [integral_add hfg hf₁g₁] at hA
  simp only [hgT, hg0, mul_zero, sub_zero] at hA
  have hB := integral_deriv_mul_eq_sub (u := g₁) (v := f) (u' := g₂) (v' := f₁)
    (fun x _ => hg₂ x) (fun x _ => hf₁ x) hg₂' hf₁'
  rw [integral_add hg₂f hg₁f₁] at hB
  simp only [hfT, hf0, mul_zero, sub_zero] at hB
  have e1 : (fun x => g₂ x * f x) = (fun x => f x * g₂ x) :=
    funext fun x => mul_comm _ _
  have e2 : (fun x => g₁ x * f₁ x) = (fun x => f₁ x * g₁ x) :=
    funext fun x => mul_comm _ _
  rw [e1, e2] at hB
  linarith

end CFT.PeriodicIBP
