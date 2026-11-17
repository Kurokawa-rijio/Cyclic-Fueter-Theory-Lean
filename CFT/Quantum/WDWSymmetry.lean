import Mathlib
import CFT.Foundations.PeriodicIntegrationByParts
import CFT.Quantum.WDWExactWKB

/-!
  命題集 `LEAN_GAP_TREES.md` 5-1（作用素の対称性）の本体への適用（a-部分）。

  ウィーラー–ドウィット作用素は `CFT.WKB.wdwOp`（`WDWExactWKB.lean`）で
    Ĥ Ψ = (1/4c)(−ħ² a Ψ_aa + 2ħ² b Ψ_ab) − c a (b² − ℓ²) Ψ
  と定義されている。b を固定した a-部分
    Ĥ_a Ψ = (1/4c)(−ħ² a ∂_a²Ψ) − c a (b² − ℓ²) Ψ
  は、重み 1/a の内積 ⟨f, g⟩ = ∫_A^B f g (dx/x)（0 < A）に関して対称である
  （`wdw_a_symm`）。運動項の係数 −a が重み 1/a と相殺して −∂_a² に帰着し、
  3-3 のディリクレ境界での対称性（`integral_secondDeriv_symm_dirichlet`）が
  そのまま使える。ポテンシャル項は掛け算作用素なので自明に対称。
  これは実関数版の機構である。残り：混合項 2ħ²b ∂_a∂_b（b 方向の部分積分と
  フビニが要る）、複素版（共役つき）、a 変数からアフィン変数 k = K − K₀
  （`AffineQuantizationInnerProduct.lean` の ⟨f, g⟩ = ∫₀^∞ f̄ g dk）への
  変数変換。`wdwAPart_eq_wdwOp` で a-部分が実際の `wdwOp` の Ψ_ab = 0 の
  場合であることを確認してある。
-/

namespace CFT.WDWSymm

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- WDW 作用素の a-部分（b を固定）：`CFT.WKB.wdwOp` の Ψ_ab 項を除いた実係数形。 -/
def wdwAPart (c l hb b a : ℝ) (Ψ Ψaa : ℝ) : ℝ :=
  (1 / (4 * c)) * (-hb ^ 2 * a * Ψaa) - c * a * (b ^ 2 - l ^ 2) * Ψ

/-- `wdwAPart` は `wdwOp` の Ψ_ab = 0 の場合（複素版との対応）。 -/
theorem wdwAPart_eq_wdwOp (c l hb b a : ℝ) (Ψ Ψaa : ℝ) :
    (wdwAPart c l hb b a Ψ Ψaa : ℂ) = CFT.WKB.wdwOp c l hb a b (Ψ : ℂ) (Ψaa : ℂ) 0 := by
  simp only [wdwAPart, CFT.WKB.wdwOp]
  push_cast
  ring

/-- ディリクレ境界での −d²/dx² の対称性（区間 [A, B] 版。3-3 の (0, T) 版の一般化）。 -/
theorem integral_secondDeriv_symm_dirichlet_AB {f g f₁ f₂ g₁ g₂ : ℝ → ℝ} {A B : ℝ}
    (hf₁ : ∀ x, HasDerivAt f (f₁ x) x) (hf₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hg₁ : ∀ x, HasDerivAt g (g₁ x) x) (hg₂ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hf₁' : IntervalIntegrable f₁ volume A B) (hf₂' : IntervalIntegrable f₂ volume A B)
    (hg₁' : IntervalIntegrable g₁ volume A B) (hg₂' : IntervalIntegrable g₂ volume A B)
    (hfg : IntervalIntegrable (fun x => f₂ x * g x) volume A B)
    (hf₁g₁ : IntervalIntegrable (fun x => f₁ x * g₁ x) volume A B)
    (hg₂f : IntervalIntegrable (fun x => g₂ x * f x) volume A B)
    (hg₁f₁ : IntervalIntegrable (fun x => g₁ x * f₁ x) volume A B)
    (hfA : f A = 0) (hfB : f B = 0) (hgA : g A = 0) (hgB : g B = 0) :
    ∫ x in A..B, f₂ x * g x = ∫ x in A..B, f x * g₂ x := by
  have hA := integral_deriv_mul_eq_sub (u := f₁) (v := g) (u' := f₂) (v' := g₁)
    (fun x _ => hf₂ x) (fun x _ => hg₁ x) hf₂' hg₁'
  rw [integral_add hfg hf₁g₁] at hA
  simp only [hgB, hgA, mul_zero, sub_zero] at hA
  have hB := integral_deriv_mul_eq_sub (u := g₁) (v := f) (u' := g₂) (v' := f₁)
    (fun x _ => hg₂ x) (fun x _ => hf₁ x) hg₂' hf₁'
  rw [integral_add hg₂f hg₁f₁] at hB
  simp only [hfB, hfA, mul_zero, sub_zero] at hB
  have e1 : (fun x => g₂ x * f x) = (fun x => f x * g₂ x) :=
    funext fun x => mul_comm _ _
  have e2 : (fun x => g₁ x * f₁ x) = (fun x => f₁ x * g₁ x) :=
    funext fun x => mul_comm _ _
  rw [e1, e2] at hB
  linarith

/-- 【5-1】WDW 作用素の a-部分は、重み 1/a の内積に関して対称
  （b を固定、ディリクレ境界、区間 [A, B] ⊂ (0, ∞)）。 -/
theorem wdw_a_symm {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (c l hb b : ℝ)
    {f g f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (hf₁ : ∀ x, HasDerivAt f (f₁ x) x) (hf₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hg₁ : ∀ x, HasDerivAt g (g₁ x) x) (hg₂ : ∀ x, HasDerivAt g₁ (g₂ x) x)
    (hf₁' : IntervalIntegrable f₁ volume A B) (hf₂' : IntervalIntegrable f₂ volume A B)
    (hg₁' : IntervalIntegrable g₁ volume A B) (hg₂' : IntervalIntegrable g₂ volume A B)
    (hfg₂ : IntervalIntegrable (fun x => f x * g₂ x) volume A B)
    (hf₂g : IntervalIntegrable (fun x => f₂ x * g x) volume A B)
    (hfg : IntervalIntegrable (fun x => f x * g x) volume A B)
    (hf₁g₁ : IntervalIntegrable (fun x => f₁ x * g₁ x) volume A B)
    (hg₂f : IntervalIntegrable (fun x => g₂ x * f x) volume A B)
    (hg₁f₁ : IntervalIntegrable (fun x => g₁ x * f₁ x) volume A B)
    (hfA : f A = 0) (hfB : f B = 0) (hgA : g A = 0) (hgB : g B = 0) :
    ∫ x in A..B, f x * wdwAPart c l hb b x (g x) (g₂ x) * (1 / x)
      = ∫ x in A..B, wdwAPart c l hb b x (f x) (f₂ x) * (1 / x) * g x := by
  have hmem : ∀ x ∈ [[A, B]], (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact lt_of_lt_of_le hA hx.1
  have eL : Set.EqOn (fun x => f x * wdwAPart c l hb b x (g x) (g₂ x) * (1 / x))
      (fun x => (1 / (4 * c)) * (-hb ^ 2) * (f x * g₂ x)
        + (-c * (b ^ 2 - l ^ 2)) * (f x * g x)) [[A, B]] := by
    intro x hx
    have hx0 : x ≠ 0 := (hmem x hx).ne'
    have key : x * (1 / x) = 1 := mul_one_div_cancel hx0
    calc f x * wdwAPart c l hb b x (g x) (g₂ x) * (1 / x)
        = ((1 / (4 * c)) * (-hb ^ 2) * (f x * g₂ x)
            + (-c * (b ^ 2 - l ^ 2)) * (f x * g x)) * (x * (1 / x)) := by
          simp only [wdwAPart]; ring
      _ = _ := by rw [key, mul_one]
  have eR : Set.EqOn (fun x => wdwAPart c l hb b x (f x) (f₂ x) * (1 / x) * g x)
      (fun x => (1 / (4 * c)) * (-hb ^ 2) * (f₂ x * g x)
        + (-c * (b ^ 2 - l ^ 2)) * (f x * g x)) [[A, B]] := by
    intro x hx
    have hx0 : x ≠ 0 := (hmem x hx).ne'
    have key : x * (1 / x) = 1 := mul_one_div_cancel hx0
    calc wdwAPart c l hb b x (f x) (f₂ x) * (1 / x) * g x
        = ((1 / (4 * c)) * (-hb ^ 2) * (f₂ x * g x)
            + (-c * (b ^ 2 - l ^ 2)) * (f x * g x)) * (x * (1 / x)) := by
          simp only [wdwAPart]; ring
      _ = _ := by rw [key, mul_one]
  have hsym := integral_secondDeriv_symm_dirichlet_AB hf₁ hf₂ hg₁ hg₂ hf₁' hf₂' hg₁' hg₂'
    hf₂g hf₁g₁ hg₂f hg₁f₁ hfA hfB hgA hgB
  have hkin : ∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f x * g₂ x)
      = ∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f₂ x * g x) := by
    rw [integral_const_mul, integral_const_mul, hsym]
  have eL' : ∫ x in A..B, f x * wdwAPart c l hb b x (g x) (g₂ x) * (1 / x)
      = ∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f x * g₂ x)
          + (-c * (b ^ 2 - l ^ 2)) * (f x * g x) :=
    integral_congr eL
  have eR' : ∫ x in A..B, wdwAPart c l hb b x (f x) (f₂ x) * (1 / x) * g x
      = ∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f₂ x * g x)
          + (-c * (b ^ 2 - l ^ 2)) * (f x * g x) :=
    integral_congr eR
  have haddL : ∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f x * g₂ x)
        + (-c * (b ^ 2 - l ^ 2)) * (f x * g x)
      = (∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f x * g₂ x))
        + ∫ x in A..B, (-c * (b ^ 2 - l ^ 2)) * (f x * g x) :=
    integral_add (hfg₂.const_mul _) (hfg.const_mul _)
  have haddR : ∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f₂ x * g x)
        + (-c * (b ^ 2 - l ^ 2)) * (f x * g x)
      = (∫ x in A..B, (1 / (4 * c)) * (-hb ^ 2) * (f₂ x * g x))
        + ∫ x in A..B, (-c * (b ^ 2 - l ^ 2)) * (f x * g x) :=
    integral_add (hf₂g.const_mul _) (hfg.const_mul _)
  rw [eL', eR', haddL, haddR, hkin]

end

end CFT.WDWSymm
