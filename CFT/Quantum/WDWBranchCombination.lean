/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件（特異境界での振る舞い））の残り
  「枝結合の閉形式（sin/cos 表示）の全 a での同定」（`GAP_5-8_prep.md` の
  OPEN-軽、(C4) の全 a 版）。

  厳密解の両枝 Ψ₊(a,b) = e^{iaσ κ}/σ、Ψ₋(a,b) = e^{−iaσ κ}/(−σ)
  （σ = √Q、κ = 1/ħ）について、指数関数のオイラー表示から

  * Ψ₊ + Ψ₋ = 2i·sin(aσ κ)/σ、Ψ₊ − Ψ₋ = 2·cos(aσ κ)/σ

  を全ての a について証明する。したがって DeWitt 型結合
  (Ψ₊ + Ψ₋)/(2i) = sin(aσ κ)/σ は a = 0 で 0 になり、
  Hartle–Hawking 型結合 (Ψ₊ − Ψ₋)/2 = cos(aσ κ)/σ は
  a = 0 で 1/σ ≠ 0 になることが、全 a での閉形式として確定する
  （a = 0 での値だけなら `WDWBoundaryConditions.lean` の
  `psiDW_zero`・`psiHH_zero` で既に証明済み）。

  証明は Q > 0 を仮定しない：σ = 0 の点でも両辺は 0 になる
  （Lean の 1/0 = 0、(−0)⁻¹ = 0 による）。
-/
import CFT.Quantum.WDWBoundaryConditions

namespace CFT.WDWBranchCombo

open Complex CFT.WKB CFT.WDWBoundary

noncomputable section

variable (c l κ : ℝ)

/-- 正の枝の明示形：Ψ₊ = (1/σ)·(cos(aσ κ) + i·sin(aσ κ)) -/
theorem psiPlus_exp (C a b : ℝ) :
    PsiPlus c l κ C a b = ((1 / Real.sqrt (Q c l C b) : ℝ) : ℂ) *
      (↑(Real.cos (a * Real.sqrt (Q c l C b) * κ))
        + I * ↑(Real.sin (a * Real.sqrt (Q c l C b) * κ))) := by
  have hexp : I * (a : ℂ) * ((Real.sqrt (Q c l C b) : ℝ) : ℂ) * (κ : ℂ)
      = ((a * Real.sqrt (Q c l C b) * κ : ℝ) : ℂ) * I := by
    push_cast
    ring
  simp only [PsiPlus, Psi]
  rw [hexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- 負の枝の明示形：Ψ₋ = −(1/σ)·(cos(aσ κ) − i·sin(aσ κ)) -/
theorem psiMinus_exp (C a b : ℝ) :
    PsiMinus c l κ C a b = (-((1 / Real.sqrt (Q c l C b) : ℝ) : ℂ)) *
      (↑(Real.cos (a * Real.sqrt (Q c l C b) * κ))
        - I * ↑(Real.sin (a * Real.sqrt (Q c l C b) * κ))) := by
  have hexp : I * (a : ℂ) * (((-Real.sqrt (Q c l C b)) : ℝ) : ℂ) * (κ : ℂ)
      = ((- (a * Real.sqrt (Q c l C b) * κ) : ℝ) : ℂ) * I := by
    push_cast
    ring
  simp only [PsiMinus, Psi]
  rw [hexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- 枝結合の閉形式（sin）：Ψ₊ + Ψ₋ = 2i·sin(aσ κ)/σ（全 a で成立） -/
theorem psiPlus_add_psiMinus (C a b : ℝ) :
    PsiPlus c l κ C a b + PsiMinus c l κ C a b
      = 2 * I * ((Real.sin (a * Real.sqrt (Q c l C b) * κ)
          / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  rw [psiPlus_exp, psiMinus_exp]
  push_cast
  ring

/-- 枝結合の閉形式（cos）：Ψ₊ − Ψ₋ = 2·cos(aσ κ)/σ（全 a で成立） -/
theorem psiPlus_sub_psiMinus (C a b : ℝ) :
    PsiPlus c l κ C a b - PsiMinus c l κ C a b
      = 2 * ((Real.cos (a * Real.sqrt (Q c l C b) * κ)
          / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  rw [psiPlus_exp, psiMinus_exp]
  push_cast
  ring

/-- DeWitt 型結合は sin 型：(Ψ₊ + Ψ₋)/(2i) = sin(aσ κ)/σ -/
theorem psiDW_eq_sin (C a b : ℝ) :
    PsiDW c l κ C a b
      = ((Real.sin (a * Real.sqrt (Q c l C b) * κ)
          / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  rw [PsiDW, psiPlus_add_psiMinus]
  have hI : (2 * I : ℂ) ≠ 0 := by simp
  exact mul_div_cancel_left₀ _ hI

/-- Hartle–Hawking 型結合は cos 型：(Ψ₊ − Ψ₋)/2 = cos(aσ κ)/σ -/
theorem psiHH_eq_cos (C a b : ℝ) :
    PsiHH c l κ C a b
      = ((Real.cos (a * Real.sqrt (Q c l C b) * κ)
          / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  rw [PsiHH, psiPlus_sub_psiMinus]
  exact mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)

end

end CFT.WDWBranchCombo
