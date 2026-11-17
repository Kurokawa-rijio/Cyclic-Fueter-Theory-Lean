/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件（特異境界での振る舞い））。

  厳密解 Ψ₊(a,b) = e^{iaσ(b)κ}/σ(b)（κ = 1/ħ、σ = √Q、Q > 0）について、
  特異境界 a → 0 での振る舞いを確定し、標準的境界条件との適合を判定する。

  * Ψ₊ は a には位相としてしか依存せず、Ψ₊(0,b) = 1/σ(b) ≠ 0、
    ‖Ψ₊(a,b)‖ は a に依らない。よって DeWitt 条件 Ψ(0) = 0 は満たさない
    (`psiPlus_zero_ne`)。
  * 枝の結合では、DeWitt 型は (Ψ₊ + Ψ₋)/(2i) = sin(aσ κ)/σ、
    Hartle–Hawking 型は (Ψ₊ − Ψ₋)/2 = cos(aσ κ)/σ であり、
    厳密解そのものは単一枝の進行波（Vilenkin 型の形）。
  * a 方向の電流：conj(Ψ₊)·(∂_aΨ₊) = iκ/σ、虚部 κ/σ は a に依らず一定。
  * LB 順序の解（振幅 √b/σ）でも a = 0 の値は √b/σ ≠ 0 で、判定は同じ。

  判定（準備メモ `GAP_5-8_prep.md`）：DeWitt 不適合、Hartle–Hawking 不適合
  （WKB 領域での状態選択の意味で）、Vilenkin 適合（規約つき：枝と古典的
  「外向き」の対応付けは未了で、5-4 の内部時計の選択と同種の問題として残る）。
-/
import CFT.Quantum.WDWTwoBranches

namespace CFT.WDWBoundary

open Complex Filter Topology CFT.WKB

noncomputable section

variable (c l κ : ℝ)

/-- 正の枝 Ψ₊(a,b) = e^{ia√Q κ}/√Q（`wdw_exact_sqrt` の解） -/
def PsiPlus (C a b : ℝ) : ℂ :=
  Psi κ (fun y => 1 / Real.sqrt (Q c l C y)) (fun y => Real.sqrt (Q c l C y)) a b

/-- 負の枝 Ψ₋(a,b) = e^{−ia√Q κ}/(−√Q)（`wdw_exact_neg` の解） -/
def PsiMinus (C a b : ℝ) : ℂ :=
  Psi κ (fun y => (-Real.sqrt (Q c l C y))⁻¹) (fun y => -Real.sqrt (Q c l C y)) a b

/-- DeWitt 型結合 (Ψ₊ + Ψ₋)/(2i) = sin(a√Q κ)/√Q -/
def PsiDW (C a b : ℝ) : ℂ := (PsiPlus c l κ C a b + PsiMinus c l κ C a b) / (2 * I)

/-- Hartle–Hawking 型結合 (Ψ₊ − Ψ₋)/2 = cos(a√Q κ)/√Q -/
def PsiHH (C a b : ℝ) : ℂ := (PsiPlus c l κ C a b - PsiMinus c l κ C a b) / 2

/-- 境界値：Ψ₊(0,b) = 1/√Q（位相因子が 1 になるだけ） -/
theorem psiPlus_zero (C b : ℝ) :
    PsiPlus c l κ C 0 b = ((1 / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  simp [PsiPlus, Psi]

/-- DeWitt 条件の否定：Q > 0 の点では Ψ₊(0,b) ≠ 0 -/
theorem psiPlus_zero_ne (C b : ℝ) (hQ : 0 < Q c l C b) :
    PsiPlus c l κ C 0 b ≠ 0 := by
  rw [psiPlus_zero]
  have h : (1 : ℝ) / Real.sqrt (Q c l C b) ≠ 0 :=
    one_div_ne_zero (Real.sqrt_pos.mpr hQ).ne'
  exact_mod_cast h

/-- 絶対値は a に依らない：‖Ψ₊(a,b)‖ = 1/√Q -/
theorem psiPlus_norm (C a b : ℝ) (hQ : 0 < Q c l C b) :
    ‖PsiPlus c l κ C a b‖ = 1 / Real.sqrt (Q c l C b) := by
  have h := norm_Psi κ (fun y => 1 / Real.sqrt (Q c l C y))
    (fun y => Real.sqrt (Q c l C y)) a b
  rw [abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hQ))] at h
  exact h

/-- a → 0 での連続性：極限は境界値そのもの（発散も振動の蓄積もない） -/
theorem psiPlus_tendsto_zero (C b : ℝ) :
    Tendsto (fun a => PsiPlus c l κ C a b) (𝓝 0) (𝓝 (PsiPlus c l κ C 0 b)) := by
  have hcont : Continuous fun a : ℝ => PsiPlus c l κ C a b := by
    unfold PsiPlus Psi
    fun_prop
  exact hcont.tendsto 0

/-- 負の枝の境界値：Ψ₋(0,b) = −1/√Q -/
theorem psiMinus_zero (C b : ℝ) :
    PsiMinus c l κ C 0 b = -((1 / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  simp [PsiMinus, Psi, inv_neg, one_div]

/-- DeWitt 型結合は a = 0 で消える（が Ψ₊ そのものではない） -/
theorem psiDW_zero (C b : ℝ) : PsiDW c l κ C 0 b = 0 := by
  simp [PsiDW, psiPlus_zero, psiMinus_zero]

/-- Hartle–Hawking 型結合の境界値：Ψ_HH(0,b) = 1/√Q ≠ 0 -/
theorem psiHH_zero (C b : ℝ) :
    PsiHH c l κ C 0 b = ((1 / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  simp only [PsiHH, psiPlus_zero, psiMinus_zero]
  ring

/-- a 方向の電流：conj(Ψ₊)·(∂_aΨ₊) = i·(κ/√Q)。
Psia = i σ κ Ψ（`hasDerivAt_Psi_a` の形）と ‖Ψ‖² = 1/Q から。 -/
theorem psiPlus_current (C a b : ℝ) (hQ : 0 < Q c l C b) :
    (starRingEnd ℂ) (PsiPlus c l κ C a b) *
      Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
        (fun y => Real.sqrt (Q c l C y)) a b
      = I * ((κ / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
  have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
  have hcc : (starRingEnd ℂ) (PsiPlus c l κ C a b) * PsiPlus c l κ C a b
      = ((1 / Real.sqrt (Q c l C b) ^ 2 : ℝ) : ℂ) := by
    have e1 := (Complex.normSq_eq_conj_mul_self (z := PsiPlus c l κ C a b)).symm
    have e2 : Complex.normSq (PsiPlus c l κ C a b)
        = 1 / Real.sqrt (Q c l C b) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, psiPlus_norm c l κ C a b hQ, div_pow, one_pow]
    rw [e1, e2]
  have key : (starRingEnd ℂ) (PsiPlus c l κ C a b) *
        Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
          (fun y => Real.sqrt (Q c l C y)) a b
      = (I * (Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ)) *
          ((starRingEnd ℂ) (PsiPlus c l κ C a b) * PsiPlus c l κ C a b) := by
    simp only [Psia, PsiPlus]
    ring
  rw [key, hcc]
  have hs0 : (Real.sqrt (Q c l C b) : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  push_cast
  field_simp
  ring

/-- κ > 0 では電流の虚部は正：Im(conj(Ψ₊)·∂_aΨ₊) = κ/√Q > 0 -/
theorem psiPlus_current_im_pos (C a b : ℝ) (hQ : 0 < Q c l C b) (hκ : 0 < κ) :
    0 < ((starRingEnd ℂ) (PsiPlus c l κ C a b) *
      Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
        (fun y => Real.sqrt (Q c l C y)) a b).im := by
  have him : (I * ((κ / Real.sqrt (Q c l C b) : ℝ) : ℂ)).im
      = κ / Real.sqrt (Q c l C b) := by simp
  rw [psiPlus_current c l κ C a b hQ, him]
  exact div_pos hκ (Real.sqrt_pos.mpr hQ)

/-- LB 順序の解も a = 0 で消えない：Ψ_LB(0,b) = √b/√Q ≠ 0
（b > 0、Q > 0）。判定は順序に依らない。 -/
theorem psiLB_zero_ne (C b : ℝ) (hb : 0 < b) (hQ : 0 < Q c l C b) :
    Psi κ (fun y => Real.sqrt y / Real.sqrt (Q c l C y))
        (fun y => Real.sqrt (Q c l C y)) 0 b ≠ 0 := by
  have h : Real.sqrt b / Real.sqrt (Q c l C b) ≠ 0 :=
    div_ne_zero (Real.sqrt_pos.mpr hb).ne' (Real.sqrt_pos.mpr hQ).ne'
  have hval : Psi κ (fun y => Real.sqrt y / Real.sqrt (Q c l C y))
        (fun y => Real.sqrt (Q c l C y)) 0 b
      = ((Real.sqrt b / Real.sqrt (Q c l C b) : ℝ) : ℂ) := by
    simp [Psi]
  rw [hval]
  exact_mod_cast h

end

end CFT.WDWBoundary
