/-
  α-IV.12 (Z13) / α-VI.4 (Z33):首の Wheeler–DeWitt 方程式と WKB の厳密性(実際の関数で)

  作用素の順序:拘束 b²·Hfun を作り、運動量 p → −iħ∂ を座標の右に置く。
    Ĥ Ψ = (1/4c)(−ħ² a ∂_a²Ψ + 2ħ² b ∂_a∂_bΨ) − c a (b² − ℓ²) Ψ
  (古典の b²·Hfun = (1/4c)(a p_a² − 2b p_a p_b) − c a (b² − ℓ²) に対応)。

  Ψ(a, b) = A(b) e^{i a σ(b)/ħ}(S = aσ は Hamilton–Jacobi の解の形)について、
  実際の偏微分(HasDerivAt)を使って
    Ĥ Ψ = e^{iaσ/ħ} · ( A · HJ(a, b) + (iħ b/2c)(σ A′ + σ′ A) )        (`wkb_identity`)
  HJ(a, b) = (aσ² − 2abσσ′)/(4c) − c a (b² − ℓ²) = b² Hfun(a, b, σ, aσ′)。
  * ħ⁰:Hamilton–Jacobi 方程式、ħ¹:輸送方程式 σA′ + σ′A = 0(A = 1/σ)。ħ² 以上の項はない。
    したがって WKB の級数は 1 次で終わり、Ψ = e^{iaσ/ħ}/σ は誤差のない厳密解(`wdw_exact_sqrt`)。
  * 定義域:Q(b) = Cb − 4c²(b² + ℓ²) > 0、σ = √Q。Q = 0 は古典の転回点(焦線)で、|Ψ| = 1/√Q が発散する。
-/
import Mathlib

namespace CFT.WKB

open Complex

noncomputable section

variable (c l κ : ℝ) (A σ : ℝ → ℝ)

/-- Ψ(a, b) = A(b) e^{i a σ(b) κ}(κ = 1/ħ) -/
def Psi (a b : ℝ) : ℂ := (A b : ℂ) * exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ))

/-- ∂_aΨ = iσκ Ψ(関数として) -/
def Psia (a b : ℝ) : ℂ := I * (σ b : ℂ) * (κ : ℂ) * Psi κ A σ a b

/-- a についての微分 -/
theorem hasDerivAt_Psi_a (a b : ℝ) :
    HasDerivAt (fun x => Psi κ A σ x b) (Psia κ A σ a b) a := by
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 a := by
    simpa using (hasDerivAt_id a).ofReal_comp
  have hg := ((hx.const_mul I).mul_const (σ b : ℂ)).mul_const (κ : ℂ)
  have h := (hg.cexp).const_mul (A b : ℂ)
  convert h using 1
  simp only [Psia, Psi]
  ring

/-- ∂_a²Ψ = (iσκ)² Ψ -/
theorem hasDerivAt_Psia_a (a b : ℝ) :
    HasDerivAt (fun x => Psia κ A σ x b)
      (I * (σ b : ℂ) * (κ : ℂ) * (I * (σ b : ℂ) * (κ : ℂ) * Psi κ A σ a b)) a := by
  have h := (hasDerivAt_Psi_a κ A σ a b).const_mul (I * (σ b : ℂ) * (κ : ℂ))
  simpa [Psia] using h

/-- b についての微分:∂_bΨ = A′ E + A E (i a σ′ κ) -/
theorem hasDerivAt_Psi_b (a b A' σ' : ℝ) (hA : HasDerivAt A A' b) (hσ : HasDerivAt σ σ' b) :
    HasDerivAt (fun y => Psi κ A σ a y)
      ((A' : ℂ) * exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ))
        + (A b : ℂ) * (exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ)) * (I * (a : ℂ) * (σ' : ℂ) * (κ : ℂ)))) b := by
  have hAc : HasDerivAt (fun y => (A y : ℂ)) (A' : ℂ) b := hA.ofReal_comp
  have hσc : HasDerivAt (fun y => (σ y : ℂ)) (σ' : ℂ) b := hσ.ofReal_comp
  have hg := (hσc.const_mul (I * (a : ℂ))).mul_const (κ : ℂ)
  have h := hAc.mul hg.cexp
  convert h using 1
  · funext y; simp only [Psi]; ring_nf
  · ring

/-- 混合微分:∂_b(∂_aΨ) = iσ′κ Ψ + iσκ ∂_bΨ -/
theorem hasDerivAt_Psia_b (a b A' σ' : ℝ) (hA : HasDerivAt A A' b) (hσ : HasDerivAt σ σ' b) :
    HasDerivAt (fun y => Psia κ A σ a y)
      (I * (σ' : ℂ) * (κ : ℂ) * Psi κ A σ a b + I * (σ b : ℂ) * (κ : ℂ) *
        ((A' : ℂ) * exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ))
          + (A b : ℂ) * (exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ)) * (I * (a : ℂ) * (σ' : ℂ) * (κ : ℂ))))) b := by
  have hσc : HasDerivAt (fun y => (σ y : ℂ)) (σ' : ℂ) b := hσ.ofReal_comp
  have h1 := (hσc.const_mul I).mul_const (κ : ℂ)
  have h := h1.mul (hasDerivAt_Psi_b κ A σ a b A' σ' hA hσ)
  convert h using 1
  · funext y; simp only [Psia]
  · ring

/-- WDW 作用素(順序:b²·Hfun、運動量を右に):
(1/4c)(−ħ² a Ψ_aa + 2ħ² b Ψ_ab) − c a (b² − ℓ²) Ψ -/
def wdwOp (hb : ℝ) (a b : ℝ) (Ψ Ψaa Ψab : ℂ) : ℂ :=
  (1 / (4 * (c : ℂ))) * (-(hb : ℂ) ^ 2 * (a : ℂ) * Ψaa + 2 * (hb : ℂ) ^ 2 * (b : ℂ) * Ψab)
    - (c : ℂ) * (a : ℂ) * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2) * Ψ

/-- 【α-IV.12】WKB の展開は 1 次で終わる:Ĥ(A e^{iaσ/ħ}) = e^{iaσ/ħ}(A·HJ + (iħb/2c)(σA′ + σ′A))。
Ψ_aa、Ψ_ab は実際の偏微分(微分は一意なので、どの値をとっても同じ)。 -/
theorem wkb_identity (hb : ℝ) (hhb : hb * κ = 1) (a b A' σ' : ℝ)
    (hA : HasDerivAt A A' b) (hσ : HasDerivAt σ σ' b) (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => Psia κ A σ x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ A σ a y) Dab b) :
    wdwOp c l hb a b (Psi κ A σ a b) Daa Dab
      = exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ)) *
        ((A b : ℂ) * ((1 / (4 * (c : ℂ))) * ((a : ℂ) * (σ b : ℂ) ^ 2
            - 2 * (a : ℂ) * (b : ℂ) * (σ b : ℂ) * (σ' : ℂ))
            - (c : ℂ) * (a : ℂ) * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2))
          + 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ) * ((σ b : ℂ) * (A' : ℂ) + (σ' : ℂ) * (A b : ℂ))) := by
  rw [hDaa.unique (hasDerivAt_Psia_a κ A σ a b), hDab.unique (hasDerivAt_Psia_b κ A σ a b A' σ' hA hσ)]
  have hu : (hb : ℂ) * (κ : ℂ) = 1 := by exact_mod_cast hhb
  have hI : I ^ 2 = -1 := I_sq
  simp only [wdwOp, Psi]
  generalize exp (I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ)) = E
  generalize (1 / (4 * (c : ℂ))) = ic
  linear_combination
    (-(ic * a * (σ b) ^ 2 * (A b) * E) * I ^ 2 * ((hb : ℂ) * κ + 1)
      + 2 * ic * I * b * σ' * (A b) * E * hb + 2 * ic * I * b * (σ b) * A' * E * hb
      + 2 * ic * a * b * (σ b) * σ' * (A b) * E * I ^ 2 * ((hb : ℂ) * κ + 1)) * hu
    + (-(ic * a * (σ b) ^ 2 * (A b) * E) + 2 * ic * a * b * (σ b) * σ' * (A b) * E) * hI

/-- Q(b) = Cb − 4c²(b² + ℓ²) -/
def Q (C : ℝ) (y : ℝ) : ℝ := C * y - 4 * c ^ 2 * (y ^ 2 + l ^ 2)

theorem hasDerivAt_Q (C b : ℝ) : HasDerivAt (Q c l C) (C - 8 * c ^ 2 * b) b := by
  have h := ((hasDerivAt_id b).const_mul C).sub
    ((((hasDerivAt_pow 2 b).add_const (l ^ 2))).const_mul (4 * c ^ 2))
  convert h using 1
  · funext y; simp [Q]
  · simp; ring

/-- 【α-IV.12、α-VI.4】Q(b) > 0 の点で、Ψ = e^{iaσ/ħ}/σ(σ = √Q)は WDW 方程式の厳密解。
作用素・定義域(Q > 0)・偏微分はすべて実際の関数について。 -/
theorem wdw_exact_sqrt (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0) (C a b : ℝ) (hQ : 0 < Q c l C b)
    (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
      (fun y => Real.sqrt (Q c l C y)) x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
      (fun y => Real.sqrt (Q c l C y)) a y) Dab b) :
    wdwOp c l hb a b (Psi κ (fun y => 1 / Real.sqrt (Q c l C y)) (fun y => Real.sqrt (Q c l C y)) a b)
      Daa Dab = 0 := by
  set s := Real.sqrt (Q c l C b) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hQ
  have hsq : s ^ 2 = Q c l C b := Real.sq_sqrt hQ.le
  have hσ : HasDerivAt (fun y => Real.sqrt (Q c l C y)) ((C - 8 * c ^ 2 * b) / (2 * s)) b :=
    (hasDerivAt_Q c l C b).sqrt hQ.ne'
  have hA : HasDerivAt (fun y => 1 / Real.sqrt (Q c l C y))
      (-((C - 8 * c ^ 2 * b) / (2 * s)) / s ^ 2) b := by
    convert hσ.inv hspos.ne' using 1
    funext y; simp [one_div]
  rw [wkb_identity c l κ _ _ hb hhb a b _ _ hA hσ Daa Dab hDaa hDab]
  simp only [← hs]
  push_cast
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hsqC : (s : ℂ) ^ 2 = (C : ℂ) * b - 4 * (c : ℂ) ^ 2 * ((b : ℂ) ^ 2 + (l : ℂ) ^ 2) := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hsq
    simpa [Q] using this
  have hsσ : (s : ℂ) * (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)) = ((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / 2 := by
    field_simp; ring
  have hic : (1 / (4 * (c : ℂ))) * (4 * c) = 1 := by field_simp
  have h1 : (1 / (4 * (c : ℂ))) * ((a : ℂ) * (s : ℂ) ^ 2
      - 2 * (a : ℂ) * (b : ℂ) * (s : ℂ) * (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)))
      - (c : ℂ) * (a : ℂ) * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2) = 0 := by
    linear_combination ((1 / (4 * (c : ℂ))) * a) * hsqC - (2 * (1 / (4 * (c : ℂ))) * a * b) * hsσ
      + ((c : ℂ) * a * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2)) * hic
  have h2 : (s : ℂ) * (-(((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)) / (s : ℂ) ^ 2)
      + (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)) * (1 / (s : ℂ)) = 0 := by
    field_simp; ring
  generalize exp (I * (a : ℂ) * (s : ℂ) * (κ : ℂ)) = E
  linear_combination (E * (1 / (s : ℂ))) * h1
    + (E * 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ)) * h2

/-- |Ψ| = |A|:位相因子の絶対値は 1(焦線 Q → 0 では A = 1/√Q が発散する) -/
theorem norm_Psi (a b : ℝ) : ‖Psi κ A σ a b‖ = |A b| := by
  simp only [Psi, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : I * (a : ℂ) * (σ b : ℂ) * (κ : ℂ) = ((a * σ b * κ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

end

end CFT.WKB
