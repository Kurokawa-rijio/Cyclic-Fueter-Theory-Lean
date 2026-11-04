/-
  α-IX.26 KMS 条件、α-IX.30 揺動散逸の関係(有限系)、α-IX.28 Planck の積分

  * IX.26 KMS(有限次元、エネルギー固有基底):G_AB(t) = Tr(e^{−βH} A(t) B)、
      A(t)_{mk} = e^{i(E_m − E_k)t}A_{mk}。H_BA(s) = Tr(e^{−βH} B A(s)) とすると
      G_AB(t) = H_BA(t + iβ)(`kms`):虚時間の方向の周期 β。
  * IX.30 揺動散逸の関係(有限系、ħ = 1。命題をこの範囲に絞る):周波数 ω = E_m − E_k の成分で、
      揺らぎ(対称化した相関)の重みは (p_k + p_m)|A_{km}|²、応答(交換子)の重みは (p_k − p_m)|A_{km}|²
      (p = e^{−βE})。(p_k + p_m) sinh(βω/2) = (p_k − p_m) cosh(βω/2)(`fdt`)、
      つまり S(ω) = coth(βω/2) χ″(ω)。詳細つり合い p_k = e^{βω} p_m(`detailed_balance`)。
      粘性・熱伝導を含む流体力学を Schwinger–Keldysh の作用から導くことは扱わない。
  * IX.28 Planck:∫₀^∞ t³/(eᵗ − 1) dt = π⁴/15(`bose_integral`)。Σ_{n≥1} e^{−nt} = 1/(eᵗ − 1)、
      Mellin 変換と Dirichlet 級数(Mathlib `hasSum_mellin`)、Γ(4) = 6、ζ(4) = π⁴/90(`hasSum_zeta_four`)。
      Stefan–Boltzmann:u = (π²/15)T⁴(`stefan_boltzmann`、ħ = c = k = 1、2 偏光)。
      帽子の輻射(IX.17)は放射の状態方程式 p = ρ/3 をもつ。
-/
import CFT.Basic
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace CFT.Stat

open Real Set MeasureTheory

/-! ### IX.26 KMS -/

section KMS

variable {n : ℕ} (E : Fin n → ℝ) (β : ℝ) (A B : Fin n → Fin n → ℂ)

/-- G_AB(t) = Σ_{m,k} e^{−βE_m} e^{i(E_m − E_k)t} A_{mk} B_{km} -/
noncomputable def Gc (t : ℂ) : ℂ :=
  ∑ m, ∑ k, Complex.exp (-(β : ℂ) * E m) * Complex.exp (Complex.I * ((E m : ℂ) - E k) * t) * A m k * B k m

/-- H_BA(s) = Σ_{k,m} e^{−βE_k} B_{km} e^{iE_m s} A_{mk} e^{−iE_k s} -/
noncomputable def Hc (s : ℂ) : ℂ :=
  ∑ k, ∑ m, Complex.exp (-(β : ℂ) * E k) * B k m * Complex.exp (Complex.I * E m * s) * A m k
    * Complex.exp (-(Complex.I * E k * s))

/-- 【α-IX.26】KMS 条件 G_AB(t) = H_BA(t + iβ) -/
theorem kms (t : ℂ) : Gc E β A B t = Hc E β A B (t + Complex.I * β) := by
  unfold Gc Hc
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have key : Complex.exp (-(β : ℂ) * E k) * Complex.exp (Complex.I * E m * (t + Complex.I * β))
      * Complex.exp (-(Complex.I * E k * (t + Complex.I * β)))
      = Complex.exp (-(β : ℂ) * E m) * Complex.exp (Complex.I * ((E m : ℂ) - E k) * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination ((β : ℂ) * ((E m : ℂ) - E k)) * hI
  linear_combination (-(A m k * B k m)) * key

end KMS

/-! ### IX.30 揺動散逸の関係 -/

/-- 【α-IX.30】(p_k + p_m) sinh(βω/2) = (p_k − p_m) cosh(βω/2)、ω = E_m − E_k、p = e^{−βE} -/
theorem fdt (β Em Ek : ℝ) :
    (exp (-β * Ek) + exp (-β * Em)) * sinh (β * (Em - Ek) / 2)
      = (exp (-β * Ek) - exp (-β * Em)) * cosh (β * (Em - Ek) / 2) := by
  have e1 : exp (-β * Em) = exp (-β * Ek) * exp (-(β * (Em - Ek) / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have huv : exp (β * (Em - Ek) / 2) * exp (-(β * (Em - Ek) / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.sinh_eq, Real.cosh_eq, e1]
  linear_combination (exp (-β * Ek) * exp (-(β * (Em - Ek) / 2))) * huv

/-- 詳細つり合い:p_k = e^{βω} p_m -/
theorem detailed_balance (β Em Ek : ℝ) : exp (-β * Ek) = exp (β * (Em - Ek)) * exp (-β * Em) := by
  rw [← Real.exp_add]; congr 1; ring

/-! ### IX.28 Planck の積分 -/

/-- Σ_{n≥1} e^{−nt} = 1/(eᵗ − 1)(t > 0) -/
theorem bose_series (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => (if n = 0 then (0 : ℂ) else 1) * ((rexp (-(n : ℝ) * t) : ℝ) : ℂ))
      ((1 / (rexp t - 1) : ℝ) : ℂ) := by
  have hr0 : 0 ≤ rexp (-t) := (exp_pos _).le
  have hr1 : rexp (-t) < 1 := by
    have := Real.exp_lt_exp.mpr (show -t < 0 by linarith); rwa [Real.exp_zero] at this
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).sub (hasSum_ite_eq 0 (1 : ℝ))
  have hfun : (fun n : ℕ => rexp (-t) ^ n - (if n = 0 then (1 : ℝ) else 0))
      = fun n : ℕ => (if n = 0 then (0 : ℝ) else 1) * rexp (-(n : ℝ) * t) := by
    funext n
    by_cases h : n = 0
    · subst h; simp
    · simp only [h, if_false, sub_zero, one_mul]
      rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hfun] at hg
  have hval : (1 - rexp (-t))⁻¹ - 1 = 1 / (rexp t - 1) := by
    have h1 : 1 < rexp t := by
      have := Real.exp_lt_exp.mpr ht; rwa [Real.exp_zero] at this
    have h2 : rexp t - 1 ≠ 0 := by linarith
    have h4 : 1 - rexp (-t) ≠ 0 := by linarith
    have hprod : rexp t * rexp (-t) = 1 := by rw [← Real.exp_add]; simp
    field_simp
    linarith [hprod]
  rw [hval] at hg
  have := (Complex.hasSum_ofReal).mpr hg
  convert this using 1
  funext n
  by_cases h : n = 0 <;> simp [h]

/-- 【α-IX.28】∫₀^∞ t³/(eᵗ − 1) dt = π⁴/15 -/
theorem bose_integral : ∫ t in Ioi (0 : ℝ), t ^ 3 / (rexp t - 1) = π ^ 4 / 15 := by
  -- Mellin 変換 = Dirichlet 級数
  have hp : ∀ i : ℕ, (if i = 0 then (0 : ℂ) else 1) = 0 ∨ 0 < (i : ℝ) := by
    intro i; by_cases h : i = 0
    · left; simp [h]
    · right; exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
  have hs : 0 < (4 : ℂ).re := by norm_num
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i : ℕ => (if i = 0 then (0 : ℂ) else 1) * rexp (-(i : ℝ) * t))
      ((1 / (rexp t - 1) : ℝ) : ℂ) := fun t ht => bose_series t ht
  have hsum : Summable fun i : ℕ => ‖(if i = 0 then (0 : ℂ) else 1)‖ / (i : ℝ) ^ (4 : ℂ).re := by
    have h4 : (4 : ℂ).re = 4 := by norm_num
    rw [h4]
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 4))
    by_cases h : i = 0 <;> simp [h]
  have hM := hasSum_mellin hp hs hF hsum
  -- 各項は Γ(4)/n⁴ = 6/n⁴
  have hΓ : Complex.Gamma 4 = 6 := by
    have : (4 : ℂ) = (3 : ℕ) + 1 := by norm_num
    rw [this, Complex.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
  have hterm : (fun i : ℕ => Complex.Gamma 4 * (if i = 0 then (0 : ℂ) else 1) / ((i : ℝ) : ℂ) ^ (4 : ℂ))
      = fun i : ℕ => (((6 : ℝ) * (1 / (i : ℝ) ^ 4) : ℝ) : ℂ) := by
    funext i
    rw [hΓ]
    by_cases h : i = 0
    · simp [h]
    · have : ((i : ℝ) : ℂ) ^ (4 : ℂ) = ((i : ℝ) : ℂ) ^ (4 : ℕ) := by
        rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      simp only [h, if_false, mul_one, this]
      push_cast; ring
  have hM2 : HasSum (fun i : ℕ => (((6 : ℝ) * (1 / (i : ℝ) ^ 4) : ℝ) : ℂ))
      (mellin (fun t : ℝ => ((1 / (rexp t - 1) : ℝ) : ℂ)) 4) := by
    rw [← hterm]; exact hM
  have hZ := (Complex.hasSum_ofReal).mpr (hasSum_zeta_four.mul_left 6)
  have hval := hM2.unique hZ
  -- mellin を実の積分に直す
  have hmel : mellin (fun t : ℝ => ((1 / (rexp t - 1) : ℝ) : ℂ)) 4
      = ((∫ t in Ioi (0 : ℝ), t ^ 3 / (rexp t - 1) : ℝ) : ℂ) := by
    rw [mellin]
    refine (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_).trans integral_ofReal
    simp only [smul_eq_mul]
    rw [show (4 : ℂ) - 1 = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast
    ring_nf
    first
    | rfl
    | (rw [← Complex.ofReal_exp]; rfl)
    | (simp only [← Complex.ofReal_exp]; rfl)
    | norm_cast
  rw [hmel] at hval
  have := Complex.ofReal_injective hval
  rw [this]; ring

/-- Stefan–Boltzmann:u = (2/(2π²))·T⁴·(π⁴/15) = (π²/15)T⁴ -/
theorem stefan_boltzmann (T : ℝ) : 2 / (2 * π ^ 2) * T ^ 4 * (π ^ 4 / 15) = π ^ 2 / 15 * T ^ 4 := by
  have := pi_ne_zero
  field_simp; ring

end CFT.Stat
