/-
  α-I.6 (Y5):Berry 接続と Wigner 接続はゲージ同値でない(Z16 の A_F も含む)

  明示式(A = Σᵢ Aᵢ dpᵢ、E = √(m² + |p|²)。導出は aux/awaf_exact2.py で記号的に検算)
    A_W = −iσ·(p×dp)/(2m(E+m))      (L = ((E+m) + σ·p)/√(2m(E+m)) の回転部分)
    A_B = +iσ·(p×dp)/(2E(E+m)) = −(m/E) A_W   (正エネルギー Dirac スピノルの Berry 接続)
    A_F = [iσ·(p×dp) − m iσ·dp]/(2E²)      (U = (m − iσ·p)/E に対する ½U⁻¹dU)
  注:以前のスクリプト awaf.py に記録された A_W, A_B の閉じた形は、どちらも全体の符号が逆
  (関係 A_B = −(m/E)A_W と曲率の Gram 不変量には影響しない)。

  形式化した内容
  1. 一般形 Aᵢ = a(s) iσ·(p×eᵢ) + b(s) iσᵢ(s = |p|²、∂ⱼa = 2pⱼa′、∂ⱼb = 2pⱼb′)の曲率は
     F*_k = i[α σ_k + β p_k (p·σ) + γ (p×σ)_k]、
     α = 2(a + a′s − b²)、β = −2(a² + a′)、γ = 2(ab + b′)        (curv_formula)
  2. Gram 不変量の和 Σ_k −2 tr(F*_k F*_k) = 4(3α² + 2αβs + β²s² + 2γ²s)   (gram_trace)
  3. この量はゲージ変換 F ↦ gFg⁻¹ で不変                             (gram_gauge)
  4. W:α = −1/(2mE)、β = −1/(2m²E(E+m))、γ = 0 → trG_W = 2/(m²E²) + 1/m⁴
     B:α = m/(2E³)、β = 1/(2E³(E+m))、γ = 0   → trG_B = 2m²/E⁶ + 1/E⁴ = (m/E)⁴ trG_W
     F:α = m²/(2E⁴)、β = 1/(2E⁴)、γ = m/(2E⁴) → trG_F = trG_B
     a, a′ の値は √ の導関数から Lean で計算する                         (*_deriv)
  5. 結論:p ≠ 0(E > m > 0)の点では trG_B < trG_W なので、F_B = gF_Wg⁻¹ となる可逆な g は
     存在しない。つまり A_B と A_W はゲージ同値でない                        (berry_not_gauge_wigner)
  前提として使う標準的事実:ゲージ同値 A′ = gAg⁻¹ + g d g⁻¹ なら F′ = gFg⁻¹(各点で)
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

namespace CFT.AlphaI_AW

open Matrix

noncomputable section

def σ1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![σ1, σ2, σ3]

/-- v·σ -/
def sd (v : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ∑ k, v k • σ k

def crossv (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

def ev (i : Fin 3) : Fin 3 → ℂ := Pi.single i 1

/-- (p×σ)_k -/
def pxs (p : Fin 3 → ℂ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![p 1 • σ3 - p 2 • σ2, p 2 • σ1 - p 0 • σ3, p 0 • σ2 - p 1 • σ1]

/-- 接続 Aᵢ = a iσ·(p×eᵢ) + b iσᵢ -/
def A (p : Fin 3 → ℂ) (a b : ℂ) (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a * Complex.I) • sd (crossv p (ev i)) + (b * Complex.I) • σ i

/-- ∂ⱼAᵢ(連鎖律:∂ⱼa = 2pⱼa′、∂ⱼb = 2pⱼb′) -/
def dA (p : Fin 3 → ℂ) (a ap bp : ℂ) (j i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 * p j * ap * Complex.I) • sd (crossv p (ev i)) + (a * Complex.I) • sd (crossv (ev j) (ev i))
    + (2 * p j * bp * Complex.I) • σ i

/-- 曲率 F_ij = ∂ᵢAⱼ − ∂ⱼAᵢ + [Aᵢ, Aⱼ] -/
def F (p : Fin 3 → ℂ) (a ap b bp : ℂ) (i j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  dA p a ap bp i j - dA p a ap bp j i + A p a b i * A p a b j - A p a b j * A p a b i

set_option maxHeartbeats 0 in
/-- 曲率の一般形(k = 1, 2, 3 の各成分) -/
theorem curv_formula (p : Fin 3 → ℂ) (a ap b bp : ℂ) :
    let s := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2
    let α := 2 * (a + ap * s - b ^ 2)
    let β := -2 * (a ^ 2 + ap)
    let γ := 2 * (a * b + bp)
    F p a ap b bp 1 2 = Complex.I • (α • σ 0 + (β * p 0) • sd p + γ • pxs p 0) ∧
    F p a ap b bp 2 0 = Complex.I • (α • σ 1 + (β * p 1) • sd p + γ • pxs p 1) ∧
    F p a ap b bp 0 1 = Complex.I • (α • σ 2 + (β * p 2) • sd p + γ • pxs p 2) := by
  intro s α β γ
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s, α, β, γ, Fin.sum_univ_three, sd, A, dA, F, pxs, crossv, ev, σ, σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.single_apply] <;>
      all_goals (first | ring1 | (linear_combination (-2*Complex.I*a^2*p 0*p 2 + 2*Complex.I*a*b*p 1) * hI) | (linear_combination (-2*Complex.I*a^2*p 1*p 2 - 2*Complex.I*a*b*p 0) * hI) | (linear_combination (-2*Complex.I*a^2*p 2^2 - 2*Complex.I*b^2) * hI) | (linear_combination (2*Complex.I*a^2*p 0*p 1 - 2*Complex.I*a*b*p 2) * hI) | (linear_combination (2*Complex.I*a^2*p 0*p 2 + 2*Complex.I*a*b*p 1) * hI) | (linear_combination (2*Complex.I*a^2*p 0*p 2 - 2*Complex.I*a*b*p 1) * hI) | (linear_combination (2*Complex.I*a^2*p 0^2 + 2*Complex.I*b^2) * hI) | (linear_combination (2*Complex.I*a^2*p 1*p 2 + 2*Complex.I*a*b*p 0) * hI) | (linear_combination (2*Complex.I*a^2*p 2^2 + 2*Complex.I*b^2) * hI))

set_option maxHeartbeats 0 in
/-- Gram 不変量の和 -/
theorem gram_trace (p : Fin 3 → ℂ) (α β γ : ℂ) :
    let s := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2
    let Fs : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
      fun k => Complex.I • (α • σ k + (β * p k) • sd p + γ • pxs p k)
    ∑ k, -2 * trace (Fs k * Fs k) = 4 * (3 * α ^ 2 + 2 * α * β * s + β ^ 2 * s ^ 2 + 2 * γ ^ 2 * s) := by
  intro s Fs
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [s, Fs, Matrix.trace_fin_two, Fin.sum_univ_three, sd, A, dA, F, pxs, crossv, ev, σ, σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.single_apply]
  linear_combination (4*α^2*Complex.I^2 - 12*α^2 + 8*α*β*Complex.I^2*p 1^2 - 8*α*β*p 0^2 - 8*α*β*p 1^2 - 8*α*β*p 2^2 + 4*β^2*Complex.I^2*p 0^2*p 1^2 + 4*β^2*Complex.I^2*p 1^4 + 4*β^2*Complex.I^2*p 1^2*p 2^2 - 4*β^2*p 0^4 - 8*β^2*p 0^2*p 1^2 - 8*β^2*p 0^2*p 2^2 - 4*β^2*p 1^4 - 8*β^2*p 1^2*p 2^2 - 4*β^2*p 2^4 + 4*γ^2*Complex.I^2*p 0^2 + 4*γ^2*Complex.I^2*p 2^2 - 8*γ^2*p 0^2 - 8*γ^2*p 1^2 - 8*γ^2*p 2^2) * hI

/-- Gram 不変量はゲージ変換 X ↦ gXg⁻¹ で不変 -/
theorem gram_gauge (g X : Matrix (Fin 2) (Fin 2) ℂ) (hg : IsUnit g.det) :
    trace ((g * X * g⁻¹) * (g * X * g⁻¹)) = trace (X * X) := by
  have h1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have h2 : (g * X * g⁻¹) * (g * X * g⁻¹) = g * (X * X) * g⁻¹ := by
    calc (g * X * g⁻¹) * (g * X * g⁻¹) = g * X * (g⁻¹ * g) * X * g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = g * (X * X) * g⁻¹ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-! ### 各接続の係数 -/

section Coeffs

variable (m E : ℝ)

/-- W:a = −1/(2m(E+m))、a′ = 1/(4mE(E+m)²)、s = E² − m² -/
theorem wigner_coeffs (hm : 0 < m) (hE : 0 < E) :
    let a := -1 / (2 * m * (E + m))
    let ap := 1 / (4 * m * E * (E + m) ^ 2)
    let s := E ^ 2 - m ^ 2
    2 * (a + ap * s - 0 ^ 2) = -1 / (2 * m * E) ∧
      -2 * (a ^ 2 + ap) = -1 / (2 * m ^ 2 * E * (E + m)) := by
  intro a ap s
  have h1 : E + m ≠ 0 := by positivity
  constructor <;> (simp only [a, ap, s]; field_simp; ring)

/-- B:a = 1/(2E(E+m))、a′ = −(2E+m)/(4E³(E+m)²) -/
theorem berry_coeffs (hm : 0 < m) (hE : 0 < E) :
    let a := 1 / (2 * E * (E + m))
    let ap := -(2 * E + m) / (4 * E ^ 3 * (E + m) ^ 2)
    let s := E ^ 2 - m ^ 2
    2 * (a + ap * s - 0 ^ 2) = m / (2 * E ^ 3) ∧
      -2 * (a ^ 2 + ap) = 1 / (2 * E ^ 3 * (E + m)) := by
  intro a ap s
  have h1 : E + m ≠ 0 := by positivity
  constructor <;> (simp only [a, ap, s]; field_simp; ring)

/-- F:a = 1/(2E²)、a′ = −1/(2E⁴)、b = −m/(2E²)、b′ = m/(2E⁴) -/
theorem fueter_coeffs (hE : 0 < E) :
    let a := 1 / (2 * E ^ 2)
    let ap := -1 / (2 * E ^ 4)
    let b := -m / (2 * E ^ 2)
    let bp := m / (2 * E ^ 4)
    let s := E ^ 2 - m ^ 2
    2 * (a + ap * s - b ^ 2) = m ^ 2 / (2 * E ^ 4) ∧ -2 * (a ^ 2 + ap) = 1 / (2 * E ^ 4) ∧
      2 * (a * b + bp) = m / (2 * E ^ 4) := by
  intro a ap b bp s
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [a, ap, b, bp, s]; field_simp; ring)

/-- Berry 接続 = −(m/E) × Wigner 接続(係数 a の関係) -/
theorem berry_eq_wigner (hm : 0 < m) (hE : 0 < E) :
    1 / (2 * E * (E + m)) = -(m / E) * (-1 / (2 * m * (E + m))) := by
  have h1 : E + m ≠ 0 := by positivity
  field_simp
  ring

/-- Gram 和:W と B -/
def trG (α β γ s : ℝ) : ℝ := 4 * (3 * α ^ 2 + 2 * α * β * s + β ^ 2 * s ^ 2 + 2 * γ ^ 2 * s)

theorem trG_W (hm : 0 < m) (hE : 0 < E) :
    trG (-1 / (2 * m * E)) (-1 / (2 * m ^ 2 * E * (E + m))) 0 (E ^ 2 - m ^ 2)
      = 2 / (m ^ 2 * E ^ 2) + 1 / m ^ 4 := by
  have h1 : E + m ≠ 0 := by positivity
  simp only [trG]; field_simp; ring

theorem trG_B (hm : 0 < m) (hE : 0 < E) :
    trG (m / (2 * E ^ 3)) (1 / (2 * E ^ 3 * (E + m))) 0 (E ^ 2 - m ^ 2)
      = 2 * m ^ 2 / E ^ 6 + 1 / E ^ 4 := by
  have h1 : E + m ≠ 0 := by positivity
  simp only [trG]; field_simp; ring

theorem trG_F (hE : 0 < E) :
    trG (m ^ 2 / (2 * E ^ 4)) (1 / (2 * E ^ 4)) (m / (2 * E ^ 4)) (E ^ 2 - m ^ 2)
      = 2 * m ^ 2 / E ^ 6 + 1 / E ^ 4 := by
  simp only [trG]; field_simp; ring

/-- trG_B = (m/E)⁴ trG_W -/
theorem ratio (hm : 0 < m) (hE : 0 < E) :
    2 * m ^ 2 / E ^ 6 + 1 / E ^ 4 = (m / E) ^ 4 * (2 / (m ^ 2 * E ^ 2) + 1 / m ^ 4) := by
  field_simp; ring

/-- E > m > 0 なら trG_B < trG_W -/
theorem trG_B_lt (hm : 0 < m) (hEm : m < E) :
    2 * m ^ 2 / E ^ 6 + 1 / E ^ 4 < 2 / (m ^ 2 * E ^ 2) + 1 / m ^ 4 := by
  have hE : 0 < E := lt_trans hm hEm
  rw [ratio m E hm hE]
  have hpos : 0 < 2 / (m ^ 2 * E ^ 2) + 1 / m ^ 4 := by positivity
  have hq : (m / E) ^ 4 < 1 := by
    have h0 : 0 ≤ m / E := by positivity
    have h1 : m / E < 1 := (div_lt_one hE).2 hEm
    calc (m / E) ^ 4 < 1 ^ 4 := by gcongr
      _ = 1 := one_pow 4
  nlinarith

end Coeffs

/-! ### a, a′ の値を √ の導関数から確かめる -/

/-- W:a(s) = −1/(2m(√(m²+s) + m)) の導関数は 1/(4mE(E+m)²)、E = √(m²+s) -/
theorem wigner_deriv (m s : ℝ) (hm : 0 < m) (hs : 0 < m ^ 2 + s) :
    HasDerivAt (fun s => -1 / (2 * m * (Real.sqrt (m ^ 2 + s) + m)))
      (1 / (4 * m * Real.sqrt (m ^ 2 + s) * (Real.sqrt (m ^ 2 + s) + m) ^ 2)) s := by
  have hE : 0 < Real.sqrt (m ^ 2 + s) := Real.sqrt_pos.2 hs
  have hsq := ((Real.hasDerivAt_sqrt hs.ne').comp s ((hasDerivAt_id s).const_add (m ^ 2)))
  have hden := ((hsq.add_const m).const_mul (2 * m))
  have hne : 2 * m * (Real.sqrt (m ^ 2 + s) + m) ≠ 0 := by positivity
  have h := (hasDerivAt_const s (-1 : ℝ)).div hden hne
  convert h using 1
  simp only [Function.comp_def, id]
  field_simp
  ring

/-- B:a(s) = 1/(2E(E+m)) の導関数は −(2E+m)/(4E³(E+m)²) -/
theorem berry_deriv (m s : ℝ) (hm : 0 < m) (hs : 0 < m ^ 2 + s) :
    HasDerivAt (fun s => 1 / (2 * Real.sqrt (m ^ 2 + s) * (Real.sqrt (m ^ 2 + s) + m)))
      (-(2 * Real.sqrt (m ^ 2 + s) + m) /
        (4 * Real.sqrt (m ^ 2 + s) ^ 3 * (Real.sqrt (m ^ 2 + s) + m) ^ 2)) s := by
  have hE : 0 < Real.sqrt (m ^ 2 + s) := Real.sqrt_pos.2 hs
  have hsq := ((Real.hasDerivAt_sqrt hs.ne').comp s ((hasDerivAt_id s).const_add (m ^ 2)))
  have hden := ((hsq.const_mul 2).mul (hsq.add_const m))
  have hne : 2 * Real.sqrt (m ^ 2 + s) * (Real.sqrt (m ^ 2 + s) + m) ≠ 0 := by positivity
  have h := (hasDerivAt_const s (1 : ℝ)).div hden hne
  convert h using 1
  simp only [Function.comp_def, id]
  field_simp
  ring

/-! ### 結論:A_B と A_W はゲージ同値でない(p ≠ 0 の各点で) -/

theorem berry_not_gauge_wigner (m E : ℝ) (hm : 0 < m) (hEm : m < E)
    (p : Fin 3 → ℂ) (hs : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = ((E ^ 2 - m ^ 2 : ℝ) : ℂ)) :
    let FW : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := fun k =>
      Complex.I • (((-1 / (2 * m * E) : ℝ) : ℂ) • σ k
        + (((-1 / (2 * m ^ 2 * E * (E + m)) : ℝ) : ℂ) * p k) • sd p + (0 : ℂ) • pxs p k)
    let FB : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := fun k =>
      Complex.I • (((m / (2 * E ^ 3) : ℝ) : ℂ) • σ k
        + (((1 / (2 * E ^ 3 * (E + m)) : ℝ) : ℂ) * p k) • sd p + (0 : ℂ) • pxs p k)
    ¬ ∃ g : Matrix (Fin 2) (Fin 2) ℂ, IsUnit g.det ∧ ∀ k, FB k = g * FW k * g⁻¹ := by
  intro FW FB
  rintro ⟨g, hg, hFB⟩
  have hE : 0 < E := lt_trans hm hEm
  have hsumW := gram_trace p ((-1 / (2 * m * E) : ℝ) : ℂ) ((-1 / (2 * m ^ 2 * E * (E + m)) : ℝ) : ℂ) 0
  have hsumB := gram_trace p ((m / (2 * E ^ 3) : ℝ) : ℂ) ((1 / (2 * E ^ 3 * (E + m)) : ℝ) : ℂ) 0
  simp only at hsumW hsumB
  have heq : (∑ k, -2 * trace (FB k * FB k)) = ∑ k, -2 * trace (FW k * FW k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hFB k, gram_gauge g (FW k) hg]
  rw [show (∑ k, -2 * trace (FB k * FB k)) = _ from hsumB,
    show (∑ k, -2 * trace (FW k * FW k)) = _ from hsumW, hs] at heq
  have hW := trG_W m E hm hE
  have hB := trG_B m E hm hE
  simp only [trG] at hW hB
  have hreal : (4 * (3 * (m / (2 * E ^ 3)) ^ 2 + 2 * (m / (2 * E ^ 3)) * (1 / (2 * E ^ 3 * (E + m)))
        * (E ^ 2 - m ^ 2) + (1 / (2 * E ^ 3 * (E + m))) ^ 2 * (E ^ 2 - m ^ 2) ^ 2
        + 2 * 0 ^ 2 * (E ^ 2 - m ^ 2)) : ℝ)
      = 4 * (3 * (-1 / (2 * m * E)) ^ 2 + 2 * (-1 / (2 * m * E)) * (-1 / (2 * m ^ 2 * E * (E + m)))
        * (E ^ 2 - m ^ 2) + (-1 / (2 * m ^ 2 * E * (E + m))) ^ 2 * (E ^ 2 - m ^ 2) ^ 2
        + 2 * 0 ^ 2 * (E ^ 2 - m ^ 2)) := by
    exact_mod_cast heq
  rw [hW, hB] at hreal
  exact absurd hreal (trG_B_lt m E hm hEm).ne

end

end CFT.AlphaI_AW
