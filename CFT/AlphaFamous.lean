/-
  有名な方程式がこの理論から出るかの点検(2026-11-12、G = 1 を基本に)

  * Birkhoff と Schwarzschild:W² = 1、W_u = 0 なら m_u = 0(`fam_birkhoff_u`)。切り口の上でも
    物質がなければ M′ = 0(`fam_birkhoff_slice`)。質量は定数で、|∇r|² = 1 − 2M/r。
  * Reissner–Nordström:W = 0 なら (m + ℓ²/(2r))_u = 0(`fam_rn_mass`)。M = m + ℓ²/(2r) が定数で F = 1 − 2M/r + ℓ²/r²。
  * JT 重力(首の近く):Φ = r²、W = 0 でポテンシャル U(Φ) = 2 − 2ℓ²/Φ。U(ℓ²) = 0(`fam_jt_U0`)、
    U′(ℓ²) = 2/ℓ²(`fam_jt_slope`)、Φ = ℓ²(1 + φ) の一次の係数 U′(ℓ²)ℓ² = 2(`fam_jt_coeff`)。
    作用は (ℓ²/4G)∫√−h R + (ℓ²/4G)∫√−h φ(R + 2/ℓ²):位相の項と JT の項。
    位相の項の係数 (ℓ²/4G)·4π = πℓ²/G(`fam_jt_S0`、極限ブラックホールのエントロピー)。
    W の二次の項 −2 + 4W² − 2W⁴(`fam_jt_Wmass`):質量の 2 乗 m²ℓ² = −1、Δ(Δ − 1) = −1 に実の解はない(`fam_no_real_dim`)。
  * Hawking 温度:F = (r − r₊)(r − r₋)/r² の地平線での傾きは (r₊ − r₋)/r₊²(`fam_hawking_slope`)。
    T = F′(r₊)/4π(周期の規則は外部)。Schwarzschild では 1/(8πM)(`fam_schw_T`)、極限(首)では 0(`fam_extremal_T`)。
  * 第一法則と面積則:M = (r₊ + ℓ²/r₊)/2 について dM/dr₊ = T · d(πr₊²)/dr₊(`fam_first_law`):S = πr₊² = A/4。
  * S³ の上の YM の Hagedorn 温度:1 粒子の分配関数 (6x² − 2x³)/(1 − x)³ = 1 の解は x = 2 − √3(`fam_hagedorn`)。
-/
import CFT.AlphaCanonical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

open Real

namespace CFT.FAM

theorem fam_birkhoff_u (r ru rv Om W Wu l : ℝ) (hW : W ^ 2 = 1) (hWu : Wu = 0) :
    -2 * l ^ 2 * Wu ^ 2 * rv / Om + ru * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2) = 0 := by
  have h1 : 1 - W ^ 2 = 0 := by linarith
  rw [hWu, h1]
  ring

theorem fam_birkhoff_slice (r r1 r2 L L1 PL PL1 Pr PW : ℝ) (hr : r ≠ 0) (hL : L ≠ 0)
    (hH : (-Pr * PL / r + L * PL ^ 2 / (2 * r ^ 2) + r * r2 / L - r * r1 * L1 / L ^ 2
          + r1 ^ 2 / (2 * L) - L / 2) + 0 = 0)
    (hHx : (Pr * r1 - L * PL1) + PW * 0 = 0) :
    PL * PL1 / r - PL ^ 2 * r1 / (2 * r ^ 2) + r1 / 2 * (1 - r1 ^ 2 / L ^ 2) - r * r1 * r2 / L ^ 2
        + r * r1 ^ 2 * L1 / L ^ 3 = 0 := by
  rw [CFT.CAN.can_mass_constraint r r1 r2 L L1 PL PL1 Pr 0 PW 0 hr hL hH hHx]
  ring

theorem fam_rn_mass (r ru rv Om l : ℝ) :
    (-2 * l ^ 2 * (0 : ℝ) ^ 2 * rv / Om + ru * l ^ 2 * (1 - (0 : ℝ) ^ 2) ^ 2 / (2 * r ^ 2))
      + -(l ^ 2 * ru) / (2 * r ^ 2) = 0 := by
  ring

theorem fam_jt_U0 (l : ℝ) (hl : l ≠ 0) : 2 - 2 * l ^ 2 / l ^ 2 = 0 := by
  rw [mul_div_assoc, div_self (pow_ne_zero 2 hl)]
  ring

theorem fam_jt_slope (l : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun Φ : ℝ => 2 - 2 * l ^ 2 * Φ⁻¹) (2 * l ^ 2 * ((l ^ 2) ^ 2)⁻¹) (l ^ 2) := by
  have h := ((hasDerivAt_inv (pow_ne_zero 2 hl)).const_mul (2 * l ^ 2)).const_sub 2
  convert h using 1
  ring

theorem fam_jt_coeff (l : ℝ) (hl : l ≠ 0) : 2 * l ^ 2 * ((l ^ 2) ^ 2)⁻¹ * l ^ 2 = 2 := by
  field_simp <;> ring

theorem fam_jt_S0 (G l : ℝ) (hG : G ≠ 0) : l ^ 2 / (4 * G) * (4 * π) = π * l ^ 2 / G := by
  field_simp <;> ring

theorem fam_jt_Wmass (W l : ℝ) (hl : l ≠ 0) :
    -2 * l ^ 2 * (1 - W ^ 2) ^ 2 / l ^ 2 = -2 + 4 * W ^ 2 - 2 * W ^ 4 := by
  field_simp <;> ring

theorem fam_no_real_dim (Δ : ℝ) : Δ * (Δ - 1) ≠ -1 := by
  intro h
  nlinarith [sq_nonneg (2 * Δ - 1)]

theorem fam_hawking_slope (a b : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun r : ℝ => (r - a) * (r - b) / (r * r)) ((a - b) / (a * a)) a := by
  have h := (((hasDerivAt_id' a).sub_const a).mul ((hasDerivAt_id' a).sub_const b)).div
    ((hasDerivAt_id' a).mul (hasDerivAt_id' a)) (mul_ne_zero ha ha)
  convert h using 1
  field_simp <;> ring

theorem fam_schw_T (M : ℝ) (hM : M ≠ 0) :
    (2 * M - 0) / ((2 * M) * (2 * M)) / (4 * π) = 1 / (8 * π * M) := by
  have hp := Real.pi_ne_zero
  field_simp <;> ring

theorem fam_extremal_T (l : ℝ) : (l - l) / (l * l) = 0 := by simp

theorem fam_first_law (rp l : ℝ) (hrp : rp ≠ 0) :
    (1 - l ^ 2 / rp ^ 2) / 2 = ((rp - l ^ 2 / rp) / (rp * rp)) / (4 * π) * (2 * π * rp) := by
  have hp := Real.pi_ne_zero
  field_simp <;> ring

theorem fam_hagedorn :
    6 * (2 - Real.sqrt 3) ^ 2 - 2 * (2 - Real.sqrt 3) ^ 3 = (1 - (2 - Real.sqrt 3)) ^ 3 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (-(3 - Real.sqrt 3)) * h

end CFT.FAM
