/-
  新しい柱 1:ローレンツ群 = 回転 × ブースト(極分解、2026-11-05)

  運動学(作用なし)。SL(2,ℂ)(I.8 の複素の球面 det M(z) = z₀² + z·z = 1)の元 M は、
    M = U·B、U は回転(U†U = 1、det U = 1:球面 S³ = SU(2))、
          B はブースト(B† = B、det B = 1、tr B > 0:双曲面 H³)
  にただ一通りに分かれる。2×2 では Cayley–Hamilton の式 X² = (tr X)X − (det X)·1 だけで、
  平方根と逆行列が明示的に書ける:
    P = M†M、t = tr P(実数、≥ 0)、s = √(t + 2)、B = (P + 1)/s、B⁻¹ = s·1 − B、U = M·B⁻¹。
  * `ch2`:Cayley–Hamilton(2×2)
  * `polar_exists`:存在(上の式)
  * `polar_unique`:一意性(B = (B² + 1)/tr B、(tr B)² = tr(B²) + 2 から)
  * `sphere_meets_hyperboloid`:回転でありブーストでもあるのは恒等変換(頂点 = 静止)だけ
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CFT.Polar

open Matrix Complex

/-- 2×2 の複素行列 -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Cayley–Hamilton(2×2):X² = (tr X)X − (det X)·1 -/
theorem ch2 (X : M2) : X * X = X.trace • X - X.det • (1 : M2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.one_apply] <;>
    ring

theorem det_add_one (X : M2) : (X + 1).det = X.det + X.trace + 1 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp [Matrix.add_apply, Matrix.one_apply]
  ring

theorem trace_add_one (X : M2) : (X + 1).trace = X.trace + 2 := by
  rw [Matrix.trace_add, Matrix.trace_one]
  simp

theorem trace_sq (X : M2) : (X * X).trace = X.trace ^ 2 - 2 * X.det := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- tr(M†M) = Σ|M_ij|²(実数) -/
theorem trace_gram (M : M2) :
    (Mᴴ * M).trace = ((Complex.normSq (M 0 0) + Complex.normSq (M 1 0) + Complex.normSq (M 0 1)
      + Complex.normSq (M 1 1) : ℝ) : ℂ) := by
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

theorem det_gram (M : M2) (hM : M.det = 1) : (Mᴴ * M).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, hM, star_one, one_mul]

theorem gram_herm (M : M2) : (Mᴴ * M)ᴴ = Mᴴ * M := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- 【柱 1】極分解の存在:det M = 1 なら M = U·B(U は SU(2)、B は正の Hermite で det 1) -/
theorem polar_exists (M : M2) (hM : M.det = 1) :
    ∃ U B : M2, Uᴴ * U = 1 ∧ U.det = 1 ∧ Bᴴ = B ∧ B.det = 1 ∧
      (∃ τ : ℝ, 0 < τ ∧ B.trace = τ) ∧ U * B = M := by
  set P : M2 := Mᴴ * M with hPdef
  set t : ℝ := Complex.normSq (M 0 0) + Complex.normSq (M 1 0) + Complex.normSq (M 0 1)
    + Complex.normSq (M 1 1) with htdef
  have ht0 : 0 ≤ t := by
    have := Complex.normSq_nonneg (M 0 0); have := Complex.normSq_nonneg (M 1 0)
    have := Complex.normSq_nonneg (M 0 1); have := Complex.normSq_nonneg (M 1 1)
    linarith
  have hPtr : P.trace = (t : ℂ) := trace_gram M
  have hPdet : P.det = 1 := det_gram M hM
  have hPh : Pᴴ = P := gram_herm M
  set s : ℝ := Real.sqrt (t + 2) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : (s : ℂ) ^ 2 = (t : ℂ) + 2 := by
    have : s ^ 2 = t + 2 := Real.sq_sqrt (by linarith)
    exact_mod_cast this
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  set B : M2 := (s : ℂ)⁻¹ • (P + 1) with hBdef
  -- B² = P
  have hPP : (P + 1) * (P + 1) = ((t : ℂ) + 2) • P := by
    have h := ch2 P
    rw [hPtr, hPdet, one_smul] at h
    rw [add_mul, mul_add, mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, h]
    module
  have hBB : B * B = P := by
    rw [hBdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPP, smul_smul]
    have : (s : ℂ)⁻¹ * (s : ℂ)⁻¹ * ((t : ℂ) + 2) = 1 := by
      rw [← hs2]; field_simp <;> ring
    rw [this, one_smul]
  have hBtr : B.trace = (s : ℂ) := by
    rw [hBdef, Matrix.trace_smul, trace_add_one, hPtr, smul_eq_mul, ← hs2]
    field_simp
    ring
  have hBdet : B.det = 1 := by
    rw [hBdef, Matrix.det_smul, det_add_one, hPdet, hPtr]
    simp only [Fintype.card_fin]
    rw [inv_pow, show (1 : ℂ) + (t : ℂ) + 1 = (t : ℂ) + 2 by ring, ← hs2]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hsc)
  have hBh : Bᴴ = B := by
    rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hPh, Matrix.conjTranspose_one]
    congr 1
    simp [Complex.conj_ofReal]
  -- B⁻¹ = s·1 − B
  set Bi : M2 := (s : ℂ) • (1 : M2) - B with hBidef
  have hchB : B * B = (s : ℂ) • B - (1 : M2) := by
    have h := ch2 B
    rw [hBtr, hBdet, one_smul] at h
    exact h
  have hBBi : B * Bi = 1 := by
    rw [hBidef, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hchB]
    abel
  have hBiB : Bi * B = 1 := by
    rw [hBidef, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hchB]
    abel
  have hBih : Biᴴ = Bi := by
    rw [hBidef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hBh]
    congr 1
    simp [Complex.conj_ofReal]
  refine ⟨M * Bi, B, ?_, ?_, hBh, hBdet, ⟨s, hs0, hBtr⟩, ?_⟩
  · rw [Matrix.conjTranspose_mul, hBih]
    calc Bi * Mᴴ * (M * Bi) = Bi * (Mᴴ * M) * Bi := by simp only [Matrix.mul_assoc]
      _ = Bi * (B * B) * Bi := by rw [← hPdef, hBB]
      _ = (Bi * B) * (B * Bi) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiB, hBBi, Matrix.one_mul]
  · have h1 : B.det * Bi.det = 1 := by rw [← Matrix.det_mul, hBBi, Matrix.det_one]
    rw [hBdet, one_mul] at h1
    rw [Matrix.det_mul, hM, h1, one_mul]
  · rw [Matrix.mul_assoc, hBiB, Matrix.mul_one]

/-- 正の Hermite で det 1 の B は B² だけで決まる:B = (B² + 1)/tr B、(tr B)² = tr(B²) + 2 -/
theorem boost_from_square (B : M2) (hdet : B.det = 1) (τ : ℝ) (hτ : B.trace = τ) (hτ0 : 0 < τ) :
    B = (τ : ℂ)⁻¹ • (B * B + 1) ∧ (τ : ℂ) ^ 2 = (B * B).trace + 2 := by
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ0.ne'
  constructor
  · rw [ch2 B, hτ, hdet, one_smul, sub_add_cancel, smul_smul, inv_mul_cancel₀ hτc, one_smul]
  · rw [trace_sq, hτ, hdet]; ring

/-- 【柱 1】極分解の一意性 -/
theorem polar_unique (U1 U2 B1 B2 : M2) (hU1 : U1ᴴ * U1 = 1) (hU2 : U2ᴴ * U2 = 1)
    (hB1 : B1ᴴ = B1) (hB2 : B2ᴴ = B2) (hd1 : B1.det = 1) (hd2 : B2.det = 1)
    (τ1 τ2 : ℝ) (ht1 : B1.trace = τ1) (ht2 : B2.trace = τ2) (h1 : 0 < τ1) (h2 : 0 < τ2)
    (h : U1 * B1 = U2 * B2) : B1 = B2 ∧ U1 = U2 := by
  have hsq : B1 * B1 = B2 * B2 := by
    have e1 : (U1 * B1)ᴴ * (U1 * B1) = B1 * B1 := by
      rw [Matrix.conjTranspose_mul, hB1]
      calc B1 * U1ᴴ * (U1 * B1) = B1 * (U1ᴴ * U1) * B1 := by simp only [Matrix.mul_assoc]
        _ = B1 * B1 := by rw [hU1, Matrix.mul_one]
    have e2 : (U2 * B2)ᴴ * (U2 * B2) = B2 * B2 := by
      rw [Matrix.conjTranspose_mul, hB2]
      calc B2 * U2ᴴ * (U2 * B2) = B2 * (U2ᴴ * U2) * B2 := by simp only [Matrix.mul_assoc]
        _ = B2 * B2 := by rw [hU2, Matrix.mul_one]
    rw [← e1, ← e2, h]
  obtain ⟨f1, g1⟩ := boost_from_square B1 hd1 τ1 ht1 h1
  obtain ⟨f2, g2⟩ := boost_from_square B2 hd2 τ2 ht2 h2
  have hτ : τ1 = τ2 := by
    have : (τ1 : ℂ) ^ 2 = (τ2 : ℂ) ^ 2 := by rw [g1, g2, hsq]
    have : τ1 ^ 2 = τ2 ^ 2 := by exact_mod_cast this
    nlinarith [sq_nonneg (τ1 - τ2), sq_nonneg (τ1 + τ2)]
  have hB : B1 = B2 := by rw [f1, f2, hsq, hτ]
  refine ⟨hB, ?_⟩
  -- B1 は可逆(B1·(τ1·1 − B1) = 1)
  have hinv : B1 * ((τ1 : ℂ) • (1 : M2) - B1) = 1 := by
    have hc := ch2 B1
    rw [ht1, hd1, one_smul] at hc
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hc]
    abel
  rw [← hB] at h
  calc U1 = U1 * (B1 * ((τ1 : ℂ) • (1 : M2) - B1)) := by rw [hinv, Matrix.mul_one]
    _ = U1 * B1 * ((τ1 : ℂ) • (1 : M2) - B1) := by rw [Matrix.mul_assoc]
    _ = U2 * B1 * ((τ1 : ℂ) • (1 : M2) - B1) := by rw [h]
    _ = U2 := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

/-- 【柱 1】球面と双曲面の交わり:回転(U†U = 1)でありブースト(U† = U、det 1、tr > 0)でもあるのは
恒等変換(頂点 = 静止)だけ -/
theorem sphere_meets_hyperboloid (U : M2) (hU : Uᴴ * U = 1) (hh : Uᴴ = U) (hd : U.det = 1)
    (τ : ℝ) (ht : U.trace = τ) (hτ : 0 < τ) : U = 1 := by
  have hsq : U * U = 1 := by rw [← hU, hh]
  obtain ⟨f, g⟩ := boost_from_square U hd τ ht hτ
  rw [hsq] at f g
  have h4 : (τ : ℂ) ^ 2 = 4 := by
    rw [g, Matrix.trace_one]; simp; norm_num
  have hτ2 : τ = 2 := by
    have : τ ^ 2 = 4 := by exact_mod_cast h4
    nlinarith
  rw [f, hτ2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> norm_num

end CFT.Polar
