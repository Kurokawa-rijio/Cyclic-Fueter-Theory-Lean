/-
  場が光的(null)であることと、2×2 複素行列の冪零性(2026-11-14、命題 Q3)

  電場 E と磁場 B(SU(2) の場なら色の成分ごと)から複素 3 ベクトル f = E + iB をつくる。
  f·f = (E² − B²) + 2i E·B なので、二つの不変量 E² − B²(∝ F·F)と E·B(∝ F·*F)がともにゼロ ⇔ f·f = 0。
  f を跡のない 2×2 複素行列 M = f·σ = [[f₃, f₁ − i f₂], [f₁ + i f₂, −f₃]] に移すと M² = (f·f)·1、det M = −f·f。
  * `M_sq`、`M_det`:M = [[a, b], [c, −a]] に対して M² = (a² + bc)·1、det M = −(a² + bc)。
  * `M_sq_zero_iff`、`M_det_zero_iff`:M² = 0 ⇔ a² + bc = 0 ⇔ det M = 0。
  * `pauli_param`:a = f₃、b = f₁ − i f₂、c = f₁ + i f₂ なら a² + bc = f₁² + f₂² + f₃²。
  * `fsq_re`、`fsq_im`:f·f の実部は E² − B²、虚部は 2 E·B。
  * `null_iff`:f·f = 0 ⇔ E² = B² かつ E·B = 0。
  * `null_iff_nilpotent`:E² = B² かつ E·B = 0 ⇔ M² = 0。
  解釈(未形式化):ゼロでない 2×2 の冪零行列は階数 1 なので、これは「階数 1 = 光的」の場の強さについての形と読める。
  階数についての定理はこのファイルにはない。
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace CFT.NullField

open Matrix

/-- 跡のない 2×2 複素行列 -/
def M (a b c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; c, -a]

theorem M_det (a b c : ℂ) : (M a b c).det = -(a ^ 2 + b * c) := by
  simp only [M, Matrix.det_fin_two_of]
  ring

theorem M_sq (a b c : ℂ) :
    M a b c * M a b c = !![a ^ 2 + b * c, 0; 0, a ^ 2 + b * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem M_sq_zero_iff (a b c : ℂ) : M a b c * M a b c = 0 ↔ a ^ 2 + b * c = 0 := by
  rw [M_sq]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00
  · intro h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem M_det_zero_iff (a b c : ℂ) : (M a b c).det = 0 ↔ a ^ 2 + b * c = 0 := by
  rw [M_det, neg_eq_zero]

theorem pauli_param (f1 f2 f3 : ℂ) :
    f3 ^ 2 + (f1 - Complex.I * f2) * (f1 + Complex.I * f2) = f1 ^ 2 + f2 ^ 2 + f3 ^ 2 := by
  linear_combination (-f2 ^ 2) * Complex.I_sq

/-- f·f(f_k = E_k + i B_k) -/
def fsq (E1 E2 E3 B1 B2 B3 : ℝ) : ℂ :=
  (⟨E1, B1⟩ : ℂ) ^ 2 + (⟨E2, B2⟩ : ℂ) ^ 2 + (⟨E3, B3⟩ : ℂ) ^ 2

theorem fsq_re (E1 E2 E3 B1 B2 B3 : ℝ) :
    (fsq E1 E2 E3 B1 B2 B3).re = (E1 ^ 2 + E2 ^ 2 + E3 ^ 2) - (B1 ^ 2 + B2 ^ 2 + B3 ^ 2) := by
  simp only [fsq, sq, Complex.add_re, Complex.mul_re]
  ring

theorem fsq_im (E1 E2 E3 B1 B2 B3 : ℝ) :
    (fsq E1 E2 E3 B1 B2 B3).im = 2 * (E1 * B1 + E2 * B2 + E3 * B3) := by
  simp only [fsq, sq, Complex.add_im, Complex.mul_im]
  ring

theorem null_iff (E1 E2 E3 B1 B2 B3 : ℝ) :
    fsq E1 E2 E3 B1 B2 B3 = 0 ↔
      E1 ^ 2 + E2 ^ 2 + E3 ^ 2 = B1 ^ 2 + B2 ^ 2 + B3 ^ 2 ∧ E1 * B1 + E2 * B2 + E3 * B3 = 0 := by
  rw [Complex.ext_iff, fsq_re, fsq_im]
  simp only [Complex.zero_re, Complex.zero_im]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- 二つの不変量がともにゼロ ⇔ M = f·σ が冪零 -/
theorem null_iff_nilpotent (E1 E2 E3 B1 B2 B3 : ℝ) :
    (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 = B1 ^ 2 + B2 ^ 2 + B3 ^ 2 ∧ E1 * B1 + E2 * B2 + E3 * B3 = 0) ↔
      M (⟨E3, B3⟩ : ℂ) ((⟨E1, B1⟩ : ℂ) - Complex.I * (⟨E2, B2⟩ : ℂ))
          ((⟨E1, B1⟩ : ℂ) + Complex.I * (⟨E2, B2⟩ : ℂ))
        * M (⟨E3, B3⟩ : ℂ) ((⟨E1, B1⟩ : ℂ) - Complex.I * (⟨E2, B2⟩ : ℂ))
          ((⟨E1, B1⟩ : ℂ) + Complex.I * (⟨E2, B2⟩ : ℂ)) = 0 := by
  rw [M_sq_zero_iff, pauli_param]
  exact (null_iff E1 E2 E3 B1 B2 B3).symm

end CFT.NullField
