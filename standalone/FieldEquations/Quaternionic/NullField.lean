import Mathlib.Tactic

/-
# Null electromagnetic fields and nilpotent matrices

For the 2×2 complex matrix M of F = E + iB, E² = B² and E·B = 0 ⇔ M² = 0 (`null_iff_nilpotent`).
-/

namespace FieldEquations.NullField

open Matrix

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

/-- Null fields correspond to nilpotent matrices. -/
theorem null_iff_nilpotent (E1 E2 E3 B1 B2 B3 : ℝ) :
    (E1 ^ 2 + E2 ^ 2 + E3 ^ 2 = B1 ^ 2 + B2 ^ 2 + B3 ^ 2 ∧ E1 * B1 + E2 * B2 + E3 * B3 = 0) ↔
      M (⟨E3, B3⟩ : ℂ) ((⟨E1, B1⟩ : ℂ) - Complex.I * (⟨E2, B2⟩ : ℂ))
          ((⟨E1, B1⟩ : ℂ) + Complex.I * (⟨E2, B2⟩ : ℂ))
        * M (⟨E3, B3⟩ : ℂ) ((⟨E1, B1⟩ : ℂ) - Complex.I * (⟨E2, B2⟩ : ℂ))
          ((⟨E1, B1⟩ : ℂ) + Complex.I * (⟨E2, B2⟩ : ℂ)) = 0 := by
  rw [M_sq_zero_iff, pauli_param]
  exact (null_iff E1 E2 E3 B1 B2 B3).symm

end FieldEquations.NullField
