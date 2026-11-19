import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-
# Fueter operators and their squares

Commuting derivations ∂₀,…,∂₃ on a commutative ring R act componentwise on ℍ[R].
D = ∂₀ + i∂₁ + j∂₂ + k∂₃ (Fueter operator), D̄ = ∂₀ − i∂₁ − j∂₂ − k∂₃.
D̄D = DD̄ = Δ₄ (`conj_product`, `product_conj`), D² + D̄² = 2□ (`square_sum`).
With I ∈ R, I² = −1, ∂I = 0, the biquaternionic operator D = ∂₀ + I(i∂₁ + j∂₂ + k∂₃) satisfies
D̄D = DD̄ = □ = ∂₀² − ∂₁² − ∂₂² − ∂₃² (`biquaternion_box`).
-/

open Quaternion

namespace FieldEquations.QuaternionOperators

set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R]

def dq (d : Derivation ℤ R R) (f : ℍ[R]) : ℍ[R] := ⟨d f.re, d f.imI, d f.imJ, d f.imK⟩

def e : Fin 4 → ℍ[R] := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

variable (d : Fin 4 → Derivation ℤ R R)

def DR (f : ℍ[R]) : ℍ[R] := ∑ a, e a * dq (d a) f

def DRbar (f : ℍ[R]) : ℍ[R] := ∑ a, star (e a) * dq (d a) f

def Lap (f : ℍ[R]) : ℍ[R] := ∑ a, dq (d a) (dq (d a) f)

def Box (f : ℍ[R]) : ℍ[R] :=
  dq (d 0) (dq (d 0) f) - dq (d 1) (dq (d 1) f) - dq (d 2) (dq (d 2) f) - dq (d 3) (dq (d 3) f)

def Vec (f : ℍ[R]) : ℍ[R] := e 1 * dq (d 1) f + e 2 * dq (d 2) f + e 3 * dq (d 3) f

section
variable (hc : ∀ a b x, d a (d b x) = d b (d a x))
include hc

private theorem c10 (x : R) : d 1 (d 0 x) = d 0 (d 1 x) := hc 1 0 x
private theorem c20 (x : R) : d 2 (d 0 x) = d 0 (d 2 x) := hc 2 0 x
private theorem c30 (x : R) : d 3 (d 0 x) = d 0 (d 3 x) := hc 3 0 x
private theorem c21 (x : R) : d 2 (d 1 x) = d 1 (d 2 x) := hc 2 1 x
private theorem c31 (x : R) : d 3 (d 1 x) = d 1 (d 3 x) := hc 3 1 x
private theorem c32 (x : R) : d 3 (d 2 x) = d 2 (d 3 x) := hc 3 2 x

/-- D̄D = Δ₄. -/
theorem conj_product (f : ℍ[R]) : DRbar d (DR d f) = Lap d f := by
  ext <;>
  simp [DR, DRbar, Lap, dq, e, Fin.sum_univ_four, Quaternion.ext_iff, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

theorem product_conj (f : ℍ[R]) : DR d (DRbar d f) = Lap d f := by
  ext <;>
  simp [DR, DRbar, Lap, dq, e, Fin.sum_univ_four, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

theorem square (f : ℍ[R]) :
    DR d (DR d f) = Box d f + (2 : R) • dq (d 0) (Vec d f) := by
  ext <;>
  simp [DR, Box, Vec, dq, e, Fin.sum_univ_four, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

theorem square_sum (f : ℍ[R]) : DR d (DR d f) + DRbar d (DRbar d f) = (2 : R) • Box d f := by
  ext <;>
  simp [DR, DRbar, Box, dq, e, Fin.sum_univ_four, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

variable (I : R) (hI : I * I = -1) (hdI : ∀ a, d a I = 0)

def DB (f : ℍ[R]) : ℍ[R] := dq (d 0) f + I • Vec d f

def DBbar (f : ℍ[R]) : ℍ[R] := dq (d 0) f - I • Vec d f

include hI hdI

/-- For the biquaternionic operator, D̄D = DD̄ = □. -/
theorem biquaternion_box (f : ℍ[R]) :
    DBbar d I (DB d I f) = Box d f ∧ DB d I (DBbar d I f) = Box d f := by
  have hd : ∀ a x, d a (I * x) = I * d a x := by
    intro a x; rw [Derivation.leibniz, hdI a]; simp [smul_eq_mul]
  constructor <;>
  ext <;>
  simp [DB, DBbar, Box, Vec, dq, e, map_add, map_sub, map_neg, hd,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;>
  (ring_nf; simp only [show I ^ 2 = -1 by rw [sq, hI]]; ring)

end

end FieldEquations.QuaternionOperators
