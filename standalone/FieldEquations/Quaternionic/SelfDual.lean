import Mathlib.Tactic

/-
# Self-dual 2-forms on ℝ⁴ and quaternions

Left and right multiplication by pure quaternions give the self-dual and anti-self-dual
2-forms; every 2-form F satisfies 2F = (self-dual part) + (anti-self-dual part) (`decomp`).
-/

namespace FieldEquations.SelfDual

@[ext] structure TwoForm4 (R : Type*) where
  f01 : R
  f02 : R
  f03 : R
  f12 : R
  f13 : R
  f23 : R

variable {R : Type*} [CommRing R]

def star (F : TwoForm4 R) : TwoForm4 R := ⟨F.f23, -F.f13, F.f12, F.f03, -F.f02, F.f01⟩

def add (F G : TwoForm4 R) : TwoForm4 R :=
  ⟨F.f01 + G.f01, F.f02 + G.f02, F.f03 + G.f03, F.f12 + G.f12, F.f13 + G.f13, F.f23 + G.f23⟩

def smul (a : R) (F : TwoForm4 R) : TwoForm4 R :=
  ⟨a * F.f01, a * F.f02, a * F.f03, a * F.f12, a * F.f13, a * F.f23⟩

def leftForm (x1 x2 x3 : R) : TwoForm4 R := ⟨-x1, -x2, -x3, -x3, x2, -x1⟩

def rightForm (x1 x2 x3 : R) : TwoForm4 R := ⟨-x1, -x2, -x3, x3, -x2, x1⟩

def innerQ (u v : Quaternion R) : R :=
  u.re * v.re + u.imI * v.imI + u.imJ * v.imJ + u.imK * v.imK

def pair (F : TwoForm4 R) (u v : Quaternion R) : R :=
  F.f01 * (u.re * v.imI - u.imI * v.re) + F.f02 * (u.re * v.imJ - u.imJ * v.re)
    + F.f03 * (u.re * v.imK - u.imK * v.re) + F.f12 * (u.imI * v.imJ - u.imJ * v.imI)
    + F.f13 * (u.imI * v.imK - u.imK * v.imI) + F.f23 * (u.imJ * v.imK - u.imK * v.imJ)

theorem star_star (F : TwoForm4 R) : star (star F) = F := by
  ext <;> simp only [star] <;> ring

theorem star_leftForm (x1 x2 x3 : R) : star (leftForm x1 x2 x3) = leftForm x1 x2 x3 := by
  ext <;> simp only [star, leftForm] <;> ring

theorem star_rightForm (x1 x2 x3 : R) :
    star (rightForm x1 x2 x3) = smul (-1) (rightForm x1 x2 x3) := by
  ext <;> simp only [star, rightForm, smul] <;> ring

theorem leftForm_spec (x u v : Quaternion R) :
    innerQ u (x * v) = x.re * innerQ u v + pair (leftForm x.imI x.imJ x.imK) u v := by
  simp only [innerQ, pair, leftForm, Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ,
    Quaternion.mul_imK]
  ring

theorem rightForm_spec (x u v : Quaternion R) :
    innerQ u (v * x) = x.re * innerQ u v + pair (rightForm x.imI x.imJ x.imK) u v := by
  simp only [innerQ, pair, rightForm, Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ,
    Quaternion.mul_imK]
  ring

/-- Decomposition of 2-forms into self-dual and anti-self-dual parts. -/
theorem decomp (F : TwoForm4 R) :
    smul 2 F = add (leftForm (-F.f01 - F.f23) (-F.f02 + F.f13) (-F.f03 - F.f12))
      (rightForm (-F.f01 + F.f23) (-F.f02 - F.f13) (-F.f03 + F.f12)) := by
  ext <;> simp only [smul, add, leftForm, rightForm] <;> ring

theorem selfDual_of_right_zero (F : TwoForm4 R)
    (h1 : -F.f01 + F.f23 = 0) (h2 : -F.f02 - F.f13 = 0) (h3 : -F.f03 + F.f12 = 0) :
    star F = F := by
  ext <;> simp only [star]
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination -h3
  · linear_combination h2
  · linear_combination -h1

theorem antiSelfDual_of_left_zero (F : TwoForm4 R)
    (h1 : -F.f01 - F.f23 = 0) (h2 : -F.f02 + F.f13 = 0) (h3 : -F.f03 - F.f12 = 0) :
    star F = smul (-1) F := by
  ext <;> simp only [star, smul]
  · linear_combination -h1
  · linear_combination -h2
  · linear_combination -h3
  · linear_combination -h3
  · linear_combination h2
  · linear_combination -h1

end FieldEquations.SelfDual
