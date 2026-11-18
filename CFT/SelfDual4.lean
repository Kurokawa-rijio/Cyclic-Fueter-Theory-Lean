/-
  R⁴ = ℍ 上の 2 形式の自己双対・反自己双対への分解と四元数(2026-11-14、命題 Q8)

  2 形式 F を成分 F_ab(a < b、6 個)で表す。Hodge の星は (*F)_01 = F_23、(*F)_02 = −F_13、(*F)_03 = F_12 など。
  * `star_star`:** = 1。
  * `star_leftForm`:虚の四元数 x の左からの掛け算がつくる 2 形式 ω^L_x(u,v) = ⟨u, x v⟩ は自己双対(*ω = ω)。
  * `star_rightForm`:右からの掛け算がつくる 2 形式 ω^R_x(u,v) = ⟨u, v x⟩ は反自己双対(*ω = −ω)。
  * `leftForm_spec`、`rightForm_spec`:⟨u, x v⟩ = x₀⟨u,v⟩ + ω^L_x(u,v)、⟨u, v x⟩ = x₀⟨u,v⟩ + ω^R_x(u,v)。
  * `decomp`:2F = ω^L_p + ω^R_q(p, q は F の成分の一次結合)。Λ² = Λ²₊ ⊕ Λ²₋ ≅ Im ℍ ⊕ Im ℍ。
  * `selfDual_of_right_zero`、`antiSelfDual_of_left_zero`:q = 0 なら *F = F、p = 0 なら *F = −F。
  八元数(R⁸)での対応物は `CFT.Cayley4`(Cayley 4 形式、7 + 21 への分解)。
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic

namespace CFT.SelfDual4

/-- R⁴ 上の 2 形式(成分 F_ab、a < b) -/
@[ext] structure TwoForm4 (R : Type*) where
  f01 : R
  f02 : R
  f03 : R
  f12 : R
  f13 : R
  f23 : R

variable {R : Type*} [CommRing R]

/-- Hodge の星(向きは e₀e₁e₂e₃) -/
def star (F : TwoForm4 R) : TwoForm4 R := ⟨F.f23, -F.f13, F.f12, F.f03, -F.f02, F.f01⟩

/-- 和 -/
def add (F G : TwoForm4 R) : TwoForm4 R :=
  ⟨F.f01 + G.f01, F.f02 + G.f02, F.f03 + G.f03, F.f12 + G.f12, F.f13 + G.f13, F.f23 + G.f23⟩

/-- スカラー倍 -/
def smul (a : R) (F : TwoForm4 R) : TwoForm4 R :=
  ⟨a * F.f01, a * F.f02, a * F.f03, a * F.f12, a * F.f13, a * F.f23⟩

/-- 虚の四元数 x₁i + x₂j + x₃k の左からの掛け算がつくる 2 形式 -/
def leftForm (x1 x2 x3 : R) : TwoForm4 R := ⟨-x1, -x2, -x3, -x3, x2, -x1⟩

/-- 虚の四元数 x₁i + x₂j + x₃k の右からの掛け算がつくる 2 形式 -/
def rightForm (x1 x2 x3 : R) : TwoForm4 R := ⟨-x1, -x2, -x3, x3, -x2, x1⟩

/-- 四元数の内積 -/
def innerQ (u v : Quaternion R) : R :=
  u.re * v.re + u.imI * v.imI + u.imJ * v.imJ + u.imK * v.imK

/-- 2 形式の値 F(u, v) -/
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

/-- 2F = (自己双対部分) + (反自己双対部分) -/
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

end CFT.SelfDual4
