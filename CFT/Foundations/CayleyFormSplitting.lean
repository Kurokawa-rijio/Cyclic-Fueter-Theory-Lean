/-
  R⁸ = 𝕆 上の Cayley 4 形式 Φ と、T = *(Φ∧·) の固有値 3、−1 による 2 形式の分け方(2026-11-14、命題 O5)
  (次元が 7 と 21 であること、直和分解になることそのものは数えていない。示したのは下の各式)

  2 形式 F を成分 F_ab(a < b、28 個)で表す。作用素 T は (T F)_ab = Σ_{c<d} Φ_abcd F_cd、つまり T F = *(Φ ∧ F)。
  Φ は八元数の積から Φ(u,v,w,z) = ½⟨u, z(w̄v) − v(w̄z)⟩ で決まる(`cayley_link`)。
  符号(向き)は、ω_x の側の固有値が +3 になるように選んだ。逆の向きでは固有値は −3 と +1 になる。
  * `T_quadratic`:T² = 2T + 3、つまり (T − 3)(T + 1) = 0。固有値は 3 と −1 だけ。
  * `T_rightForm`:虚の八元数 x の右からの掛け算がつくる 2 形式 ω_x(u,v) = ⟨u, v x⟩ は T ω_x = 3 ω_x をみたす(x は虚の八元数で成分は 7 個。張る空間の次元は数えていない)。
    `rightForm_spec`:⟨u, v x⟩ = x₀⟨u,v⟩ + ω_x(u,v)。
  * `T_decomp`:T F = −F + ω_(p(F))。p(F) は F と 7 個の ω_i との内積(`proj7`)。
    `T_eigen_neg_one`:p(F) = 0(7 本の一次条件)なら T F = −F(28 個の成分に 7 本の条件。21 次元であることは数えていない)。
  * `proj7_rightForm`:p(ω_x) = 4 x(7 個の ω_i は直交し、長さの 2 乗は 4)。`proj7_T`:p(T F) = 3 p(F)。
-/
import CFT.Foundations.OctonionAlgebra

namespace CFT.Oct8

/-- R⁸ 上の 2 形式(成分 F_ab、a < b) -/
@[ext] structure TwoForm (R : Type*) where
  f01 : R
  f02 : R
  f03 : R
  f04 : R
  f05 : R
  f06 : R
  f07 : R
  f12 : R
  f13 : R
  f14 : R
  f15 : R
  f16 : R
  f17 : R
  f23 : R
  f24 : R
  f25 : R
  f26 : R
  f27 : R
  f34 : R
  f35 : R
  f36 : R
  f37 : R
  f45 : R
  f46 : R
  f47 : R
  f56 : R
  f57 : R
  f67 : R

variable {R : Type*} [CommRing R]

namespace TwoForm

/-- T F = *(Φ ∧ F):(T F)_ab = Σ_{c<d} Φ_abcd F_cd -/
def T (F : TwoForm R) : TwoForm R :=
  ⟨-F.f23 - F.f45 + F.f67,
   F.f13 - F.f46 - F.f57,
   -F.f12 - F.f47 + F.f56,
   F.f15 + F.f26 + F.f37,
   -F.f14 + F.f27 - F.f36,
   -F.f17 - F.f24 + F.f35,
   F.f16 - F.f25 - F.f34,
   -F.f03 + F.f47 - F.f56,
   F.f02 - F.f46 - F.f57,
   -F.f05 - F.f27 + F.f36,
   F.f04 + F.f26 + F.f37,
   F.f07 - F.f25 - F.f34,
   -F.f06 + F.f24 - F.f35,
   -F.f01 + F.f45 - F.f67,
   -F.f06 + F.f17 - F.f35,
   -F.f07 - F.f16 + F.f34,
   F.f04 + F.f15 + F.f37,
   F.f05 - F.f14 - F.f36,
   -F.f07 - F.f16 + F.f25,
   F.f06 - F.f17 - F.f24,
   -F.f05 + F.f14 - F.f27,
   F.f04 + F.f15 + F.f26,
   -F.f01 + F.f23 - F.f67,
   -F.f02 - F.f13 + F.f57,
   -F.f03 + F.f12 - F.f56,
   F.f03 - F.f12 - F.f47,
   -F.f02 - F.f13 + F.f46,
   F.f01 - F.f23 - F.f45⟩

/-- 一次結合 a F + b G -/
def lin (a b : R) (F G : TwoForm R) : TwoForm R :=
  ⟨a * F.f01 + b * G.f01,
   a * F.f02 + b * G.f02,
   a * F.f03 + b * G.f03,
   a * F.f04 + b * G.f04,
   a * F.f05 + b * G.f05,
   a * F.f06 + b * G.f06,
   a * F.f07 + b * G.f07,
   a * F.f12 + b * G.f12,
   a * F.f13 + b * G.f13,
   a * F.f14 + b * G.f14,
   a * F.f15 + b * G.f15,
   a * F.f16 + b * G.f16,
   a * F.f17 + b * G.f17,
   a * F.f23 + b * G.f23,
   a * F.f24 + b * G.f24,
   a * F.f25 + b * G.f25,
   a * F.f26 + b * G.f26,
   a * F.f27 + b * G.f27,
   a * F.f34 + b * G.f34,
   a * F.f35 + b * G.f35,
   a * F.f36 + b * G.f36,
   a * F.f37 + b * G.f37,
   a * F.f45 + b * G.f45,
   a * F.f46 + b * G.f46,
   a * F.f47 + b * G.f47,
   a * F.f56 + b * G.f56,
   a * F.f57 + b * G.f57,
   a * F.f67 + b * G.f67⟩

/-- スカラー倍 -/
def smul (a : R) (F : TwoForm R) : TwoForm R :=
  ⟨a * F.f01,
   a * F.f02,
   a * F.f03,
   a * F.f04,
   a * F.f05,
   a * F.f06,
   a * F.f07,
   a * F.f12,
   a * F.f13,
   a * F.f14,
   a * F.f15,
   a * F.f16,
   a * F.f17,
   a * F.f23,
   a * F.f24,
   a * F.f25,
   a * F.f26,
   a * F.f27,
   a * F.f34,
   a * F.f35,
   a * F.f36,
   a * F.f37,
   a * F.f45,
   a * F.f46,
   a * F.f47,
   a * F.f56,
   a * F.f57,
   a * F.f67⟩

/-- 外積 u ∧ v -/
def wedge (u v : Oct R) : TwoForm R :=
  ⟨u.x0 * v.x1 - u.x1 * v.x0,
   u.x0 * v.x2 - u.x2 * v.x0,
   u.x0 * v.x3 - u.x3 * v.x0,
   u.x0 * v.x4 - u.x4 * v.x0,
   u.x0 * v.x5 - u.x5 * v.x0,
   u.x0 * v.x6 - u.x6 * v.x0,
   u.x0 * v.x7 - u.x7 * v.x0,
   u.x1 * v.x2 - u.x2 * v.x1,
   u.x1 * v.x3 - u.x3 * v.x1,
   u.x1 * v.x4 - u.x4 * v.x1,
   u.x1 * v.x5 - u.x5 * v.x1,
   u.x1 * v.x6 - u.x6 * v.x1,
   u.x1 * v.x7 - u.x7 * v.x1,
   u.x2 * v.x3 - u.x3 * v.x2,
   u.x2 * v.x4 - u.x4 * v.x2,
   u.x2 * v.x5 - u.x5 * v.x2,
   u.x2 * v.x6 - u.x6 * v.x2,
   u.x2 * v.x7 - u.x7 * v.x2,
   u.x3 * v.x4 - u.x4 * v.x3,
   u.x3 * v.x5 - u.x5 * v.x3,
   u.x3 * v.x6 - u.x6 * v.x3,
   u.x3 * v.x7 - u.x7 * v.x3,
   u.x4 * v.x5 - u.x5 * v.x4,
   u.x4 * v.x6 - u.x6 * v.x4,
   u.x4 * v.x7 - u.x7 * v.x4,
   u.x5 * v.x6 - u.x6 * v.x5,
   u.x5 * v.x7 - u.x7 * v.x5,
   u.x6 * v.x7 - u.x7 * v.x6⟩

/-- 2 形式の値 F(u, v) -/
def pair (F : TwoForm R) (u v : Oct R) : R :=
  F.f01 * (u.x0 * v.x1 - u.x1 * v.x0) + F.f02 * (u.x0 * v.x2 - u.x2 * v.x0) + F.f03 * (u.x0 * v.x3 - u.x3 * v.x0) + F.f04 * (u.x0 * v.x4 - u.x4 * v.x0) + F.f05 * (u.x0 * v.x5 - u.x5 * v.x0) + F.f06 * (u.x0 * v.x6 - u.x6 * v.x0) + F.f07 * (u.x0 * v.x7 - u.x7 * v.x0) + F.f12 * (u.x1 * v.x2 - u.x2 * v.x1) + F.f13 * (u.x1 * v.x3 - u.x3 * v.x1) + F.f14 * (u.x1 * v.x4 - u.x4 * v.x1) + F.f15 * (u.x1 * v.x5 - u.x5 * v.x1) + F.f16 * (u.x1 * v.x6 - u.x6 * v.x1) + F.f17 * (u.x1 * v.x7 - u.x7 * v.x1) + F.f23 * (u.x2 * v.x3 - u.x3 * v.x2) + F.f24 * (u.x2 * v.x4 - u.x4 * v.x2) + F.f25 * (u.x2 * v.x5 - u.x5 * v.x2) + F.f26 * (u.x2 * v.x6 - u.x6 * v.x2) + F.f27 * (u.x2 * v.x7 - u.x7 * v.x2) + F.f34 * (u.x3 * v.x4 - u.x4 * v.x3) + F.f35 * (u.x3 * v.x5 - u.x5 * v.x3) + F.f36 * (u.x3 * v.x6 - u.x6 * v.x3) + F.f37 * (u.x3 * v.x7 - u.x7 * v.x3) + F.f45 * (u.x4 * v.x5 - u.x5 * v.x4) + F.f46 * (u.x4 * v.x6 - u.x6 * v.x4) + F.f47 * (u.x4 * v.x7 - u.x7 * v.x4) + F.f56 * (u.x5 * v.x6 - u.x6 * v.x5) + F.f57 * (u.x5 * v.x7 - u.x7 * v.x5) + F.f67 * (u.x6 * v.x7 - u.x7 * v.x6)

/-- 八元数 x の虚部の右からの掛け算がつくる 2 形式 ω_x(u,v) = ⟨u, v·Im x⟩ -/
def rightForm (x : Oct R) : TwoForm R :=
  ⟨-x.x1,
   -x.x2,
   -x.x3,
   -x.x4,
   -x.x5,
   -x.x6,
   -x.x7,
   x.x3,
   -x.x2,
   x.x5,
   -x.x4,
   -x.x7,
   x.x6,
   x.x1,
   x.x6,
   x.x7,
   -x.x4,
   -x.x5,
   x.x7,
   -x.x6,
   x.x5,
   -x.x4,
   x.x1,
   x.x2,
   x.x3,
   -x.x3,
   x.x2,
   -x.x1⟩

/-- F と 7 個の ω_i との内積を並べた虚の八元数 -/
def proj7 (F : TwoForm R) : Oct R :=
  ⟨0,
   -F.f01 + F.f23 + F.f45 - F.f67,
   -F.f02 - F.f13 + F.f46 + F.f57,
   -F.f03 + F.f12 + F.f47 - F.f56,
   -F.f04 - F.f15 - F.f26 - F.f37,
   -F.f05 + F.f14 - F.f27 + F.f36,
   -F.f06 + F.f17 + F.f24 - F.f35,
   -F.f07 - F.f16 + F.f25 + F.f34⟩

theorem T_quadratic (F : TwoForm R) : T (T F) = lin 2 3 (T F) F := by
  ext <;> simp only [T, lin] <;> ring

theorem T_rightForm (x : Oct R) : T (rightForm x) = smul 3 (rightForm x) := by
  ext <;> simp only [T, smul, rightForm] <;> ring

theorem rightForm_spec (x u v : Oct R) :
    inner u (mul v x) = x.x0 * inner u v + pair (rightForm x) u v := by
  simp only [inner, mul, pair, rightForm]
  ring

theorem T_decomp (F : TwoForm R) : T F = lin (-1) 1 F (rightForm (proj7 F)) := by
  ext <;> simp only [T, lin, rightForm, proj7] <;> ring

theorem T_eigen_neg_one (F : TwoForm R) (h : proj7 F = ofScalar 0) : T F = smul (-1) F := by
  rw [T_decomp, h]
  ext <;> simp only [lin, smul, rightForm, ofScalar] <;> ring

theorem proj7_rightForm (x : Oct R) :
    proj7 (rightForm x) = ⟨0, 4 * x.x1, 4 * x.x2, 4 * x.x3, 4 * x.x4, 4 * x.x5, 4 * x.x6, 4 * x.x7⟩ := by
  ext <;> simp only [proj7, rightForm] <;> ring

theorem proj7_T (F : TwoForm R) : proj7 (T F) = Oct8.smul 3 (proj7 F) := by
  ext <;> simp only [proj7, T, Oct8.smul] <;> ring

set_option maxHeartbeats 2000000 in
/-- T は八元数の積からできる Cayley 4 形式である:2 Φ(u,v,w,z) = ⟨u, z(w̄v)⟩ − ⟨u, v(w̄z)⟩ -/
theorem cayley_link (u v w z : Oct R) :
    2 * pair (T (wedge u v)) w z
      = inner u (mul z (mul (conj w) v)) - inner u (mul v (mul (conj w) z)) := by
  simp only [pair, T, wedge, inner, mul, conj]
  ring

end TwoForm

end CFT.Oct8
