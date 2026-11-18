/-
  八元数 𝕆 を成分 8 個の構造体として定義し、基本の恒等式を示す(2026-11-14、命題 O0)

  積は Cayley–Dickson 構成 (a,b)(c,d) = (ac − d̄b, da + bc̄)(a, b, c, d は四元数)を成分で書いたもの。
  係数環 R は任意の可換環(ℝ でも ℂ でもよい)。
  * `normSq_mul`:ノルムの乗法性 |xy|² = |x|²|y|²(8 平方恒等式)。
  * `left_alt`、`right_alt`、`flexible`:交代律 (xx)y = x(xy)、(yx)x = y(xx) と柔軟律 (xy)x = x(yx)。
  * `moufang_left`、`moufang_right`、`moufang_middle`:Moufang 恒等式。
  * `conj_mul`:(xy)‾ = ȳ x̄。`mul_conj`、`conj_mul_self`:x x̄ = x̄ x = |x|²。
  * `inner_mul_left`、`inner_mul_right`:⟨xy, xz⟩ = |x|²⟨y, z⟩、⟨yx, zx⟩ = |x|²⟨y, z⟩(合成代数)。
  * `not_assoc`:(e₁e₂)e₄ ≠ e₁(e₂e₄)(結合律は成り立たない)。
  * `null_example`:複素係数では 1 + i e₁ はゼロでないのに長さゼロ(|x|² = 0)。
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CFT.Oct8

/-- 八元数(成分 8 個)。x0 が実部、x1..x7 が虚部 -/
@[ext] structure Oct (R : Type*) where
  x0 : R
  x1 : R
  x2 : R
  x3 : R
  x4 : R
  x5 : R
  x6 : R
  x7 : R

variable {R : Type*} [CommRing R]

/-- 八元数の積(Cayley–Dickson 構成) -/
def mul (x y : Oct R) : Oct R :=
  ⟨x.x0 * y.x0 - x.x1 * y.x1 - x.x2 * y.x2 - x.x3 * y.x3 - x.x4 * y.x4 - x.x5 * y.x5 - x.x6 * y.x6 - x.x7 * y.x7,
   x.x0 * y.x1 + x.x1 * y.x0 + x.x2 * y.x3 - x.x3 * y.x2 + x.x4 * y.x5 - x.x5 * y.x4 - x.x6 * y.x7 + x.x7 * y.x6,
   x.x0 * y.x2 - x.x1 * y.x3 + x.x2 * y.x0 + x.x3 * y.x1 + x.x4 * y.x6 + x.x5 * y.x7 - x.x6 * y.x4 - x.x7 * y.x5,
   x.x0 * y.x3 + x.x1 * y.x2 - x.x2 * y.x1 + x.x3 * y.x0 + x.x4 * y.x7 - x.x5 * y.x6 + x.x6 * y.x5 - x.x7 * y.x4,
   x.x0 * y.x4 - x.x1 * y.x5 - x.x2 * y.x6 - x.x3 * y.x7 + x.x4 * y.x0 + x.x5 * y.x1 + x.x6 * y.x2 + x.x7 * y.x3,
   x.x0 * y.x5 + x.x1 * y.x4 - x.x2 * y.x7 + x.x3 * y.x6 - x.x4 * y.x1 + x.x5 * y.x0 - x.x6 * y.x3 + x.x7 * y.x2,
   x.x0 * y.x6 + x.x1 * y.x7 + x.x2 * y.x4 - x.x3 * y.x5 - x.x4 * y.x2 + x.x5 * y.x3 + x.x6 * y.x0 - x.x7 * y.x1,
   x.x0 * y.x7 - x.x1 * y.x6 + x.x2 * y.x5 + x.x3 * y.x4 - x.x4 * y.x3 - x.x5 * y.x2 + x.x6 * y.x1 + x.x7 * y.x0⟩

/-- 共役 -/
def conj (x : Oct R) : Oct R := ⟨x.x0, -x.x1, -x.x2, -x.x3, -x.x4, -x.x5, -x.x6, -x.x7⟩

/-- ノルムの 2 乗 -/
def normSq (x : Oct R) : R :=
  x.x0 * x.x0 + x.x1 * x.x1 + x.x2 * x.x2 + x.x3 * x.x3 + x.x4 * x.x4 + x.x5 * x.x5 + x.x6 * x.x6 + x.x7 * x.x7

/-- 内積 -/
def inner (x y : Oct R) : R :=
  x.x0 * y.x0 + x.x1 * y.x1 + x.x2 * y.x2 + x.x3 * y.x3 + x.x4 * y.x4 + x.x5 * y.x5 + x.x6 * y.x6 + x.x7 * y.x7

/-- スカラーの埋め込み -/
def ofScalar (r : R) : Oct R := ⟨r, 0, 0, 0, 0, 0, 0, 0⟩

/-- スカラー倍 -/
def smul (r : R) (x : Oct R) : Oct R :=
  ⟨r * x.x0, r * x.x1, r * x.x2, r * x.x3, r * x.x4, r * x.x5, r * x.x6, r * x.x7⟩

theorem normSq_mul (x y : Oct R) : normSq (mul x y) = normSq x * normSq y := by
  simp only [normSq, mul]
  ring

theorem left_alt (x y : Oct R) : mul (mul x x) y = mul x (mul x y) := by
  ext <;> simp only [mul] <;> ring

theorem right_alt (x y : Oct R) : mul (mul y x) x = mul y (mul x x) := by
  ext <;> simp only [mul] <;> ring

theorem flexible (x y : Oct R) : mul (mul x y) x = mul x (mul y x) := by
  ext <;> simp only [mul] <;> ring

set_option maxHeartbeats 1000000 in
theorem moufang_left (x y z : Oct R) : mul z (mul x (mul z y)) = mul (mul (mul z x) z) y := by
  ext <;> simp only [mul] <;> ring

set_option maxHeartbeats 1000000 in
theorem moufang_right (x y z : Oct R) : mul x (mul z (mul y z)) = mul (mul (mul x z) y) z := by
  ext <;> simp only [mul] <;> ring

set_option maxHeartbeats 1000000 in
theorem moufang_middle (x y z : Oct R) : mul (mul z x) (mul y z) = mul (mul z (mul x y)) z := by
  ext <;> simp only [mul] <;> ring

theorem conj_mul (x y : Oct R) : conj (mul x y) = mul (conj y) (conj x) := by
  ext <;> simp only [mul, conj] <;> ring

theorem mul_conj (x : Oct R) : mul x (conj x) = ofScalar (normSq x) := by
  ext <;> simp only [mul, conj, ofScalar, normSq] <;> ring

theorem conj_mul_self (x : Oct R) : mul (conj x) x = ofScalar (normSq x) := by
  ext <;> simp only [mul, conj, ofScalar, normSq] <;> ring

theorem inner_mul_left (x y z : Oct R) : inner (mul x y) (mul x z) = normSq x * inner y z := by
  simp only [inner, normSq, mul]
  ring

theorem inner_mul_right (x y z : Oct R) : inner (mul y x) (mul z x) = normSq x * inner y z := by
  simp only [inner, normSq, mul]
  ring

/-- 虚数単位 e₁, e₂, e₄ -/
def e1 : Oct R := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩
def e2 : Oct R := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
def e4 : Oct R := ⟨0, 0, 0, 0, 1, 0, 0, 0⟩

/-- 結合律は成り立たない:(e₁e₂)e₄ と e₁(e₂e₄) は符号が逆 -/
theorem not_assoc : mul (mul (e1 : Oct ℝ) e2) e4 ≠ mul e1 (mul e2 e4) := by
  intro h
  have h7 := congrArg Oct.x7 h
  simp only [mul, e1, e2, e4] at h7
  norm_num at h7

/-- 複素係数では、ゼロでないのに長さゼロの元がある:1 + i e₁ -/
theorem null_example :
    normSq (⟨1, Complex.I, 0, 0, 0, 0, 0, 0⟩ : Oct ℂ) = 0 := by
  simp only [normSq]
  linear_combination Complex.I_mul_I

end CFT.Oct8
