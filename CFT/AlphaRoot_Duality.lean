/-
  根幹の見直し 2:量子球面と相対双曲面は「隣り合う二つの領域」ではなく「一つのものの二つの顔」(2026-11-05)

  v6 の出発点(M₂(ℂ) = ℍ_ℂ の二つの可換な実構造、g_Q = h_ms/(2E²)、χ = gd η)を、滑らかさの観点で定理にする。

  * 運動学(作用なし):
    (1) 一つの複素線形写像 M(z) = z₀ + i(z₁σ₁ + z₂σ₂ + z₃σ₃)(四元数の埋め込み)の行列式は
        複素 2 次形式 z₀² + z₁² + z₂² + z₃²(`det_M`)。
    (2) 実の切り口 z = x(実数):M(x)†M(x) = |x|²·1、つまり SU(2)(の定数倍)= 量子のスピン、
        |x| = 1 で S³(`real_slice_unitary`)。
    (3) 虚の切り口 z₀ = x₀、z_k = −i y_k:M は Hermite 行列 [[x₀ + y₃, y₁ − iy₂], [y₁ + iy₂, x₀ − y₃]]
        で行列式は x₀² − |y|²(Minkowski)。det = 1 の正の部分が質量殻 H³(`imag_slice_hermitian`)。
    (4) 二つの切り口は、回転 z_k ↦ c·z_k(c = e^{−iθ}、θ: 0 → π/2)で滑らかにつながる。
        det = x₀² + c²|x|²(`wick_path`):c = 1 で球、c = −i で双曲面。間で跳ぶところはない。
        曲率 1/R² は R² ↦ −R² で符号が変わる(Cartan の双対:S³ = SU(2) と H³ = SL(2,ℂ)/SU(2))。
    (5) 量子半球 Q = (m/E, p/E) = (sech η, tanh η n̂) は、相対双曲面の「半球模型」そのもの:
        Q は単位球の上(`hemisphere_on_sphere`)、計量は h_ms の Q₀² = (m/E)² 倍(共形、
        `hemisphere_conformal`:動径方向 |dQ/dη|² = sech²η、角度方向 tanh η = sech η · sinh η)。
    (6) 半球の赤道(Q₀ = m/E → 0)は双曲面の無限遠(光的な極限、天球):1/cosh η ≤ 2/(η + 1)
        (`equator_at_infinity`)。
  * 診断:v6 では量子半球と相対双曲面は同じ点の上の二つの計量で、滑らかに(共形に)結ばれていた。
    半球の赤道が双曲面に「出会う」のは有限の接合ではなく、双曲面の無限遠。ダンベルは赤道を首の有限の
    場所に貼ったので、曲率と密度が跳んだ(AlphaRoot_Junction)。
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp

namespace CFT.RootDuality

open Matrix Complex

/-- 四元数の埋め込み M(z) = z₀ + i z·σ -/
def M (z0 z1 z2 z3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z0 + I * z3, I * z1 + z2; I * z1 - z2, z0 - I * z3]

/-- 【根幹 2】det M(z) = z₀² + z₁² + z₂² + z₃²(一つの複素 2 次形式) -/
theorem det_M (z0 z1 z2 z3 : ℂ) : (M z0 z1 z2 z3).det = z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2 := by
  unfold M
  rw [Matrix.det_fin_two_of]
  linear_combination (-(z1 ^ 2 + z3 ^ 2)) * Complex.I_sq

/-- 【根幹 2】実の切り口:M(x)†M(x) = |x|²·1(SU(2) の定数倍、|x| = 1 で S³ = SU(2)) -/
theorem real_slice_unitary (x0 x1 x2 x3 : ℝ) :
    (M x0 x1 x2 x3)ᴴ * M x0 x1 x2 x3
      = ((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff, pow_two] <;>
    (try constructor) <;> ring

/-- 【根幹 2】虚の切り口:z₀ = x₀、z_k = −i y_k で M は Hermite(Minkowski の点)、det = x₀² − |y|² -/
theorem imag_slice_hermitian (x0 y1 y2 y3 : ℝ) :
    M x0 (-I * y1) (-I * y2) (-I * y3) = !![(x0 + y3 : ℂ), y1 - I * y2; y1 + I * y2, x0 - y3] ∧
    (M x0 (-I * y1) (-I * y2) (-I * y3)).det = ((x0 ^ 2 - y1 ^ 2 - y2 ^ 2 - y3 ^ 2 : ℝ) : ℂ) := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [M] <;> ring_nf <;> (try simp [Complex.I_sq]) <;> (try ring)
  · rw [det_M]
    push_cast
    linear_combination ((y1 : ℂ) ^ 2 + (y2 : ℂ) ^ 2 + (y3 : ℂ) ^ 2) * Complex.I_sq

/-- 【根幹 2】回転でつなぐ:z_k = c·x_k なら det = x₀² + c²|x|²。c = 1 で球、c = −i で双曲面 -/
theorem wick_path (x0 x1 x2 x3 : ℝ) (c : ℂ) :
    (M x0 (c * x1) (c * x2) (c * x3)).det = x0 ^ 2 + c ^ 2 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) ∧
    (M x0 x1 x2 x3).det = ((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 : ℝ) : ℂ) ∧
    (M x0 (-I * x1) (-I * x2) (-I * x3)).det = ((x0 ^ 2 - x1 ^ 2 - x2 ^ 2 - x3 ^ 2 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, (imag_slice_hermitian x0 x1 x2 x3).2⟩
  · rw [det_M]; ring
  · rw [det_M]; push_cast; ring

/-- 【根幹 2】曲率の符号:半径 R の球の曲率 1/R² は R² ↦ −R² で −1/R²(双曲面)になる -/
theorem curvature_flip (R : ℝ) (hR : R ≠ 0) : 1 / (-(R ^ 2)) = -(1 / R ^ 2) := by
  rw [div_neg]

/-- 【根幹 2】量子半球は相対双曲面の半球模型:Q = (sech η, tanh η) は単位円(球)の上で Q₀ > 0 -/
theorem hemisphere_on_sphere (η : ℝ) :
    (1 / Real.cosh η) ^ 2 + (Real.sinh η / Real.cosh η) ^ 2 = 1 ∧ 0 < 1 / Real.cosh η := by
  have hc := Real.cosh_pos η
  have h := Real.cosh_sq_sub_sinh_sq η
  constructor
  · field_simp
    linarith
  · positivity

/-- Q₀ = 1/cosh η、Q₁ = sinh η/cosh η の η 微分 -/
theorem hemisphere_deriv (η : ℝ) :
    HasDerivAt (fun e => 1 / Real.cosh e) (-(Real.sinh η) / Real.cosh η ^ 2) η ∧
    HasDerivAt (fun e => Real.sinh e / Real.cosh e) (1 / Real.cosh η ^ 2) η := by
  have hc := (Real.cosh_pos η).ne'
  constructor
  · have h := (hasDerivAt_const η (1 : ℝ)).div (Real.hasDerivAt_cosh η) hc
    convert h using 1; ring
  · have h := (Real.hasDerivAt_sinh η).div (Real.hasDerivAt_cosh η) hc
    convert h using 1
    have h2 := Real.cosh_sq_sub_sinh_sq η
    field_simp
    nlinarith [h2]

/-- 【根幹 2】共形:|dQ/dη|² = sech²η = Q₀²·(双曲面の動径の速さ 1)、角度方向 tanh η = Q₀·sinh η。
したがって半球の計量 = Q₀² × 双曲面の計量(Q₀ = m/E) -/
theorem hemisphere_conformal (η : ℝ) :
    (-(Real.sinh η) / Real.cosh η ^ 2) ^ 2 + (1 / Real.cosh η ^ 2) ^ 2 = (1 / Real.cosh η) ^ 2 * 1 ∧
    Real.sinh η / Real.cosh η = (1 / Real.cosh η) * Real.sinh η := by
  have hc := (Real.cosh_pos η).ne'
  have h := Real.cosh_sq_sub_sinh_sq η
  have e : Real.sinh η ^ 2 = Real.cosh η ^ 2 - 1 := by linarith
  constructor
  · rw [div_pow, neg_sq, e]
    field_simp <;> ring
  · ring

/-- 【根幹 2】半球の赤道は双曲面の無限遠:Q₀ = 1/cosh η ≤ 2/(η + 1)(η ≥ 0)で、η → ∞ で 0 -/
theorem equator_at_infinity (η : ℝ) (hη : 0 ≤ η) : 1 / Real.cosh η ≤ 2 / (η + 1) := by
  have h1 : η + 1 ≤ Real.exp η := Real.add_one_le_exp η
  have h2 : Real.exp η / 2 ≤ Real.cosh η := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-η)
    linarith
  have hpos : 0 < (η + 1) / 2 := by linarith
  have h3 : (η + 1) / 2 ≤ Real.cosh η := by linarith
  calc 1 / Real.cosh η ≤ 1 / ((η + 1) / 2) := one_div_le_one_div_of_le hpos h3
    _ = 2 / (η + 1) := by rw [one_div_div]

end CFT.RootDuality
