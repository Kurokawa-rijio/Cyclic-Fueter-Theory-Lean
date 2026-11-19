/-
  剛性定理の 3 つの共形キリング場は、喉(Bertotti–Robinson の AdS₂ 部分)の等長変換である(2026-11-14、命題 Q11)

  Einstein 静的宇宙の (η, χ) 平面で
    ξ₀ = ∂_η、 ξ₁ = sin η cos χ ∂_η + cos η sin χ ∂_χ、 ξ₂ = cos η cos χ ∂_η − sin η sin χ ∂_χ。
  喉の AdS₂ 部分の計量は g = f(χ)(−dη² + dχ²)、f = 1/sin²χ(ℓ = 1)。
  ξ = a ∂_η + b ∂_χ に対する Killing 方程式 L_ξ g = 0 は
    b f′ + 2 f ∂_η a = 0、 b f′ + 2 f ∂_χ b = 0、 ∂_η b − ∂_χ a = 0。
  * `hasDerivAt_f`:f′ = −2 cos χ / sin³χ。
  * `xi1_*`、`xi2_*`:成分の偏微分(HasDerivAt)。
  * `killing_xi0`、`killing_xi1`、`killing_xi2`:3 つとも Killing 方程式をみたす。
    `Killing` は偏微分の値を引数に取る代数の式で、その値が実際の偏微分であることは `xi1_*`、`xi2_*` が別に示す
    (2 つを 1 本の定理にまとめてはいない)。
  * `comm_01_*`、`comm_02_*`、`comm_12_*`:[ξ₀, ξ₁] = ξ₂、[ξ₀, ξ₂] = −ξ₁、[ξ₁, ξ₂] = −ξ₀(sl(2,ℝ))。
    これも偏微分の値を代入した恒等式。
  解釈(未形式化):Tolman 宇宙の線形摂動として残る 3 つのゲージの向きは、喉の対称性 sl(2,ℝ) と同じである。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

open Real

namespace CFT.ThroatSymmetry

/-- 喉の AdS₂ 部分の共形因子の 2 乗(ℓ = 1) -/
noncomputable def f (χ : ℝ) : ℝ := 1 / (sin χ * sin χ)

/-- f の微分 -/
noncomputable def fχ (χ : ℝ) : ℝ := -2 * cos χ / sin χ ^ 3

theorem hasDerivAt_f (χ : ℝ) (hχ : sin χ ≠ 0) : HasDerivAt f (fχ χ) χ := by
  have hs := Real.hasDerivAt_sin χ
  have h1 := (hasDerivAt_const χ (1 : ℝ)).div (hs.mul hs) (mul_ne_zero hχ hχ)
  refine h1.congr_deriv ?_
  unfold fχ
  field_simp
  ring

/-! ξ₁ = sin η cos χ ∂_η + cos η sin χ ∂_χ の成分の偏微分 -/

theorem xi1_a_eta (η χ : ℝ) : HasDerivAt (fun y => sin y * cos χ) (cos η * cos χ) η :=
  (Real.hasDerivAt_sin η).mul_const (cos χ)

theorem xi1_a_chi (η χ : ℝ) : HasDerivAt (fun y => sin η * cos y) (sin η * (-sin χ)) χ :=
  (Real.hasDerivAt_cos χ).const_mul (sin η)

theorem xi1_b_eta (η χ : ℝ) : HasDerivAt (fun y => cos y * sin χ) (-sin η * sin χ) η :=
  (Real.hasDerivAt_cos η).mul_const (sin χ)

theorem xi1_b_chi (η χ : ℝ) : HasDerivAt (fun y => cos η * sin y) (cos η * cos χ) χ :=
  (Real.hasDerivAt_sin χ).const_mul (cos η)

/-! ξ₂ = cos η cos χ ∂_η − sin η sin χ ∂_χ の成分の偏微分 -/

theorem xi2_a_eta (η χ : ℝ) : HasDerivAt (fun y => cos y * cos χ) (-sin η * cos χ) η :=
  (Real.hasDerivAt_cos η).mul_const (cos χ)

theorem xi2_a_chi (η χ : ℝ) : HasDerivAt (fun y => cos η * cos y) (cos η * (-sin χ)) χ :=
  (Real.hasDerivAt_cos χ).const_mul (cos η)

theorem xi2_b_eta (η χ : ℝ) : HasDerivAt (fun y => -(sin y * sin χ)) (-(cos η * sin χ)) η :=
  ((Real.hasDerivAt_sin η).mul_const (sin χ)).neg

theorem xi2_b_chi (η χ : ℝ) : HasDerivAt (fun y => -(sin η * sin y)) (-(sin η * cos χ)) χ :=
  ((Real.hasDerivAt_sin χ).const_mul (sin η)).neg

/-- g = f(χ)(−dη² + dχ²) に対する Killing 方程式。ξ = a ∂_η + b ∂_χ、aη = ∂_η a などは偏微分の値 -/
def Killing (χ b aη aχ bη bχ : ℝ) : Prop :=
  b * fχ χ + 2 * f χ * aη = 0 ∧ b * fχ χ + 2 * f χ * bχ = 0 ∧ bη - aχ = 0

/-- ξ₀ = ∂_η(a = 1、b = 0) -/
theorem killing_xi0 (χ : ℝ) : Killing χ 0 0 0 0 0 := by
  unfold Killing
  refine ⟨by ring, by ring, by ring⟩

theorem killing_xi1 (η χ : ℝ) (hχ : sin χ ≠ 0) :
    Killing χ (cos η * sin χ) (cos η * cos χ) (sin η * (-sin χ)) (-sin η * sin χ)
      (cos η * cos χ) := by
  unfold Killing f fχ
  refine ⟨?_, ?_, by ring⟩
  · field_simp
    ring
  · field_simp
    ring

theorem killing_xi2 (η χ : ℝ) (hχ : sin χ ≠ 0) :
    Killing χ (-(sin η * sin χ)) (-sin η * cos χ) (cos η * (-sin χ)) (-(cos η * sin χ))
      (-(sin η * cos χ)) := by
  unfold Killing f fχ
  refine ⟨?_, ?_, by ring⟩
  · field_simp
    ring
  · field_simp
    ring

/-! 交換関係。[X, Y] の成分は X(Y の成分) − Y(X の成分) -/

/-- [ξ₀, ξ₁] の η 成分 = ξ₂ の η 成分 -/
theorem comm_01_a (η χ : ℝ) :
    1 * (cos η * cos χ) + 0 * (sin η * (-sin χ)) - (sin η * cos χ) * 0 - (cos η * sin χ) * 0
      = cos η * cos χ := by ring

/-- [ξ₀, ξ₁] の χ 成分 = ξ₂ の χ 成分 -/
theorem comm_01_b (η χ : ℝ) :
    1 * (-sin η * sin χ) + 0 * (cos η * cos χ) - (sin η * cos χ) * 0 - (cos η * sin χ) * 0
      = -(sin η * sin χ) := by ring

/-- [ξ₀, ξ₂] の η 成分 = −(ξ₁ の η 成分) -/
theorem comm_02_a (η χ : ℝ) :
    1 * (-sin η * cos χ) + 0 * (cos η * (-sin χ)) - (cos η * cos χ) * 0 - (-(sin η * sin χ)) * 0
      = -(sin η * cos χ) := by ring

/-- [ξ₀, ξ₂] の χ 成分 = −(ξ₁ の χ 成分) -/
theorem comm_02_b (η χ : ℝ) :
    1 * (-(cos η * sin χ)) + 0 * (-(sin η * cos χ)) - (cos η * cos χ) * 0
        - (-(sin η * sin χ)) * 0
      = -(cos η * sin χ) := by ring

/-- [ξ₁, ξ₂] の η 成分 = −1 = −(ξ₀ の η 成分) -/
theorem comm_12_a (η χ : ℝ) :
    (sin η * cos χ) * (-sin η * cos χ) + (cos η * sin χ) * (cos η * (-sin χ))
        - (cos η * cos χ) * (cos η * cos χ) - (-(sin η * sin χ)) * (sin η * (-sin χ))
      = -1 := by
  linear_combination (-(sin χ ^ 2 + cos χ ^ 2)) * Real.sin_sq_add_cos_sq η
    - Real.sin_sq_add_cos_sq χ

/-- [ξ₁, ξ₂] の χ 成分 = 0 = −(ξ₀ の χ 成分) -/
theorem comm_12_b (η χ : ℝ) :
    (sin η * cos χ) * (-(cos η * sin χ)) + (cos η * sin χ) * (-(sin η * cos χ))
        - (cos η * cos χ) * (-sin η * sin χ) - (-(sin η * sin χ)) * (cos η * cos χ)
      = 0 := by ring

end CFT.ThroatSymmetry
