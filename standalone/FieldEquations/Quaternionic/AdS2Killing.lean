import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-
# Killing fields of AdS₂ in global coordinates

g = (−dη² + dχ²)/sin²χ. The fields ξ₀ = ∂_η, ξ₁ = sin η cos χ ∂_η + cos η sin χ ∂_χ,
ξ₂ = cos η cos χ ∂_η − sin η sin χ ∂_χ (conformal Killing fields of the flat (η,χ) plane)
satisfy the Killing equations (`killing_xi0`, `killing_xi1`, `killing_xi2`) and the sl(2,ℝ)
relations [ξ₀,ξ₁] = ξ₂, [ξ₀,ξ₂] = −ξ₁, [ξ₁,ξ₂] = −ξ₀ (`comm_*`). The Killing equations and
brackets are stated for the values of the partial derivatives, which are proved separately
(`xi1_*`, `xi2_*`).
-/

open Real

namespace FieldEquations.AdS2Killing

noncomputable def f (χ : ℝ) : ℝ := 1 / (sin χ * sin χ)

noncomputable def fχ (χ : ℝ) : ℝ := -2 * cos χ / sin χ ^ 3

theorem hasDerivAt_f (χ : ℝ) (hχ : sin χ ≠ 0) : HasDerivAt f (fχ χ) χ := by
  have hs := Real.hasDerivAt_sin χ
  have h1 := (hasDerivAt_const χ (1 : ℝ)).div (hs.mul hs) (mul_ne_zero hχ hχ)
  refine h1.congr_deriv ?_
  unfold fχ
  field_simp
  ring

theorem xi1_a_eta (η χ : ℝ) : HasDerivAt (fun y => sin y * cos χ) (cos η * cos χ) η :=
  (Real.hasDerivAt_sin η).mul_const (cos χ)

theorem xi1_a_chi (η χ : ℝ) : HasDerivAt (fun y => sin η * cos y) (sin η * (-sin χ)) χ :=
  (Real.hasDerivAt_cos χ).const_mul (sin η)

theorem xi1_b_eta (η χ : ℝ) : HasDerivAt (fun y => cos y * sin χ) (-sin η * sin χ) η :=
  (Real.hasDerivAt_cos η).mul_const (sin χ)

theorem xi1_b_chi (η χ : ℝ) : HasDerivAt (fun y => cos η * sin y) (cos η * cos χ) χ :=
  (Real.hasDerivAt_sin χ).const_mul (cos η)

theorem xi2_a_eta (η χ : ℝ) : HasDerivAt (fun y => cos y * cos χ) (-sin η * cos χ) η :=
  (Real.hasDerivAt_cos η).mul_const (cos χ)

theorem xi2_a_chi (η χ : ℝ) : HasDerivAt (fun y => cos η * cos y) (cos η * (-sin χ)) χ :=
  (Real.hasDerivAt_cos χ).const_mul (cos η)

theorem xi2_b_eta (η χ : ℝ) : HasDerivAt (fun y => -(sin y * sin χ)) (-(cos η * sin χ)) η :=
  ((Real.hasDerivAt_sin η).mul_const (sin χ)).neg

theorem xi2_b_chi (η χ : ℝ) : HasDerivAt (fun y => -(sin η * sin y)) (-(sin η * cos χ)) χ :=
  ((Real.hasDerivAt_sin χ).const_mul (sin η)).neg

def Killing (χ b aη aχ bη bχ : ℝ) : Prop :=
  b * fχ χ + 2 * f χ * aη = 0 ∧ b * fχ χ + 2 * f χ * bχ = 0 ∧ bη - aχ = 0

theorem killing_xi0 (χ : ℝ) : Killing χ 0 0 0 0 0 := by
  unfold Killing
  refine ⟨by ring, by ring, by ring⟩

/-- ξ₁ is a Killing field of AdS₂. -/
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

theorem comm_01_a (η χ : ℝ) :
    1 * (cos η * cos χ) + 0 * (sin η * (-sin χ)) - (sin η * cos χ) * 0 - (cos η * sin χ) * 0
      = cos η * cos χ := by ring

theorem comm_01_b (η χ : ℝ) :
    1 * (-sin η * sin χ) + 0 * (cos η * cos χ) - (sin η * cos χ) * 0 - (cos η * sin χ) * 0
      = -(sin η * sin χ) := by ring

theorem comm_02_a (η χ : ℝ) :
    1 * (-sin η * cos χ) + 0 * (cos η * (-sin χ)) - (cos η * cos χ) * 0 - (-(sin η * sin χ)) * 0
      = -(sin η * cos χ) := by ring

theorem comm_02_b (η χ : ℝ) :
    1 * (-(cos η * sin χ)) + 0 * (-(sin η * cos χ)) - (cos η * cos χ) * 0
        - (-(sin η * sin χ)) * 0
      = -(cos η * sin χ) := by ring

theorem comm_12_a (η χ : ℝ) :
    (sin η * cos χ) * (-sin η * cos χ) + (cos η * sin χ) * (cos η * (-sin χ))
        - (cos η * cos χ) * (cos η * cos χ) - (-(sin η * sin χ)) * (sin η * (-sin χ))
      = -1 := by
  linear_combination (-(sin χ ^ 2 + cos χ ^ 2)) * Real.sin_sq_add_cos_sq η
    - Real.sin_sq_add_cos_sq χ

theorem comm_12_b (η χ : ℝ) :
    (sin η * cos χ) * (-(cos η * sin χ)) + (cos η * sin χ) * (-(sin η * cos χ))
        - (cos η * cos χ) * (-sin η * sin χ) - (-(sin η * sin χ)) * (cos η * cos χ)
      = 0 := by ring

end FieldEquations.AdS2Killing
