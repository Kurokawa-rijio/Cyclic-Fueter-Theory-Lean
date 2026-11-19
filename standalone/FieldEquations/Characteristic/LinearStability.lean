import FieldEquations.Characteristic.Dependence

/-
# Stability estimate for linear characteristic systems

For a linear system d_{uv} = Σ_j (c₀ d_j + c₁ ∂_u d_j + c₂ ∂_v d_j) with bounded coefficients
(|c| ≤ M), `linear_stability` gives the Grönwall-type bound
  Σ (|d| + |d_u| + |d_v|) ≤ 6nE e^{4 max(n(1+M),1)(u+v)}
in terms of the edge size E of the data.
-/

open Real Set
open FieldEquations.CharacteristicUniqueness FieldEquations.CharacteristicDependence

namespace FieldEquations.LinearStability

theorem linear_rhs_bound {n : ℕ} {M : ℝ} (hM : 0 ≤ M) (c : Fin n → Fin 3 → ℝ)
    (hc : ∀ j k, |c j k| ≤ M) (x y z : Fin n → ℝ) :
    |∑ j, (c j 0 * x j + c j 1 * y j + c j 2 * z j)| ≤ M * ∑ j, (|x j| + |y j| + |z j|) := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have h0 : |c j 0 * x j| ≤ M * |x j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc j 0) (abs_nonneg _)
  have h1 : |c j 1 * y j| ≤ M * |y j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc j 1) (abs_nonneg _)
  have h2 : |c j 2 * z j| ≤ M * |z j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc j 2) (abs_nonneg _)
  calc |c j 0 * x j + c j 1 * y j + c j 2 * z j|
      ≤ |c j 0 * x j + c j 1 * y j| + |c j 2 * z j| := abs_add _ _
    _ ≤ |c j 0 * x j| + |c j 1 * y j| + |c j 2 * z j| := by
        linarith [abs_add (c j 0 * x j) (c j 1 * y j)]
    _ ≤ M * (|x j| + |y j| + |z j|) := by linarith

/-- Grönwall-type stability bound for linear characteristic systems with bounded coefficients. -/
theorem linear_stability {n : ℕ} {a b M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (d du dv duv : Fin n → ℝ → ℝ → ℝ)
    (hC : ∀ i, C2Data a b (d i) (du i) (dv i) (duv i))
    (c : Fin n → Fin n → Fin 3 → ℝ → ℝ → ℝ)
    (hc : ∀ i j k, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, |c i j k u v| ≤ M)
    (heq : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      duv i u v = ∑ j, (c i j 0 u v * d j u v + c i j 1 u v * du j u v + c i j 2 u v * dv j u v))
    (hE1 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, |d i u 0| ≤ E)
    (hE2 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, |du i u 0| ≤ E)
    (hE3 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, |dv i 0 v| ≤ E) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      ∑ j, (|d j u v| + |du j u v| + |dv j u v|)
        ≤ 2 * (3 * n * E) * exp ((4 * max (n * (1 + M)) 1) * (u + v)) :=
  char_dependence hM hE d du dv duv hC hE1 hE2 hE3 (fun i u hu v hv => by
    rw [heq i u hu v hv]
    exact linear_rhs_bound hM (fun j k => c i j k u v) (fun j k => hc i j k u hu v hv)
      (fun j => d j u v) (fun j => du j u v) (fun j => dv j u v))

end FieldEquations.LinearStability
