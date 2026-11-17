/-
  6-1 シュワルツシルト温度の導出（`BlackHoleThermodynamics.lean` の IX.21 の当てはめ）

  * 一般の地平線では `horizon_polar`・`conical_period` が既に証明済み：
    f ≈ f₁x のとき円錐特異点がない ⇔ β = 4π/f₁、T = f₁/(4π)。
  * このモジュールはシュワルツシルト計量 f = 1 − 2M/r への当てはめ：
    地平線 r_h = 2M での傾き f′(2M) = 1/(2M)（`schwarzschild_slope`）、
    したがって β = 4π/f₁ = 8πM（`schwarzschild_period`）、T = 1/(8πM)
    （`schwarzschild_temperature`）。定数は sympy による明示計算でも照合済み。
  * 極限の場合（T = 0）は `extremal_cold` が既に扱っている。
-/
import CFT.Quantum.BlackHoleThermodynamics

namespace CFT.Thermo

open Real

/-- シュワルツシルト計量 f = 1 − 2M/r の地平線 r = 2M での傾きは 1/(2M)。 -/
theorem schwarzschild_slope (M : ℝ) (hM : 0 < M) :
    HasDerivAt (fun r => 1 - 2 * M / r) (1 / (2 * M)) (2 * M) := by
  have h2M : (2 * M) ≠ 0 := by positivity
  have hmul := (hasDerivAt_inv h2M).const_mul (2 * M)
  have hsub := (hasDerivAt_const (2 * M) (1 : ℝ)).sub hmul
  have heq : (fun r => 1 - 2 * M / r) = (fun r => 1 - 2 * M * r⁻¹) := by
    funext r; rw [div_eq_mul_inv]
  rw [heq]
  convert hsub using 1
  field_simp
  ring

/-- シュワルツシルトの逆温度：β = 4π/f₁ = 8πM（`conical_period` に f₁ = 1/(2M) を代入）。 -/
theorem schwarzschild_period (M β : ℝ) (hM : 0 < M) :
    (1 / (2 * M)) / 2 * β = 2 * π ↔ β = 8 * π * M := by
  have h := conical_period (1 / (2 * M)) β (by positivity)
  rw [show 4 * π / (1 / (2 * M)) = 8 * π * M by field_simp; ring] at h
  exact h

/-- シュワルツシルトのホーキング温度：T = f₁/(4π) = 1/(8πM)。 -/
theorem schwarzschild_temperature (M : ℝ) (hM : 0 < M) :
    (1 / (2 * M)) / (4 * π) = 1 / (8 * π * M) := by
  have hM' : M ≠ 0 := ne_of_gt hM
  field_simp
  ring

/-- まとめ：シュワルツシルトでは円錐条件が β = 8πM を与え、温度は T = 1/(8πM)。 -/
theorem schwarzschild_hawking (M : ℝ) (hM : 0 < M) :
    (1 / (2 * M)) / 2 * (8 * π * M) = 2 * π ∧
    (1 / (2 * M)) / (4 * π) = 1 / (8 * π * M) := by
  refine ⟨?_, schwarzschild_temperature M hM⟩
  have hM' : M ≠ 0 := ne_of_gt hM
  field_simp
  ring

end CFT.Thermo
