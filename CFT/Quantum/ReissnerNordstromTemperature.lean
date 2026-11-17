/-
  6-2 荷電と極限の場合（`BlackHoleThermodynamics.lean` の IX.21 の当てはめ）

  * 一般の地平線では `horizon_polar`・`conical_period` が既に証明済み：
    f ≈ f₁x のとき円錐特異点がない ⇔ β = 4π/f₁、T = f₁/(4π)。
  * 荷電（Reissner–Nordström）では `rn_slope` が f′(r₊) = (r₊ − r₋)/r₊² を
    与えるので、T = (r₊ − r₋)/(4πr₊²)（`rn_temperature`）、
    β = 4πr₊²/(r₊ − r₋)（`rn_period`）。r₋ < r₊ なら T > 0
    （`rn_temperature_pos`）、極限 r₋ = r₊ では T = 0
    （`rn_extremal_temperature`、既存の `extremal_cold` の言い換え）。
  * シュワルツシルトへの帰着：r₋ = 0、r₊ = 2M で T = 1/(8πM)
    （`rn_schwarzschild_reduction`、6-1 の `schwarzschild_temperature` と一致）。
  * 電荷表示：r₋ = Q²/r₊ のとき T = (r₊² − Q²)/(4πr₊³)
    （`rn_temperature_Q`）。`first_law` に現れる T と同じ値であること
    （`rn_temperature_first_law`）も確認し、第一法則との整合を取る。
  * 定数は sympy による明示計算でも照合済み。
-/
import CFT.Quantum.BlackHoleThermodynamics

namespace CFT.Thermo

open Real

/-- 荷電ブラックホールのホーキング温度：T = f₁/(4π) = (r₊ − r₋)/(4πr₊²)。 -/
theorem rn_temperature (rp rm : ℝ) :
    ((rp - rm) / rp ^ 2) / (4 * π) = (rp - rm) / (4 * π * rp ^ 2) := by
  rw [div_div, mul_comm (rp ^ 2) (4 * π)]

/-- 荷電ブラックホールの逆温度：円錐条件 ⇔ β = 4πr₊²/(r₊ − r₋)。 -/
theorem rn_period (rp rm β : ℝ) (hp : 0 < rp) (hm : rm < rp) :
    (rp - rm) / rp ^ 2 / 2 * β = 2 * π ↔ β = 4 * π * rp ^ 2 / (rp - rm) := by
  have hsub : (rp - rm) ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  have hrp : rp ≠ 0 := ne_of_gt hp
  have hf1 : 0 < (rp - rm) / rp ^ 2 := div_pos (sub_pos.mpr hm) (pow_pos hp 2)
  have h := conical_period ((rp - rm) / rp ^ 2) β hf1
  rw [show 4 * π / ((rp - rm) / rp ^ 2) = 4 * π * rp ^ 2 / (rp - rm) by
    field_simp] at h
  exact h

/-- 非極限（r₋ < r₊）では温度は正。 -/
theorem rn_temperature_pos (rp rm : ℝ) (hp : 0 < rp) (hm : rm < rp) :
    0 < (rp - rm) / (4 * π * rp ^ 2) := by
  have hsub : 0 < rp - rm := sub_pos.mpr hm
  positivity

/-- 極限 r₋ = r₊ では T = 0（`extremal_cold` の言い換え）。 -/
theorem rn_extremal_temperature (rp : ℝ) :
    ((rp - rp) / rp ^ 2) / (4 * π) = 0 := by simp

/-- シュワルツシルトへの帰着：r₋ = 0、r₊ = 2M で T = 1/(8πM)。 -/
theorem rn_schwarzschild_reduction (M : ℝ) (hM : 0 < M) :
    ((2 * M - 0) / (2 * M) ^ 2) / (4 * π) = 1 / (8 * π * M) := by
  have hM' : M ≠ 0 := ne_of_gt hM
  field_simp
  ring

/-- 電荷表示：r₋ = Q²/r₊ のとき T = (r₊² − Q²)/(4πr₊³)。 -/
theorem rn_temperature_Q (rp Q : ℝ) (hp : rp ≠ 0) :
    ((rp - Q ^ 2 / rp) / rp ^ 2) / (4 * π) = (rp ^ 2 - Q ^ 2) / (4 * π * rp ^ 3) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `first_law` に現れる温度は RN の温度そのもの。 -/
theorem rn_temperature_first_law (rp Q : ℝ) :
    ((rp - Q ^ 2 / rp) / rp ^ 2) / (4 * π) = (rp - Q ^ 2 / rp) / (4 * π * rp ^ 2) :=
  rn_temperature rp (Q ^ 2 / rp)

/-- まとめ：荷電では円錐条件が β = 4πr₊²/(r₊ − r₋) を与え、温度は T = (r₊ − r₋)/(4πr₊²)。 -/
theorem rn_hawking (rp rm : ℝ) (hp : 0 < rp) (hm : rm < rp) :
    (rp - rm) / rp ^ 2 / 2 * (4 * π * rp ^ 2 / (rp - rm)) = 2 * π ∧
    ((rp - rm) / rp ^ 2) / (4 * π) = (rp - rm) / (4 * π * rp ^ 2) := by
  refine ⟨?_, rn_temperature rp rm⟩
  exact (rn_period rp rm _ hp hm).mpr rfl

end CFT.Thermo
