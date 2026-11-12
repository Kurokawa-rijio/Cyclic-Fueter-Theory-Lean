/-
  ダンベルの形(続き):W = r′ は仮定ではなく等号の場合(2026-11-12)

  時間対称な切り口で、ハミルトン拘束を Misner–Sharp の質量 m = (r/2)(1 − r′²) で書くと
  m′ = r′ℓ²(W′² + (1 − W²)²/(2r²))(`ds2_mass_prime`)。
  共形平坦(2mr = ℓ²(1 − W²)²)を切り口に沿って微分して拘束と合わせると
  r r′ W′² + 2WW′(1 − W²) + (1 − W²)² r′/r = 0。
  `ds2_bogomolny`:これに r′ をかけると平方の完成
  ((r r′ W′ + W(1 − W²))² + (1 − W²)²(r′² − W²))/r になる。
  `ds2_W_ge`:したがって W² ≠ 1 なら r′² ≤ W²。
  `ds2_saturated`:等号 W² = r′²(スピン接続型)のとき r r′ W′ = −W(1 − W²)(1 階の方程式)。
  `ds2_friedmann`:時間の方向の拘束 Ω² + Ω_η² = ℓ² は、空間の方向の r² + ℓ²r′² = ℓ² と同じ形。
  `ds2_neck_action`:首のユークリッド作用の体積の項は (1/(8πGℓ²))·4πℓ²·A = A/(2G)(A は 2 次元の部分の面積)。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

namespace CFT.DS

theorem ds2_mass_prime (r r' r'' W W' l : ℝ)
    (hH : -4 * r * r'' + 2 * (1 - r' ^ 2) = 4 * l ^ 2 * (W' ^ 2 + (1 - W ^ 2) ^ 2 / (2 * r ^ 2))) :
    r' * (1 - r' ^ 2) / 2 - r * r' * r'' = r' * l ^ 2 * (W' ^ 2 + (1 - W ^ 2) ^ 2 / (2 * r ^ 2)) := by
  linear_combination (r' / 4) * hH

theorem ds2_bogomolny (r r' W W' : ℝ) (hr : r ≠ 0) :
    r' * (r * r' * W' ^ 2 + 2 * W * W' * (1 - W ^ 2) + (1 - W ^ 2) ^ 2 * r' / r)
      = ((r * r' * W' + W * (1 - W ^ 2)) ^ 2 + (1 - W ^ 2) ^ 2 * (r' ^ 2 - W ^ 2)) / r := by
  field_simp
  ring

theorem ds2_num (r r' W W' : ℝ) (hr : r ≠ 0)
    (hQ : r * r' * W' ^ 2 + 2 * W * W' * (1 - W ^ 2) + (1 - W ^ 2) ^ 2 * r' / r = 0) :
    (r * r' * W' + W * (1 - W ^ 2)) ^ 2 + (1 - W ^ 2) ^ 2 * (r' ^ 2 - W ^ 2) = 0 := by
  have hb := ds2_bogomolny r r' W W' hr
  rw [hQ, mul_zero] at hb
  rcases div_eq_zero_iff.mp hb.symm with h | h
  · exact h
  · exact absurd h hr

theorem ds2_W_ge (r r' W W' : ℝ) (hr : r ≠ 0) (hW : 1 - W ^ 2 ≠ 0)
    (hQ : r * r' * W' ^ 2 + 2 * W * W' * (1 - W ^ 2) + (1 - W ^ 2) ^ 2 * r' / r = 0) :
    r' ^ 2 ≤ W ^ 2 := by
  have hnum := ds2_num r r' W W' hr hQ
  have hpos : 0 < (1 - W ^ 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hW))
  by_contra hlt
  push_neg at hlt
  have hp := mul_pos hpos (sub_pos.mpr hlt)
  linarith [sq_nonneg (r * r' * W' + W * (1 - W ^ 2))]

theorem ds2_saturated (r r' W W' : ℝ) (hr : r ≠ 0) (hE : W ^ 2 = r' ^ 2)
    (hQ : r * r' * W' ^ 2 + 2 * W * W' * (1 - W ^ 2) + (1 - W ^ 2) ^ 2 * r' / r = 0) :
    r * r' * W' + W * (1 - W ^ 2) = 0 := by
  have hnum := ds2_num r r' W W' hr hQ
  have h0 : (r * r' * W' + W * (1 - W ^ 2)) ^ 2 = 0 := by
    linear_combination hnum + (1 - W ^ 2) ^ 2 * hE
  exact (pow_eq_zero_iff two_ne_zero).mp h0

theorem ds2_friedmann (l η : ℝ) : (l * cos η) ^ 2 + (-(l * sin η)) ^ 2 = l ^ 2 := by
  linear_combination l ^ 2 * sin_sq_add_cos_sq η

theorem ds2_neck_action (G l A : ℝ) (hG : G ≠ 0) (hl : l ≠ 0) :
    1 / (8 * π * G * l ^ 2) * (4 * π * l ^ 2) * A = A / (2 * G) := by
  have hp := Real.pi_ne_zero
  field_simp <;> ring

end CFT.DS
