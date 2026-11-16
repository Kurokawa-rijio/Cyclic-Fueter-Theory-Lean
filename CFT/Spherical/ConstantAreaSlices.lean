/-
  垂直に切った断面積がどこでも一定(r(x) = r₀)という条件だけを課した初期データ(2026-11-12)

  時間対称な切り口のハミルトン拘束 −4r r″ + 2(1 − r′²) = 4ℓ²(W′² + (1 − W²)²/(2r²)) に r′ = 0、r″ = 0 を入れる。
  * `ca_constraint`:W′² = (1 − ℓ²(1 − W²)²/r²)/(2ℓ²)。面積が一定でも W は軸に沿って変われる(変わり方は決まる)。
  * `ca_turning`:W² = 1 + r₀/ℓ で W′ = 0(折り返し)。半径 r₀ ごとに W の振れ幅が決まる。
  * `ca_neck_fixed`:r₀ = ℓ では W′² = W²(2 − W²)/(2ℓ²)。W = 0(首)が不動点。
  * `ca_soliton_deriv`、`ca_soliton`:r₀ = ℓ では W = √2/cosh(x/ℓ) も解(両端で首に近づく孤立した山)。
  * `ca_collapse`:このとき r の時間の 2 階微分の符号を決める量 −(1 − ℓ²(1 − W²)²/r²) は −2ℓ²W′² ≤ 0。
    W が軸に沿って変わっているところでは、面積は次の瞬間に縮み始める。一定のままでいられるのは W′ = 0 の首だけ。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace CFT.CA

theorem ca_constraint (r W W1 l : ℝ) (hl : l ≠ 0)
    (hH : -4 * r * 0 + 2 * (1 - (0 : ℝ) ^ 2) = 4 * l ^ 2 * (W1 ^ 2 + (1 - W ^ 2) ^ 2 / (2 * r ^ 2))) :
    W1 ^ 2 = (1 - l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2) / (2 * l ^ 2) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero 2 hl))]
  linear_combination (-1 / 2 : ℝ) * hH

theorem ca_turning (r0 l : ℝ) (hr : r0 ≠ 0) (hl : l ≠ 0) :
    1 - l ^ 2 * (1 - (1 + r0 / l)) ^ 2 / r0 ^ 2 = 0 := by
  field_simp

theorem ca_neck_fixed (W l : ℝ) (hl : l ≠ 0) :
    (1 - l ^ 2 * (1 - W ^ 2) ^ 2 / l ^ 2) / (2 * l ^ 2) = W ^ 2 * (2 - W ^ 2) / (2 * l ^ 2) := by
  field_simp
  ring

theorem ca_soliton_deriv (q l x : ℝ) :
    HasDerivAt (fun y : ℝ => q * (Real.cosh (y / l))⁻¹)
      (q * (-(Real.sinh (x / l) * (1 / l)) / Real.cosh (x / l) ^ 2)) x :=
  ((((hasDerivAt_id' x).div_const l).cosh).inv (ne_of_gt (Real.cosh_pos _))).const_mul q

theorem ca_soliton (q sh ch ci li : ℝ) (hq : q ^ 2 = 2) (hcs : ch ^ 2 - sh ^ 2 = 1)
    (hci : ch * ci = 1) :
    (-q * sh * li * ci ^ 2) ^ 2 = (q * ci) ^ 2 * (2 - (q * ci) ^ 2) * li ^ 2 / 2 := by
  have h1 : sh ^ 2 * ci ^ 2 = 1 - ci ^ 2 := by
    linear_combination (-ci ^ 2) * hcs + (ch * ci + 1) * hci
  linear_combination (2 * li ^ 2 * ci ^ 2) * h1
    + (sh ^ 2 * li ^ 2 * ci ^ 4 - ci ^ 2 * li ^ 2 + (q ^ 2 + 2) * ci ^ 4 * li ^ 2 / 2) * hq

theorem ca_collapse (r W W1 l : ℝ) (hl : l ≠ 0)
    (hW : W1 ^ 2 = (1 - l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2) / (2 * l ^ 2)) :
    -(1 - l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2) = -(2 * l ^ 2 * W1 ^ 2)
      ∧ -(2 * l ^ 2 * W1 ^ 2) ≤ 0 := by
  have h2 : 2 * l ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hl)
  rw [eq_div_iff h2] at hW
  constructor
  · linarith
  · have : 0 ≤ 2 * l ^ 2 * W1 ^ 2 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
    linarith

end CFT.CA
