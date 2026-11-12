/-
  対称性を仮定しない定式化に向けて:断面の形の自由度(2026-11-12)

  2+2 分解:ds² = −2e^f du dv + r² q_AB (dy^A + s^A du)(dy^B + s^B du)、det q = det γ(面積要素は r² が担う)。
  q は面積を変えない断面の形で、楕円率 β と向き θ で
    q = [[C + S c, S s], [S s, C − S c]]、C = cosh 2β、S = sinh 2β、c = cos 2θ、s = sin 2θ
  と書ける。重力波の二つの偏極がこの (β, θ)。
  * `gen_unimodular`:det q = 1(楕円率と向きを変えても面積要素は変わらない)。
  * `gen_trace_free`:tr(q⁻¹ q̇) = 0。
  * `gen_shear`:ずれの 2 乗 σ² = −det(q̇)/4 = β̇² + sinh²(2β) θ̇²(形の空間は双曲平面 SL(2,ℝ)/SO(2))。
  * `gen_focusing`:拘束 r_uu − ω_u r_u + B = 0 で B = r(β_u² + S²θ_u²) + 2ℓ²W_u²/r ≥ 0 なので r_uu − ω_u r_u ≤ 0。
    形の変化(重力波)は、ゲージ場の W_u² と同じ場所に、同じ符号で入る(ずれのない場合。Raychaudhuri の式は外部)。
  回転する首(極限 Kerr–Newman の地平線、断面は丸くないが軸に沿って同じ):
  * `gen_kn_area`:M² = a² + Q² なら面積 4π(M² + a²) = 4π(Q² + 2a²)。
  * `gen_kn_area_ge`、`gen_kn_round_iff`:面積 ≥ 4πQ²、等号は a = 0(丸い首)だけ。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

namespace CFT.GEN

theorem gen_unimodular (C S c s : ℝ) (hC : C ^ 2 - S ^ 2 = 1) (hc : c ^ 2 + s ^ 2 = 1) :
    (C + S * c) * (C - S * c) - (S * s) ^ 2 = 1 := by
  linear_combination hC - S ^ 2 * hc

theorem gen_trace_free (C S c s bd td : ℝ) (hc : c ^ 2 + s ^ 2 = 1) :
    (C - S * c) * (2 * bd * (S + C * c) - 2 * td * S * s)
      + (C + S * c) * (2 * bd * (S - C * c) + 2 * td * S * s)
      - 2 * (S * s) * (2 * bd * C * s + 2 * td * S * c) = 0 := by
  linear_combination (-4 * bd * S * C) * hc

theorem gen_shear (C S c s bd td : ℝ) (hC : C ^ 2 - S ^ 2 = 1) (hc : c ^ 2 + s ^ 2 = 1) :
    -((2 * bd * (S + C * c) - 2 * td * S * s) * (2 * bd * (S - C * c) + 2 * td * S * s)
        - (2 * bd * C * s + 2 * td * S * c) ^ 2) / 4
      = bd ^ 2 + S ^ 2 * td ^ 2 := by
  linear_combination (bd ^ 2 * C ^ 2 + td ^ 2 * S ^ 2) * hc + bd ^ 2 * hC

theorem gen_focusing (r ru ruu w S bu tu Wu l : ℝ) (hr : 0 < r)
    (hC : ruu - w * ru + (r * (bu ^ 2 + S ^ 2 * tu ^ 2) + 2 * l ^ 2 * Wu ^ 2 / r) = 0) :
    ruu - w * ru ≤ 0 := by
  have hB : 0 ≤ r * (bu ^ 2 + S ^ 2 * tu ^ 2) + 2 * l ^ 2 * Wu ^ 2 / r :=
    add_nonneg
      (mul_nonneg hr.le (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)) hr.le)
  linarith

theorem gen_kn_area (a Q M : ℝ) (h : M ^ 2 = a ^ 2 + Q ^ 2) :
    4 * π * (M ^ 2 + a ^ 2) = 4 * π * (Q ^ 2 + 2 * a ^ 2) := by
  linear_combination 4 * π * h

theorem gen_kn_area_ge (a Q : ℝ) : 4 * π * Q ^ 2 ≤ 4 * π * (Q ^ 2 + 2 * a ^ 2) := by
  have hp : 0 ≤ 4 * π := by positivity
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a]) hp

theorem gen_kn_round_iff (a Q : ℝ) : 4 * π * (Q ^ 2 + 2 * a ^ 2) = 4 * π * Q ^ 2 ↔ a = 0 := by
  constructor
  · intro h
    have h2 : π * a ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 Real.pi_ne_zero
    · exact (pow_eq_zero_iff two_ne_zero).mp h3
  · intro h
    rw [h]
    ring

end CFT.GEN
