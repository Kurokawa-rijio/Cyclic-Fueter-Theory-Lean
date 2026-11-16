/-
  形を自由に動かしたときの変動と、体積一定・断面積一定(2026-11-12、G = 1)

  正準変数(h = −N²dt² + Λ²dx²、ずれなし):P_Λ = −r ṙ/N、P_r = −(Λ ṙ + r Λ̇)/N。体積の密度は Λ r²、断面積は 4π r²。
  * `sf_volume_rate`:体積の密度の時間変化 Λ̇ r² + 2Λ r ṙ = −N(r P_r + Λ P_Λ)。
    体積の変化率は、伸縮の生成子 D = r P_r + Λ P_Λ そのもの(平均の外部曲率、York の時間にあたる)。
  * `sf_weight_volume`、`sf_weight_area`:{Λ r², D} = 3Λ r²、{r², D} = 2r²(体積は重み 3、面積は重み 2)。
    体積と D、面積と P_r/(2r) が共役。どちらを確定させるかが「体積一定」「面積一定」の選択。
  * `sf_area_const_rigid`:光の方向に沿って面積が一定(r_u = 0、r_uu = 0)なら、拘束
    r(β_u² + S²θ_u²) + 2ℓ²W_u²/r = 0 から β_u = 0、S θ_u = 0、W_u = 0。
    古典的には、面積一定は形の運動もゲージ場の運動も許さない(孤立した地平線の条件)。
  * `sf_quantum_focus`:形の変化率の 2 乗の期待値 e > 0 なら −r e < 0。
    零点振動があるかぎり、面積は厳密には一定でいられない。
-/
import Mathlib.Tactic

namespace CFT.SF

theorem sf_volume_rate (r rd L Ld N : ℝ) (hN : N ≠ 0) :
    Ld * r ^ 2 + 2 * L * r * rd
      = -N * (r * (-(L * rd + r * Ld) / N) + L * (-(r * rd) / N)) := by
  field_simp
  ring

theorem sf_weight_volume (r L : ℝ) : (2 * L * r) * r + r ^ 2 * L = 3 * (L * r ^ 2) := by ring

theorem sf_weight_area (r : ℝ) : (2 * r) * r = 2 * r ^ 2 := by ring

theorem sf_area_const_rigid (r S bu tu Wu l : ℝ) (hr : 0 < r) (hl : l ≠ 0)
    (h : r * (bu ^ 2 + S ^ 2 * tu ^ 2) + 2 * l ^ 2 * Wu ^ 2 / r = 0) :
    bu = 0 ∧ S * tu = 0 ∧ Wu = 0 := by
  have h1 : 0 ≤ r * (bu ^ 2 + S ^ 2 * tu ^ 2) :=
    mul_nonneg hr.le (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have h2 : 0 ≤ 2 * l ^ 2 * Wu ^ 2 / r :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)) hr.le
  have e1 : r * (bu ^ 2 + S ^ 2 * tu ^ 2) = 0 := by linarith
  have e2 : 2 * l ^ 2 * Wu ^ 2 / r = 0 := by linarith
  have e3 : bu ^ 2 + S ^ 2 * tu ^ 2 = 0 := (mul_eq_zero.mp e1).resolve_left hr.ne'
  have hst : 0 ≤ S ^ 2 * tu ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb : bu ^ 2 = 0 := by linarith [sq_nonneg bu]
  have ht : S ^ 2 * tu ^ 2 = 0 := by linarith [sq_nonneg bu]
  have ht2 : (S * tu) ^ 2 = 0 := by rw [mul_pow]; exact ht
  have e4 : 2 * l ^ 2 * Wu ^ 2 = 0 := (div_eq_zero_iff.mp e2).resolve_right hr.ne'
  have e5 : Wu ^ 2 = 0 :=
    (mul_eq_zero.mp e4).resolve_left (mul_ne_zero two_ne_zero (pow_ne_zero 2 hl))
  exact ⟨(pow_eq_zero_iff two_ne_zero).mp hb, (pow_eq_zero_iff two_ne_zero).mp ht2,
    (pow_eq_zero_iff two_ne_zero).mp e5⟩

theorem sf_quantum_focus (r e : ℝ) (hr : 0 < r) (he : 0 < e) : -(r * e) < 0 :=
  neg_neg_of_pos (mul_pos hr he)

end CFT.SF
