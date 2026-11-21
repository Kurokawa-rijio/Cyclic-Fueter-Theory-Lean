/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **P(r₁) の符号の確定（第一段）**。前段
  （`WedgeHorizonDefectB1W0Count`）で、P の (0, ∞) での零点の個数は
  P(r₁)・P(r₂) の符号の問題に帰着した。ここでは二次式への帰着
    P(r) = Q₂(r)/2 − (r/2)·g(r),
    Q₂(r) = (r₊²+9)r² − 15r·r₊ + 6r₊²
  を証明し、g(r₁) = 0 から P(r₁) = Q₂(r₁)/2 を得る。Q₂(r₁) > 0 は
  r₊² と 3/8 の場合分けで示す：
    * r₊² > 3/8 なら平方完成 Q₂(r) = (r₊²+9)(r − r_v)²
      + r₊²(24r₊²−9)/(4(r₊²+9)) の最小値が正なので、すべての r で
      Q₂(r) > 0。
    * r₊² ≤ 3/8 なら g(2r₊/3) = r₊((10/9)r₊² − 1) < 0 と g の
      (0, r*] 上での狭義単調減少から r₁ < 2r₊/3 であり、
      Q₂(2r₊/3) = (4/9)r₊⁴ > 0 と差の因数分解
      Q₂(r₁) − Q₂(2r₊/3)
        = (r₁ − 2r₊/3)·((r₊²+9)(r₁ + 2r₊/3) − 15r₊)
      （両因子とも負）から Q₂(r₁) > (4/9)r₊⁴ > 0。
  したがって P(r₁) > 0。P(r₂) > 0 は次の段に残す（r₂ > r* からの
  Q₂ の単調増加と Q₂(r*) > 0 の評価が要る）。
  式の確認は sympy による明示計算でも照合済み
  （`/tmp/check_critsign.py`・`/tmp/check_critsign2.py`：
  帰着・平方完成・Q₂(2r₊/3)・g(2r₊/3)・差の因数分解と、
  r₊ = 0.1〜0.612 での r₁ < 2r₊/3 と Q₂(r₁) > 0 の数値確認）。
-/
import CFT.Spherical.WedgeHorizonDefectB1W0Zeros

open Real Set Filter Topology
open CFT.WedgeDefectB1W0Zero
open CFT.WedgeDefectB1W0Deriv
open CFT.WedgeDefectB1W0Threshold
open CFT.WedgeDefectB1W0Zeros

namespace CFT.WedgeDefectB1W0CritSign

/-- 二次式 Q₂(r) = (r₊²+9)r² − 15r·r₊ + 6r₊²。P(r) = Q₂(r)/2 − (r/2)·g(r)。 -/
noncomputable def defectQuadQ2 (r rp : ℝ) : ℝ :=
  (rp ^ 2 + 9) * r ^ 2 - 15 * r * rp + 6 * rp ^ 2

/-- 四次式の二次式への帰着：P(r) = Q₂(r)/2 − (r/2)·g(r)。 -/
theorem defectQuarticB1W0_eq_Q2 {r rp : ℝ} :
    defectQuarticB1W0 r rp
      = defectQuadQ2 r rp / 2 - (r / 2) * defectCubicB1W0Deriv r rp := by
  rw [defectQuarticB1W0_eq]
  unfold defectQuadQ2 defectCubicB1W0Deriv
  ring

/-- g の零点では P(r) = Q₂(r)/2。 -/
theorem defectQuarticB1W0_eq_Q2_div_two_of_deriv_eq_zero {r rp : ℝ}
    (h : defectCubicB1W0Deriv r rp = 0) :
    defectQuarticB1W0 r rp = defectQuadQ2 r rp / 2 := by
  rw [defectQuarticB1W0_eq_Q2, h]
  ring

/-- Q₂(2r₊/3) = (4/9)r₊⁴。 -/
theorem defectQuadQ2_at_two_thirds_rp {rp : ℝ} :
    defectQuadQ2 (2 * rp / 3) rp = 4 * rp ^ 4 / 9 := by
  unfold defectQuadQ2
  ring

/-- Q₂ の平方完成。最小値は r₊²(24r₊²−9)/(4(r₊²+9))。 -/
theorem defectQuadQ2_complete_square {r rp : ℝ} :
    defectQuadQ2 r rp
      = (rp ^ 2 + 9) * (r - 15 * rp / (2 * (rp ^ 2 + 9))) ^ 2
        + rp ^ 2 * (24 * rp ^ 2 - 9) / (4 * (rp ^ 2 + 9)) := by
  have h9 : (rp ^ 2 + 9 : ℝ) ≠ 0 := by positivity
  unfold defectQuadQ2
  field_simp
  ring

/-- r₊² > 3/8 なら Q₂ はすべての r で正（平方完成の最小値が正）。 -/
theorem defectQuadQ2_pos_of_sq_gt_three_eighths {r rp : ℝ}
    (hsq : (3 : ℝ) / 8 < rp ^ 2) :
    0 < defectQuadQ2 r rp := by
  have hrp2 : (0 : ℝ) < rp ^ 2 := by linarith
  rw [defectQuadQ2_complete_square]
  have h1 : (0 : ℝ)
      ≤ (rp ^ 2 + 9) * (r - 15 * rp / (2 * (rp ^ 2 + 9))) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have h2 : (0 : ℝ) < rp ^ 2 * (24 * rp ^ 2 - 9) / (4 * (rp ^ 2 + 9)) :=
    div_pos (mul_pos hrp2 (by linarith)) (by positivity)
  linarith

/-- g(2r₊/3) = r₊(10r₊² − 9)/9。 -/
theorem defectCubicB1W0Deriv_at_two_thirds_rp {rp : ℝ} :
    defectCubicB1W0Deriv (2 * rp / 3) rp = rp * (10 * rp ^ 2 - 9) / 9 := by
  unfold defectCubicB1W0Deriv
  ring

/-- r₊² ≤ 3/8 なら g(2r₊/3) < 0。 -/
theorem defectCubicB1W0Deriv_at_two_thirds_rp_neg {rp : ℝ} (hrp : 0 < rp)
    (hsq : rp ^ 2 ≤ 3 / 8) :
    defectCubicB1W0Deriv (2 * rp / 3) rp < 0 := by
  rw [defectCubicB1W0Deriv_at_two_thirds_rp]
  have h9 : (10 : ℝ) * rp ^ 2 - 9 < 0 := by nlinarith [hsq]
  nlinarith [mul_neg_of_pos_of_neg hrp h9]

/-- r₊² ≤ 3/8 なら 2r₊/3 < r*。 -/
theorem two_thirds_rp_lt_critPoint {rp : ℝ} (hrp : 0 < rp)
    (hsq : rp ^ 2 ≤ 3 / 8) :
    2 * rp / 3 < defectQuarticCritPoint rp := by
  have hsq2 : (2 * rp / 3) ^ 2 < (defectQuarticCritPoint rp) ^ 2 := by
    rw [defectQuarticCritPoint_sq]
    nlinarith [hsq]
  exact (sq_lt_sq₀ (by linarith : (0 : ℝ) ≤ 2 * rp / 3)
    defectQuarticCritPoint_pos.le).mp hsq2

/-- r₊² ≤ 3/8 なら左の零点は r₁ < 2r₊/3（g の狭義単調減少による）。 -/
theorem defectCubicB1W0Deriv_zero_left_lt_two_thirds {rp r₁ : ℝ}
    (hrp : 0 < rp) (hsq : rp ^ 2 ≤ 3 / 8)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0) :
    r₁ < 2 * rp / 3 := by
  have h23 : (0 : ℝ) < 2 * rp / 3 := by linarith
  have h23lt : 2 * rp / 3 < defectQuarticCritPoint rp :=
    two_thirds_rp_lt_critPoint hrp hsq
  have hg : defectCubicB1W0Deriv (2 * rp / 3) rp < 0 :=
    defectCubicB1W0Deriv_at_two_thirds_rp_neg hrp hsq
  by_contra hcon
  push_neg at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · have h := defectCubicB1W0Deriv_strictAntiOn_Ioc_zero_crit
      ⟨h23, h23lt.le⟩ ⟨h1.1, h1.2.le⟩ hlt
    have h' : defectCubicB1W0Deriv r₁ rp
        < defectCubicB1W0Deriv (2 * rp / 3) rp := h
    rw [h1z] at h'
    linarith
  · subst heq
    rw [h1z] at hg
    linarith

/-- r₊² ≤ 3/8 なら Q₂(r₁) > 0（Q₂(2r₊/3) との差の因数分解による）。 -/
theorem defectQuadQ2_pos_at_zero_left_of_sq_le {rp r₁ : ℝ}
    (hrp : 0 < rp) (hsq : rp ^ 2 ≤ 3 / 8)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0) :
    0 < defectQuadQ2 r₁ rp := by
  have hlt : r₁ < 2 * rp / 3 :=
    defectCubicB1W0Deriv_zero_left_lt_two_thirds hrp hsq h1 h1z
  have hQ : defectQuadQ2 (2 * rp / 3) rp = 4 * rp ^ 4 / 9 :=
    defectQuadQ2_at_two_thirds_rp
  have hdiff : defectQuadQ2 r₁ rp - defectQuadQ2 (2 * rp / 3) rp
      = (r₁ - 2 * rp / 3)
        * ((rp ^ 2 + 9) * (r₁ + 2 * rp / 3) - 15 * rp) := by
    unfold defectQuadQ2
    ring
  have hB1 : (rp ^ 2 + 9) * (r₁ + 2 * rp / 3)
      < (rp ^ 2 + 9) * (4 * rp / 3) := by
    apply mul_lt_mul_of_pos_left _ (by positivity)
    linarith [hlt]
  have hB2 : (0 : ℝ) < 3 - (4 / 3) * rp ^ 2 := by nlinarith [hsq]
  have hB : (rp ^ 2 + 9) * (r₁ + 2 * rp / 3) - 15 * rp < 0 := by
    nlinarith [hB1, mul_pos hrp hB2]
  have hprod : (0 : ℝ) < (r₁ - 2 * rp / 3)
      * ((rp ^ 2 + 9) * (r₁ + 2 * rp / 3) - 15 * rp) :=
    mul_pos_of_neg_of_neg (by linarith [hlt]) hB
  have hrp4 : (0 : ℝ) < 4 * rp ^ 4 / 9 :=
    div_pos (mul_pos (by norm_num) (pow_pos hrp 4)) (by norm_num)
  linarith [hdiff, hQ, hprod, hrp4]

/-- 主結果：左の臨界点で P(r₁) > 0（r₊² と 3/8 の場合分け）。 -/
theorem defectQuarticB1W0_pos_at_crit_left {rp r₁ : ℝ}
    (hrp : 0 < rp)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0) :
    0 < defectQuarticB1W0 r₁ rp := by
  have hQ : 0 < defectQuadQ2 r₁ rp := by
    rcases le_or_lt (rp ^ 2) (3 / 8) with hsq | hsq
    · exact defectQuadQ2_pos_at_zero_left_of_sq_le hrp hsq h1 h1z
    · exact defectQuadQ2_pos_of_sq_gt_three_eighths hsq
  rw [defectQuarticB1W0_eq_Q2_div_two_of_deriv_eq_zero h1z]
  linarith

end CFT.WedgeDefectB1W0CritSign
