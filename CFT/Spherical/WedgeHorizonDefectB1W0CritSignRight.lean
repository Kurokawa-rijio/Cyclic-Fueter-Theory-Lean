/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **P(r₂) の符号の確定（第二段）と P の零点の個数の確定**。前段
  （`WedgeHorizonDefectB1W0CritSign`）で P(r₁) > 0 が閉じ、P の
  (0, ∞) での零点の個数は P(r₂) の符号だけに帰着した。ここでは
  g(r₂) = 0 から P(r₂) = Q₂(r₂)/2 を得て、Q₂(r₂) > 0 を示す：
    * Q₂(r*) = (r₊²+9)²/18 − 15r₊r* + 6r₊² > 0 は、両辺を二乗した
      四次式の不等式 (s²+126s+81)² > 4050s(s+9)（s = r₊²）に帰着する。
      差は s⁴ + 252s³ + (11988s² − 16038s + 6561) で、括弧内は判別式が
      負（−57395628）の二次式なのでつねに正。
    * r₂ > r* では差の因数分解
      Q₂(r₂) − Q₂(r*) = (r₂ − r*)·((r₊²+9)(r₂ + r*) − 15r₊)
      の第二因子が、Q₂′(r*) = −3g(r*) > 0（g(r*) < 0 は閾値の結果）
      から正。したがって Q₂(r₂) > Q₂(r*) > 0。
  まとめとして P(r₂) > 0。Count モジュールの組み立てと合わせると、
  P は (0, ∞) でちょうど一個の零点を持ち、それは (r₂, 2) にある。
  式の確認は sympy による明示計算でも照合済み
  （`/tmp/check_critsign_r2.py`・`/tmp/check_critsign_r2b.py`：
  Q₂(r*) の形・A²−B² の四次式・判別式・r₊ = 0.1〜0.99 での
  Q₂(r*) > 0 と g(r*) < 0 の数値確認）。
-/
import CFT.Spherical.WedgeHorizonDefectB1W0CritSign
import CFT.Spherical.WedgeHorizonDefectB1W0Count

open Real Set Filter Topology
open CFT.WedgeDefectB1W0Zero
open CFT.WedgeDefectB1W0Deriv
open CFT.WedgeDefectB1W0Threshold
open CFT.WedgeDefectB1W0Zeros
open CFT.WedgeDefectB1W0CritSign
open CFT.WedgeDefectB1W0Count

namespace CFT.WedgeDefectB1W0CritSignRight

/-- 四次式の不等式：s ≥ 0 なら (s²+126s+81)² > 4050s(s+9)。
    差は s⁴ + 252s³ + (11988s² − 16038s + 6561) で、括弧内は
    11988(s − 99/148)² + 177147/148 > 0。 -/
theorem quartic_poly_sq_gt {s : ℝ} (hs : 0 ≤ s) :
    4050 * s * (s + 9) < (s ^ 2 + 126 * s + 81) ^ 2 := by
  have key : (s ^ 2 + 126 * s + 81) ^ 2 - 4050 * s * (s + 9)
      = s ^ 4 + 252 * s ^ 3 + 11988 * (s - 99 / 148) ^ 2 + 177147 / 148 := by
    ring
  have h1 : (0 : ℝ) ≤ s ^ 4 := by positivity
  have h2 : (0 : ℝ) ≤ 252 * s ^ 3 := by positivity
  have h3 : (0 : ℝ) ≤ 11988 * (s - 99 / 148) ^ 2 := by positivity
  linarith

/-- 臨界点での Q₂ の値：Q₂(r*) = (r₊²+9)²/18 − 15r₊r* + 6r₊²。 -/
theorem defectQuadQ2_at_critPoint {rp : ℝ} :
    defectQuadQ2 (defectQuarticCritPoint rp) rp
      = (rp ^ 2 + 9) ^ 2 / 18 - 15 * rp * defectQuarticCritPoint rp
        + 6 * rp ^ 2 := by
  have h2 := defectQuarticCritPoint_sq (rp := rp)
  unfold defectQuadQ2
  linear_combination (rp ^ 2 + 9) * h2

/-- 臨界点で Q₂ > 0（両辺の二乗による比較）。 -/
theorem defectQuadQ2_pos_at_critPoint {rp : ℝ} (hrp : 0 < rp) :
    0 < defectQuadQ2 (defectQuarticCritPoint rp) rp := by
  have hA : (0 : ℝ) < (rp ^ 2 + 9) ^ 2 / 18 + 6 * rp ^ 2 := by
    have h1 : (0 : ℝ) < (rp ^ 2 + 9) ^ 2 / 18 := by positivity
    have h2 : (0 : ℝ) ≤ 6 * rp ^ 2 := by positivity
    linarith
  have hB : (0 : ℝ) ≤ 15 * rp * defectQuarticCritPoint rp :=
    mul_nonneg (mul_nonneg (by norm_num) hrp.le) defectQuarticCritPoint_pos.le
  have hsq : (15 * rp * defectQuarticCritPoint rp) ^ 2
      < ((rp ^ 2 + 9) ^ 2 / 18 + 6 * rp ^ 2) ^ 2 := by
    have hpoly := quartic_poly_sq_gt (s := rp ^ 2) (sq_nonneg rp)
    have hcr := defectQuarticCritPoint_sq (rp := rp)
    have hAeq : (rp ^ 2 + 9) ^ 2 / 18 + 6 * rp ^ 2
        = ((rp ^ 2) ^ 2 + 126 * rp ^ 2 + 81) / 18 := by ring
    have hBeq : (15 * rp * defectQuarticCritPoint rp) ^ 2
        = 225 * rp ^ 2 * (rp ^ 2 + 9) / 18 := by
      rw [mul_pow, mul_pow, hcr]
      ring
    rw [hAeq, hBeq, div_pow]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 18 ^ 2)]
    nlinarith [hpoly]
  have hlt : 15 * rp * defectQuarticCritPoint rp
      < (rp ^ 2 + 9) ^ 2 / 18 + 6 * rp ^ 2 :=
    (sq_lt_sq₀ hB hA.le).mp hsq
  rw [defectQuadQ2_at_critPoint]
  linarith

/-- Q₂ の差の因数分解：Q₂(r) − Q₂(r*) = (r − r*)·((r₊²+9)(r + r*) − 15r₊)。 -/
theorem defectQuadQ2_sub_at_critPoint {rp r : ℝ} :
    defectQuadQ2 r rp - defectQuadQ2 (defectQuarticCritPoint rp) rp
      = (r - defectQuarticCritPoint rp)
        * ((rp ^ 2 + 9) * (r + defectQuarticCritPoint rp) - 15 * rp) := by
  unfold defectQuadQ2
  ring

/-- r₂ > r* なら Q₂(r₂) > Q₂(r*)（第二因子は Q₂′(r*) = −3g(r*) > 0 から正）。 -/
theorem defectQuadQ2_gt_at_critPoint_of_gt {rp r₂ : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (h2 : defectQuarticCritPoint rp < r₂) :
    defectQuadQ2 (defectQuarticCritPoint rp) rp < defectQuadQ2 r₂ rp := by
  have hg : defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp < 0 :=
    defectCubicB1W0Deriv_at_critPoint_neg_of_le_99 hrp hle
  have hgc := defectCubicB1W0Deriv_at_critPoint (rp := rp)
  have hfactor : (0 : ℝ)
      < (rp ^ 2 + 9) * (r₂ + defectQuarticCritPoint rp) - 15 * rp := by
    have h1 : (rp ^ 2 + 9) * (2 * defectQuarticCritPoint rp)
        < (rp ^ 2 + 9) * (r₂ + defectQuarticCritPoint rp) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      linarith [h2]
    have h2' : (rp ^ 2 + 9) * (2 * defectQuarticCritPoint rp) - 15 * rp
        = -3 * defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp := by
      rw [hgc]
      ring
    have h3 : (0 : ℝ)
        < (rp ^ 2 + 9) * (2 * defectQuarticCritPoint rp) - 15 * rp := by
      rw [h2']
      linarith [hg]
    linarith [h1, h3]
  have hdiff : (0 : ℝ)
      < defectQuadQ2 r₂ rp - defectQuadQ2 (defectQuarticCritPoint rp) rp := by
    rw [defectQuadQ2_sub_at_critPoint]
    exact mul_pos (by linarith [h2]) hfactor
  linarith

/-- 主結果：右の臨界点で P(r₂) > 0。 -/
theorem defectQuarticB1W0_pos_at_crit_right {rp r₂ : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0) :
    0 < defectQuarticB1W0 r₂ rp := by
  rw [defectQuarticB1W0_eq_Q2_div_two_of_deriv_eq_zero h2z]
  apply div_pos _ (by norm_num)
  exact lt_trans (defectQuadQ2_pos_at_critPoint hrp)
    (defectQuadQ2_gt_at_critPoint_of_gt hrp hle h2.1)

/-- 組み立て：P(r₁) > 0 かつ P(r₂) > 0 なら P は (0, ∞) でちょうど一個の
    零点を持ち、それは (r₂, 2) にある。 -/
theorem defectQuarticB1W0_exactly_one_zero {rp r₁ r₂ : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (huniq : ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂) :
    ∃ r₀ : ℝ, r₂ < r₀ ∧ r₀ < 2 ∧ defectQuarticB1W0 r₀ rp = 0 ∧
      ∀ r : ℝ, 0 < r → defectQuarticB1W0 r rp = 0 → r = r₀ :=
  defectQuarticB1W0_exactly_one_zero_of_critPos hrp hle h1 h1z h2 h2z huniq
    (defectQuarticB1W0_pos_at_crit_left hrp h1 h1z)
    (defectQuarticB1W0_pos_at_crit_right hrp hle h2 h2z)

/-- 見出しの形：0 < r₊ ≤ 99/100 なら P は (0, ∞) でちょうど一個の零点を持つ。 -/
theorem defectQuarticB1W0_exactly_one_zero_of_rp {rp : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ defectQuarticB1W0 r₀ rp = 0 ∧
      ∀ r : ℝ, 0 < r → defectQuarticB1W0 r rp = 0 → r = r₀ := by
  obtain ⟨r₁, r₂, h1pos, h1lt, h2gt, h2lt, hz1, hz2, huniq⟩ :=
    defectCubicB1W0Deriv_exactly_two_zeros hrp hle
  obtain ⟨r₀, hr₀, hr₀2, hz₀, huniq₀⟩ :=
    defectQuarticB1W0_exactly_one_zero hrp hle ⟨h1pos, h1lt⟩ hz1 ⟨h2gt, h2lt⟩
      hz2 huniq
  exact ⟨r₀, defectQuarticCritPoint_pos.trans (h2gt.trans hr₀), hz₀, huniq₀⟩

end CFT.WedgeDefectB1W0CritSignRight
