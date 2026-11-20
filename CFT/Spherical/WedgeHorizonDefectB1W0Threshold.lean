/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **g(r*) の符号による r₊ の場合分け（閾値の挟み込み）**。
  前段（`WedgeHorizonDefectB1W0Deriv`）で臨界点での値
    g(r*) = 5r₊ − (2/3)(r₊²+9)·r*、r* = √((r₊²+9)/18)
  の公式が閉じた。ここではその符号を r₊ の場合分けで確定する。
  両辺を二乗すると符号は多項式
    φ(t) = 2(t+9)³ − 2025t、t = r₊²
  の符号に帰着する：
    g(r*) < 0 ⟺ 2025r₊² < 2(r₊²+9)³、
    g(r*) > 0 ⟺ 2(r₊²+9)³ < 2025r₊²、
    g(r*) = 0 ⟺ 2(r₊²+9)³ = 2025r₊²。
  φ は [0, 4] 上で狭義単調減少（φ′(t) = 6(t+9)² − 2025 < 0）で、
  φ(1) = −25 < 0 < φ(9801/10000) ≈ 3.381 である。よって
    0 < r₊ ≤ 99/100 なら g(r*) < 0、
    1 ≤ r₊ ≤ 2 なら g(r*) > 0。
  さらに中間値の定理から、g(r*) = 0 となる閾値 r₀ が区間
  (99/100, 1) に存在する（r₀ ≈ 0.9912、sympy による数値確認と一致）。
  これで g の最小値の符号が r₊ の大小で確定し、P の零点の一意性・
  個数の判定が g(r*) の符号の問題に帰着した。残りは、外側・内側の
  零点の一意性・個数の確定と、それによる S = 0 の角から離れた領域
  での導出である。式の確認は sympy による明示計算でも照合済み
  （`/tmp/check_threshold.py`）。
-/
import CFT.Spherical.WedgeHorizonDefectB1W0Deriv
import CFT.Spherical.WedgeHorizonFirstZero

open Real Set Filter Topology
open CFT.WedgeDefectB1W0Deriv
open CFT.WedgeFirstZero

namespace CFT.WedgeDefectB1W0Threshold

/-- 閾値多項式 φ(t) = 2(t+9)³ − 2025t（t = r₊²）。g(r*) の符号は
    φ(r₊²) の符号で決まる。 -/
noncomputable def thresholdPoly (t : ℝ) : ℝ :=
  2 * (t + 9) ^ 3 - 2025 * t

/-- φ(1) = −25。 -/
theorem thresholdPoly_one : thresholdPoly 1 = -25 := by
  unfold thresholdPoly
  norm_num

/-- φ(9801/10000) > 0（≈ 3.381）。 -/
theorem thresholdPoly_9801_pos : 0 < thresholdPoly (9801 / 10000) := by
  unfold thresholdPoly
  norm_num

/-- φ の導関数（`HasDerivAt` 版）。 -/
theorem thresholdPoly_hasDerivAt {t : ℝ} :
    HasDerivAt thresholdPoly (6 * (t + 9) ^ 2 - 2025) t := by
  have heq : thresholdPoly
      = (fun x => 2 * x ^ 3 + 54 * x ^ 2 - 1539 * x + 1458) := by
    funext x
    unfold thresholdPoly
    ring
  rw [heq]
  have h1 := (hasDerivAt_pow 3 t).const_mul (2 : ℝ)
  have h2 := (hasDerivAt_pow 2 t).const_mul (54 : ℝ)
  have h3 := (hasDerivAt_id t).const_mul (1539 : ℝ)
  have h4 := hasDerivAt_const t (1458 : ℝ)
  have h := ((h1.add h2).sub h3).add h4
  convert h using 1
  ring

/-- φ の導関数は 6(t+9)² − 2025。 -/
theorem thresholdPoly_deriv_eq {t : ℝ} :
    deriv thresholdPoly t = 6 * (t + 9) ^ 2 - 2025 :=
  thresholdPoly_hasDerivAt.deriv

/-- φ は連続。 -/
theorem thresholdPoly_continuous : Continuous thresholdPoly := by
  unfold thresholdPoly
  continuity

/-- φ は [0, 4] 上で狭義単調減少（φ′ < 0）。 -/
theorem thresholdPoly_strictAntiOn :
    StrictAntiOn thresholdPoly (Icc 0 4) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 4)
    thresholdPoly_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [thresholdPoly_deriv_eq]
  have hpos : (0 : ℝ) < x + 9 := by linarith [hx.1]
  have hlt : x + 9 < 13 := by linarith [hx.2]
  have hsq : (x + 9) ^ 2 < 13 ^ 2 :=
    (sq_lt_sq₀ hpos.le (by norm_num : (0 : ℝ) ≤ 13)).mpr hlt
  nlinarith [hsq]

/-- 臨界点の値の第二項の二乗：((2/3)(r₊²+9)r*)² = (2/81)(r₊²+9)³。 -/
theorem defectCubicB1W0Deriv_at_critPoint_term_sq {rp : ℝ} :
    ((2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp) ^ 2
      = (2 / 81) * (rp ^ 2 + 9) ^ 3 := by
  have h2 := defectQuarticCritPoint_sq (rp := rp)
  linear_combination (4 / 9) * (rp ^ 2 + 9) ^ 2 * h2

/-- g(r*) < 0 ⟺ 2025r₊² < 2(r₊²+9)³（r₊ > 0）。 -/
theorem defectCubicB1W0Deriv_at_critPoint_neg_iff {rp : ℝ} (hrp : 0 < rp) :
    defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp < 0
      ↔ 2025 * rp ^ 2 < 2 * (rp ^ 2 + 9) ^ 3 := by
  rw [defectCubicB1W0Deriv_at_critPoint]
  have hc : 0 < defectQuarticCritPoint rp := defectQuarticCritPoint_pos
  have hB : 0 < (2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp := by
    positivity
  have hA : (0 : ℝ) ≤ 5 * rp := by linarith
  constructor
  · intro h
    have hlt : 5 * rp
        < (2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp := by linarith
    have hsq := (sq_lt_sq₀ hA hB.le).mpr hlt
    rw [defectCubicB1W0Deriv_at_critPoint_term_sq] at hsq
    nlinarith [hsq]
  · intro h
    have hsq : (5 * rp) ^ 2
        < ((2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp) ^ 2 := by
      rw [defectCubicB1W0Deriv_at_critPoint_term_sq]
      nlinarith [h]
    have hlt := (sq_lt_sq₀ hA hB.le).mp hsq
    linarith

/-- 0 < g(r*) ⟺ 2(r₊²+9)³ < 2025r₊²（r₊ > 0）。 -/
theorem defectCubicB1W0Deriv_at_critPoint_pos_iff {rp : ℝ} (hrp : 0 < rp) :
    0 < defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp
      ↔ 2 * (rp ^ 2 + 9) ^ 3 < 2025 * rp ^ 2 := by
  rw [defectCubicB1W0Deriv_at_critPoint]
  have hc : 0 < defectQuarticCritPoint rp := defectQuarticCritPoint_pos
  have hB : 0 < (2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp := by
    positivity
  have hA : (0 : ℝ) ≤ 5 * rp := by linarith
  constructor
  · intro h
    have hlt : (2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp < 5 * rp := by
      linarith
    have hsq := (sq_lt_sq₀ hB.le hA).mpr hlt
    rw [defectCubicB1W0Deriv_at_critPoint_term_sq] at hsq
    nlinarith [hsq]
  · intro h
    have hsq : ((2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp) ^ 2
        < (5 * rp) ^ 2 := by
      rw [defectCubicB1W0Deriv_at_critPoint_term_sq]
      nlinarith [h]
    have hlt := (sq_lt_sq₀ hB.le hA).mp hsq
    linarith

/-- g(r*) = 0 ⟺ 2(r₊²+9)³ = 2025r₊²（r₊ > 0）。 -/
theorem defectCubicB1W0Deriv_at_critPoint_eq_zero_iff {rp : ℝ} (hrp : 0 < rp) :
    defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp = 0
      ↔ 2 * (rp ^ 2 + 9) ^ 3 = 2025 * rp ^ 2 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_trichotomy (2025 * rp ^ 2) (2 * (rp ^ 2 + 9) ^ 3) with h1 | h1 | h1
    · have h2 := (defectCubicB1W0Deriv_at_critPoint_neg_iff hrp).mpr h1
      linarith
    · exact hne h1.symm
    · have h2 := (defectCubicB1W0Deriv_at_critPoint_pos_iff hrp).mpr h1
      linarith
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 := (defectCubicB1W0Deriv_at_critPoint_neg_iff hrp).mp h1
      linarith
    · have h2 := (defectCubicB1W0Deriv_at_critPoint_pos_iff hrp).mp h1
      linarith

/-- 0 < r₊ ≤ 99/100 なら g(r*) < 0。 -/
theorem defectCubicB1W0Deriv_at_critPoint_neg_of_le_99 {rp : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100) :
    defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp < 0 := by
  rw [defectCubicB1W0Deriv_at_critPoint_neg_iff hrp]
  have ht : rp ^ 2 ≤ 9801 / 10000 := by
    have h := pow_le_pow_left₀ hrp.le hle 2
    norm_num at h
    exact h
  have hmem : rp ^ 2 ∈ Icc (0 : ℝ) 4 :=
    ⟨by positivity, by nlinarith [hle, hrp]⟩
  have hmem2 : (9801 / 10000 : ℝ) ∈ Icc (0 : ℝ) 4 :=
    ⟨by norm_num, by norm_num⟩
  rcases eq_or_lt_of_le ht with h | h
  · rw [h]
    have hpos := thresholdPoly_9801_pos
    unfold thresholdPoly at hpos
    linarith
  · have hlt := thresholdPoly_strictAntiOn hmem hmem2 h
    have hpos := thresholdPoly_9801_pos
    have hgt : 0 < thresholdPoly (rp ^ 2) := lt_trans hpos hlt
    unfold thresholdPoly at hgt
    linarith

/-- 1 ≤ r₊ ≤ 2 なら 0 < g(r*)。 -/
theorem defectCubicB1W0Deriv_at_critPoint_pos_of_mem_Icc {rp : ℝ} (h1 : 1 ≤ rp)
    (h2 : rp ≤ 2) :
    0 < defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp := by
  have hrp : 0 < rp := by linarith
  rw [defectCubicB1W0Deriv_at_critPoint_pos_iff hrp]
  have ht1 : (1 : ℝ) ≤ rp ^ 2 := by
    have h := pow_le_pow_left₀ zero_le_one h1 2
    simpa using h
  have ht2 : rp ^ 2 ≤ 4 := by nlinarith [h2, hrp]
  have hmem : rp ^ 2 ∈ Icc (0 : ℝ) 4 := ⟨by positivity, ht2⟩
  have hmem1 : (1 : ℝ) ∈ Icc (0 : ℝ) 4 := ⟨by norm_num, by norm_num⟩
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [← h]
    norm_num
  · have hlt := thresholdPoly_strictAntiOn hmem1 hmem h
    rw [thresholdPoly_one] at hlt
    have hneg : thresholdPoly (rp ^ 2) < 0 := lt_trans hlt (by norm_num)
    unfold thresholdPoly at hneg
    linarith

/-- 閾値が区間 (99/100, 1) に存在する：2(r₀²+9)³ = 2025r₀²。 -/
theorem exists_threshold_in_Ioo :
    ∃ r₀ ∈ Ioo ((99 : ℝ) / 100) 1, 2 * (r₀ ^ 2 + 9) ^ 3 = 2025 * r₀ ^ 2 := by
  have hcont : ContinuousOn (fun rp : ℝ => thresholdPoly (rp ^ 2))
      (Icc (99 / 100) 1) :=
    (thresholdPoly_continuous.comp (continuous_pow 2)).continuousOn
  have ha : 0 < thresholdPoly ((99 / 100 : ℝ) ^ 2) := by
    have h : (99 / 100 : ℝ) ^ 2 = 9801 / 10000 := by norm_num
    rw [h]
    exact thresholdPoly_9801_pos
  have hb : thresholdPoly ((1 : ℝ) ^ 2) < 0 := by
    have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h1, thresholdPoly_one]
    norm_num
  obtain ⟨r₀, hr₀, h0⟩ := exists_zero_of_sign_change (by norm_num) hcont ha hb
  refine ⟨r₀, hr₀, ?_⟩
  unfold thresholdPoly at h0
  linarith

/-- 閾値では臨界点での g の値が 0 になる。 -/
theorem exists_critPoint_zero_in_Ioo :
    ∃ r₀ ∈ Ioo ((99 : ℝ) / 100) 1,
      defectCubicB1W0Deriv (defectQuarticCritPoint r₀) r₀ = 0 := by
  obtain ⟨r₀, hr₀, h0⟩ := exists_threshold_in_Ioo
  refine ⟨r₀, hr₀, ?_⟩
  have hrp : 0 < r₀ := by linarith [hr₀.1]
  exact (defectCubicB1W0Deriv_at_critPoint_eq_zero_iff hrp).mpr h0

end CFT.WedgeDefectB1W0Threshold
