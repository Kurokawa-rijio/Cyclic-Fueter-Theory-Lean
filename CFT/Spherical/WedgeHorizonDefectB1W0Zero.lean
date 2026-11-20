/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **残余 R の係数 B1|_{W=0} の四次式の解析**。前段
  （`WedgeHorizonDefectC1Zero`）で C1 の零点が正の領域に存在しない
  ことが閉じ、残る係数の零点は B1|_{W=0} = 0 の四次式だけになった。
  ここではその分子の四次式
    P(r) = −3r⁴ + r²r₊² + Q、Q = 9r² − 10r·r₊ + 3r₊²
  を解析する。きれいな因数分解はない（sympy で確認）。端点値は
    P(0) = 3r₊² > 0、P(r₊) = 2r₊²(1 − r₊²)
  で、地平線での符号は r₊ と 1 の大小で決まる。中間値の定理から、
  r₊ < 1 なら地平線の外側 (r₊, 2) に、r₊ > 1 なら地平線の内側
  (0, r₊) に P の零点が存在する。すなわち B1|_{W=0} は r₊ < 1 では
  地平線の外側で消える点を持ち、R = 0 の判定は B1|_{W=0} ≠ 0 だけ
  には帰着しない。r₊ = 1 では P(r) = −(r − 1)·N(r)（N は C1 の三次式）
  と因数分解され、r ≥ 0 では P(r) = 0 ⟺ r = 1 である。端点値と零点の
  位置は sympy による明示計算でも確認済み。
-/
import CFT.Spherical.WedgeHorizonDefectRemainderExtremal
import CFT.Spherical.WedgeHorizonDefectC1Zero
import CFT.Spherical.WedgeHorizonFirstZero

open Real Set Filter Topology
open CFT.WedgeDefectRemainderExtremal
open CFT.WedgeDefectTransport
open CFT.WedgeDefectSourceDeriv
open CFT.WedgeDefectC1Zero
open CFT.WedgeFirstZero
open CFT.RNLogDeriv

namespace CFT.WedgeDefectB1W0Zero

/-- B1|_{W=0} の極端版の分子の四次式 P(r) = −3r⁴ + r²r₊² + Q。 -/
noncomputable def defectQuarticB1W0 (r rp : ℝ) : ℝ :=
  -3 * r ^ 4 + r ^ 2 * rp ^ 2 + defectRemainderQuadCoeff r rp

/-- 四次式の展開形。 -/
theorem defectQuarticB1W0_eq {r rp : ℝ} :
    defectQuarticB1W0 r rp
      = -3 * r ^ 4 + r ^ 2 * rp ^ 2 + 9 * r ^ 2 - 10 * r * rp + 3 * rp ^ 2 := by
  unfold defectQuarticB1W0 defectRemainderQuadCoeff
  ring

/-- r = 0 での値：P(0) = 3r₊²。 -/
theorem defectQuarticB1W0_at_zero {rp : ℝ} :
    defectQuarticB1W0 0 rp = 3 * rp ^ 2 := by
  unfold defectQuarticB1W0 defectRemainderQuadCoeff
  ring

/-- r = r₊ での値：P(r₊) = 2r₊²(1 − r₊²)。地平線での符号は r₊ と 1 の大小で決まる。 -/
theorem defectQuarticB1W0_at_rp {rp : ℝ} :
    defectQuarticB1W0 rp rp = 2 * rp ^ 2 * (1 - rp ^ 2) := by
  unfold defectQuarticB1W0 defectRemainderQuadCoeff
  ring

/-- P(0) > 0（r₊ ≠ 0）。 -/
theorem defectQuarticB1W0_pos_at_zero {rp : ℝ} (hrp : rp ≠ 0) :
    0 < defectQuarticB1W0 0 rp := by
  rw [defectQuarticB1W0_at_zero]
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero hrp)

/-- r₊ < 1 なら P(r₊) > 0。 -/
theorem defectQuarticB1W0_pos_at_rp_of_lt_one {rp : ℝ} (hrp : 0 < rp) (h1 : rp < 1) :
    0 < defectQuarticB1W0 rp rp := by
  rw [defectQuarticB1W0_at_rp]
  have hsq : rp ^ 2 < 1 := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 - rp by linarith)
      (show (0 : ℝ) < 1 + rp by linarith)]
  have h2 : 0 < 1 - rp ^ 2 := by linarith
  exact mul_pos (mul_pos (by norm_num) (pow_pos hrp 2)) h2

/-- r₊ > 1 なら P(r₊) < 0。 -/
theorem defectQuarticB1W0_neg_at_rp_of_gt_one {rp : ℝ} (h1 : 1 < rp) :
    defectQuarticB1W0 rp rp < 0 := by
  rw [defectQuarticB1W0_at_rp]
  have hsq : 1 < rp ^ 2 := by
    nlinarith [mul_pos (show (0 : ℝ) < rp - 1 by linarith)
      (show (0 : ℝ) < rp + 1 by linarith)]
  have h2 : 1 - rp ^ 2 < 0 := by linarith
  exact mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) (pow_pos (show (0 : ℝ) < rp by linarith) 2)) h2

/-- r = 2 での値：P(2) = −12 + 7r₊² − 20r₊。 -/
theorem defectQuarticB1W0_at_two {rp : ℝ} :
    defectQuarticB1W0 2 rp = -12 + 7 * rp ^ 2 - 20 * rp := by
  unfold defectQuarticB1W0 defectRemainderQuadCoeff
  ring

/-- 0 ≤ r₊ ≤ 1 なら P(2) < 0（外側の零点の存在に使う右端の符号）。 -/
theorem defectQuarticB1W0_neg_at_two {rp : ℝ} (h0 : 0 ≤ rp) (h1 : rp ≤ 1) :
    defectQuarticB1W0 2 rp < 0 := by
  rw [defectQuarticB1W0_at_two]
  nlinarith [mul_nonneg h0 (show (0 : ℝ) ≤ 20 - 7 * rp by linarith)]

/-- 四次式は r について連続。 -/
theorem defectQuarticB1W0_continuous {rp : ℝ} :
    Continuous fun r => defectQuarticB1W0 r rp := by
  unfold defectQuarticB1W0 defectRemainderQuadCoeff
  continuity

/-- B1|_{W=0} の極端版の零点：B1 = 0 ⟺ P(r) = 0。 -/
theorem defectRemainderCoeffB1_extremal_at_zero_eq_zero_iff {rp r : ℝ} (hr : r ≠ 0)
    (hrp : r ≠ rp) :
    defectRemainderCoeffB1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r 0 = 0
      ↔ defectQuarticB1W0 r rp = 0 := by
  rw [defectRemainderCoeffB1_extremal_at_zero hr hrp, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 (sub_ne_zero.mpr hrp))
  · intro h
    left
    exact h

/-- 四次式の零点は地平線の外側に存在する（r₊ < 1 の場合）。 -/
theorem defectQuarticB1W0_exists_zero_outside {rp : ℝ} (hrp : 0 < rp) (h1 : rp < 1) :
    ∃ r₀ ∈ Ioo rp 2, defectQuarticB1W0 r₀ rp = 0 :=
  exists_zero_of_sign_change (by linarith)
    defectQuarticB1W0_continuous.continuousOn
    (defectQuarticB1W0_pos_at_rp_of_lt_one hrp h1)
    (defectQuarticB1W0_neg_at_two (le_of_lt hrp) (le_of_lt h1))

/-- B1|_{W=0} は r₊ < 1 では地平線の外側で消える点を持つ。 -/
theorem defectRemainderCoeffB1_exists_zero_outside {rp : ℝ} (hrp : 0 < rp)
    (h1 : rp < 1) :
    ∃ r₀ ∈ Ioo rp 2,
      defectRemainderCoeffB1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r₀ 0 = 0 := by
  obtain ⟨r₀, hr₀, hzero⟩ := defectQuarticB1W0_exists_zero_outside hrp h1
  refine ⟨r₀, hr₀, ?_⟩
  have hr0 : r₀ ≠ 0 := ne_of_gt (lt_trans hrp hr₀.1)
  have hrne : r₀ ≠ rp := ne_of_gt hr₀.1
  exact (defectRemainderCoeffB1_extremal_at_zero_eq_zero_iff hr0 hrne).mpr hzero

/-- 四次式の零点は地平線の内側に存在する（r₊ > 1 の場合）。 -/
theorem defectQuarticB1W0_exists_zero_inside {rp : ℝ} (h1 : 1 < rp) :
    ∃ r₀ ∈ Ioo 0 rp, defectQuarticB1W0 r₀ rp = 0 :=
  exists_zero_of_sign_change (by linarith)
    defectQuarticB1W0_continuous.continuousOn
    (defectQuarticB1W0_pos_at_zero (ne_of_gt (show (0 : ℝ) < rp by linarith)))
    (defectQuarticB1W0_neg_at_rp_of_gt_one h1)

/-- B1|_{W=0} は r₊ > 1 では地平線の内側で消える点を持つ。 -/
theorem defectRemainderCoeffB1_exists_zero_inside {rp : ℝ} (h1 : 1 < rp) :
    ∃ r₀ ∈ Ioo 0 rp,
      defectRemainderCoeffB1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r₀ 0 = 0 := by
  obtain ⟨r₀, hr₀, hzero⟩ := defectQuarticB1W0_exists_zero_inside h1
  refine ⟨r₀, hr₀, ?_⟩
  have hr0 : r₀ ≠ 0 := ne_of_gt hr₀.1
  have hrne : r₀ ≠ rp := ne_of_lt hr₀.2
  exact (defectRemainderCoeffB1_extremal_at_zero_eq_zero_iff hr0 hrne).mpr hzero

/-- r₊ = 1 では四次式は C1 の三次式で因数分解される：P(r) = −(r − 1)·N(r)。 -/
theorem defectQuarticB1W0_at_rp_one {r : ℝ} :
    defectQuarticB1W0 r 1 = -(r - 1) * defectCubicC1 r 1 := by
  unfold defectQuarticB1W0 defectRemainderQuadCoeff defectCubicC1
  ring

/-- r₊ = 1、r ≥ 0 では P(r) = 0 ⟺ r = 1（地平線そのもの）。 -/
theorem defectQuarticB1W0_eq_zero_iff_of_rp_eq_one {r : ℝ} (hr : 0 ≤ r) :
    defectQuarticB1W0 r 1 = 0 ↔ r = 1 := by
  rw [defectQuarticB1W0_at_rp_one, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · have h' : r - 1 = 0 := neg_eq_zero.mp h
      linarith
    · exact absurd h (defectCubicC1_ne_zero (by norm_num) hr)
  · intro h
    left
    rw [h]
    norm_num

end CFT.WedgeDefectB1W0Zero
