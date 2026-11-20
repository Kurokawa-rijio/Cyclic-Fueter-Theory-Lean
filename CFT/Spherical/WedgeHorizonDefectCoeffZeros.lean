/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **残余 R の係数の極端 RN 版の零点の解析**。前段
  （`WedgeHorizonDefectRemainderExtremal`）で証明された極端版の明示公式
    C1 = 2(3r³ + 3r²r₊ − 7r·r₊² + 3r₊³)/(r−r₊)³、
    C2 = −2(r² + r·r₊ − r₊²)/(r−r₊)²、
    C3 = 2(2r−r₊)/(r−r₊)、
    B1 = (Q·(W⁴ − 2W²) + (−3r⁴ + r²r₊² + Q))/(r−r₊)²、
      ただし Q = 9r² − 10r·r₊ + 3r₊²
  について、軽い零点（C3・C2）と Q の正値性を証明する：
    C3 = 0 ⟺ r = r₊/2（地平線の内側）、
    C2 = 0 ⟺ r² + r·r₊ − r₊² = 0、
    r₊ > 0、r > 0 のもとでは C2 = 0 ⟺ r = r₊(√5−1)/2（黄金比の共役、
    地平線の内側）、
    Q = 9(r − 5r₊/9)² + (2/9)r₊² > 0（r₊ ≠ 0；判別式 −8r₊² < 0）。
  帰結として、地平線の外側（r > r₊ > 0）では C3 > 0、C2 ≠ 0 であり、
  Q ≠ 0 である。すなわち C2・C3・Q の零点はすべて地平線の内側か
  存在せず、R = 0 の判定において地平線の外側ではこれらの係数は
  消えない。C1 = 0 の三次式と B1|_{W=0} = 0 の四次式の解析は
  次の段に残す。零点の位置は sympy による明示計算でも確認済み。
-/
import CFT.Spherical.WedgeHorizonDefectRemainderExtremal

open Real Set Filter Topology
open CFT.WedgeDefectRemainderExtremal
open CFT.WedgeDefectTransport
open CFT.RNLogDeriv

namespace CFT.WedgeDefectCoeffZeros

/-- C3 の極端版の零点：C3 = 0 ⟺ r = r₊/2。 -/
theorem defectRemainderCoeffC3_extremal_eq_zero_iff {rp r : ℝ} (hr : r ≠ 0)
    (hrp : r ≠ rp) :
    defectRemainderCoeffC3 (rnLogDeriv rp rp) r = 0 ↔ r = rp / 2 := by
  rw [defectRemainderCoeffC3_extremal hr hrp, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · have h2 : 2 * r - rp = 0 := by
        rcases mul_eq_zero.mp h with h2 | h2
        · norm_num at h2
        · exact h2
      linarith
    · exact absurd h (sub_ne_zero.mpr hrp)
  · intro h
    left
    rw [h]
    ring

/-- C2 の極端版の零点：C2 = 0 ⟺ r² + r·r₊ − r₊² = 0。 -/
theorem defectRemainderCoeffC2_extremal_eq_zero_iff {rp r : ℝ} (hr : r ≠ 0)
    (hrp : r ≠ rp) :
    defectRemainderCoeffC2 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r = 0
      ↔ r ^ 2 + r * rp - rp ^ 2 = 0 := by
  rw [defectRemainderCoeffC2_extremal hr hrp, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · have h2 : r ^ 2 + r * rp - rp ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h2 | h2
        · norm_num at h2
        · exact h2
      exact h2
    · exact absurd h (pow_ne_zero 2 (sub_ne_zero.mpr hrp))
  · intro h
    left
    rw [h]
    simp

/-- C2 の極端版の零点（正の領域）：r₊ > 0、r > 0 のもとでは
    C2 = 0 ⟺ r = r₊(√5−1)/2。二次式の因数分解
    (r − r₊(√5−1)/2)(r + r₊(√5+1)/2) = r² + r·r₊ − r₊² による。
    もう一つの因子は正の領域では 0 にならない。 -/
theorem defectRemainderCoeffC2_extremal_eq_zero_of_pos {rp r : ℝ}
    (hrp : 0 < rp) (hr : 0 < r) (hrne : r ≠ rp) :
    defectRemainderCoeffC2 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r = 0
      ↔ r = rp * (Real.sqrt 5 - 1) / 2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    rw [defectRemainderCoeffC2_extremal_eq_zero_iff hr0 hrne] at h
    have hfactor : (r - rp * (Real.sqrt 5 - 1) / 2)
        * (r + rp * (Real.sqrt 5 + 1) / 2) = 0 := by
      linear_combination h - (rp ^ 2 / 4) * hs
    rcases mul_eq_zero.mp hfactor with h1 | h1
    · linarith
    · have h2 : 0 < rp * (Real.sqrt 5 + 1) / 2 := by positivity
      linarith
  · intro h
    rw [defectRemainderCoeffC2_extremal_eq_zero_iff hr0 hrne]
    have hzero : r ^ 2 + r * rp - rp ^ 2 = 0 := by
      rw [h]
      linear_combination (rp ^ 2 / 4) * hs
    exact hzero

/-- Q の平方完成：Q = 9(r − 5r₊/9)² + (2/9)r₊²。 -/
theorem defectRemainderQuadCoeff_eq_sq {r rp : ℝ} :
    defectRemainderQuadCoeff r rp
      = 9 * (r - 5 * rp / 9) ^ 2 + (2 / 9) * rp ^ 2 := by
  unfold defectRemainderQuadCoeff
  ring

/-- Q の正値性：r₊ ≠ 0 ならば Q > 0。r についての判別式は −8r₊² < 0。 -/
theorem defectRemainderQuadCoeff_pos {r rp : ℝ} (hrp : rp ≠ 0) :
    0 < defectRemainderQuadCoeff r rp := by
  rw [defectRemainderQuadCoeff_eq_sq]
  have h1 : 0 ≤ 9 * (r - 5 * rp / 9) ^ 2 := by positivity
  have h2 : 0 < (2 / 9) * rp ^ 2 := by
    have hsq : 0 < rp ^ 2 := sq_pos_of_ne_zero hrp
    linarith
  linarith

/-- Q は r₊ ≠ 0 のもとで決して 0 にならない。 -/
theorem defectRemainderQuadCoeff_ne_zero {r rp : ℝ} (hrp : rp ≠ 0) :
    defectRemainderQuadCoeff r rp ≠ 0 :=
  ne_of_gt (defectRemainderQuadCoeff_pos hrp)

/-- C3 は地平線の外側で正：0 < r₊ < r ならば C3 > 0。 -/
theorem defectRemainderCoeffC3_extremal_pos_of_gt {rp r : ℝ} (hrp : 0 < rp)
    (h : rp < r) :
    0 < defectRemainderCoeffC3 (rnLogDeriv rp rp) r := by
  rw [defectRemainderCoeffC3_extremal (ne_of_gt (lt_trans hrp h)) (ne_of_gt h)]
  exact div_pos (by linarith) (by linarith)

/-- C3 の零点は地平線の内側にある：C3 = 0 ならば r < r₊。 -/
theorem defectRemainderCoeffC3_extremal_zero_lt {rp r : ℝ} (hrp : 0 < rp)
    (hr : r ≠ 0) (hrne : r ≠ rp)
    (h : defectRemainderCoeffC3 (rnLogDeriv rp rp) r = 0) :
    r < rp := by
  rw [defectRemainderCoeffC3_extremal_eq_zero_iff hr hrne] at h
  linarith

/-- C2 は地平線の外側で 0 にならない：0 < r₊ < r ならば C2 ≠ 0。 -/
theorem defectRemainderCoeffC2_extremal_ne_zero_of_gt {rp r : ℝ} (hrp : 0 < rp)
    (h : rp < r) :
    defectRemainderCoeffC2 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r ≠ 0 := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans hrp h)
  have hrne : r ≠ rp := ne_of_gt h
  intro hzero
  rw [defectRemainderCoeffC2_extremal_eq_zero_iff hr0 hrne] at hzero
  have h1 : 0 < r ^ 2 - rp ^ 2 := by
    have hprod : 0 < (r - rp) * (r + rp) := mul_pos (sub_pos.mpr h) (by linarith)
    nlinarith [hprod]
  have h2 : 0 < r * rp := mul_pos (lt_trans hrp h) hrp
  linarith

/-- C2 の零点は地平線の内側にある：r₊ > 0、r > 0 のもとで C2 = 0 ならば
    r < r₊（√5 < 3 より (√5−1)/2 < 1）。 -/
theorem defectRemainderCoeffC2_extremal_zero_lt {rp r : ℝ} (hrp : 0 < rp)
    (hr : 0 < r) (hrne : r ≠ rp)
    (h : defectRemainderCoeffC2 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r = 0) :
    r < rp := by
  rw [defectRemainderCoeffC2_extremal_eq_zero_of_pos hrp hr hrne] at h
  have hsqrt : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hmul : rp * Real.sqrt 5 < rp * 3 := mul_lt_mul_of_pos_left hsqrt hrp
  linarith

end CFT.WedgeDefectCoeffZeros
