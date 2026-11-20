/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **残余 R の係数 C1 の三次式の解析**。前段
  （`WedgeHorizonDefectCoeffZeros`）で C3・C2 の零点と Q の正値性が
  閉じ、地平線の外側では C2・C3・Q は消えないことが確定した。残る
  係数の零点は C1 = 0 の三次式と B1|_{W=0} = 0 の四次式だけである。
  ここでは C1 の分子の三次式
    N(r) = 3r³ + 3r²r₊ − 7r·r₊² + 3r₊³
  を解析する。無次元化 x = r/r₊ と置いた三次式
    g(x) = 3x³ + 3x² − 7x + 3
  の判別式は −1356 < 0（sympy で確認）なので実根はちょうど一つで、
  それは負（x ≈ −2.2406）である。Lean では判別式の議論ではなく、
  平方和分解
    N(r) = 3r(r − r₊/2)² + 6r₊(r − 31r₊/48)² + (191/384)r₊³
  により、r₊ > 0、r ≥ 0 のもとで N(r) > 0 を直接証明する（r = 0 では
  N = 3r₊³、r = r₊ では N = 2r₊³ ともに正）。帰結として、地平線の
  外側（0 < r₊ < r）では C1 > 0、地平線の内側（0 < r < r₊）では
  C1 < 0 であり、C1 は正の領域では決して 0 にならない。すなわち
  C1 の零点は正の領域には存在せず、R = 0 の判定において地平線の
  外側では C1 も消えない。残る係数の零点は B1|_{W=0} = 0 の四次式
  だけになった。平方和分解と根の位置は sympy による明示計算でも確認済み。
-/
import CFT.Spherical.WedgeHorizonDefectRemainderExtremal

open Real Set Filter Topology
open CFT.WedgeDefectRemainderExtremal
open CFT.WedgeDefectTransport
open CFT.WedgeDefectSourceDeriv
open CFT.RNLogDeriv

namespace CFT.WedgeDefectC1Zero

/-- C1 の極端版の分子の三次式 N(r) = 3r³ + 3r²r₊ − 7r·r₊² + 3r₊³。 -/
noncomputable def defectCubicC1 (r rp : ℝ) : ℝ :=
  3 * r ^ 3 + 3 * r ^ 2 * rp - 7 * r * rp ^ 2 + 3 * rp ^ 3

/-- 三次式の平方和分解。定数項 (191/384)r₊³ が正であることが要点。 -/
theorem defectCubicC1_eq_sos {r rp : ℝ} :
    defectCubicC1 r rp
      = 3 * r * (r - rp / 2) ^ 2 + 6 * rp * (r - 31 * rp / 48) ^ 2
        + (191 / 384) * rp ^ 3 := by
  unfold defectCubicC1
  ring

/-- 三次式の正値性：r₊ > 0、r ≥ 0 のもとで N(r) > 0。 -/
theorem defectCubicC1_pos {r rp : ℝ} (hrp : 0 < rp) (hr : 0 ≤ r) :
    0 < defectCubicC1 r rp := by
  rw [defectCubicC1_eq_sos]
  have h1 : 0 ≤ 3 * r * (r - rp / 2) ^ 2 := by positivity
  have h2 : 0 ≤ 6 * rp * (r - 31 * rp / 48) ^ 2 := by positivity
  have h3 : 0 < (191 / 384) * rp ^ 3 := by positivity
  linarith

/-- 三次式は r₊ > 0、r ≥ 0 のもとで決して 0 にならない。 -/
theorem defectCubicC1_ne_zero {r rp : ℝ} (hrp : 0 < rp) (hr : 0 ≤ r) :
    defectCubicC1 r rp ≠ 0 :=
  ne_of_gt (defectCubicC1_pos hrp hr)

/-- r = 0 での値：N(0) = 3r₊³。 -/
theorem defectCubicC1_at_zero {rp : ℝ} :
    defectCubicC1 0 rp = 3 * rp ^ 3 := by
  unfold defectCubicC1
  ring

/-- r = r₊ での値：N(r₊) = 2r₊³（地平線で C1 の分子は消えない）。 -/
theorem defectCubicC1_at_rp {rp : ℝ} :
    defectCubicC1 rp rp = 2 * rp ^ 3 := by
  unfold defectCubicC1
  ring

/-- 三次式の零点は負の領域にしかない：r₊ > 0 で N(r) = 0 ならば r < 0。
    すなわち C1 の零点は正の領域には存在しない（判別式 −1356 < 0 の
    Lean 版の帰結として、平方和分解から直接出る方向）。 -/
theorem defectCubicC1_eq_zero_lt {r rp : ℝ} (hrp : 0 < rp)
    (h : defectCubicC1 r rp = 0) : r < 0 := by
  by_contra hcon
  push_neg at hcon
  exact defectCubicC1_ne_zero hrp hcon h

/-- C1 の極端版の零点：C1 = 0 ⟺ N(r) = 0。 -/
theorem defectRemainderCoeffC1_extremal_eq_zero_iff {rp r : ℝ} (hr : r ≠ 0)
    (hrp : r ≠ rp) :
    defectRemainderCoeffC1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) r = 0
      ↔ defectCubicC1 r rp = 0 := by
  rw [defectRemainderCoeffC1_extremal hr hrp, div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · rcases mul_eq_zero.mp h with h2 | h2
      · norm_num at h2
      · exact h2
    · exact absurd h (pow_ne_zero 3 (sub_ne_zero.mpr hrp))
  · intro h
    left
    have h' : (3 * r ^ 3 + 3 * r ^ 2 * rp - 7 * r * rp ^ 2 + 3 * rp ^ 3) = 0 := h
    rw [h']
    simp

/-- C1 は正の領域で 0 にならない：r₊ > 0、r > 0、r ≠ r₊ ならば C1 ≠ 0。 -/
theorem defectRemainderCoeffC1_extremal_ne_zero_of_pos {rp r : ℝ}
    (hrp : 0 < rp) (hr : 0 < r) (hrne : r ≠ rp) :
    defectRemainderCoeffC1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) r ≠ 0 := by
  intro hzero
  rw [defectRemainderCoeffC1_extremal_eq_zero_iff (ne_of_gt hr) hrne] at hzero
  exact defectCubicC1_ne_zero hrp (le_of_lt hr) hzero

/-- C1 は地平線の外側で正：0 < r₊ < r ならば C1 > 0。 -/
theorem defectRemainderCoeffC1_extremal_pos_of_gt {rp r : ℝ} (hrp : 0 < rp)
    (h : rp < r) :
    0 < defectRemainderCoeffC1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) r := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans hrp h)
  have hrne : r ≠ rp := ne_of_gt h
  rw [defectRemainderCoeffC1_extremal hr0 hrne]
  apply div_pos
  · exact mul_pos (by norm_num)
      (defectCubicC1_pos hrp (le_of_lt (lt_trans hrp h)))
  · exact pow_pos (sub_pos.mpr h) 3

/-- C1 は地平線の内側で負：0 < r < r₊ ならば C1 < 0。 -/
theorem defectRemainderCoeffC1_extremal_neg_of_lt {rp r : ℝ} (hrp : 0 < rp)
    (hr : 0 < r) (hlt : r < rp) :
    defectRemainderCoeffC1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) r < 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrne : r ≠ rp := ne_of_lt hlt
  rw [defectRemainderCoeffC1_extremal hr0 hrne]
  have hden : (r - rp) ^ 3 < 0 := by
    have hsq : 0 < (r - rp) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hlt))
    have hneg : r - rp < 0 := sub_neg.mpr hlt
    calc (r - rp) ^ 3 = (r - rp) ^ 2 * (r - rp) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hsq hneg
  exact div_neg_of_pos_of_neg
    (mul_pos (by norm_num) (defectCubicC1_pos hrp (le_of_lt hr))) hden

end CFT.WedgeDefectC1Zero
