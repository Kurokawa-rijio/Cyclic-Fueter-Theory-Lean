/-
  12-8 (b) の軽い部分：f の二重ゼロと T = 0 の代数

  RN の計量関数 f(r) = (r − r₊)(r − r₋)/r² について：
  * f(r₊) = 0（地平線）。
  * f′(r₊) = (r₊ − r₋)/r₊²（既存の `CFT.Thermo.rn_slope`）。
  * f′(r₊) = 0 ⟺ r₊ = r₋（二重ゼロ ⟺ 極端）。
  * T = f′(r₊)/(4π) = (r₊ − r₋)/(4πr₊²)（6-2 の `CFT.Thermo.rn_temperature`）なので、
    T = 0 ⟺ r₊ = r₋。非極限では一次ゼロで T > 0。
  * 極端の場合 f(r) = (r − r₊)²/r² ≥ 0 で、地平線近傍では
    f(r₊ + ε) = ε²/(r₊ + ε)² と二次で消える（一次ゼロではない）。
  * 因数形と標準形 1 − 2M/r + Q²/r² の対応（r₊ + r₋ = 2M、r₊r₋ = Q²）。

  これが (b)「Ω のゼロの位数による分類」の温度側の代数部分。
  くさび EYM 系の形での分類そのもの（近地平線極限 AdS₂ × S² など）は残り。
-/
import CFT.Quantum.BlackHoleThermodynamics
import CFT.Quantum.ReissnerNordstromTemperature

namespace CFT.RNExtremalZero

open Real

/-- RN の計量関数 f(r) = (r − r₊)(r − r₋)/r²（因数形）。 -/
noncomputable def rnF (rp rm r : ℝ) : ℝ := (r - rp) * (r - rm) / r ^ 2

/-- 地平線では f = 0。 -/
theorem rnF_at_rp (rp rm : ℝ) : rnF rp rm rp = 0 := by
  simp [rnF]

/-- 因数形と標準形の対応：f(r) = 1 − (r₊ + r₋)/r + (r₊r₋)/r²。 -/
theorem rnF_eq_standard (rp rm r : ℝ) (hr : r ≠ 0) :
    rnF rp rm r = 1 - (rp + rm) / r + (rp * rm) / r ^ 2 := by
  simp only [rnF]
  field_simp
  ring

/-- r₊ + r₋ = 2M、r₊r₋ = Q² のとき、標準の RN 形 1 − 2M/r + Q²/r²。 -/
theorem rnF_eq_standard_MQ (rp rm r M Q : ℝ) (hr : r ≠ 0)
    (hsum : rp + rm = 2 * M) (hprod : rp * rm = Q ^ 2) :
    rnF rp rm r = 1 - 2 * M / r + Q ^ 2 / r ^ 2 := by
  rw [rnF_eq_standard rp rm r hr, hsum, hprod]

/-- f′(r₊) = (r₊ − r₋)/r₊²（`rn_slope` の言い換え）。 -/
theorem rnF_hasDerivAt (rp rm : ℝ) (hp : rp ≠ 0) :
    HasDerivAt (rnF rp rm) ((rp - rm) / rp ^ 2) rp :=
  CFT.Thermo.rn_slope rp rm hp

/-- f′(r₊) の `deriv` 形。 -/
theorem rnF_deriv_at_rp (rp rm : ℝ) (hp : rp ≠ 0) :
    deriv (rnF rp rm) rp = (rp - rm) / rp ^ 2 :=
  (rnF_hasDerivAt rp rm hp).deriv

/-- f′(r₊) = 0 ⟺ r₊ = r₋（二重ゼロ ⟺ 極端）。 -/
theorem rnF_deriv_at_rp_eq_zero_iff (rp rm : ℝ) (hp : rp ≠ 0) :
    deriv (rnF rp rm) rp = 0 ↔ rp = rm := by
  rw [rnF_deriv_at_rp rp rm hp, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact sub_eq_zero.mp h
    · exact absurd h (pow_ne_zero 2 hp)
  · intro h
    left
    exact sub_eq_zero.mpr h

/-- 非極限では f′(r₊) ≠ 0（一次ゼロ）。 -/
theorem rnF_deriv_at_rp_ne_zero_of_ne (rp rm : ℝ) (hp : rp ≠ 0) (hne : rp ≠ rm) :
    deriv (rnF rp rm) rp ≠ 0 := by
  rw [rnF_deriv_at_rp rp rm hp]
  exact div_ne_zero (sub_ne_zero.mpr hne) (pow_ne_zero 2 hp)

/-- 極端の場合：f(r) = (r − r₊)²/r²。 -/
theorem rnF_extremal (rp r : ℝ) : rnF rp rp r = (r - rp) ^ 2 / r ^ 2 := by
  simp only [rnF, ← pow_two]

/-- 極端の場合：f(r) ≥ 0。 -/
theorem rnF_extremal_nonneg (rp r : ℝ) : 0 ≤ rnF rp rp r := by
  rw [rnF_extremal]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- 極端の場合の地平線近傍の形：f(r₊ + ε) = ε²/(r₊ + ε)²（二次で消える）。 -/
theorem rnF_extremal_near_horizon (rp ε : ℝ) :
    rnF rp rp (rp + ε) = ε ^ 2 / (rp + ε) ^ 2 := by
  rw [rnF_extremal, add_sub_cancel_left]

/-- T = f′(r₊)/(4π)。 -/
theorem rn_temperature_eq_fderiv (rp rm : ℝ) (hp : rp ≠ 0) :
    deriv (rnF rp rm) rp / (4 * π) = (rp - rm) / (4 * π * rp ^ 2) := by
  rw [rnF_deriv_at_rp rp rm hp]
  exact CFT.Thermo.rn_temperature rp rm

/-- T = 0 ⟺ r₊ = r₋。 -/
theorem rn_temperature_zero_iff (rp rm : ℝ) (hp : rp ≠ 0) :
    (rp - rm) / (4 * π * rp ^ 2) = 0 ↔ rp = rm := by
  have hd : (4 * π * rp ^ 2) ≠ 0 := by
    have h1 : (0:ℝ) < 4 * π := by positivity
    have h2 : (0:ℝ) < rp ^ 2 := sq_pos_of_ne_zero hp
    exact ne_of_gt (mul_pos h1 h2)
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact sub_eq_zero.mp h
    · exact absurd h hd
  · intro h
    left
    exact sub_eq_zero.mpr h

/-- まとめ：二重ゼロ ⟺ T = 0。 -/
theorem rn_double_zero_iff_temperature_zero (rp rm : ℝ) (hp : rp ≠ 0) :
    deriv (rnF rp rm) rp = 0 ↔ (rp - rm) / (4 * π * rp ^ 2) = 0 := by
  rw [rnF_deriv_at_rp_eq_zero_iff rp rm hp, rn_temperature_zero_iff rp rm hp]

/-- 非極限では一次ゼロで温度は正（6-2 の `rn_temperature_pos` の言い換え）。 -/
theorem rn_simple_zero_pos_temperature (rp rm : ℝ) (hp : 0 < rp) (hm : rm < rp) :
    deriv (rnF rp rm) rp ≠ 0 ∧ 0 < (rp - rm) / (4 * π * rp ^ 2) :=
  ⟨rnF_deriv_at_rp_ne_zero_of_ne rp rm (ne_of_gt hp) (ne_of_gt hm),
   CFT.Thermo.rn_temperature_pos rp rm hp hm⟩

/-- まとめ：地平線での分類。 -/
theorem rn_double_zero_classification (rp rm : ℝ) (hp : rp ≠ 0) :
    rnF rp rm rp = 0 ∧ (deriv (rnF rp rm) rp = 0 ↔ rp = rm) ∧
    ((rp - rm) / (4 * π * rp ^ 2) = 0 ↔ rp = rm) := by
  exact ⟨rnF_at_rp rp rm, rnF_deriv_at_rp_eq_zero_iff rp rm hp,
    rn_temperature_zero_iff rp rm hp⟩

end CFT.RNExtremalZero
