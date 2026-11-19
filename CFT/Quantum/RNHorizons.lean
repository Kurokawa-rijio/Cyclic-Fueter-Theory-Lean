/-
  命題集 `LEAN_GAP_TREES.md` 12-7.6（荷電セクター）・11-13（RN）の残り：
  「地平線 r± の扱い」。

  これまで RN の計量関数 f(r) = (r − r₊)(r − r₋)/r² は、r₊・r₋ を
  与えられたパラメータとして扱ってきた（`RNExtremalDoubleZero`、
  `BlackHoleThermodynamics` の `rn_slope`、6-2 の温度公式）。
  ここでは質量 M・電荷 Q から地平線を明示的に構成する：

    r₊ = M + √(M² − Q²),   r₋ = M − √(M² − Q²).

  示すこと：
  * Vieta の関係 r₊ + r₋ = 2M、r₊r₋ = Q²（`rPlus_add_rMinus`・
    `rPlus_mul_rMinus`）。これにより因数形が標準形
    1 − 2M/r + Q²/r² に一致する（`rnF_horizons_eq_standard`、
    `RNExtremalDoubleZero.rnF_eq_standard_MQ` の当てはめ）。
  * 標準形の零点はちょうど {r₊, r₋} である
    （`rnF_horizon_iff`）。これが「地平線の扱い」の本体。
  * 順序と正値性：0 < M なら 0 ≤ r₋ ≤ r₊、r₊ > 0。非極端
    （Q² < M²）なら r₋ < r₊ かつ r₋ > 0（Q ≠ 0 のとき）。
  * 判別式の三分法：極端（M² = Q²）では r₊ = r₋ = M
    （`extremal_horizons`、二重ゼロ ⟺ 極端は `extremal_iff_horizons_eq`）；
    裸（M² < Q²）では標準形は r ≠ 0 でつねに正で、地平線は存在しない
    （`standard_form_pos_of_naked`）。
  * Q = 0 では r₊ = 2M、r₋ = 0 に帰着する
    （`schwarzschild_horizons`、6-1 のシュワルツシルト温度への接続）。
  * 温度の明示式：非極端では T = √(M² − Q²)/(2π r₊²)
    （`rn_temperature_explicit`）、とくに T > 0
    （`rn_temperature_pos_explicit`）。6-2 の `rn_temperature` との
    整合（`rn_temperature_horizons`）も確認する。

  残り：くさび EYM 系への Einstein–Maxwell ソース項の導入
  （Abelian 射影、W 場側への埋め込み）。地平線の扱いはここで閉じる。
-/
import CFT.Quantum.RNExtremalDoubleZero
import CFT.Quantum.ReissnerNordstromTemperature

namespace CFT.RNHorizons

open Real

/-- 外側の地平線：r₊ = M + √(M² − Q²)。 -/
noncomputable def rPlus (M Q : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - Q ^ 2)

/-- 内側の地平線：r₋ = M − √(M² − Q²)。 -/
noncomputable def rMinus (M Q : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - Q ^ 2)

/-- Vieta：r₊ + r₋ = 2M。 -/
theorem rPlus_add_rMinus (M Q : ℝ) : rPlus M Q + rMinus M Q = 2 * M := by
  unfold rPlus rMinus
  ring

/-- Vieta：r₊r₋ = Q²（判別式が非負のとき）。 -/
theorem rPlus_mul_rMinus {M Q : ℝ} (hdisc : 0 ≤ M ^ 2 - Q ^ 2) :
    rPlus M Q * rMinus M Q = Q ^ 2 := by
  have hs : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := Real.sq_sqrt hdisc
  unfold rPlus rMinus
  have h : (M + Real.sqrt (M ^ 2 - Q ^ 2)) * (M - Real.sqrt (M ^ 2 - Q ^ 2))
      = M ^ 2 - Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 := by ring
  rw [h, hs]
  ring

/-- r₊ − r₋ = 2√(M² − Q²)。 -/
theorem rPlus_sub_rMinus (M Q : ℝ) :
    rPlus M Q - rMinus M Q = 2 * Real.sqrt (M ^ 2 - Q ^ 2) := by
  unfold rPlus rMinus
  ring

/-- 因数形は標準の RN 形 1 − 2M/r + Q²/r² に一致する。 -/
theorem rnF_horizons_eq_standard {M Q r : ℝ} (hr : r ≠ 0)
    (hdisc : 0 ≤ M ^ 2 - Q ^ 2) :
    CFT.RNExtremalZero.rnF (rPlus M Q) (rMinus M Q) r
      = 1 - 2 * M / r + Q ^ 2 / r ^ 2 :=
  CFT.RNExtremalZero.rnF_eq_standard_MQ _ _ r M Q hr
    (rPlus_add_rMinus M Q) (rPlus_mul_rMinus hdisc)

/-- 標準形の零点はちょうど {r₊, r₋} である（地平線の扱いの本体）。 -/
theorem rnF_horizon_iff {M Q r : ℝ} (hr : r ≠ 0) :
    CFT.RNExtremalZero.rnF (rPlus M Q) (rMinus M Q) r = 0 ↔
      r = rPlus M Q ∨ r = rMinus M Q := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp only [CFT.RNExtremalZero.rnF, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hr2
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

/-- 0 < M なら r₊ > 0。 -/
theorem rPlus_pos {M Q : ℝ} (hM : 0 < M) : 0 < rPlus M Q := by
  have h : M ≤ rPlus M Q := by
    unfold rPlus
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  linarith

/-- 0 < M、判別式が非負なら r₋ ≥ 0。 -/
theorem rMinus_nonneg {M Q : ℝ} (hM : 0 < M) (hdisc : 0 ≤ M ^ 2 - Q ^ 2) :
    0 ≤ rMinus M Q := by
  have h1 : Real.sqrt (M ^ 2 - Q ^ 2) ≤ Real.sqrt (M ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Q])
  rw [Real.sqrt_sq hM.le] at h1
  unfold rMinus
  linarith

/-- 非極端（Q² < M²）なら r₋ < r₊。 -/
theorem rMinus_lt_rPlus {M Q : ℝ} (hQ : Q ^ 2 < M ^ 2) :
    rMinus M Q < rPlus M Q := by
  have hs : (0 : ℝ) < Real.sqrt (M ^ 2 - Q ^ 2) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hQ)
  unfold rPlus rMinus
  linarith

/-- Q ≠ 0（かつ 0 < M）なら r₋ > 0。 -/
theorem rMinus_pos {M Q : ℝ} (hM : 0 < M) (hQ : Q ≠ 0) :
    0 < rMinus M Q := by
  have hQ2 : (0 : ℝ) < Q ^ 2 := sq_pos_of_ne_zero hQ
  have hlt : Real.sqrt (M ^ 2 - Q ^ 2) < M := by
    rw [Real.sqrt_lt' hM]
    nlinarith
  unfold rMinus
  linarith

/-- 極端（M² = Q²）では r₊ = r₋ = M。 -/
theorem extremal_horizons {M Q : ℝ} (h : M ^ 2 = Q ^ 2) :
    rPlus M Q = M ∧ rMinus M Q = M := by
  have hs : Real.sqrt (M ^ 2 - Q ^ 2) = 0 := by
    rw [show M ^ 2 - Q ^ 2 = 0 by linarith, Real.sqrt_zero]
  refine ⟨?_, ?_⟩
  · show M + Real.sqrt (M ^ 2 - Q ^ 2) = M
    rw [hs]
    simp
  · show M - Real.sqrt (M ^ 2 - Q ^ 2) = M
    rw [hs]
    simp

/-- 二重ゼロ ⟺ 極端：r₊ = r₋ ⟺ M² = Q²（判別式が非負のとき）。 -/
theorem extremal_iff_horizons_eq {M Q : ℝ} (hdisc : 0 ≤ M ^ 2 - Q ^ 2) :
    rPlus M Q = rMinus M Q ↔ M ^ 2 = Q ^ 2 := by
  constructor
  · intro h
    have hsub : rPlus M Q - rMinus M Q = 2 * Real.sqrt (M ^ 2 - Q ^ 2) :=
      rPlus_sub_rMinus M Q
    have hs0 : Real.sqrt (M ^ 2 - Q ^ 2) = 0 := by
      have hz : rPlus M Q - rMinus M Q = 0 := sub_eq_zero.mpr h
      rw [hsub] at hz
      linarith
    have hle : M ^ 2 - Q ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp hs0
    linarith
  · intro h
    have hs : Real.sqrt (M ^ 2 - Q ^ 2) = 0 := by
      rw [show M ^ 2 - Q ^ 2 = 0 by linarith, Real.sqrt_zero]
    show M + Real.sqrt (M ^ 2 - Q ^ 2) = M - Real.sqrt (M ^ 2 - Q ^ 2)
    rw [hs]
    simp

/-- 裸（M² < Q²）では標準形は r ≠ 0 でつねに正：地平線は存在しない。 -/
theorem standard_form_pos_of_naked {M Q r : ℝ} (hr : r ≠ 0)
    (h : M ^ 2 - Q ^ 2 < 0) :
    0 < 1 - 2 * M / r + Q ^ 2 / r ^ 2 := by
  have hr2 : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero hr
  have hkey : (0 : ℝ) < (r - M) ^ 2 + (Q ^ 2 - M ^ 2) := by
    have hnn := sq_nonneg (r - M)
    linarith
  have heq : 1 - 2 * M / r + Q ^ 2 / r ^ 2
      = ((r - M) ^ 2 + (Q ^ 2 - M ^ 2)) / r ^ 2 := by
    field_simp
    ring
  rw [heq]
  exact div_pos hkey hr2

/-- Q = 0 では r₊ = 2M、r₋ = 0（シュワルツシルトへの帰着）。 -/
theorem schwarzschild_horizons {M : ℝ} (hM : 0 ≤ M) :
    rPlus M 0 = 2 * M ∧ rMinus M 0 = 0 := by
  have hs : Real.sqrt (M ^ 2 - (0 : ℝ) ^ 2) = M := by
    rw [show M ^ 2 - (0 : ℝ) ^ 2 = M ^ 2 by ring, Real.sqrt_sq hM]
  constructor
  · show M + Real.sqrt (M ^ 2 - (0 : ℝ) ^ 2) = 2 * M
    rw [hs]
    ring
  · show M - Real.sqrt (M ^ 2 - (0 : ℝ) ^ 2) = 0
    rw [hs]
    ring

/-- 6-2 の温度公式との整合：T = (r₊ − r₋)/(4π r₊²)。 -/
theorem rn_temperature_horizons (M Q : ℝ) :
    ((rPlus M Q - rMinus M Q) / (rPlus M Q) ^ 2) / (4 * Real.pi)
      = (rPlus M Q - rMinus M Q) / (4 * Real.pi * (rPlus M Q) ^ 2) :=
  CFT.Thermo.rn_temperature _ _

/-- 温度の明示式：非極端では T = √(M² − Q²)/(2π r₊²)。 -/
theorem rn_temperature_explicit {M Q : ℝ} (hM : 0 < M) (hQ : Q ^ 2 < M ^ 2) :
    ((rPlus M Q - rMinus M Q) / (rPlus M Q) ^ 2) / (4 * Real.pi)
      = Real.sqrt (M ^ 2 - Q ^ 2) / (2 * Real.pi * (rPlus M Q) ^ 2) := by
  have hp : rPlus M Q ≠ 0 := ne_of_gt (rPlus_pos hM)
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsub : rPlus M Q - rMinus M Q = 2 * Real.sqrt (M ^ 2 - Q ^ 2) :=
    rPlus_sub_rMinus M Q
  rw [hsub]
  field_simp
  ring

/-- 非極端では温度は正。 -/
theorem rn_temperature_pos_explicit {M Q : ℝ} (hM : 0 < M) (hQ : Q ^ 2 < M ^ 2) :
    0 < ((rPlus M Q - rMinus M Q) / (rPlus M Q) ^ 2) / (4 * Real.pi) := by
  rw [rn_temperature_explicit hM hQ]
  have hs : (0 : ℝ) < Real.sqrt (M ^ 2 - Q ^ 2) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hQ)
  have hp : (0 : ℝ) < rPlus M Q := rPlus_pos hM
  positivity

end CFT.RNHorizons
