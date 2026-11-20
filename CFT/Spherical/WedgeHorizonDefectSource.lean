/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **ソース項 S の明示形と S = 0 の同値な定式化**。前段
  （`WedgeHorizonDefectTransport`）では欠陥 D の v 微分がソース項
    S = (Ω/r² + 2·r_u·r_v/r² − 2Ω(1−W²)²/r⁴)
      − (g′(r)·r_v·r_u + g(r)·rhsR)
  に等しいことが示され、前々段（`WedgeHorizonDefectConstancy`）では
  S = 0 かつ一点での D = 0 から区間上で D = 0 が従うことが示された。
  残るのは S = 0 そのものの発展方程式からの導出である。
  ここではその一段として、rhsR の明示形を代入して S を
    S = Ω(1−W²)²·(−2/r⁴ − g/(2r³)) + Ω·(1/r² + g/(2r))
      + r_u·r_v·(2/r² − g′ + g/r)
  と書き直す（`defectSource_eq`）。すなわち S は Ω に比例する二項と
  r_u·r_v に比例する一項の和であり、S = 0 はその和が 0 であることと
  同値（`defectSource_eq_zero_iff`）、Ω 側と r_u·r_v 側の釣り合い
    Ω(1−W²)²·(−2/r⁴ − g/(2r³)) + Ω·(1/r² + g/(2r))
      = −r_u·r_v·(2/r² − g′ + g/r)
  とも同値（`defectSource_eq_zero_iff_balance`）である。
  RN への特殊化（`defectSource_rn_eq`）では g′ の明示形により
  r_u·r_v の係数の 2/r² が相殺し、
    2/r² − g′ + g/r = 1/(r−r₊)² + 1/(r−r₋)² + g/r
  となる。S = 0 の RN 版も同様に定式化する
  （`defectSource_rn_eq_zero_iff`）。

  恒等式の定数は sympy による明示計算（`/tmp/check_source.py`）でも照合済み。
-/
import CFT.Spherical.WedgeHorizonDefectTransport

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.RNLogDeriv

namespace CFT.WedgeDefectSource

/-- ソース項の明示形：rhsR を展開し、Ω に比例する二項と
    r_u·r_v に比例する一項にまとめる。 -/
theorem defectSource_eq {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0) :
    defectSource F g g' u v =
      F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4 - g (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2 + g (F.r u v) / (2 * F.r u v))
        + Du F.r u v * Dv F.r u v
          * (2 / (F.r u v) ^ 2 - g' (F.r u v) + g (F.r u v) / F.r u v) := by
  simp only [defectSource, rhsR]
  field_simp
  ring

/-- S = 0 は明示形の和が 0 であることと同値。 -/
theorem defectSource_eq_zero_iff {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0) :
    defectSource F g g' u v = 0 ↔
      F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4 - g (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2 + g (F.r u v) / (2 * F.r u v))
        + Du F.r u v * Dv F.r u v
          * (2 / (F.r u v) ^ 2 - g' (F.r u v) + g (F.r u v) / F.r u v) = 0 := by
  rw [defectSource_eq hr]

/-- S = 0 は Ω 側と r_u·r_v 側の釣り合いと同値。 -/
theorem defectSource_eq_zero_iff_balance {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0) :
    defectSource F g g' u v = 0 ↔
      F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4 - g (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2 + g (F.r u v) / (2 * F.r u v))
        = - (Du F.r u v * Dv F.r u v
          * (2 / (F.r u v) ^ 2 - g' (F.r u v) + g (F.r u v) / F.r u v)) := by
  rw [defectSource_eq_zero_iff hr]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- RN への特殊化：g′ の明示形により r_u·r_v の係数の 2/r² が相殺する。 -/
theorem defectSource_rn_eq {F : WedgeFields} {rp rm u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm) :
    defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v =
      F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4
            - rnLogDeriv rp rm (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2
            + rnLogDeriv rp rm (F.r u v) / (2 * F.r u v))
        + Du F.r u v * Dv F.r u v
          * (1 / (F.r u v - rp) ^ 2 + 1 / (F.r u v - rm) ^ 2
            + rnLogDeriv rp rm (F.r u v) / F.r u v) := by
  rw [defectSource_eq hr]
  have hrp' : F.r u v - rp ≠ 0 := sub_ne_zero.mpr hrp
  have hrm' : F.r u v - rm ≠ 0 := sub_ne_zero.mpr hrm
  simp only [rnLogDeriv, rnLogDeriv']
  field_simp
  ring

/-- S = 0 の RN 版：明示形の和が 0 であることと同値。 -/
theorem defectSource_rn_eq_zero_iff {F : WedgeFields} {rp rm u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm) :
    defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v = 0 ↔
      F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4
            - rnLogDeriv rp rm (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2
            + rnLogDeriv rp rm (F.r u v) / (2 * F.r u v))
        + Du F.r u v * Dv F.r u v
          * (1 / (F.r u v - rp) ^ 2 + 1 / (F.r u v - rm) ^ 2
            + rnLogDeriv rp rm (F.r u v) / F.r u v) = 0 := by
  rw [defectSource_rn_eq hr hrp hrm]

end CFT.WedgeDefectSource
