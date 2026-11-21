/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **S = 0 になる一点の構成の仮定のうち、切片の左端での負値の検証**。
  前段（`WedgeHorizonDefectZeroPoint`）では、固定したヌル切片
  （v = const）上で S = 0 になる一点 u₁ ∈ (0, u₀) が、中間値の定理から
  構成された（`defectSource_eq_zero_of_horizon_blowup`）。その仮定の
  一つは切片の左端での負値
    S(0, v) < 0
  であった。ここではそれを、実際の特性データ（`HasWedgeData`）から
  検証する。首面（u = 0）では r ≡ 1、W ≡ 0、Ω = neckOm v であり、
  r は v 方向に定数なので Dv r = 0。S の明示形（`defectSource_eq`）に
  代入すると g(1) の項が相殺し、任意の g, g′ に対して
    S(0, v) = −neckOm v < 0
  となる（`defectSource_zero_slice_eq`・`defectSource_zero_slice_neg`）。
  RN 版も同じ（`defectSource_zero_slice_rn_eq`・
  `defectSource_zero_slice_rn_neg`）。すなわち
  `defectSource_eq_zero_of_horizon_blowup` の仮定 hS0 は、特性データを
  持つ任意の場で、任意の v に対して成り立つ。

  v = 0 では neckOm 0 = 1 なので S(0, 0) = −1 となり、角での明示計算
  （`defectSource_corner_eq`）と一致する
  （`defectSource_zero_slice_zero`）。

  残る仮定：切片上の S の連続性、地平線への接近 r → r₊、r_u·r_v の
  正の下界、Ω 項の下界は、実際のくさび解の地平線付近での振る舞いの
  解析が要るため、次の段以降に残す。ρ そのものの構成も未解決。
-/
import CFT.Spherical.WedgeHorizonDefectSource
import CFT.Spherical.WedgeCornerConditions
import CFT.Spherical.WedgeHorizonFirstExit
import CFT.Quantum.RNLogDerivative

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource CFT.RNLogDeriv

namespace CFT.WedgeDefectZeroPointData

/-- 首面（u = 0）では r は v 方向に定数 1 なので Dv r = 0。 -/
theorem Dv_r_zero_slice {F : WedgeFields} (hdata : HasWedgeData F) (v : ℝ) :
    Dv F.r 0 v = 0 := by
  show deriv (fun v' => F.r 0 v') v = 0
  rw [CFT.WedgeCorner.slice_r_neck hdata]
  simp

/-- 首面でのソース項の値：g(1) の項が相殺し、S(0, v) = −neckOm v になる。 -/
theorem defectSource_zero_slice_eq {F : WedgeFields} {g g' : ℝ → ℝ}
    (hdata : HasWedgeData F) (v : ℝ) :
    defectSource F g g' 0 v = -neckOm v := by
  have hr : F.r 0 v ≠ 0 := by rw [(hdata.2 v).1]; norm_num
  rw [defectSource_eq hr, (hdata.2 v).1, (hdata.2 v).2.1, (hdata.2 v).2.2,
    Dv_r_zero_slice hdata v]
  ring

/-- 首面ではソース項は負：S(0, v) = −neckOm v < 0。 -/
theorem defectSource_zero_slice_neg {F : WedgeFields} {g g' : ℝ → ℝ}
    (hdata : HasWedgeData F) (v : ℝ) :
    defectSource F g g' 0 v < 0 := by
  rw [defectSource_zero_slice_eq hdata v]
  exact neg_lt_zero.mpr (CFT.WedgeFirstExit.neckOm_pos v)

/-- RN 版：首面でのソース項の値も −neckOm v。 -/
theorem defectSource_zero_slice_rn_eq {F : WedgeFields} {rp rm : ℝ}
    (hdata : HasWedgeData F) (v : ℝ) :
    defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) 0 v = -neckOm v :=
  defectSource_zero_slice_eq hdata v

/-- RN 版（極端）：首面では S(0, v) < 0。すなわち
    `defectSource_eq_zero_of_horizon_blowup` の仮定 hS0 は、特性データを
    持つ任意の場で、任意の v に対して成り立つ。 -/
theorem defectSource_zero_slice_rn_neg {F : WedgeFields} {rp : ℝ}
    (hdata : HasWedgeData F) (v : ℝ) :
    defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) 0 v < 0 :=
  defectSource_zero_slice_neg hdata v

/-- v = 0 での整合性：neckOm 0 = 1 なので S(0, 0) = −1 となり、角での
    明示計算（`defectSource_corner_eq`）と一致する。 -/
theorem defectSource_zero_slice_zero {F : WedgeFields} {g g' : ℝ → ℝ}
    (hdata : HasWedgeData F) : defectSource F g g' 0 0 = -1 := by
  rw [defectSource_zero_slice_eq hdata 0]
  simp [neckOm]

end CFT.WedgeDefectZeroPointData
