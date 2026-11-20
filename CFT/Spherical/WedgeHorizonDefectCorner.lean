/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **角 (0, 0) でのソース項 S の明示計算**。前段
  （`WedgeHorizonDefectSource`）では S が
    S = Ω(1−W²)²·(−2/r⁴ − g/(2r³)) + Ω·(1/r² + g/(2r))
      + r_u·r_v·(2/r² − g′ + g/r)
  と書き直され、S = 0 は Ω 側と r_u·r_v 側の釣り合いと同値になった。
  ここでは角での特性データ（`WedgeCornerConditions`：r = Ω = 1、W = 0、
  r_u = r_v = 0）を代入し、角での S の値を明示する。g(1) の項は相殺し、
  任意の g, g′ に対して
    S(0, 0) = −1
  となる（`defectSource_corner_eq`、RN 版も同じ `defectSource_corner_rn_eq`）。
  したがって S = 0 は角では成り立たない（`defectSource_corner_ne_zero`）。

  同時に、角では欠陥 D 自体は 0 である（`logDerivDefect_corner_eq_zero`：
  Ω_u = 0、r_u = 0 による）。しかし輸送方程式（`WedgeHorizonDefectTransport`）
  により D の v 微分は S に等しいので、角では
    ∂_v D(0, 0) = −1
  である（`defect_deriv_v_corner`）。すなわち D は角で 0 だが、v 方向に
  すぐ負になる（`defect_neg_near_corner`：小さな v > 0 では D(0, v) < 0）。

  帰結：対応仮説の証明で使う「S = 0 かつ一点での D = 0 から区間上で D = 0」
  （`WedgeHorizonDefectConstancy`）は、角を含む v 区間では使えない。
  S = 0 は角から離れたところで確立しなければならず、D = 0 の一点も
  角から離して取らなければならない。角は対応仮説にとって特異な点であり、
  対応は角の外側の領域の問題であることが、明示計算で固定された。

  恒等式の定数は sympy による明示計算（`/tmp/check_corner_S.py`）でも照合済み。
-/
import CFT.Spherical.WedgeHorizonDefectSource
import CFT.Spherical.WedgeCornerConditions

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource CFT.RNLogDeriv

namespace CFT.WedgeDefectCorner

/-- 角でのソース項の値：g(1) の項が相殺し、S(0, 0) = −1 になる。 -/
theorem defectSource_corner_eq {F : WedgeFields} {g g' : ℝ → ℝ}
    (hdata : HasWedgeData F) :
    defectSource F g g' 0 0 = -1 := by
  obtain ⟨hr1, hOm1, hW0⟩ := CFT.WedgeCorner.data_values hdata
  have hr : F.r 0 0 ≠ 0 := by rw [hr1]; norm_num
  rw [defectSource_eq hr, hr1, hOm1, hW0, CFT.WedgeCorner.data_r_u hdata,
    CFT.WedgeCorner.data_r_v hdata]
  ring

/-- 角では S = 0 は成り立たない。 -/
theorem defectSource_corner_ne_zero {F : WedgeFields} {g g' : ℝ → ℝ}
    (hdata : HasWedgeData F) : defectSource F g g' 0 0 ≠ 0 := by
  rw [defectSource_corner_eq hdata]
  norm_num

/-- RN 版：角でのソース項の値も −1。 -/
theorem defectSource_corner_rn_eq {F : WedgeFields} {rp rm : ℝ}
    (hdata : HasWedgeData F) :
    defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) 0 0 = -1 :=
  defectSource_corner_eq hdata

/-- 角では欠陥 D 自体は 0 である（Ω_u = 0、r_u = 0 による）。 -/
theorem logDerivDefect_corner_eq_zero {F : WedgeFields} {g : ℝ → ℝ}
    (hdata : HasWedgeData F) :
    logDerivDefect F g 0 0 = 0 := by
  obtain ⟨hr1, hOm1, _⟩ := CFT.WedgeCorner.data_values hdata
  simp only [logDerivDefect, CFT.WedgeCorner.data_Om_u hdata,
    CFT.WedgeCorner.data_r_u hdata, hr1, hOm1]
  simp

/-- 角での欠陥の v 微分：輸送方程式により ∂_v D(0, 0) = S(0, 0) = −1。 -/
theorem defect_deriv_v_corner {F : WedgeFields} {g g' : ℝ → ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hg : HasDerivAt g (g' (F.r 0 0)) (F.r 0 0))
    (hOmu : HasDerivAt (fun v' => Du F.Om 0 v') (Duv F.Om 0 0) 0)
    (hOmv : HasDerivAt (fun v' => F.Om 0 v') (Dv F.Om 0 0) 0)
    (hrv : HasDerivAt (fun v' => F.r 0 v') (Dv F.r 0 0) 0)
    (hru : HasDerivAt (fun v' => Du F.r 0 v') (Duv F.r 0 0) 0) :
    deriv (fun v' => logDerivDefect F g 0 v') 0 = -1 := by
  obtain ⟨hr1, hOm1, _⟩ := CFT.WedgeCorner.data_values hdata
  have hOm : F.Om 0 0 ≠ 0 := by rw [hOm1]; norm_num
  have hr : F.r 0 0 ≠ 0 := by rw [hr1]; norm_num
  have h := defect_deriv_v heq hOm hr hg hOmu hOmv hrv hru
  rw [h, defectSource_corner_eq hdata]

/-- D は角で 0 だが、v 方向にすぐ負になる：小さな v > 0 では D(0, v) < 0。
    傾きの極限（`HasDerivAt.tendsto_slope`）による。 -/
theorem defect_neg_near_corner {F : WedgeFields} {g g' : ℝ → ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hg : HasDerivAt g (g' (F.r 0 0)) (F.r 0 0))
    (hOmu : HasDerivAt (fun v' => Du F.Om 0 v') (Duv F.Om 0 0) 0)
    (hOmv : HasDerivAt (fun v' => F.Om 0 v') (Dv F.Om 0 0) 0)
    (hrv : HasDerivAt (fun v' => F.r 0 v') (Dv F.r 0 0) 0)
    (hru : HasDerivAt (fun v' => Du F.r 0 v') (Duv F.r 0 0) 0) :
    ∃ δ > 0, ∀ v ∈ Set.Ioo 0 δ, logDerivDefect F g 0 v < 0 := by
  obtain ⟨hr1, hOm1, _⟩ := CFT.WedgeCorner.data_values hdata
  have hOm : F.Om 0 0 ≠ 0 := by rw [hOm1]; norm_num
  have hr : F.r 0 0 ≠ 0 := by rw [hr1]; norm_num
  have hderiv : HasDerivAt (fun v' => logDerivDefect F g 0 v') (-1) 0 := by
    have h := defect_hasDerivAt_v heq hOm hr hg hOmu hOmv hrv hru
    rwa [defectSource_corner_eq hdata] at h
  have hev : ∀ᶠ v in 𝓝[≠] (0 : ℝ),
      slope (fun v' => logDerivDefect F g 0 v') 0 v < 0 :=
    (hasDerivAt_iff_tendsto_slope.mp hderiv).eventually
      (Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num))
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ'⟩ := hev
  refine ⟨δ, hδ, fun v hv => ?_⟩
  have hv0 : v ≠ 0 := ne_of_gt hv.1
  have hlt := hδ' (show dist v 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hv.1]; exact hv.2) hv0
  have hf0 : logDerivDefect F g 0 0 = 0 := logDerivDefect_corner_eq_zero hdata
  rw [slope_def_field, hf0] at hlt
  simp only [sub_zero] at hlt
  rcases (div_neg_iff.mp hlt) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h2 (not_lt.mpr (le_of_lt hv.1))
  · exact h1

end CFT.WedgeDefectCorner
