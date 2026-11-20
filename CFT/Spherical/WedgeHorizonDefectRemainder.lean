/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **残余 R = 0 の判定（第一段）と角での ∂_v S の明示計算**。前段
  （`WedgeHorizonDefectSourceDerivClosed`）では ∂_v S の閉形
    ∂_v S = (Ω_v/Ω)·S + R
  が証明され、S = 0 の点では ∂_v S = R になることが示された。ここでは
  R の構造（`defectSourceRemainder` の四項はすべて Dv r か Dv W を
  因子に持つ）から、R = 0 の十分条件
    Dv r = 0 かつ Dv W = 0 ならば R = 0
  を証明する（`defectSourceRemainder_eq_zero_of_Dv_zero`）。
  角では特性データにより Dv r = Dv W = 0 なので R(0, 0) = 0
  （`defectSourceRemainder_corner_eq_zero`）。さらに閉形と
  S(0, 0) = −1（`WedgeHorizonDefectCorner`）、Ω_v(0, 0) = 0 から、
  角では ∂_v S(0, 0) = 0 になること
  （`defectSource_deriv_v_corner_eq_zero`）を証明する。すなわち
  D は角で v 方向に傾き −1 で負になる（`defect_deriv_v_corner`）が、
  S 自体は角で v 方向に停留している。

  一般の判定として、S = 0 かつ R = 0 の点では ∂_v S = 0 になること
  （`defectSource_deriv_v_eq_zero_of_source_zero_and_remainder_zero`）
  も証明する。S = 0 の v 方向への伝播の第一歩である。

  RN への特殊化の係数（`/tmp/check_R_coeffs.py` で確認）：非極端では
  C1・C2・C3・B1|_{W=0} は (r−r₊)・(r−r₋) を分母に持つ巨大な有理式に
  なり、きれいな因数分解はない。極端（r₊ = r₋）では
  C3 = 2(2r−r₊)/(r−r₊)、C2 = −2(r² + r·r₊ − r₊²)/(r−r₊)²、
  C1 = 2(3r³ + 3r²r₊ − 7r·r₊² + 3r₊³)/(r−r₊)³ と簡潔になる。
  RN 版の係数解析は重い段として次回以降に残す。
-/
import CFT.Spherical.WedgeHorizonDefectSourceDerivClosed
import CFT.Spherical.WedgeHorizonDefectCorner

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource
open CFT.WedgeDefectSourceDeriv CFT.WedgeDefectSourceDerivClosed CFT.WedgeDefectCorner

namespace CFT.WedgeDefectRemainder

/-- 残余 R は Dv r と Dv W を因子に持つ四項の和なので、両方が 0 なら R = 0。 -/
theorem defectSourceRemainder_eq_zero_of_Dv_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hrv : Dv F.r u v = 0) (hWv : Dv F.W u v = 0) :
    defectSourceRemainder F g g' g'' u v = 0 := by
  simp [defectSourceRemainder, hrv, hWv]

/-- 角では特性データにより Dv r = Dv W = 0 なので R(0, 0) = 0。 -/
theorem defectSourceRemainder_corner_eq_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ} (hdata : HasWedgeData F) :
    defectSourceRemainder F g g' g'' 0 0 = 0 :=
  defectSourceRemainder_eq_zero_of_Dv_zero (CFT.WedgeCorner.data_r_v hdata)
    (CFT.WedgeCorner.data_W_v hdata)

/-- S = 0 かつ R = 0 の点では、閉形 ∂_v S = (Ω_v/Ω)·S + R により ∂_v S = 0。
    S = 0 の v 方向への伝播の第一歩。 -/
theorem defectSource_deriv_v_eq_zero_of_source_zero_and_remainder_zero
    {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v)
    (hS : defectSource F g g' u v = 0)
    (hR : defectSourceRemainder F g g' g'' u v = 0) :
    deriv (fun v' => defectSource F g g' u v') v = 0 := by
  rw [defectSource_deriv_v_closed heq hcon hOm hr hg hg' hOmv hWv hrv hru hrvv, hS, hR]
  simp

/-- 角での S の v 微分は 0（HasDerivAt 版）：Ω_v(0, 0) = 0、S(0, 0) = −1、
    R(0, 0) = 0 を閉形に代入する。 -/
theorem defectSource_hasDerivAt_v_corner_eq_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hdata : HasWedgeData F)
    (hg : HasDerivAt g (g' (F.r 0 0)) (F.r 0 0))
    (hg' : HasDerivAt g' (g'' (F.r 0 0)) (F.r 0 0))
    (hOmv : HasDerivAt (fun v' => F.Om 0 v') (Dv F.Om 0 0) 0)
    (hWv : HasDerivAt (fun v' => F.W 0 v') (Dv F.W 0 0) 0)
    (hrv : HasDerivAt (fun v' => F.r 0 v') (Dv F.r 0 0) 0)
    (hru : HasDerivAt (fun v' => Du F.r 0 v') (Duv F.r 0 0) 0)
    (hrvv : HasDerivAt (fun v' => Dv F.r 0 v') (Dvv F.r 0 0) 0) :
    HasDerivAt (fun v' => defectSource F g g' 0 v') 0 0 := by
  obtain ⟨hr1, hOm1, _⟩ := CFT.WedgeCorner.data_values hdata
  have hOm : F.Om 0 0 ≠ 0 := by rw [hOm1]; norm_num
  have hr : F.r 0 0 ≠ 0 := by rw [hr1]; norm_num
  have h := defectSource_hasDerivAt_v_closed heq hcon hOm hr hg hg' hOmv hWv hrv hru hrvv
  rw [CFT.WedgeCorner.data_Om_v hdata, hOm1, defectSource_corner_eq hdata,
    defectSourceRemainder_corner_eq_zero hdata] at h
  simpa using h

/-- 角での S の v 微分は 0（`deriv` 版）。 -/
theorem defectSource_deriv_v_corner_eq_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hdata : HasWedgeData F)
    (hg : HasDerivAt g (g' (F.r 0 0)) (F.r 0 0))
    (hg' : HasDerivAt g' (g'' (F.r 0 0)) (F.r 0 0))
    (hOmv : HasDerivAt (fun v' => F.Om 0 v') (Dv F.Om 0 0) 0)
    (hWv : HasDerivAt (fun v' => F.W 0 v') (Dv F.W 0 0) 0)
    (hrv : HasDerivAt (fun v' => F.r 0 v') (Dv F.r 0 0) 0)
    (hru : HasDerivAt (fun v' => Du F.r 0 v') (Duv F.r 0 0) 0)
    (hrvv : HasDerivAt (fun v' => Dv F.r 0 v') (Dvv F.r 0 0) 0) :
    deriv (fun v' => defectSource F g g' 0 v') 0 = 0 :=
  (defectSource_hasDerivAt_v_corner_eq_zero heq hcon hdata hg hg' hOmv hWv hrv hru hrvv).deriv

end CFT.WedgeDefectRemainder
