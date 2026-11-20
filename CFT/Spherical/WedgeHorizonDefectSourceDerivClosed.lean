/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **ソース項 S の v 微分の閉形（発展方程式・拘束の代入）**。前段
  （`WedgeHorizonDefectSourceDeriv`）では ∂_v S の明示形が
  r_uv・r_vv を抽象的な微分値として残す形で証明された。ここでは
  r_uv に発展方程式 `rhsR`、r_vv に拘束 C_v
    r_vv = (Ω_v/Ω)·r_v − 2·W_v²/r
  を代入し、∂_v S を同次部分と残余に分けた閉形
    ∂_v S = (Ω_v/Ω)·S + R
  として証明する（`defectSource_hasDerivAt_v_closed`・
  `defectSource_deriv_v_closed`）。残余 R は Ω_v を含まず、
  r_v・r_v²・W_v・W_v² の四項だけからなる（`defectSourceRemainder`）。
  したがって S = 0 の点では ∂_v S = R であり、S = 0 の v 方向への
  伝播は R = 0 かどうかで決まる（次の段の判定対象）。

  恒等式の定数は sympy による明示計算（`/tmp/check_dSdv_closed3.py`、
  ∂_v S − ((Ω_v/Ω)·S + R) = 0）でも照合済み。RN への特殊化は
  残余が (r−r₊)³(r−r₋)³ を分母に持つ巨大な有理式になるため、
  この段では行わない（重い段として記録）。
-/
import CFT.Spherical.WedgeHorizonDefectSourceDeriv

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource CFT.WedgeDefectSourceDeriv

namespace CFT.WedgeDefectSourceDerivClosed

/-- ∂_v S の閉形における残余項 R。Ω_v を含まず、r_v・r_v²・W_v・W_v²
    の四項だけからなる。 -/
noncomputable def defectSourceRemainder (F : WedgeFields) (g g' g'' : ℝ → ℝ) (u v : ℝ) : ℝ :=
  Dv F.r u v * (F.Om u v / (F.r u v) ^ 5)
      * (2 * (F.W u v) ^ 4 * g (F.r u v) * F.r u v
        - (F.W u v) ^ 4 * g' (F.r u v) * (F.r u v) ^ 2 + 9 * (F.W u v) ^ 4
        - 4 * (F.W u v) ^ 2 * g (F.r u v) * F.r u v
        + 2 * (F.W u v) ^ 2 * g' (F.r u v) * (F.r u v) ^ 2 - 18 * (F.W u v) ^ 2
        - g (F.r u v) * (F.r u v) ^ 3 + 2 * g (F.r u v) * F.r u v
        + g' (F.r u v) * (F.r u v) ^ 4 - g' (F.r u v) * (F.r u v) ^ 2
        - 3 * (F.r u v) ^ 2 + 9)
    + (Dv F.r u v) ^ 2 * (-(Du F.r u v) / (F.r u v) ^ 3)
      * (2 * g (F.r u v) * F.r u v - 2 * g' (F.r u v) * (F.r u v) ^ 2
        + g'' (F.r u v) * (F.r u v) ^ 3 + 6)
    + Dv F.W u v * (2 * F.Om u v * F.W u v * (1 - (F.W u v) ^ 2)
        * (g (F.r u v) * F.r u v + 4) / (F.r u v) ^ 4)
    + (Dv F.W u v) ^ 2 * (2 * Du F.r u v / (F.r u v) ^ 3)
      * (-(g (F.r u v)) * F.r u v + g' (F.r u v) * (F.r u v) ^ 2 - 2)

/-- ∂_v S の明示形は、発展方程式・拘束を代入すると同次部分
    (Ω_v/Ω)·S と残余 R の和になる。 -/
theorem defectSourceDerivV_eq {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0) :
    defectSourceDerivV F g g' g'' u v
      = Dv F.Om u v / F.Om u v * defectSource F g g' u v
        + defectSourceRemainder F g g' g'' u v := by
  have hruv : Duv F.r u v
      = rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v) := (heq u v).1
  have hrvv : Dvv F.r u v
      = Dv F.Om u v / F.Om u v * Dv F.r u v - 2 * (Dv F.W u v) ^ 2 / F.r u v := by
    have h := (hcon u v).2
    linarith
  unfold defectSourceDerivV defectSourceDerivV1 defectSourceDerivV2
    defectSourceDerivV3 defectSource defectSourceRemainder
  rw [hruv, hrvv]
  unfold rhsR
  field_simp
  ring

/-- ソース項 S の v 微分の閉形（発展方程式・拘束の代入後）。 -/
theorem defectSource_hasDerivAt_v_closed {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    HasDerivAt (fun v' => defectSource F g g' u v')
      (Dv F.Om u v / F.Om u v * defectSource F g g' u v
        + defectSourceRemainder F g g' g'' u v) v := by
  rw [← defectSourceDerivV_eq heq hcon hOm hr]
  exact defectSource_hasDerivAt_v hr hg hg' hOmv hWv hrv hru hrvv

/-- ソース項 S の v 微分の閉形の `deriv` 版。 -/
theorem defectSource_deriv_v_closed {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    deriv (fun v' => defectSource F g g' u v') v
      = Dv F.Om u v / F.Om u v * defectSource F g g' u v
        + defectSourceRemainder F g g' g'' u v :=
  (defectSource_hasDerivAt_v_closed heq hcon hOm hr hg hg' hOmv hWv hrv hru hrvv).deriv

/-- S = 0 の点では ∂_v S は残余 R に等しい（同次部分が落ちる）。
    S = 0 の伝播は R = 0 かどうかで決まる。 -/
theorem defectSource_deriv_v_closed_of_source_zero {F : WedgeFields} {g g' g'' : ℝ → ℝ}
    {u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v)
    (hS : defectSource F g g' u v = 0) :
    deriv (fun v' => defectSource F g g' u v') v
      = defectSourceRemainder F g g' g'' u v := by
  rw [defectSource_deriv_v_closed heq hcon hOm hr hg hg' hOmv hWv hrv hru hrvv, hS,
    mul_zero, zero_add]

end CFT.WedgeDefectSourceDerivClosed
