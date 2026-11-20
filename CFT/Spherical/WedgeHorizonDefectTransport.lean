/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **対数微分の一致の輸送方程式**。前段（`WedgeHorizonRatioODE`）では、
  対応仮説 Ω = c·f(r) が切片上の対数微分の一致
    dOm/Ω = (f′/f)(r)·dr
  に帰着され、RN の f に対して右辺は明示された（`RNLogDerivative`）。
  ここではその一致条件を、Ω と r の発展方程式の形に書き直す。
  欠陥
    D(u, v) := (∂_u Ω)/Ω − g(r)·(∂_u r)   （g = f′/f）
  に対して、v 方向の微分は発展方程式だけから明示形を持つ：
    ∂_v D = S
  ここで S は Ω, r, W とその 1 階微分だけの式（`defectSource`）。
  鍵は ∂_v(Ω_u/Ω) における相殺で、Ω_uv の右辺を代入すると
    ∂_v(Ω_u/Ω) = Ω/r² + 2·r_u·r_v/r² − 2Ω(1−W²)²/r⁴
  となり、Ω_u 自体は現れない。したがって D が v 区間上で恒等的に 0
  （すなわち対応がその区間全体で成り立つ）ならば、S = 0 が従う
  （`correspondence_nec_source_zero`）：S = 0 は対応仮説が発展方程式と
  両立するための可積分性条件である。逆に S = 0 から D = 0 を導くには
  さらに D についての同次方程式化が要り、次の段以降に残す。

  混合微分の交換（∂_v(∂_u Ω) = Ω_uv など）は `C2Data.deriv_uv_v` の
  仮定として受け取る。C² 級の解への適用版（`defect_hasDerivAt_v_of_C2`）
  では `C2On` から引き出す。RN への特殊化（`defect_transport_rn`）では
  g = `rnLogDeriv`、g′ はその明示微分 `rnLogDeriv'` を使う。
-/
import CFT.Spherical.WedgeUniqueness
import CFT.Quantum.RNLogDerivative

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.RNLogDeriv

namespace CFT.WedgeDefectTransport

/-- 対数微分の欠陥：切片上で (∂_u Ω)/Ω と g(r)·(∂_u r) の差。
    0 なら対数微分が一致する（`WedgeHorizonRatioODE` の一致条件）。 -/
noncomputable def logDerivDefect (F : WedgeFields) (g : ℝ → ℝ) (u v : ℝ) : ℝ :=
  Du F.Om u v / F.Om u v - g (F.r u v) * Du F.r u v

/-- 欠陥の輸送方程式の右辺（ソース項）。発展方程式の右辺 `rhsR` を使う。
    第 1 項が ∂_v(Ω_u/Ω) の閉形、第 2 項が ∂_v(g(r)·r_u) の閉形。 -/
noncomputable def defectSource (F : WedgeFields) (g g' : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (F.Om u v / (F.r u v) ^ 2 + 2 * Du F.r u v * Dv F.r u v / (F.r u v) ^ 2
    - 2 * F.Om u v * (1 - (F.W u v) ^ 2) ^ 2 / (F.r u v) ^ 4)
  - (g' (F.r u v) * Dv F.r u v * Du F.r u v
    + g (F.r u v) * rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v))

/-- Ω の対数微分の v 微分：発展方程式（Ω_uv と r_uv の右辺）を代入すると
    Ω_u が相殺し、Ω, r, W とその 1 階微分だけの閉形になる。 -/
theorem Om_logDeriv_hasDerivAt_v {F : WedgeFields} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hOmu : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v) :
    HasDerivAt (fun v' => Du F.Om u v' / F.Om u v')
      (F.Om u v / (F.r u v) ^ 2 + 2 * Du F.r u v * Dv F.r u v / (F.r u v) ^ 2
        - 2 * F.Om u v * (1 - (F.W u v) ^ 2) ^ 2 / (F.r u v) ^ 4) v := by
  have hdiv := hOmu.div hOmv hOm
  have hOmEq := (heq u v).2.1
  have hrEq := (heq u v).1
  rw [hOmEq, hrEq] at hdiv
  convert hdiv using 1
  simp only [rhsOm, rhsR]
  field_simp
  ring

/-- g(r)·r_u の v 微分：連鎖律と積の微分。 -/
theorem rLogDeriv_hasDerivAt_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v) :
    HasDerivAt (fun v' => g (F.r u v') * Du F.r u v')
      (g' (F.r u v) * Dv F.r u v * Du F.r u v
        + g (F.r u v) * Duv F.r u v) v := by
  have hcomp : HasDerivAt (fun v' => g (F.r u v'))
      (g' (F.r u v) * Dv F.r u v) v := hg.comp v hrv
  exact hcomp.mul hru

/-- 欠陥の輸送方程式：発展方程式をみたす場では、欠陥の v 微分は
    ソース項 `defectSource` に等しい。 -/
theorem defect_hasDerivAt_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOmu : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v) :
    HasDerivAt (fun v' => logDerivDefect F g u v') (defectSource F g g' u v) v := by
  have hA := Om_logDeriv_hasDerivAt_v heq hOm hr hOmu hOmv
  have hB := rLogDeriv_hasDerivAt_v hg hrv hru
  have hB' : HasDerivAt (fun v' => g (F.r u v') * Du F.r u v')
      (g' (F.r u v) * Dv F.r u v * Du F.r u v
        + g (F.r u v) * rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v)) v := by
    rw [(heq u v).1] at hB
    exact hB
  have hsub := hA.sub hB'
  convert hsub using 1

/-- 欠陥の輸送方程式の `deriv` 版。 -/
theorem defect_deriv_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOmu : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v) :
    deriv (fun v' => logDerivDefect F g u v') v = defectSource F g g' u v :=
  (defect_hasDerivAt_v heq hOm hr hg hOmu hOmv hrv hru).deriv

/-- 可積分性条件：欠陥が v の開区間上で恒等的に 0（すなわち対応が
    その区間全体で成り立つ）ならば、その区間の内点ではソース項は 0。
    対応仮説が発展方程式と両立するための必要条件。 -/
theorem correspondence_nec_source_zero {F : WedgeFields} {g g' : ℝ → ℝ}
    {u v : ℝ} {a b : ℝ}
    (hv : v ∈ Ioo a b)
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOmu : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hdef : ∀ v' ∈ Ioo a b, logDerivDefect F g u v' = 0) :
    defectSource F g g' u v = 0 := by
  have hder := defect_hasDerivAt_v heq hOm hr hg hOmu hOmv hrv hru
  have hEq : (fun v' => logDerivDefect F g u v') =ᶠ[𝓝 v] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with v' hv'
    exact hdef v' hv'
  have h0 : HasDerivAt (fun v' => logDerivDefect F g u v') 0 v :=
    (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq hEq
  exact hder.unique h0

/-- C² 級の解への適用版：混合微分の交換は `C2On` から引き出す。 -/
theorem defect_hasDerivAt_v_of_C2 {F : WedgeFields} {g g' : ℝ → ℝ} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hC2Om : C2On a b F.Om) (hC2r : C2On a b F.r)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b) :
    HasDerivAt (fun v' => logDerivDefect F g u v') (defectSource F g g' u v) v :=
  defect_hasDerivAt_v heq hOm hr hg
    (hC2Om.deriv_uv_v u hu v hv) (hC2Om.deriv_v u hu v hv)
    (hC2r.deriv_v u hu v hv) (hC2r.deriv_uv_v u hu v hv)

/-- RN の対数微分 f′/f の導関数：
    g(r) = 1/(r−r₊) + 1/(r−r₋) − 2/r に対して
    g′(r) = −1/(r−r₊)² − 1/(r−r₋)² + 2/r²。 -/
noncomputable def rnLogDeriv' (rp rm r : ℝ) : ℝ :=
  -1 / (r - rp) ^ 2 - 1 / (r - rm) ^ 2 + 2 / r ^ 2

/-- RN の対数微分は `rnLogDeriv'` を導関数に持つ。 -/
theorem rnLogDeriv_hasDerivAt {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) (hrm : r ≠ rm) :
    HasDerivAt (rnLogDeriv rp rm) (rnLogDeriv' rp rm r) r := by
  have h1 : HasDerivAt (fun x => (x - rp)⁻¹) (-1 / (r - rp) ^ 2) r :=
    ((hasDerivAt_id r).sub_const rp).inv (sub_ne_zero.mpr hrp)
  have h2 : HasDerivAt (fun x => (x - rm)⁻¹) (-1 / (r - rm) ^ 2) r :=
    ((hasDerivAt_id r).sub_const rm).inv (sub_ne_zero.mpr hrm)
  have h3 : HasDerivAt (fun x => 2 * x⁻¹) (2 * (-1 / r ^ 2)) r :=
    ((hasDerivAt_id r).inv hr).const_mul 2
  have h := (h1.add h2).sub h3
  convert h using 1
  · ext x
    simp [rnLogDeriv, one_div, div_eq_mul_inv]
  · simp only [rnLogDeriv']
    ring

/-- RN への特殊化：欠陥の輸送方程式（g = RN の対数微分）。 -/
theorem defect_transport_rn {F : WedgeFields} {rp rm u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm)
    (hOmu : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v) :
    HasDerivAt (fun v' => logDerivDefect F (rnLogDeriv rp rm) u v')
      (defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v) v :=
  defect_hasDerivAt_v heq hOm hr
    (rnLogDeriv_hasDerivAt hr hrp hrm) hOmu hOmv hrv hru

/-- RN への特殊化：可積分性条件。 -/
theorem correspondence_nec_source_zero_rn {F : WedgeFields} {rp rm u v : ℝ} {a b : ℝ}
    (hv : v ∈ Ioo a b)
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm)
    (hOmu : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hdef : ∀ v' ∈ Ioo a b, logDerivDefect F (rnLogDeriv rp rm) u v' = 0) :
    defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v = 0 :=
  correspondence_nec_source_zero hv heq hOm hr
    (rnLogDeriv_hasDerivAt hr hrp hrm) hOmu hOmv hrv hru hdef

end CFT.WedgeDefectTransport
