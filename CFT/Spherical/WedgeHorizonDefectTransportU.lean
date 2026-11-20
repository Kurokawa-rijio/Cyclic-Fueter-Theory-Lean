/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **u 方向の輸送方程式**。前段までで v 方向の輸送
    ∂_v D = S、D(u, v) := (∂_u Ω)/Ω − g(r)·(∂_u r)
  が示され、S の明示形と角での値 S(0, 0) = −1 が固定された。
  しかし対応仮説 Ω = c·f(r) は u・v 両方向の対数微分の一致を要する。
  ここでは v 方向の欠陥
    D_v(u, v) := (∂_v Ω)/Ω − g(r)·(∂_v r)
  に対して u 方向の輸送方程式
    ∂_u D_v = S
  を示す（`defectV_hasDerivAt_u`）。鍵は ∂_u(Ω_v/Ω) における相殺で、
  Ω_vu = Ω_uv の右辺を代入すると
    ∂_u(Ω_v/Ω) = Ω/r² + 2·r_u·r_v/r² − 2Ω(1−W²)²/r⁴
  となり、v 方向の ∂_v(Ω_u/Ω) と**同じ閉形**になる
  （sympy による明示計算 `/tmp/check_u_transport.py` でも照合済み）。
  したがって u 方向の可積分性条件も同じソース項 S であり、両方向の
  輸送は一つの S を共有する（`defect_sources_agree`）。
  角では D_v 自体も 0 で、その u 微分は ∂_u D_v(0, 0) = −1 である。

  混合微分の交換（∂_u(∂_v Ω) = Ω_uv など）は `C2Data.deriv_uv_u` の
  仮定として受け取る。C² 級の解への適用版（`defectV_hasDerivAt_u_of_C2`）
  では `C2On` から引き出す。RN への特殊化（`defectV_transport_rn`）では
  g = `rnLogDeriv`、g′ はその明示微分 `rnLogDeriv'` を使う。
-/
import CFT.Spherical.WedgeHorizonDefectTransport
import CFT.Spherical.WedgeHorizonDefectCorner

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeUniq CFT.RNLogDeriv

namespace CFT.WedgeDefectTransportU

/-- v 方向の対数微分の欠陥：u 切片上で (∂_v Ω)/Ω と g(r)·(∂_v r) の差。
    0 なら v 方向の対数微分が一致する。 -/
noncomputable def logDerivDefectV (F : WedgeFields) (g : ℝ → ℝ) (u v : ℝ) : ℝ :=
  Dv F.Om u v / F.Om u v - g (F.r u v) * Dv F.r u v

/-- Ω の対数微分の u 微分：発展方程式（Ω_uv と r_uv の右辺）を代入すると
    Ω_v が相殺し、v 方向の ∂_v(Ω_u/Ω) と同じ閉形になる。 -/
theorem Om_logDeriv_hasDerivAt_u {F : WedgeFields} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' v) (Duv F.Om u v) u)
    (hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u) :
    HasDerivAt (fun u' => Dv F.Om u' v / F.Om u' v)
      (F.Om u v / (F.r u v) ^ 2 + 2 * Du F.r u v * Dv F.r u v / (F.r u v) ^ 2
        - 2 * F.Om u v * (1 - (F.W u v) ^ 2) ^ 2 / (F.r u v) ^ 4) u := by
  have hdiv := hOvu.div hOmu hOm
  have hOmEq := (heq u v).2.1
  have hrEq := (heq u v).1
  rw [hOmEq, hrEq] at hdiv
  convert hdiv using 1
  simp only [rhsOm, rhsR]
  field_simp
  ring

/-- g(r)·r_v の u 微分：連鎖律と積の微分。値の因子の順序は `defectSource` に合わせる。 -/
theorem rLogDeriv_hasDerivAt_u {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hru : HasDerivAt (fun u' => F.r u' v) (Du F.r u v) u)
    (hrv : HasDerivAt (fun u' => Dv F.r u' v) (Duv F.r u v) u) :
    HasDerivAt (fun u' => g (F.r u' v) * Dv F.r u' v)
      (g' (F.r u v) * Dv F.r u v * Du F.r u v
        + g (F.r u v) * Duv F.r u v) u := by
  have hcomp : HasDerivAt (fun u' => g (F.r u' v))
      (g' (F.r u v) * Du F.r u v) u := hg.comp u hru
  have hmul := hcomp.mul hrv
  convert hmul using 1
  ring

/-- v 方向の欠陥の u 方向の輸送方程式：発展方程式をみたす場では、
    v 方向の欠陥の u 微分は v 方向の輸送と同じソース項 `defectSource` に等しい。 -/
theorem defectV_hasDerivAt_u {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' v) (Duv F.Om u v) u)
    (hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u)
    (hru : HasDerivAt (fun u' => F.r u' v) (Du F.r u v) u)
    (hrv : HasDerivAt (fun u' => Dv F.r u' v) (Duv F.r u v) u) :
    HasDerivAt (fun u' => logDerivDefectV F g u' v) (defectSource F g g' u v) u := by
  have hA := Om_logDeriv_hasDerivAt_u heq hOm hr hOvu hOmu
  have hB := rLogDeriv_hasDerivAt_u hg hru hrv
  have hB' : HasDerivAt (fun u' => g (F.r u' v) * Dv F.r u' v)
      (g' (F.r u v) * Dv F.r u v * Du F.r u v
        + g (F.r u v) * rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v)) u := by
    rw [(heq u v).1] at hB
    exact hB
  have hsub := hA.sub hB'
  convert hsub using 1

/-- v 方向の欠陥の u 方向の輸送方程式の `deriv` 版。 -/
theorem defectV_deriv_u {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' v) (Duv F.Om u v) u)
    (hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u)
    (hru : HasDerivAt (fun u' => F.r u' v) (Du F.r u v) u)
    (hrv : HasDerivAt (fun u' => Dv F.r u' v) (Duv F.r u v) u) :
    deriv (fun u' => logDerivDefectV F g u' v) u = defectSource F g g' u v :=
  (defectV_hasDerivAt_u heq hOm hr hg hOvu hOmu hru hrv).deriv

/-- u 方向の可積分性条件：v 方向の欠陥が u の開区間上で恒等的に 0 ならば、
    その区間の内点ではソース項は 0。 -/
theorem correspondence_nec_source_zero_u {F : WedgeFields} {g g' : ℝ → ℝ}
    {u v : ℝ} {a b : ℝ}
    (hu : u ∈ Ioo a b)
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' v) (Duv F.Om u v) u)
    (hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u)
    (hru : HasDerivAt (fun u' => F.r u' v) (Du F.r u v) u)
    (hrv : HasDerivAt (fun u' => Dv F.r u' v) (Duv F.r u v) u)
    (hdef : ∀ u' ∈ Ioo a b, logDerivDefectV F g u' v = 0) :
    defectSource F g g' u v = 0 := by
  have hder := defectV_hasDerivAt_u heq hOm hr hg hOvu hOmu hru hrv
  have hEq : (fun u' => logDerivDefectV F g u' v) =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with u' hu'
    exact hdef u' hu'
  have h0 : HasDerivAt (fun u' => logDerivDefectV F g u' v) 0 u :=
    (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hEq
  exact hder.unique h0

/-- C² 級の解への適用版：混合微分の交換は `C2On` から引き出す。 -/
theorem defectV_hasDerivAt_u_of_C2 {F : WedgeFields} {g g' : ℝ → ℝ} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hC2Om : C2On a b F.Om) (hC2r : C2On a b F.r)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b) :
    HasDerivAt (fun u' => logDerivDefectV F g u' v) (defectSource F g g' u v) u :=
  defectV_hasDerivAt_u heq hOm hr hg
    (hC2Om.deriv_uv_u u hu v hv) (hC2Om.deriv_u u hu v hv)
    (hC2r.deriv_u u hu v hv) (hC2r.deriv_uv_u u hu v hv)

/-- RN への特殊化：v 方向の欠陥の u 方向の輸送方程式。 -/
theorem defectV_transport_rn {F : WedgeFields} {rp rm u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm)
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' v) (Duv F.Om u v) u)
    (hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u)
    (hru : HasDerivAt (fun u' => F.r u' v) (Du F.r u v) u)
    (hrv : HasDerivAt (fun u' => Dv F.r u' v) (Duv F.r u v) u) :
    HasDerivAt (fun u' => logDerivDefectV F (rnLogDeriv rp rm) u' v)
      (defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v) u :=
  defectV_hasDerivAt_u heq hOm hr
    (rnLogDeriv_hasDerivAt hr hrp hrm) hOvu hOmu hru hrv

/-- 両方向の輸送は同じソース項を共有する：u 方向の欠陥の v 微分と
    v 方向の欠陥の u 微分は等しい。 -/
theorem defect_sources_agree {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOmu_v : HasDerivAt (fun v' => Du F.Om u v') (Duv F.Om u v) v)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru_v : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' v) (Duv F.Om u v) u)
    (hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u)
    (hru : HasDerivAt (fun u' => F.r u' v) (Du F.r u v) u)
    (hrv_u : HasDerivAt (fun u' => Dv F.r u' v) (Duv F.r u v) u) :
    deriv (fun v' => logDerivDefect F g u v') v
      = deriv (fun u' => logDerivDefectV F g u' v) u := by
  rw [defect_deriv_v heq hOm hr hg hOmu_v hOmv hrv hru_v,
    defectV_deriv_u heq hOm hr hg hOvu hOmu hru hrv_u]

/-- 角では v 方向の欠陥 D_v 自体も 0 である（Ω_v = 0、r_v = 0 による）。 -/
theorem logDerivDefectV_corner_eq_zero {F : WedgeFields} {g : ℝ → ℝ}
    (hdata : HasWedgeData F) :
    logDerivDefectV F g 0 0 = 0 := by
  obtain ⟨hr1, hOm1, _⟩ := CFT.WedgeCorner.data_values hdata
  simp only [logDerivDefectV, CFT.WedgeCorner.data_Om_v hdata,
    CFT.WedgeCorner.data_r_v hdata, hr1, hOm1]
  simp

/-- 角での v 方向の欠陥の u 微分：u 方向の輸送方程式により ∂_u D_v(0, 0) = S(0, 0) = −1。 -/
theorem defectV_deriv_u_corner {F : WedgeFields} {g g' : ℝ → ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hg : HasDerivAt g (g' (F.r 0 0)) (F.r 0 0))
    (hOvu : HasDerivAt (fun u' => Dv F.Om u' 0) (Duv F.Om 0 0) 0)
    (hOmu : HasDerivAt (fun u' => F.Om u' 0) (Du F.Om 0 0) 0)
    (hru : HasDerivAt (fun u' => F.r u' 0) (Du F.r 0 0) 0)
    (hrv : HasDerivAt (fun u' => Dv F.r u' 0) (Duv F.r 0 0) 0) :
    deriv (fun u' => logDerivDefectV F g u' 0) 0 = -1 := by
  obtain ⟨hr1, hOm1, _⟩ := CFT.WedgeCorner.data_values hdata
  have hOm : F.Om 0 0 ≠ 0 := by rw [hOm1]; norm_num
  have hr : F.r 0 0 ≠ 0 := by rw [hr1]; norm_num
  have h := defectV_deriv_u heq hOm hr hg hOvu hOmu hru hrv
  rw [h, CFT.WedgeDefectCorner.defectSource_corner_eq hdata]

end CFT.WedgeDefectTransportU
