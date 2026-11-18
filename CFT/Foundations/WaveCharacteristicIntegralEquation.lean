import CFT.Spherical.WedgeEnergyBalance
import CFT.Spherical.WedgeEYMSystem

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の第1層 (a)：PDE ⟺ 積分方程式の同値。

  スカラーの波動方程式 φ_uv = F について、特性方向の基本定理（FTC）の組み立てで
  次を示す：
  - `wave_integral_repr`：PDE の解は特性データと F の二重積分で表される
    （PDE → 積分方程式）。
  - `goursatFromData_*`：逆に、特性データ p, q と F から積分方程式で作った関数は
    データを再現し、混合微分が F になる（積分方程式 → PDE）。
  - `wave_eq_integral_of_pde` / `pde_of_wave_eq_integral`：両方向を合わせた同値。
  - `wedge_integral_repr`：くさび EYM 系の 3 本の方程式への当てはめ
    （r, Ω, W のそれぞれが、右辺 rhsR/rhsOm/rhsW の二重積分による表示を持つ）。

  残り（4-17 の第2・第3層）：(b) 係数を凍らせた反復写像の定義、(c) 矩形の小ささに
  よる C¹ ノルムでの縮小評価。縮小は sup ノルムではなく C¹ ノルムで取る
  （波動方程式の右辺が一階微分に依存するため）。キャップ（r = 0）を含む版は
  4-16 に残る。
-/


namespace CFT.WaveIntegralEq

open MeasureTheory intervalIntegral
open scoped Interval Topology

noncomputable section

/-- パラメータ積分の連続性：F が連続なら、t ↦ ∫ s in u₀..u, F s t は連続。
    コンパクトな矩形上での一様連続性と、区間積分のノルム評価による。 -/
theorem continuousAt_param_integral {F : ℝ → ℝ → ℝ} {u₀ u v : ℝ}
    (hF : Continuous (Function.uncurry F)) :
    ContinuousAt (fun t => ∫ s in u₀..u, F s t) v := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set L : ℝ := |u - u₀| + 1 with hL
  have hLpos : 0 < L := by
    have h0 : 0 ≤ |u - u₀| := abs_nonneg _
    linarith
  have hK : IsCompact (Set.Icc (min u₀ u) (max u₀ u) ×ˢ Set.Icc (v - 1) (v + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn (Function.uncurry F)
      (Set.Icc (min u₀ u) (max u₀ u) ×ˢ Set.Icc (v - 1) (v + 1)) :=
    hK.uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / L) (div_pos hε hLpos)
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro t ht
  have htδ : dist t v < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht1 : t ∈ Set.Icc (v - 1) (v + 1) := by
    have h1 : |t - v| < 1 := by
      rw [← Real.dist_eq]
      exact lt_of_lt_of_le ht (min_le_right _ _)
    constructor <;> linarith [abs_lt.mp h1]
  have hsub : (∫ s in u₀..u, F s t) - (∫ s in u₀..u, F s v)
      = ∫ s in u₀..u, (F s t - F s v) := by
    have hc1 : Continuous fun s => F s t :=
      hF.comp (continuous_id.prod_mk continuous_const)
    have hc2 : Continuous fun s => F s v :=
      hF.comp (continuous_id.prod_mk continuous_const)
    have hI1 : IntervalIntegrable (fun s => F s t) volume u₀ u :=
      hc1.intervalIntegrable u₀ u
    have hI2 : IntervalIntegrable (fun s => F s v) volume u₀ u :=
      hc2.intervalIntegrable u₀ u
    exact (intervalIntegral.integral_sub hI1 hI2).symm
  have hpt : ∀ s ∈ Set.uIoc u₀ u, ‖F s t - F s v‖ ≤ ε / L := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (min u₀ u) (max u₀ u) := by
      rw [Set.mem_uIoc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_of_lt (lt_of_le_of_lt (min_le_left u₀ u) h1),
          le_trans h2 (le_max_right u₀ u)⟩
      · exact ⟨le_of_lt (lt_of_le_of_lt (min_le_right u₀ u) h1),
          le_trans h2 (le_max_left u₀ u)⟩
    have hsK : (s, t) ∈ Set.Icc (min u₀ u) (max u₀ u) ×ˢ Set.Icc (v - 1) (v + 1) :=
      ⟨hsIcc, ht1⟩
    have hvK : (s, v) ∈ Set.Icc (min u₀ u) (max u₀ u) ×ˢ Set.Icc (v - 1) (v + 1) :=
      ⟨hsIcc, ⟨by linarith, by linarith⟩⟩
    have hd : dist (s, t) (s, v) < δ := by
      have hdeq : dist (s, t) (s, v) = dist t v := by
        rw [Prod.dist_eq]
        show max (dist s s) (dist t v) = dist t v
        rw [dist_self]
        exact max_eq_right dist_nonneg
      rw [hdeq]
      exact htδ
    have h := hδF (s, t) hsK (s, v) hvK hd
    rw [dist_eq_norm] at h
    exact h.le
  have hnorm : ‖∫ s in u₀..u, (F s t - F s v)‖ ≤ (ε / L) * |u - u₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [dist_eq_norm, hsub]
  calc ‖∫ s in u₀..u, (F s t - F s v)‖
      ≤ (ε / L) * |u - u₀| := hnorm
    _ < ε := by
      have h1 : (ε / L) * |u - u₀| < (ε / L) * L := by
        apply mul_lt_mul_of_pos_left _ (div_pos hε hLpos)
        have h0 : 0 ≤ |u - u₀| := abs_nonneg _
        linarith
      have h2 : (ε / L) * L = ε := div_mul_cancel₀ ε (ne_of_gt hLpos)
      exact lt_of_lt_of_eq h1 h2

/-- 二重積分の内側の積分は、区間上可積分である（フビニの部品）。 -/
theorem intervalIntegrable_param_integral {F : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hF_c : Continuous (Function.uncurry F)) :
    IntervalIntegrable (fun t => ∫ s in u₀..u, F s t) volume v₀ v := by
  have hJoint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc u₀ u)).prod (volume.restrict (Set.Ioc v₀ v))) :=
    CFT.WedgeBalance.integrable_prod_restrict_of_continuousOn hF_c.continuousOn
  have h := hJoint.integral_prod_right
  have heq : (fun t => ∫ s, Function.uncurry F (s, t) ∂(volume.restrict (Set.Ioc u₀ u)))
      = (fun t => ∫ s in u₀..u, F s t) := by
    funext t
    show (∫ s in Set.Ioc u₀ u, F s t) = ∫ s in u₀..u, F s t
    exact (intervalIntegral.integral_of_le hu).symm
  rw [heq] at h
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hv]

/-- PDE → 積分方程式：混合微分 φ_uv = φuv を持つ関数は、特性データと
    φuv の二重積分で表される（特性方向の基本定理の組み立て）。 -/
theorem wave_integral_repr {φ φv φuv : ℝ → ℝ → ℝ} {u₀ v₀ u v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hφv : ∀ u, ∀ t, HasDerivAt (fun t' => φ u t') (φv u t) t)
    (hφuv : ∀ t, ∀ s, HasDerivAt (fun s' => φv s' t) (φuv s t) s)
    (hφv_c : Continuous (Function.uncurry φv))
    (hφuv_c : Continuous (Function.uncurry φuv)) :
    φ u v = φ u₀ v + φ u v₀ - φ u₀ v₀
      + ∫ s in u₀..u, ∫ t in v₀..v, φuv s t := by
  have hφv_int : ∀ u, IntervalIntegrable (fun t => φv u t) volume v₀ v := by
    intro u
    have hc : Continuous fun t => φv u t := by
      have h1 : Continuous (fun t : ℝ => (u, t)) := continuous_const.prod_mk continuous_id
      exact hφv_c.comp h1
    exact hc.intervalIntegrable v₀ v
  have hφuv_int : ∀ t, IntervalIntegrable (fun s => φuv s t) volume u₀ u := by
    intro t
    have hc : Continuous fun s => φuv s t := by
      have h1 : Continuous (fun s : ℝ => (s, t)) := continuous_id.prod_mk continuous_const
      exact hφuv_c.comp h1
    exact hc.intervalIntegrable u₀ u
  have h1 : φ u v - φ u v₀ = ∫ t in v₀..v, φv u t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφv u t)
      (hφv_int u)).symm
  have h2 : ∀ t, φv u t - φv u₀ t = ∫ s in u₀..u, φuv s t :=
    fun t => (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφuv t s)
      (hφuv_int t)).symm
  have h3 : φ u₀ v - φ u₀ v₀ = ∫ t in v₀..v, φv u₀ t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφv u₀ t)
      (hφv_int u₀)).symm
  have hJoint : Integrable (Function.uncurry φuv)
      ((volume.restrict (Set.Ioc u₀ u)).prod (volume.restrict (Set.Ioc v₀ v))) :=
    CFT.WedgeBalance.integrable_prod_restrict_of_continuousOn hφuv_c.continuousOn
  have hswap : ∫ s in u₀..u, ∫ t in v₀..v, φuv s t
      = ∫ t in v₀..v, ∫ s in u₀..u, φuv s t :=
    CFT.WedgeBalance.intervalIntegral_swap hu hv hJoint
  have hIntSwap : IntervalIntegrable (fun t => ∫ s in u₀..u, φuv s t) volume v₀ v :=
    intervalIntegrable_param_integral hu hv hφuv_c
  have h4 : ∫ t in v₀..v, φv u t
      = (∫ t in v₀..v, φv u₀ t) + ∫ s in u₀..u, ∫ t in v₀..v, φuv s t := by
    have h5 : (fun t => φv u t) = (fun t => φv u₀ t + ∫ s in u₀..u, φuv s t) := by
      funext t
      have h := h2 t
      linarith
    rw [h5, intervalIntegral.integral_add (hφv_int u₀) hIntSwap, hswap]
  linarith [h1, h3, h4]

/-- 積分方程式で作った Goursat 問題の候補関数。データ p（v = v₀ 上）、q（u = u₀ 上）
    と右辺 F から、φ(u, v) = p u + q v − q v₀ + ∫∫ F と置く。 -/
noncomputable def goursatFromData (p q : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (u₀ v₀ : ℝ)
    (u v : ℝ) : ℝ :=
  p u + q v - q v₀ + ∫ s in u₀..u, ∫ t in v₀..v, F s t

/-- 候補は v = v₀ 上でデータ p を再現する。 -/
theorem goursatFromData_on_v {p q : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ} (u : ℝ) :
    goursatFromData p q F u₀ v₀ u v₀ = p u := by
  show p u + q v₀ - q v₀ + ∫ s in u₀..u, ∫ t in v₀..v₀, F s t = p u
  simp only [intervalIntegral.integral_same, intervalIntegral.integral_zero]
  ring

/-- 候補は u = u₀ 上でデータ q を再現する（角の両立条件 q v₀ = p u₀ を使う）。 -/
theorem goursatFromData_on_u {p q : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hcorner : q v₀ = p u₀) (v : ℝ) :
    goursatFromData p q F u₀ v₀ u₀ v = q v := by
  show p u₀ + q v - q v₀ + ∫ s in u₀..u₀, ∫ t in v₀..v, F s t = q v
  simp only [intervalIntegral.integral_same]
  rw [hcorner]
  ring

/-- 積分方程式で作った関数の v 微分：q の微分と F の u 方向の積分になる
    （FTC の逆向きの組み立て。v₀ < v の近傍で示す）。 -/
theorem goursatFromData_hasDerivAt_v {p q q' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hq : ∀ v, HasDerivAt q (q' v) v)
    (hq'c : Continuous q')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ ≤ u) (hv : v₀ < v) :
    HasDerivAt (fun v' => goursatFromData p q F u₀ v₀ u v')
      (q' v + ∫ s in u₀..u, F s v) v := by
  have hgC : Continuous (fun t => q' t + ∫ s in u₀..u, F s t) := by
    apply Continuous.add hq'c
    exact continuous_iff_continuousAt.mpr (fun t => continuousAt_param_integral hF_c)
  have hgc : ∀ t, ContinuousAt (fun t' => q' t' + ∫ s in u₀..u, F s t') t :=
    fun t => hgC.continuousAt
  have hFint : ∀ v', v₀ ≤ v' →
      IntervalIntegrable (fun t => ∫ s in u₀..u, F s t) volume v₀ v' :=
    fun v' hv' => intervalIntegrable_param_integral hu hv' hF_c
  have hid : ∀ v', v₀ < v' →
      goursatFromData p q F u₀ v₀ u v' - goursatFromData p q F u₀ v₀ u v₀
        = ∫ t in v₀..v', (q' t + ∫ s in u₀..u, F s t) := by
    intro v' hv'
    have hv'le : v₀ ≤ v' := le_of_lt hv'
    have hJoint : Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioc u₀ u)).prod (volume.restrict (Set.Ioc v₀ v'))) :=
      CFT.WedgeBalance.integrable_prod_restrict_of_continuousOn hF_c.continuousOn
    have hswap : ∫ s in u₀..u, ∫ t in v₀..v', F s t
        = ∫ t in v₀..v', ∫ s in u₀..u, F s t :=
      CFT.WedgeBalance.intervalIntegral_swap hu hv'le hJoint
    have hqint : IntervalIntegrable q' volume v₀ v' :=
      hq'c.intervalIntegrable v₀ v'
    have hqFTC : ∫ t in v₀..v', q' t = q v' - q v₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hq t) hqint
    have hsplit : ∫ t in v₀..v', (q' t + ∫ s in u₀..u, F s t)
        = (∫ t in v₀..v', q' t) + ∫ t in v₀..v', ∫ s in u₀..u, F s t :=
      intervalIntegral.integral_add hqint (hFint v' hv'le)
    have hLHS : goursatFromData p q F u₀ v₀ u v' - goursatFromData p q F u₀ v₀ u v₀
        = (q v' - q v₀) + ∫ s in u₀..u, ∫ t in v₀..v', F s t := by
      rw [goursatFromData_on_v]
      unfold goursatFromData
      ring
    rw [hLHS, hsplit, hqFTC, hswap]
  have hprim : HasDerivAt
      (fun v' => goursatFromData p q F u₀ v₀ u v₀
        + ∫ t in v₀..v', (q' t + ∫ s in u₀..u, F s t))
      (q' v + ∫ s in u₀..u, F s v) v := by
    have hint : IntervalIntegrable (fun t => q' t + ∫ s in u₀..u, F s t) volume v₀ v :=
      (hq'c.intervalIntegrable v₀ v).add (hFint v (le_of_lt hv))
    have hmeas : StronglyMeasurableAtFilter (fun t => q' t + ∫ s in u₀..u, F s t)
        (𝓝 v) volume :=
      hgC.stronglyMeasurableAtFilter volume (𝓝 v)
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas (hgc v)).const_add _
  apply hprim.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with v' hv'
  have h := hid v' hv'
  linarith

/-- 積分方程式で作った関数の v 微分の値。 -/
theorem goursatFromData_vderiv_eq {p q q' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hq : ∀ v, HasDerivAt q (q' v) v)
    (hq'c : Continuous q')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ ≤ u) (hv : v₀ < v) :
    deriv (fun v' => goursatFromData p q F u₀ v₀ u v') v
      = q' v + ∫ s in u₀..u, F s v :=
  (goursatFromData_hasDerivAt_v hq hq'c hF_c hu hv).deriv

/-- 積分方程式で作った関数の混合微分は F になる（積分方程式 → PDE の核）。 -/
theorem goursatFromData_hasDerivAt_uv {p q q' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hq : ∀ v, HasDerivAt q (q' v) v)
    (hq'c : Continuous q')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ < u) (hv : v₀ < v) :
    HasDerivAt (fun u' => deriv (fun v' => goursatFromData p q F u₀ v₀ u' v') v)
      (F u v) u := by
  have hψ : HasDerivAt (fun u' => q' v + ∫ s in u₀..u', F s v) (F u v) u := by
    have hc : Continuous fun s => F s v := by
      have h1 : Continuous (fun s : ℝ => (s, v)) := continuous_id.prod_mk continuous_const
      exact hF_c.comp h1
    have hFint : IntervalIntegrable (fun s => F s v) volume u₀ u :=
      hc.intervalIntegrable u₀ u
    have hmeas : StronglyMeasurableAtFilter (fun s => F s v) (𝓝 u) volume :=
      hc.stronglyMeasurableAtFilter volume (𝓝 u)
    exact (intervalIntegral.integral_hasDerivAt_right hFint hmeas hc.continuousAt).const_add _
  apply hψ.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with u' hu'
  exact goursatFromData_vderiv_eq hq hq'c hF_c (le_of_lt hu') hv

/-- PDE → 積分方程式：PDE の解は特性データから作った積分表示に等しい。 -/
theorem wave_eq_integral_of_pde {φ φv φuv : ℝ → ℝ → ℝ} {p q : ℝ → ℝ} {u₀ v₀ u v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hφv : ∀ u, ∀ t, HasDerivAt (fun t' => φ u t') (φv u t) t)
    (hφuv : ∀ t, ∀ s, HasDerivAt (fun s' => φv s' t) (φuv s t) s)
    (hφv_c : Continuous (Function.uncurry φv))
    (hφuv_c : Continuous (Function.uncurry φuv))
    (hdata_v : ∀ u, φ u v₀ = p u)
    (hdata_u : ∀ v, φ u₀ v = q v) :
    φ u v = goursatFromData p q φuv u₀ v₀ u v := by
  have hrep := wave_integral_repr hu hv hφv hφuv hφv_c hφuv_c
  rw [hdata_u v, hdata_v u] at hrep
  have hcorner : φ u₀ v₀ = q v₀ := hdata_u v₀
  show φ u v = p u + q v - q v₀ + ∫ s in u₀..u, ∫ t in v₀..v, φuv s t
  linarith

/-- 積分方程式 → PDE：積分表示の関数は、データのもとで混合微分が F になる。 -/
theorem pde_of_wave_eq_integral {φ : ℝ → ℝ → ℝ} {p q q' : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    {u₀ v₀ u v : ℝ}
    (hq : ∀ v, HasDerivAt q (q' v) v)
    (hq'c : Continuous q')
    (hF_c : Continuous (Function.uncurry F))
    (hu : u₀ < u) (hv : v₀ < v)
    (hφ : ∀ u' v', φ u' v' = goursatFromData p q F u₀ v₀ u' v') :
    HasDerivAt (fun u' => deriv (fun v' => φ u' v') v) (F u v) u := by
  have heq : (fun u' => deriv (fun v' => φ u' v') v)
      = (fun u' => deriv (fun v' => goursatFromData p q F u₀ v₀ u' v') v) := by
    funext u'
    simp only [hφ]
  rw [heq]
  exact goursatFromData_hasDerivAt_uv hq hq'c hF_c hu hv

/-- くさび系の r 方程式の右辺を (s, t) の関数として見たもの。 -/
noncomputable def wedgeRhsR (F : CFT.Wedge.WedgeFields) (s t : ℝ) : ℝ :=
  CFT.Wedge.rhsR (F.Om s t) (F.W s t) (CFT.Wedge.Du F.r s t) (CFT.Wedge.Dv F.r s t)
    (F.r s t)

/-- くさび系の Ω 方程式の右辺を (s, t) の関数として見たもの。 -/
noncomputable def wedgeRhsOm (F : CFT.Wedge.WedgeFields) (s t : ℝ) : ℝ :=
  CFT.Wedge.rhsOm (F.Om s t) (CFT.Wedge.Du F.Om s t) (CFT.Wedge.Dv F.Om s t)
    (CFT.Wedge.Duv F.r s t) (F.r s t) (F.W s t)

/-- くさび系の W 方程式の右辺を (s, t) の関数として見たもの。 -/
noncomputable def wedgeRhsW (F : CFT.Wedge.WedgeFields) (s t : ℝ) : ℝ :=
  CFT.Wedge.rhsW (F.Om s t) (F.W s t) (F.r s t)

/-- くさび系の1本の方程式へのスカラー表示の当てはめ（部品）。 -/
theorem wedge_field_integral_repr {φ : ℝ → ℝ → ℝ} {rhs : ℝ → ℝ → ℝ} {u₀ v₀ u v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hreg1 : ∀ u, Differentiable ℝ (fun t' => φ u t'))
    (hreg2 : ∀ t, Differentiable ℝ (fun s' => CFT.Wedge.Dv φ s' t))
    (heq : ∀ s t, CFT.Wedge.Duv φ s t = rhs s t)
    (hDv_c : Continuous (Function.uncurry (CFT.Wedge.Dv φ)))
    (hrhs_c : Continuous (Function.uncurry rhs)) :
    φ u v = φ u₀ v + φ u v₀ - φ u₀ v₀ + ∫ s in u₀..u, ∫ t in v₀..v, rhs s t := by
  apply wave_integral_repr hu hv
  · intro u t
    exact (hreg1 u t).hasDerivAt
  · intro t s
    have h := (hreg2 t s).hasDerivAt
    have h2 : HasDerivAt (fun s' => CFT.Wedge.Dv φ s' t) (CFT.Wedge.Duv φ s t) s := h
    rw [heq s t] at h2
    exact h2
  · exact hDv_c
  · exact hrhs_c

/-- くさび EYM 系の積分方程式表示：r, Ω, W のそれぞれが、特性データと
    右辺の二重積分で表される（4-17 第1層 (a) のくさび系への当てはめ）。 -/
theorem wedge_integral_repr {F : CFT.Wedge.WedgeFields} {u₀ v₀ u v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (heq : CFT.Wedge.WedgeEvolutionEqs F)
    (hr_reg : (∀ u, Differentiable ℝ (fun t' => F.r u t'))
      ∧ (∀ t, Differentiable ℝ (fun s' => CFT.Wedge.Dv F.r s' t)))
    (hOm_reg : (∀ u, Differentiable ℝ (fun t' => F.Om u t'))
      ∧ (∀ t, Differentiable ℝ (fun s' => CFT.Wedge.Dv F.Om s' t)))
    (hW_reg : (∀ u, Differentiable ℝ (fun t' => F.W u t'))
      ∧ (∀ t, Differentiable ℝ (fun s' => CFT.Wedge.Dv F.W s' t)))
    (hDr_c : Continuous (Function.uncurry (CFT.Wedge.Dv F.r)))
    (hDOm_c : Continuous (Function.uncurry (CFT.Wedge.Dv F.Om)))
    (hDW_c : Continuous (Function.uncurry (CFT.Wedge.Dv F.W)))
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR F)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm F)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW F))) :
    F.r u v = F.r u₀ v + F.r u v₀ - F.r u₀ v₀
        + ∫ s in u₀..u, ∫ t in v₀..v, wedgeRhsR F s t
    ∧ F.Om u v = F.Om u₀ v + F.Om u v₀ - F.Om u₀ v₀
        + ∫ s in u₀..u, ∫ t in v₀..v, wedgeRhsOm F s t
    ∧ F.W u v = F.W u₀ v + F.W u v₀ - F.W u₀ v₀
        + ∫ s in u₀..u, ∫ t in v₀..v, wedgeRhsW F s t := by
  refine ⟨?_, ?_, ?_⟩
  · exact wedge_field_integral_repr hu hv hr_reg.1 hr_reg.2
      (fun s t => (heq s t).1) hDr_c hrhsR_c
  · exact wedge_field_integral_repr hu hv hOm_reg.1 hOm_reg.2
      (fun s t => (heq s t).2.1) hDOm_c hrhsOm_c
  · exact wedge_field_integral_repr hu hv hW_reg.1 hW_reg.2
      (fun s t => (heq s t).2.2) hDW_c hrhsW_c

end

end CFT.WaveIntegralEq
