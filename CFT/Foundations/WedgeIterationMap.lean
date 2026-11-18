import CFT.Foundations.WaveCharacteristicIntegralEquation

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の第2層 (b)：係数を凍らせた反復写像の定義と、C¹ への写像。

  第1層 (a)（`CFT.Foundations.WaveCharacteristicIntegralEquation`）で、スカラーの
  波動方程式 φ_uv = F に対する PDE ⟺ 積分方程式の同値を示した。ここでは
  凍結した場 G に対し、右辺を G で評価した積分表示で新しい場を作る反復写像
  `wedgeIterate` を定義し、次を示す：
  - 特性データの再現（両面）。
  - u・v 両方向の微分公式と、偏微分の連続性（反復写像は C¹ 関数を C¹ 関数に写す）。
  - 混合微分は凍結した右辺に等しい（反復写像の像は「凍結した PDE」を満たす）。
  - 不動点は真の発展方程式を満たす（存在への橋渡し）。

  残り（4-17 の第3層 (c)）：矩形の小ささによる C¹ ノルムでの縮小評価。
  キャップ（r = 0）を含む版は 4-16 に残る。
-/

namespace CFT.WedgeIterate

open MeasureTheory intervalIntegral
open scoped Interval Topology
open CFT.WaveIntegralEq
open CFT.Wedge

noncomputable section

/-- パラメータ積分の連続性（第1変数側）：F が連続なら、
    s ↦ ∫ t in v₀..v, F s t は連続。第1層の `continuousAt_param_integral` を
    変数を入れ替えた関数に適用して得る。 -/
theorem continuousAt_param_integral_symm {F : ℝ → ℝ → ℝ} {v₀ v u : ℝ}
    (hF : Continuous (Function.uncurry F)) :
    ContinuousAt (fun s => ∫ t in v₀..v, F s t) u := by
  have hF' : Continuous (Function.uncurry (fun a b => F b a)) := by
    have hswap : Function.uncurry (fun a b => F b a)
        = (Function.uncurry F) ∘ Prod.swap := by
      funext p
      rfl
    rw [hswap]
    exact hF.comp continuous_swap
  exact continuousAt_param_integral (F := fun a b => F b a)
    (u₀ := v₀) (u := v) (v := u) hF'

/-- 二重積分の内側の積分は、区間上可積分である（第1変数側の版）。 -/
theorem intervalIntegrable_param_integral_symm {F : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hF_c : Continuous (Function.uncurry F)) :
    IntervalIntegrable (fun s => ∫ t in v₀..v, F s t) volume u₀ u := by
  have hF' : Continuous (Function.uncurry (fun a b => F b a)) := by
    have hswap : Function.uncurry (fun a b => F b a)
        = (Function.uncurry F) ∘ Prod.swap := by
      funext p
      rfl
    rw [hswap]
    exact hF_c.comp continuous_swap
  exact intervalIntegrable_param_integral (F := fun a b => F b a)
    (u₀ := v₀) (u := v) (v₀ := u₀) (v := u) hv hu hF'

/-- 積分方程式で作った関数の u 微分：p の微分と F の v 方向の積分になる
    （v 微分版 `goursatFromData_hasDerivAt_v` の対称版。u₀ < u の近傍で示す）。 -/
theorem goursatFromData_hasDerivAt_u {p p' q : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hp : ∀ u, HasDerivAt p (p' u) u)
    (hp'c : Continuous p')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ < u) (hv : v₀ ≤ v) :
    HasDerivAt (fun u' => goursatFromData p q F u₀ v₀ u' v)
      (p' u + ∫ t in v₀..v, F u t) u := by
  have hgC : Continuous (fun s => p' s + ∫ t in v₀..v, F s t) := by
    apply Continuous.add hp'c
    exact continuous_iff_continuousAt.mpr
      (fun s => continuousAt_param_integral_symm hF_c)
  have hFint : ∀ u', u₀ ≤ u' →
      IntervalIntegrable (fun s => ∫ t in v₀..v, F s t) volume u₀ u' :=
    fun u' hu' => intervalIntegrable_param_integral_symm hu' hv hF_c
  have hid : ∀ u', u₀ < u' →
      goursatFromData p q F u₀ v₀ u' v - goursatFromData p q F u₀ v₀ u₀ v
        = ∫ s in u₀..u', (p' s + ∫ t in v₀..v, F s t) := by
    intro u' hu'
    have hu'le : u₀ ≤ u' := le_of_lt hu'
    have hpint : IntervalIntegrable p' volume u₀ u' := hp'c.intervalIntegrable u₀ u'
    have hpFTC : ∫ s in u₀..u', p' s = p u' - p u₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s) hpint
    have hsplit : ∫ s in u₀..u', (p' s + ∫ t in v₀..v, F s t)
        = (∫ s in u₀..u', p' s) + ∫ s in u₀..u', ∫ t in v₀..v, F s t :=
      intervalIntegral.integral_add hpint (hFint u' hu'le)
    have hLHS : goursatFromData p q F u₀ v₀ u' v - goursatFromData p q F u₀ v₀ u₀ v
        = (p u' - p u₀) + ∫ s in u₀..u', ∫ t in v₀..v, F s t := by
      show (p u' + q v - q v₀ + ∫ s in u₀..u', ∫ t in v₀..v, F s t)
          - (p u₀ + q v - q v₀ + ∫ s in u₀..u₀, ∫ t in v₀..v, F s t)
          = (p u' - p u₀) + ∫ s in u₀..u', ∫ t in v₀..v, F s t
      simp only [intervalIntegral.integral_same]
      ring
    rw [hLHS, hsplit, hpFTC]
  have hprim : HasDerivAt
      (fun u' => goursatFromData p q F u₀ v₀ u₀ v
        + ∫ s in u₀..u', (p' s + ∫ t in v₀..v, F s t))
      (p' u + ∫ t in v₀..v, F u t) u := by
    have hint : IntervalIntegrable (fun s => p' s + ∫ t in v₀..v, F s t) volume u₀ u :=
      (hp'c.intervalIntegrable u₀ u).add (hFint u (le_of_lt hu))
    have hmeas : StronglyMeasurableAtFilter (fun s => p' s + ∫ t in v₀..v, F s t)
        (𝓝 u) volume :=
      hgC.stronglyMeasurableAtFilter volume (𝓝 u)
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas
      (hgC.continuousAt)).const_add _
  apply hprim.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with u' hu'
  have h := hid u' hu'
  linarith

/-- 積分方程式で作った関数の u 微分の値。 -/
theorem goursatFromData_uderiv_eq {p p' q : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hp : ∀ u, HasDerivAt p (p' u) u)
    (hp'c : Continuous p')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ < u) (hv : v₀ ≤ v) :
    deriv (fun u' => goursatFromData p q F u₀ v₀ u' v) u
      = p' u + ∫ t in v₀..v, F u t :=
  (goursatFromData_hasDerivAt_u hp hp'c hF_c hu hv).deriv

/-- 係数を凍らせた反復写像：凍結した場 G の右辺を積分表示に代入して新しい場を作る。
    (b) の中心となる定義。不動点が真の解になる（下の `wedgeIterate_fixedPoint_eqs`）。 -/
noncomputable def wedgeIterate (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (u₀ v₀ : ℝ) : WedgeFields where
  r := goursatFromData p_r q_r (wedgeRhsR G) u₀ v₀
  Om := goursatFromData p_Om q_Om (wedgeRhsOm G) u₀ v₀
  W := goursatFromData p_W q_W (wedgeRhsW G) u₀ v₀

/-- 反復写像の像は v = v₀ 上でデータ p を再現する。 -/
theorem wedgeIterate_on_v (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (u₀ v₀ : ℝ) (u : ℝ) :
    (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v₀ = p_r u
      ∧ (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v₀ = p_Om u
      ∧ (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v₀ = p_W u :=
  ⟨goursatFromData_on_v u, goursatFromData_on_v u, goursatFromData_on_v u⟩

/-- 反復写像の像は u = u₀ 上でデータ q を再現する（角の両立条件のもと）。 -/
theorem wedgeIterate_on_u (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hcorner_r : q_r v₀ = p_r u₀) (hcorner_Om : q_Om v₀ = p_Om u₀)
    (hcorner_W : q_W v₀ = p_W u₀) (v : ℝ) :
    (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u₀ v = q_r v
      ∧ (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u₀ v = q_Om v
      ∧ (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u₀ v = q_W v :=
  ⟨goursatFromData_on_u hcorner_r v, goursatFromData_on_u hcorner_Om v,
    goursatFromData_on_u hcorner_W v⟩

/-- 反復写像の像の v 微分：q の微分と凍結右辺の u 積分。 -/
theorem wedgeIterate_hasDerivAt_v (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (q_r' q_Om' q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {u v : ℝ} (hu : u₀ ≤ u) (hv : v₀ < v) :
    HasDerivAt (fun v' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v')
        (q_r' v + ∫ s in u₀..u, wedgeRhsR G s v) v
      ∧ HasDerivAt (fun v' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v')
        (q_Om' v + ∫ s in u₀..u, wedgeRhsOm G s v) v
      ∧ HasDerivAt (fun v' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v')
        (q_W' v + ∫ s in u₀..u, wedgeRhsW G s v) v :=
  ⟨goursatFromData_hasDerivAt_v hq_r hq_r'c hrhsR_c hu hv,
    goursatFromData_hasDerivAt_v hq_Om hq_Om'c hrhsOm_c hu hv,
    goursatFromData_hasDerivAt_v hq_W hq_W'c hrhsW_c hu hv⟩

/-- 反復写像の像の u 微分：p の微分と凍結右辺の v 積分。 -/
theorem wedgeIterate_hasDerivAt_u (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (p_r' p_Om' p_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hp_r : ∀ u, HasDerivAt p_r (p_r' u) u) (hp_r'c : Continuous p_r')
    (hp_Om : ∀ u, HasDerivAt p_Om (p_Om' u) u) (hp_Om'c : Continuous p_Om')
    (hp_W : ∀ u, HasDerivAt p_W (p_W' u) u) (hp_W'c : Continuous p_W')
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {u v : ℝ} (hu : u₀ < u) (hv : v₀ ≤ v) :
    HasDerivAt (fun u' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u' v)
        (p_r' u + ∫ t in v₀..v, wedgeRhsR G u t) u
      ∧ HasDerivAt (fun u' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u' v)
        (p_Om' u + ∫ t in v₀..v, wedgeRhsOm G u t) u
      ∧ HasDerivAt (fun u' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u' v)
        (p_W' u + ∫ t in v₀..v, wedgeRhsW G u t) u :=
  ⟨goursatFromData_hasDerivAt_u hp_r hp_r'c hrhsR_c hu hv,
    goursatFromData_hasDerivAt_u hp_Om hp_Om'c hrhsOm_c hu hv,
    goursatFromData_hasDerivAt_u hp_W hp_W'c hrhsW_c hu hv⟩

/-- 反復写像の像の v 偏微分は、開矩形の v 方向に連続である（C¹ の半分）。 -/
theorem wedgeIterate_vderiv_continuousOn (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (q_r' q_Om' q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {u : ℝ} (hu : u₀ ≤ u) :
    ContinuousOn (fun v => Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v)
        (Set.Ioi v₀)
      ∧ ContinuousOn (fun v => Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v)
        (Set.Ioi v₀)
      ∧ ContinuousOn (fun v => Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v)
        (Set.Ioi v₀) := by
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun v => q_r' v + ∫ s in u₀..u, wedgeRhsR G s v) :=
      Continuous.add hq_r'c (continuous_iff_continuousAt.mpr
        (fun v => continuousAt_param_integral hrhsR_c))
    have heq : ∀ v ∈ Set.Ioi v₀,
        Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v
          = q_r' v + ∫ s in u₀..u, wedgeRhsR G s v := by
      intro v hv
      exact (goursatFromData_vderiv_eq hq_r hq_r'c hrhsR_c hu hv)
    exact hcont.continuousOn.congr heq
  · have hcont : Continuous (fun v => q_Om' v + ∫ s in u₀..u, wedgeRhsOm G s v) :=
      Continuous.add hq_Om'c (continuous_iff_continuousAt.mpr
        (fun v => continuousAt_param_integral hrhsOm_c))
    have heq : ∀ v ∈ Set.Ioi v₀,
        Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v
          = q_Om' v + ∫ s in u₀..u, wedgeRhsOm G s v := by
      intro v hv
      exact (goursatFromData_vderiv_eq hq_Om hq_Om'c hrhsOm_c hu hv)
    exact hcont.continuousOn.congr heq
  · have hcont : Continuous (fun v => q_W' v + ∫ s in u₀..u, wedgeRhsW G s v) :=
      Continuous.add hq_W'c (continuous_iff_continuousAt.mpr
        (fun v => continuousAt_param_integral hrhsW_c))
    have heq : ∀ v ∈ Set.Ioi v₀,
        Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v
          = q_W' v + ∫ s in u₀..u, wedgeRhsW G s v := by
      intro v hv
      exact (goursatFromData_vderiv_eq hq_W hq_W'c hrhsW_c hu hv)
    exact hcont.continuousOn.congr heq

/-- 反復写像の像の u 偏微分は、開矩形の u 方向に連続である（C¹ の半分）。 -/
theorem wedgeIterate_uderiv_continuousOn (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (p_r' p_Om' p_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hp_r : ∀ u, HasDerivAt p_r (p_r' u) u) (hp_r'c : Continuous p_r')
    (hp_Om : ∀ u, HasDerivAt p_Om (p_Om' u) u) (hp_Om'c : Continuous p_Om')
    (hp_W : ∀ u, HasDerivAt p_W (p_W' u) u) (hp_W'c : Continuous p_W')
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {v : ℝ} (hv : v₀ ≤ v) :
    ContinuousOn (fun u => Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v)
        (Set.Ioi u₀)
      ∧ ContinuousOn (fun u => Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v)
        (Set.Ioi u₀)
      ∧ ContinuousOn (fun u => Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v)
        (Set.Ioi u₀) := by
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun u => p_r' u + ∫ t in v₀..v, wedgeRhsR G u t) :=
      Continuous.add hp_r'c (continuous_iff_continuousAt.mpr
        (fun u => continuousAt_param_integral_symm hrhsR_c))
    have heq : ∀ u ∈ Set.Ioi u₀,
        Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v
          = p_r' u + ∫ t in v₀..v, wedgeRhsR G u t := by
      intro u hu
      exact (goursatFromData_uderiv_eq hp_r hp_r'c hrhsR_c hu hv)
    exact hcont.continuousOn.congr heq
  · have hcont : Continuous (fun u => p_Om' u + ∫ t in v₀..v, wedgeRhsOm G u t) :=
      Continuous.add hp_Om'c (continuous_iff_continuousAt.mpr
        (fun u => continuousAt_param_integral_symm hrhsOm_c))
    have heq : ∀ u ∈ Set.Ioi u₀,
        Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v
          = p_Om' u + ∫ t in v₀..v, wedgeRhsOm G u t := by
      intro u hu
      exact (goursatFromData_uderiv_eq hp_Om hp_Om'c hrhsOm_c hu hv)
    exact hcont.continuousOn.congr heq
  · have hcont : Continuous (fun u => p_W' u + ∫ t in v₀..v, wedgeRhsW G u t) :=
      Continuous.add hp_W'c (continuous_iff_continuousAt.mpr
        (fun u => continuousAt_param_integral_symm hrhsW_c))
    have heq : ∀ u ∈ Set.Ioi u₀,
        Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v
          = p_W' u + ∫ t in v₀..v, wedgeRhsW G u t := by
      intro u hu
      exact (goursatFromData_uderiv_eq hp_W hp_W'c hrhsW_c hu hv)
    exact hcont.continuousOn.congr heq

/-- 反復写像の像の混合微分は、凍結した右辺に等しい
    （像は「凍結した PDE」を満たす）。 -/
theorem wedgeIterate_hasDerivAt_uv (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (q_r' q_Om' q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {u v : ℝ} (hu : u₀ < u) (hv : v₀ < v) :
    HasDerivAt (fun u' => deriv (fun v' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u' v') v)
        (wedgeRhsR G u v) u
      ∧ HasDerivAt (fun u' => deriv (fun v' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u' v') v)
        (wedgeRhsOm G u v) u
      ∧ HasDerivAt (fun u' => deriv (fun v' => (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u' v') v)
        (wedgeRhsW G u v) u :=
  ⟨goursatFromData_hasDerivAt_uv hq_r hq_r'c hrhsR_c hu hv,
    goursatFromData_hasDerivAt_uv hq_Om hq_Om'c hrhsOm_c hu hv,
    goursatFromData_hasDerivAt_uv hq_W hq_W'c hrhsW_c hu hv⟩

/-- 反復写像の不動点は、開矩形上で真の発展方程式を満たす（存在への橋渡し）。
    第3層 (c) で不動点の存在を示せば、4-17 の局所存在が閉じる。 -/
theorem wedgeIterate_fixedPoint_eqs (G : WedgeFields)
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (q_r' q_Om' q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsR_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_c : Continuous (Function.uncurry (wedgeRhsW G)))
    (hfix : G = wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀)
    {u v : ℝ} (hu : u₀ < u) (hv : v₀ < v) :
    Duv G.r u v = rhsR (G.Om u v) (G.W u v) (Du G.r u v) (Dv G.r u v) (G.r u v)
      ∧ Duv G.Om u v
          = rhsOm (G.Om u v) (Du G.Om u v) (Dv G.Om u v) (Duv G.r u v) (G.r u v) (G.W u v)
      ∧ Duv G.W u v = rhsW (G.Om u v) (G.W u v) (G.r u v) := by
  have hr : G.r = (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r :=
    congrArg WedgeFields.r hfix
  have hOm : G.Om = (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om :=
    congrArg WedgeFields.Om hfix
  have hW : G.W = (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W :=
    congrArg WedgeFields.W hfix
  have hmix := wedgeIterate_hasDerivAt_uv G p_r q_r p_Om q_Om p_W q_W
    q_r' q_Om' q_W' u₀ v₀ hq_r hq_r'c hq_Om hq_Om'c hq_W hq_W'c
    hrhsR_c hrhsOm_c hrhsW_c hu hv
  refine ⟨?_, ?_, ?_⟩
  · calc Duv G.r u v
        = Duv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r u v := by
          rw [hr]
      _ = wedgeRhsR G u v := hmix.1.deriv
      _ = rhsR (G.Om u v) (G.W u v) (Du G.r u v) (Dv G.r u v) (G.r u v) := rfl
  · calc Duv G.Om u v
        = Duv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om u v := by
          rw [hOm]
      _ = wedgeRhsOm G u v := hmix.2.1.deriv
      _ = rhsOm (G.Om u v) (Du G.Om u v) (Dv G.Om u v) (Duv G.r u v) (G.r u v)
          (G.W u v) := rfl
  · calc Duv G.W u v
        = Duv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W u v := by
          rw [hW]
      _ = wedgeRhsW G u v := hmix.2.2.deriv
      _ = rhsW (G.Om u v) (G.W u v) (G.r u v) := rfl

end

end CFT.WedgeIterate
