import CFT.Foundations.WedgeC1Norm

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の第3層 (c)：矩形の小ささによる C¹ ノルムでの縮小評価 — の第3段。
  反復写像の像の偏微分の差の縮小（微分の部分）。

  微分の部分の縮小の要点：反復写像の像の v 微分はデータの微分と凍結右辺の
  u 方向の単積分、u 微分はデータの微分と凍結右辺の v 方向の単積分で表される
  （第2層 (b) の微分公式の、閉矩形の境界を含む版 — 順序なしのフビニ交換と
  境界での FTC による）。2つの凍結場に対する像の偏微分の差は、データが相殺して
  単積分の差に等しく、凍結右辺の差は第1段のリプシッツ評価でジェット距離 D で
  抑えられるので、v 微分の差は u 方向の辺の長さ (s - u₀) × (定数 × D)、
  u 微分の差は v 方向の辺の長さ (t - v₀) × (定数 × D) で抑えられる。
  値の部分（第2段）は面積因子 (s - u₀)(t - v₀) で抑えられた。
  残り（4-17 の第3層 (c) の組み立て）：9 成分を束ねた C¹ ノルム全体での縮小と、
  矩形を小さく取れば縮小定数 < 1 になることの証明。
  キャップ（r = 0）を含む版は 4-16 に残る。
-/


namespace CFT.WedgeDeriv

open MeasureTheory intervalIntegral
open scoped Interval Topology
open CFT.WaveIntegralEq
open CFT.Wedge
open CFT.WedgeRhsLip
open CFT.WedgeIterate
open CFT.WedgeC1

noncomputable section

/-- 順序なしの区間フビニ交換：内側の区間の向きを問わない。 -/
theorem intervalIntegral_swap_any {F : ℝ → ℝ → ℝ} {u₀ u v₀ v' : ℝ}
    (hu : u₀ ≤ u) (hF_c : Continuous (Function.uncurry F)) :
    ∫ s in u₀..u, ∫ t in v₀..v', F s t = ∫ t in v₀..v', ∫ s in u₀..u, F s t := by
  rcases le_total v₀ v' with h | h
  · exact CFT.WedgeBalance.intervalIntegral_swap hu h
      (CFT.WedgeBalance.integrable_prod_restrict_of_continuousOn hF_c.continuousOn)
  · have hswap : ∫ s in u₀..u, ∫ t in v'..v₀, F s t
        = ∫ t in v'..v₀, ∫ s in u₀..u, F s t :=
      CFT.WedgeBalance.intervalIntegral_swap hu h
        (CFT.WedgeBalance.integrable_prod_restrict_of_continuousOn hF_c.continuousOn)
    calc ∫ s in u₀..u, ∫ t in v₀..v', F s t
        = ∫ s in u₀..u, (-∫ t in v'..v₀, F s t) := by
          apply intervalIntegral.integral_congr
          intro s _
          exact intervalIntegral.integral_symm v' v₀
      _ = -(∫ s in u₀..u, ∫ t in v'..v₀, F s t) :=
          intervalIntegral.integral_neg
      _ = -(∫ t in v'..v₀, ∫ s in u₀..u, F s t) := by rw [hswap]
      _ = ∫ t in v₀..v', ∫ s in u₀..u, F s t :=
          (intervalIntegral.integral_symm v' v₀).symm

/-- 積分方程式で作った関数の v 微分：境界 v = v₀ を含む版
    （`goursatFromData_hasDerivAt_v` の `v₀ < v` を `v₀ ≤ v` に弱めたもの）。 -/
theorem goursatFromData_hasDerivAt_v_of_le {p q q' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hq : ∀ v, HasDerivAt q (q' v) v)
    (hq'c : Continuous q')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ ≤ u) :
    HasDerivAt (fun v' => goursatFromData p q F u₀ v₀ u v')
      (q' v + ∫ s in u₀..u, F s v) v := by
  have hIntC : Continuous (fun t => ∫ s in u₀..u, F s t) :=
    continuous_iff_continuousAt.mpr (fun t => continuousAt_param_integral hF_c)
  have hgC : Continuous (fun t => q' t + ∫ s in u₀..u, F s t) :=
    Continuous.add hq'c hIntC
  have hgc : ∀ t, ContinuousAt (fun t' => q' t' + ∫ s in u₀..u, F s t') t :=
    fun t => hgC.continuousAt
  have hFint : ∀ v', IntervalIntegrable (fun t => ∫ s in u₀..u, F s t) volume v₀ v' :=
    fun v' => hIntC.intervalIntegrable v₀ v'
  have hid : ∀ v',
      goursatFromData p q F u₀ v₀ u v' - goursatFromData p q F u₀ v₀ u v₀
        = ∫ t in v₀..v', (q' t + ∫ s in u₀..u, F s t) := by
    intro v'
    have hswap : ∫ s in u₀..u, ∫ t in v₀..v', F s t
        = ∫ t in v₀..v', ∫ s in u₀..u, F s t :=
      intervalIntegral_swap_any hu hF_c
    have hqint : IntervalIntegrable q' volume v₀ v' :=
      hq'c.intervalIntegrable v₀ v'
    have hqFTC : ∫ t in v₀..v', q' t = q v' - q v₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hq t) hqint
    have hsplit : ∫ t in v₀..v', (q' t + ∫ s in u₀..u, F s t)
        = (∫ t in v₀..v', q' t) + ∫ t in v₀..v', ∫ s in u₀..u, F s t :=
      intervalIntegral.integral_add hqint (hFint v')
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
      (hq'c.intervalIntegrable v₀ v).add (hFint v)
    have hmeas : StronglyMeasurableAtFilter (fun t => q' t + ∫ s in u₀..u, F s t)
        (𝓝 v) volume :=
      hgC.stronglyMeasurableAtFilter volume (𝓝 v)
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas (hgc v)).const_add _
  apply hprim.congr_of_eventuallyEq
  apply Filter.EventuallyEq.of_eq
  funext v'
  have h := hid v'
  linarith

/-- 積分方程式で作った関数の v 微分の値（境界を含む版）。 -/
theorem goursatFromData_vderiv_eq_of_le {p q q' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hq : ∀ v, HasDerivAt q (q' v) v)
    (hq'c : Continuous q')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} (hu : u₀ ≤ u) :
    deriv (fun v' => goursatFromData p q F u₀ v₀ u v') v
      = q' v + ∫ s in u₀..u, F s v :=
  (goursatFromData_hasDerivAt_v_of_le hq hq'c hF_c hu).deriv

/-- 積分方程式で作った関数の u 微分：境界 u = u₀ を含む版
    （`goursatFromData_hasDerivAt_u` の `u₀ < u` を `u₀ ≤ u` に弱めたもの）。 -/
theorem goursatFromData_hasDerivAt_u_of_le {p p' q : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hp : ∀ u, HasDerivAt p (p' u) u)
    (hp'c : Continuous p')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} :
    HasDerivAt (fun u' => goursatFromData p q F u₀ v₀ u' v)
      (p' u + ∫ t in v₀..v, F u t) u := by
  have hIntC : Continuous (fun s => ∫ t in v₀..v, F s t) :=
    continuous_iff_continuousAt.mpr
      (fun s => continuousAt_param_integral_symm hF_c)
  have hgC : Continuous (fun s => p' s + ∫ t in v₀..v, F s t) :=
    Continuous.add hp'c hIntC
  have hFint : ∀ u', IntervalIntegrable (fun s => ∫ t in v₀..v, F s t) volume u₀ u' :=
    fun u' => hIntC.intervalIntegrable u₀ u'
  have hid : ∀ u',
      goursatFromData p q F u₀ v₀ u' v - goursatFromData p q F u₀ v₀ u₀ v
        = ∫ s in u₀..u', (p' s + ∫ t in v₀..v, F s t) := by
    intro u'
    have hpint : IntervalIntegrable p' volume u₀ u' := hp'c.intervalIntegrable u₀ u'
    have hpFTC : ∫ s in u₀..u', p' s = p u' - p u₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s) hpint
    have hsplit : ∫ s in u₀..u', (p' s + ∫ t in v₀..v, F s t)
        = (∫ s in u₀..u', p' s) + ∫ s in u₀..u', ∫ t in v₀..v, F s t :=
      intervalIntegral.integral_add hpint (hFint u')
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
      (hp'c.intervalIntegrable u₀ u).add (hFint u)
    have hmeas : StronglyMeasurableAtFilter (fun s => p' s + ∫ t in v₀..v, F s t)
        (𝓝 u) volume :=
      hgC.stronglyMeasurableAtFilter volume (𝓝 u)
    exact (intervalIntegral.integral_hasDerivAt_right hint hmeas
      (hgC.continuousAt)).const_add _
  apply hprim.congr_of_eventuallyEq
  apply Filter.EventuallyEq.of_eq
  funext u'
  have h := hid u'
  linarith

/-- 積分方程式で作った関数の u 微分の値（境界を含む版）。 -/
theorem goursatFromData_uderiv_eq_of_le {p p' q : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {u₀ v₀ : ℝ}
    (hp : ∀ u, HasDerivAt p (p' u) u)
    (hp'c : Continuous p')
    (hF_c : Continuous (Function.uncurry F))
    {u v : ℝ} :
    deriv (fun u' => goursatFromData p q F u₀ v₀ u' v) u
      = p' u + ∫ t in v₀..v, F u t :=
  (goursatFromData_hasDerivAt_u_of_le hp hp'c hF_c).deriv


/-- 単積分の差の評価（1変数版）：区間上で被積分関数の差が M で抑えられれば、
    単積分の差は区間の長さ × M で抑えられる。 -/
theorem single_integral_sub_le_gen {f g : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ M) :
    |(∫ x in a..b, f x) - (∫ x in a..b, g x)| ≤ (b - a) * M := by
  rw [← intervalIntegral.integral_sub hf hg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x => f x - g x) (C := M) (fun x hx => by
      rw [Real.norm_eq_abs]
      have hxIcc : x ∈ Set.Icc a b := by
        have h1 : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
        rwa [Set.uIcc_of_le hab] at h1
      exact hfg x hxIcc)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  rwa [mul_comm] at h

/-- 単積分の差の評価（第1変数版）：区間上で右辺の差が M で抑えられれば、
    単積分の差は区間の長さ × M で抑えられる。 -/
theorem single_integral_sub_le {F G : ℝ → ℝ → ℝ} {u₀ u M : ℝ}
    (hu : u₀ ≤ u)
    (hF_c : Continuous (Function.uncurry F)) (hG_c : Continuous (Function.uncurry G))
    {t : ℝ} (hFG : ∀ s ∈ Set.Icc u₀ u, |F s t - G s t| ≤ M) :
    |(∫ s in u₀..u, F s t) - (∫ s in u₀..u, G s t)| ≤ (u - u₀) * M :=
  single_integral_sub_le_gen hu
    ((hF_c.comp (continuous_id.prod_mk continuous_const)).intervalIntegrable u₀ u)
    ((hG_c.comp (continuous_id.prod_mk continuous_const)).intervalIntegrable u₀ u)
    hFG

/-- 単積分の差の評価（第2変数版）：区間上で右辺の差が M で抑えられれば、
    単積分の差は区間の長さ × M で抑えられる。 -/
theorem single_integral_sub_le_symm {F G : ℝ → ℝ → ℝ} {v₀ v M : ℝ}
    (hv : v₀ ≤ v)
    (hF_c : Continuous (Function.uncurry F)) (hG_c : Continuous (Function.uncurry G))
    {s : ℝ} (hFG : ∀ t ∈ Set.Icc v₀ v, |F s t - G s t| ≤ M) :
    |(∫ t in v₀..v, F s t) - (∫ t in v₀..v, G s t)| ≤ (v - v₀) * M :=
  single_integral_sub_le_gen hv
    ((hF_c.comp (continuous_const.prod_mk continuous_id)).intervalIntegrable v₀ v)
    ((hG_c.comp (continuous_const.prod_mk continuous_id)).intervalIntegrable v₀ v)
    hFG

/-- 反復写像の像の v 偏微分の差の縮小（r 成分）：像の v 微分の差は
    u 方向の辺の長さ × (定数 × D) で抑えられる。 -/
theorem wedgeIterate_r_vderiv_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (q_r' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hrhsR_F_c : Continuous (Function.uncurry (wedgeRhsR F)))
    (hrhsR_G_c : Continuous (Function.uncurry (wedgeRhsR G)))
    {u v M_Om M_W M_u M_v M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v)
    (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hruF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t| ≤ M_u)
    (hrvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t| ≤ M_v)
    (hrvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.r s t| ≤ M_v)
    (hD : WedgeJetLe F G u₀ u v₀ v D) :
    |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
      ≤ (s - u₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) := by
  have hF : Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
      = q_r' t + ∫ s' in u₀..s, wedgeRhsR F s' t := by
    show deriv (fun t' => goursatFromData p_r q_r (wedgeRhsR F) u₀ v₀ s t') t
        = q_r' t + ∫ s' in u₀..s, wedgeRhsR F s' t
    exact goursatFromData_vderiv_eq_of_le hq_r hq_r'c hrhsR_F_c hs
  have hG : Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
      = q_r' t + ∫ s' in u₀..s, wedgeRhsR G s' t := by
    show deriv (fun t' => goursatFromData p_r q_r (wedgeRhsR G) u₀ v₀ s t') t
        = q_r' t + ∫ s' in u₀..s, wedgeRhsR G s' t
    exact goursatFromData_vderiv_eq_of_le hq_r hq_r'c hrhsR_G_c hs
  rw [hF, hG]
  have hsub : (q_r' t + ∫ s' in u₀..s, wedgeRhsR F s' t)
        - (q_r' t + ∫ s' in u₀..s, wedgeRhsR G s' t)
      = (∫ s' in u₀..s, wedgeRhsR F s' t) - (∫ s' in u₀..s, wedgeRhsR G s' t) := by ring
  rw [hsub]
  apply single_integral_sub_le hs hrhsR_F_c hrhsR_G_c
  intro s' hs'
  have hs'u : s' ∈ Set.Icc u₀ u := ⟨hs'.1, le_trans hs'.2 hsu⟩
  have ht'v : t ∈ Set.Icc v₀ v := ⟨ht, htv⟩
  exact wedgeRhsR_sub_le_of_jet_le hr₀ hMOm hMW hMu hMv hMr
    (hB.rF_ge s' hs'u t ht'v) (hB.rG_ge s' hs'u t ht'v)
    (hB.rF_le s' hs'u t ht'v) (hB.rG_le s' hs'u t ht'v)
    (hB.OmF_le s' hs'u t ht'v)
    (hB.WF_le s' hs'u t ht'v) (hB.WG_le s' hs'u t ht'v)
    (hruF s' hs'u t ht'v)
    (hrvF s' hs'u t ht'v) (hrvG s' hs'u t ht'v)
    ⟨hD.r_le s' hs'u t ht'v, hD.Om_le s' hs'u t ht'v,
      hD.W_le s' hs'u t ht'v, hD.ru_le s' hs'u t ht'v,
      hD.rv_le s' hs'u t ht'v⟩

/-- 反復写像の像の u 偏微分の差の縮小（r 成分）：像の u 微分の差は
    v 方向の辺の長さ × (定数 × D) で抑えられる。 -/
theorem wedgeIterate_r_uderiv_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (p_r' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hp_r : ∀ u, HasDerivAt p_r (p_r' u) u) (hp_r'c : Continuous p_r')
    (hrhsR_F_c : Continuous (Function.uncurry (wedgeRhsR F)))
    (hrhsR_G_c : Continuous (Function.uncurry (wedgeRhsR G)))
    {u v M_Om M_W M_u M_v M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v)
    (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hruF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t| ≤ M_u)
    (hrvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t| ≤ M_v)
    (hrvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.r s t| ≤ M_v)
    (hD : WedgeJetLe F G u₀ u v₀ v D) :
    |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
      ≤ (t - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) := by
  have hF : Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
      = p_r' s + ∫ t' in v₀..t, wedgeRhsR F s t' := by
    show deriv (fun s' => goursatFromData p_r q_r (wedgeRhsR F) u₀ v₀ s' t) s
        = p_r' s + ∫ t' in v₀..t, wedgeRhsR F s t'
    exact goursatFromData_uderiv_eq_of_le hp_r hp_r'c hrhsR_F_c
  have hG : Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
      = p_r' s + ∫ t' in v₀..t, wedgeRhsR G s t' := by
    show deriv (fun s' => goursatFromData p_r q_r (wedgeRhsR G) u₀ v₀ s' t) s
        = p_r' s + ∫ t' in v₀..t, wedgeRhsR G s t'
    exact goursatFromData_uderiv_eq_of_le hp_r hp_r'c hrhsR_G_c
  rw [hF, hG]
  have hsub : (p_r' s + ∫ t' in v₀..t, wedgeRhsR F s t')
        - (p_r' s + ∫ t' in v₀..t, wedgeRhsR G s t')
      = (∫ t' in v₀..t, wedgeRhsR F s t') - (∫ t' in v₀..t, wedgeRhsR G s t') := by ring
  rw [hsub]
  apply single_integral_sub_le_symm ht hrhsR_F_c hrhsR_G_c
  intro t' ht'
  have hs'u : s ∈ Set.Icc u₀ u := ⟨hs, hsu⟩
  have ht'v : t' ∈ Set.Icc v₀ v := ⟨ht'.1, le_trans ht'.2 htv⟩
  exact wedgeRhsR_sub_le_of_jet_le hr₀ hMOm hMW hMu hMv hMr
    (hB.rF_ge s hs'u t' ht'v) (hB.rG_ge s hs'u t' ht'v)
    (hB.rF_le s hs'u t' ht'v) (hB.rG_le s hs'u t' ht'v)
    (hB.OmF_le s hs'u t' ht'v)
    (hB.WF_le s hs'u t' ht'v) (hB.WG_le s hs'u t' ht'v)
    (hruF s hs'u t' ht'v)
    (hrvF s hs'u t' ht'v) (hrvG s hs'u t' ht'v)
    ⟨hD.r_le s hs'u t' ht'v, hD.Om_le s hs'u t' ht'v,
      hD.W_le s hs'u t' ht'v, hD.ru_le s hs'u t' ht'v,
      hD.rv_le s hs'u t' ht'v⟩

/-- 反復写像の像の v 偏微分の差の縮小（Ω 成分）。 -/
theorem wedgeIterate_Om_vderiv_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (q_Om' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hrhsOm_F_c : Continuous (Function.uncurry (wedgeRhsOm F)))
    (hrhsOm_G_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    {u v M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hOuF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t| ≤ M_Ou)
    (hOvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t| ≤ M_Ov)
    (hOvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.Om s t| ≤ M_Ov)
    (hruvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv F.r s t| ≤ M_uv)
    (hruvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv G.r s t| ≤ M_uv)
    (hD : WedgeJetLe F G u₀ u v₀ v D) :
    |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
      ≤ (s - u₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) := by
  have hF : Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
      = q_Om' t + ∫ s' in u₀..s, wedgeRhsOm F s' t := by
    show deriv (fun t' => goursatFromData p_Om q_Om (wedgeRhsOm F) u₀ v₀ s t') t
        = q_Om' t + ∫ s' in u₀..s, wedgeRhsOm F s' t
    exact goursatFromData_vderiv_eq_of_le hq_Om hq_Om'c hrhsOm_F_c hs
  have hG : Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
      = q_Om' t + ∫ s' in u₀..s, wedgeRhsOm G s' t := by
    show deriv (fun t' => goursatFromData p_Om q_Om (wedgeRhsOm G) u₀ v₀ s t') t
        = q_Om' t + ∫ s' in u₀..s, wedgeRhsOm G s' t
    exact goursatFromData_vderiv_eq_of_le hq_Om hq_Om'c hrhsOm_G_c hs
  rw [hF, hG]
  have hsub : (q_Om' t + ∫ s' in u₀..s, wedgeRhsOm F s' t)
        - (q_Om' t + ∫ s' in u₀..s, wedgeRhsOm G s' t)
      = (∫ s' in u₀..s, wedgeRhsOm F s' t) - (∫ s' in u₀..s, wedgeRhsOm G s' t) := by ring
  rw [hsub]
  apply single_integral_sub_le hs hrhsOm_F_c hrhsOm_G_c
  intro s' hs'
  have hs'u : s' ∈ Set.Icc u₀ u := ⟨hs'.1, le_trans hs'.2 hsu⟩
  have ht'v : t ∈ Set.Icc v₀ v := ⟨ht, htv⟩
  exact wedgeRhsOm_sub_le_of_jet_le hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMr
    (hB.rF_ge s' hs'u t ht'v) (hB.rG_ge s' hs'u t ht'v)
    (hB.rF_le s' hs'u t ht'v) (hB.rG_le s' hs'u t ht'v)
    (hB.OmF_ge s' hs'u t ht'v) (hB.OmG_ge s' hs'u t ht'v)
    (hB.OmF_le s' hs'u t ht'v) (hB.OmG_le s' hs'u t ht'v)
    (hOuF s' hs'u t ht'v)
    (hOvF s' hs'u t ht'v) (hOvG s' hs'u t ht'v)
    (hruvF s' hs'u t ht'v) (hruvG s' hs'u t ht'v)
    (hB.WF_le s' hs'u t ht'v) (hB.WG_le s' hs'u t ht'v)
    ⟨hD.r_le s' hs'u t ht'v, hD.Om_le s' hs'u t ht'v,
      hD.W_le s' hs'u t ht'v, hD.Ou_le s' hs'u t ht'v,
      hD.Ov_le s' hs'u t ht'v, hD.ruv_le s' hs'u t ht'v⟩

/-- 反復写像の像の u 偏微分の差の縮小（Ω 成分）。 -/
theorem wedgeIterate_Om_uderiv_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (p_Om' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hp_Om : ∀ u, HasDerivAt p_Om (p_Om' u) u) (hp_Om'c : Continuous p_Om')
    (hrhsOm_F_c : Continuous (Function.uncurry (wedgeRhsOm F)))
    (hrhsOm_G_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    {u v M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hOuF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t| ≤ M_Ou)
    (hOvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t| ≤ M_Ov)
    (hOvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.Om s t| ≤ M_Ov)
    (hruvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv F.r s t| ≤ M_uv)
    (hruvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv G.r s t| ≤ M_uv)
    (hD : WedgeJetLe F G u₀ u v₀ v D) :
    |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
      ≤ (t - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) := by
  have hF : Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
      = p_Om' s + ∫ t' in v₀..t, wedgeRhsOm F s t' := by
    show deriv (fun s' => goursatFromData p_Om q_Om (wedgeRhsOm F) u₀ v₀ s' t) s
        = p_Om' s + ∫ t' in v₀..t, wedgeRhsOm F s t'
    exact goursatFromData_uderiv_eq_of_le hp_Om hp_Om'c hrhsOm_F_c
  have hG : Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
      = p_Om' s + ∫ t' in v₀..t, wedgeRhsOm G s t' := by
    show deriv (fun s' => goursatFromData p_Om q_Om (wedgeRhsOm G) u₀ v₀ s' t) s
        = p_Om' s + ∫ t' in v₀..t, wedgeRhsOm G s t'
    exact goursatFromData_uderiv_eq_of_le hp_Om hp_Om'c hrhsOm_G_c
  rw [hF, hG]
  have hsub : (p_Om' s + ∫ t' in v₀..t, wedgeRhsOm F s t')
        - (p_Om' s + ∫ t' in v₀..t, wedgeRhsOm G s t')
      = (∫ t' in v₀..t, wedgeRhsOm F s t') - (∫ t' in v₀..t, wedgeRhsOm G s t') := by ring
  rw [hsub]
  apply single_integral_sub_le_symm ht hrhsOm_F_c hrhsOm_G_c
  intro t' ht'
  have hs'u : s ∈ Set.Icc u₀ u := ⟨hs, hsu⟩
  have ht'v : t' ∈ Set.Icc v₀ v := ⟨ht'.1, le_trans ht'.2 htv⟩
  exact wedgeRhsOm_sub_le_of_jet_le hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMr
    (hB.rF_ge s hs'u t' ht'v) (hB.rG_ge s hs'u t' ht'v)
    (hB.rF_le s hs'u t' ht'v) (hB.rG_le s hs'u t' ht'v)
    (hB.OmF_ge s hs'u t' ht'v) (hB.OmG_ge s hs'u t' ht'v)
    (hB.OmF_le s hs'u t' ht'v) (hB.OmG_le s hs'u t' ht'v)
    (hOuF s hs'u t' ht'v)
    (hOvF s hs'u t' ht'v) (hOvG s hs'u t' ht'v)
    (hruvF s hs'u t' ht'v) (hruvG s hs'u t' ht'v)
    (hB.WF_le s hs'u t' ht'v) (hB.WG_le s hs'u t' ht'v)
    ⟨hD.r_le s hs'u t' ht'v, hD.Om_le s hs'u t' ht'v,
      hD.W_le s hs'u t' ht'v, hD.Ou_le s hs'u t' ht'v,
      hD.Ov_le s hs'u t' ht'v, hD.ruv_le s hs'u t' ht'v⟩

/-- 反復写像の像の v 偏微分の差の縮小（W 成分）。 -/
theorem wedgeIterate_W_vderiv_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsW_F_c : Continuous (Function.uncurry (wedgeRhsW F)))
    (hrhsW_G_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {u v M_Om M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hD : WedgeJetLe F G u₀ u v₀ v D) :
    |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
      ≤ (s - u₀) * (wedgeLipW M_Om M_W M_r r₀ * D) := by
  have hF : Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
      = q_W' t + ∫ s' in u₀..s, wedgeRhsW F s' t := by
    show deriv (fun t' => goursatFromData p_W q_W (wedgeRhsW F) u₀ v₀ s t') t
        = q_W' t + ∫ s' in u₀..s, wedgeRhsW F s' t
    exact goursatFromData_vderiv_eq_of_le hq_W hq_W'c hrhsW_F_c hs
  have hG : Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
      = q_W' t + ∫ s' in u₀..s, wedgeRhsW G s' t := by
    show deriv (fun t' => goursatFromData p_W q_W (wedgeRhsW G) u₀ v₀ s t') t
        = q_W' t + ∫ s' in u₀..s, wedgeRhsW G s' t
    exact goursatFromData_vderiv_eq_of_le hq_W hq_W'c hrhsW_G_c hs
  rw [hF, hG]
  have hsub : (q_W' t + ∫ s' in u₀..s, wedgeRhsW F s' t)
        - (q_W' t + ∫ s' in u₀..s, wedgeRhsW G s' t)
      = (∫ s' in u₀..s, wedgeRhsW F s' t) - (∫ s' in u₀..s, wedgeRhsW G s' t) := by ring
  rw [hsub]
  apply single_integral_sub_le hs hrhsW_F_c hrhsW_G_c
  intro s' hs'
  have hs'u : s' ∈ Set.Icc u₀ u := ⟨hs'.1, le_trans hs'.2 hsu⟩
  have ht'v : t ∈ Set.Icc v₀ v := ⟨ht, htv⟩
  exact wedgeRhsW_sub_le_of_jet_le hr₀ hMOm hMW hMr
    (hB.rF_ge s' hs'u t ht'v) (hB.rG_ge s' hs'u t ht'v)
    (hB.rF_le s' hs'u t ht'v) (hB.rG_le s' hs'u t ht'v)
    (hB.OmF_le s' hs'u t ht'v)
    (hB.WF_le s' hs'u t ht'v) (hB.WG_le s' hs'u t ht'v)
    ⟨hD.r_le s' hs'u t ht'v, hD.Om_le s' hs'u t ht'v,
      hD.W_le s' hs'u t ht'v⟩

/-- 反復写像の像の u 偏微分の差の縮小（W 成分）。 -/
theorem wedgeIterate_W_uderiv_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (p_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    (hp_W : ∀ u, HasDerivAt p_W (p_W' u) u) (hp_W'c : Continuous p_W')
    (hrhsW_F_c : Continuous (Function.uncurry (wedgeRhsW F)))
    (hrhsW_G_c : Continuous (Function.uncurry (wedgeRhsW G)))
    {u v M_Om M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hD : WedgeJetLe F G u₀ u v₀ v D) :
    |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
      ≤ (t - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) := by
  have hF : Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
      = p_W' s + ∫ t' in v₀..t, wedgeRhsW F s t' := by
    show deriv (fun s' => goursatFromData p_W q_W (wedgeRhsW F) u₀ v₀ s' t) s
        = p_W' s + ∫ t' in v₀..t, wedgeRhsW F s t'
    exact goursatFromData_uderiv_eq_of_le hp_W hp_W'c hrhsW_F_c
  have hG : Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
      = p_W' s + ∫ t' in v₀..t, wedgeRhsW G s t' := by
    show deriv (fun s' => goursatFromData p_W q_W (wedgeRhsW G) u₀ v₀ s' t) s
        = p_W' s + ∫ t' in v₀..t, wedgeRhsW G s t'
    exact goursatFromData_uderiv_eq_of_le hp_W hp_W'c hrhsW_G_c
  rw [hF, hG]
  have hsub : (p_W' s + ∫ t' in v₀..t, wedgeRhsW F s t')
        - (p_W' s + ∫ t' in v₀..t, wedgeRhsW G s t')
      = (∫ t' in v₀..t, wedgeRhsW F s t') - (∫ t' in v₀..t, wedgeRhsW G s t') := by ring
  rw [hsub]
  apply single_integral_sub_le_symm ht hrhsW_F_c hrhsW_G_c
  intro t' ht'
  have hs'u : s ∈ Set.Icc u₀ u := ⟨hs, hsu⟩
  have ht'v : t' ∈ Set.Icc v₀ v := ⟨ht'.1, le_trans ht'.2 htv⟩
  exact wedgeRhsW_sub_le_of_jet_le hr₀ hMOm hMW hMr
    (hB.rF_ge s hs'u t' ht'v) (hB.rG_ge s hs'u t' ht'v)
    (hB.rF_le s hs'u t' ht'v) (hB.rG_le s hs'u t' ht'v)
    (hB.OmF_le s hs'u t' ht'v)
    (hB.WF_le s hs'u t' ht'v) (hB.WG_le s hs'u t' ht'v)
    ⟨hD.r_le s hs'u t' ht'v, hD.Om_le s hs'u t' ht'v,
      hD.W_le s hs'u t' ht'v⟩

end

end CFT.WedgeDeriv
