/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **r_u·r_v の内部での厳密な正値性（第三段：W の微分の非ゼロからの厳密化）**。
  前段（`WedgeHorizonRProductSign`）では拘束から内部で r_u ≤ 0 かつ
  r_v ≤ 0、したがって r_u·r_v ≥ 0 であることを示した。ここでは、W の
  微分が区間内のどこかで非ゼロなら、商 Dv r/Ω・Du r/Ω はその点の先で
  真に減少し、したがって r_v < 0・r_u < 0 が厳密に成り立つことを示す。
  すなわち r_u·r_v > 0（内部、W の微分の非ゼロを仮定して）。

  鍵は実解析の一般補題である：微分 ≤ 0 の関数について、微分が一点で
  < 0 であり、その点で微分が連続なら、区間の右端の値は左端より真に
  小さい（`lt_of_deriv_nonpos_of_exists_deriv_neg`）。微分の連続性に
  より微分 < 0 の近傍が取れ、その小さい区間上では狭義単調減少
  （`strictAntiOn_of_deriv_neg`）、両側では非増加
  （`antitoneOn_of_deriv_nonpos`）であることによる。商の微分
  −2(Dv W)²/(r·Ω) は Dv W ≠ 0 の点で < 0 であり（`Dv_r_div_Om_deriv_neg_of_DvW_ne_zero`）、
  C² 級の場ではその微分は連続である（`Dv_r_div_Om_deriv_continuousAt`）。

  残りは、一様な正の下界 r_u·r_v ≥ m > 0 の実際のくさび解からの検証
  （厳密な正値性は各点ごとのもので、一様な下界 m > 0 にはさらに
  コンパクト性・定量評価が要る）と、ρ そのものの構成である。
-/
import CFT.Spherical.WedgeHorizonRProductSign

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeRProductData CFT.CharUniqueness
open CFT.WedgeRProductSign

namespace CFT.WedgeRProductStrict

/-- 微分 ≤ 0 で、一点で微分 < 0（かつ微分がその点で連続）なら、右端の値は左端より真に小さい。 -/
theorem lt_of_deriv_nonpos_of_exists_deriv_neg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (interior (Icc a b)))
    (hder : ∀ x ∈ interior (Icc a b), deriv f x ≤ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hneg : deriv f t₀ < 0)
    (hcontderiv : ContinuousAt (deriv f) t₀) :
    f b < f a := by
  have hev1 : ∀ᶠ t in 𝓝 t₀, t ∈ Ioo a b := Ioo_mem_nhds ht₀.1 ht₀.2
  have hev2 : ∀ᶠ t in 𝓝 t₀, deriv f t < 0 :=
    hcontderiv.eventually (Iio_mem_nhds hneg)
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ Ioo a b ∧ deriv f t < 0 := hev1.and hev2
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδball⟩ := hev
  set c₁ := t₀ - δ / 2 with hc₁
  set c₂ := t₀ + δ / 2 with hc₂
  have hδ2 : δ / 2 < δ := half_lt_self hδ
  have hc₁mem : c₁ ∈ Ioo a b := by
    have h1 : dist c₁ t₀ < δ := by
      rw [Real.dist_eq]
      have habs : |c₁ - t₀| = δ / 2 := by
        have h2 : c₁ - t₀ = -(δ / 2) := by rw [hc₁]; ring
        rw [h2, abs_neg, abs_of_pos (half_pos hδ)]
      rw [habs]; exact hδ2
    exact (hδball h1).1
  have hc₂mem : c₂ ∈ Ioo a b := by
    have h1 : dist c₂ t₀ < δ := by
      rw [Real.dist_eq]
      have habs : |c₂ - t₀| = δ / 2 := by
        have h2 : c₂ - t₀ = δ / 2 := by rw [hc₂]; ring
        rw [h2, abs_of_pos (half_pos hδ)]
      rw [habs]; exact hδ2
    exact (hδball h1).1
  have hc₁c₂ : c₁ < c₂ := by rw [hc₁, hc₂]; linarith [hδ]
  -- [a, c₁] 上では非増加
  have hanti1 : AntitoneOn f (Icc a c₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a c₁)
    · exact hcont.mono (Icc_subset_Icc le_rfl hc₁mem.2.le)
    · apply hdiff.mono
      rw [interior_Icc, interior_Icc]
      exact Ioo_subset_Ioo_right hc₁mem.2.le
    · intro x hx
      rw [interior_Icc] at hx
      apply hder
      rw [interior_Icc]
      exact ⟨hx.1, hx.2.trans_le hc₁mem.2.le⟩
  -- [c₁, c₂] 上では狭義単調減少（微分 < 0 の近傍）
  have hstrict : StrictAntiOn f (Icc c₁ c₂) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c₁ c₂)
    · exact hcont.mono (Icc_subset_Icc hc₁mem.1.le hc₂mem.2.le)
    · intro x hx
      rw [interior_Icc] at hx
      have hdist : dist x t₀ < δ := by
        rw [Real.dist_eq]
        have h1 : -(δ / 2) < x - t₀ := by rw [hc₁] at hx; linarith [hx.1]
        have h2 : x - t₀ < δ / 2 := by rw [hc₂] at hx; linarith [hx.2]
        rw [abs_lt]; exact ⟨by linarith [h1, hδ], by linarith [h2, hδ]⟩
      exact (hδball hdist).2
  -- [c₂, b] 上では非増加
  have hanti2 : AntitoneOn f (Icc c₂ b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc c₂ b)
    · exact hcont.mono (Icc_subset_Icc hc₂mem.1.le le_rfl)
    · apply hdiff.mono
      rw [interior_Icc, interior_Icc]
      exact Ioo_subset_Ioo_left hc₂mem.1.le
    · intro x hx
      rw [interior_Icc] at hx
      apply hder
      rw [interior_Icc]
      exact ⟨hc₂mem.1.trans hx.1, hx.2⟩
  have h1 : f c₁ ≤ f a :=
    hanti1 ⟨le_rfl, hc₁mem.1.le⟩ ⟨hc₁mem.1.le, le_rfl⟩ hc₁mem.1.le
  have h2 : f c₂ < f c₁ :=
    hstrict ⟨le_rfl, hc₁c₂.le⟩ ⟨hc₁c₂.le, le_rfl⟩ hc₁c₂
  have h3 : f b ≤ f c₂ :=
    hanti2 ⟨le_rfl, hc₂mem.2.le⟩ ⟨hc₂mem.2.le, le_rfl⟩ hc₂mem.2.le
  linarith [h1, h2, h3]

/-- Dv W ≠ 0 の点では、v ↦ Dv r/Ω の微分は真に負。 -/
theorem Dv_r_div_Om_deriv_neg_of_DvW_ne_zero {F : WedgeFields} {a b u v₁ : ℝ}
    (hcon : WedgeConstraints F) (hC2Om : C2On a b F.Om)
    (hu : u ∈ Icc (0 : ℝ) a) (hv₁ : v₁ ∈ Icc (0 : ℝ) b)
    (hOm : 0 < F.Om u v₁) (hr : 0 < F.r u v₁)
    (hW : Dv F.W u v₁ ≠ 0)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v₁) v₁) :
    deriv (fun v' => Dv F.r u v' / F.Om u v') v₁ < 0 := by
  rw [(Dv_r_div_Om_hasDerivAt hcon hC2Om hu hv₁ hOm.ne' hr.ne' hrvv).deriv]
  have hsq : (0 : ℝ) < (Dv F.W u v₁) ^ 2 := sq_pos_of_ne_zero hW
  have hpos : (0 : ℝ) < 2 * (Dv F.W u v₁) ^ 2 / (F.r u v₁ * F.Om u v₁) :=
    div_pos (by linarith) (mul_pos hr hOm)
  have h4 : -2 * (Dv F.W u v₁) ^ 2 / (F.r u v₁ * F.Om u v₁)
      = -(2 * (Dv F.W u v₁) ^ 2 / (F.r u v₁ * F.Om u v₁)) := by ring
  rw [h4]
  linarith [hpos]

/-- v ↦ Dv r/Ω の微分は、C² 級の場では内点で連続（明示形による）。 -/
theorem Dv_r_div_Om_deriv_continuousAt {F : WedgeFields} {a b u v₁ : ℝ}
    (hcon : WedgeConstraints F) (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (hC2W : C2On a b F.W)
    (hu : u ∈ Icc (0 : ℝ) a) (hv₁ : v₁ ∈ Ioo (0 : ℝ) b)
    (hOm : ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' ≠ 0)
    (hr : ∀ v' ∈ Icc (0 : ℝ) b, F.r u v' ≠ 0)
    (hrvv : ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u v'') (Dvv F.r u v') v') :
    ContinuousAt (deriv (fun v' => Dv F.r u v' / F.Om u v')) v₁ := by
  have hv₁Icc : Icc (0 : ℝ) b ∈ 𝓝 v₁ := Icc_mem_nhds hv₁.1 hv₁.2
  have hWc : ContinuousOn (fun t => Dv F.W u t) (Icc (0 : ℝ) b) :=
    sliceOn1 hC2W.cont_v hu
  have hrc : ContinuousOn (fun t => F.r u t) (Icc (0 : ℝ) b) :=
    sliceOn1 hC2r.cont hu
  have hOmc : ContinuousOn (fun t => F.Om u t) (Icc (0 : ℝ) b) :=
    sliceOn1 hC2Om.cont hu
  have hnum : ContinuousOn (fun t => -2 * (Dv F.W u t * Dv F.W u t)) (Icc (0 : ℝ) b) :=
    continuousOn_const.mul (hWc.mul hWc)
  have hden : ContinuousOn (fun t => F.r u t * F.Om u t) (Icc (0 : ℝ) b) :=
    hrc.mul hOmc
  have hcont_e : ContinuousOn
      (fun t => -2 * (Dv F.W u t * Dv F.W u t) / (F.r u t * F.Om u t))
      (Icc (0 : ℝ) b) :=
    hnum.div hden (fun t ht => mul_ne_zero (hr t ht) (hOm t ht))
  have heq : (fun t => -2 * (Dv F.W u t * Dv F.W u t) / (F.r u t * F.Om u t))
      =ᶠ[𝓝 v₁] deriv (fun v' => Dv F.r u v' / F.Om u v') := by
    filter_upwards [Ioo_mem_nhds hv₁.1 hv₁.2] with t ht
    have htI : t ∈ Icc (0 : ℝ) b := ⟨ht.1.le, ht.2.le⟩
    show -2 * (Dv F.W u t * Dv F.W u t) / (F.r u t * F.Om u t)
      = deriv (fun v' => Dv F.r u v' / F.Om u v') t
    rw [(Dv_r_div_Om_hasDerivAt hcon hC2Om hu htI (hOm t htI) (hr t htI)
      (hrvv t htI)).deriv, pow_two]
  exact (hcont_e.continuousAt hv₁Icc).congr heq

/-- Dv W が区間内のどこかで非ゼロなら、その先では r_v < 0（厳密）。 -/
theorem Dv_r_lt_zero_of_exists_DvW_ne_zero {F : WedgeFields} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hrvv : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u' v'') (Dvv F.r u' v') v')
    {v₁ : ℝ} (hv₁ : v₁ ∈ Ioo (0 : ℝ) b) (hv₁v : v₁ < v)
    (hW : Dv F.W u v₁ ≠ 0) :
    Dv F.r u v < 0 := by
  have hv0 : (0 : ℝ) < v := hv₁.1.trans hv₁v
  have hb0 : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hlt : Dv F.r u v / F.Om u v < Dv F.r u 0 / F.Om u 0 := by
    have h := lt_of_deriv_nonpos_of_exists_deriv_neg
      (f := fun v' => Dv F.r u v' / F.Om u v')
      (a := (0 : ℝ)) (b := v) hv0
      (hcont := (Dv_r_div_Om_continuousOn hC2r hC2Om hu
        (fun v' hv' => (hOm u hu v' hv').ne')).mono (Icc_subset_Icc le_rfl hv.2))
      (hdiff := by
        intro x hx
        rw [interior_Icc] at hx
        have hxI : x ∈ Icc (0 : ℝ) b := ⟨hx.1.le, hx.2.le.trans hv.2⟩
        have hd : DifferentiableAt ℝ (fun v' => Dv F.r u v' / F.Om u v') x :=
          (Dv_r_div_Om_hasDerivAt hcon hC2Om hu hxI
            (hOm u hu x hxI).ne' (hr u hu x hxI).ne' (hrvv u hu x hxI)).differentiableAt
        exact hd.differentiableWithinAt)
      (hder := by
        intro x hx
        rw [interior_Icc] at hx
        have hxI : x ∈ Icc (0 : ℝ) b := ⟨hx.1.le, hx.2.le.trans hv.2⟩
        exact Dv_r_div_Om_deriv_nonpos hcon hC2Om hu hxI
          (hOm u hu x hxI) (hr u hu x hxI) (hrvv u hu x hxI))
      (t₀ := v₁) (ht₀ := ⟨hv₁.1, hv₁v⟩)
      (hneg := Dv_r_div_Om_deriv_neg_of_DvW_ne_zero hcon hC2Om hu
        ⟨hv₁.1.le, hv₁.2.le⟩ (hOm u hu v₁ ⟨hv₁.1.le, hv₁.2.le⟩)
        (hr u hu v₁ ⟨hv₁.1.le, hv₁.2.le⟩) hW
        (hrvv u hu v₁ ⟨hv₁.1.le, hv₁.2.le⟩))
      (hcontderiv := Dv_r_div_Om_deriv_continuousAt hcon hC2r hC2Om hC2W hu hv₁
        (fun v' hv' => (hOm u hu v' hv').ne')
        (fun v' hv' => (hr u hu v' hv').ne')
        (fun v' hv' => hrvv u hu v' hv'))
    exact h
  have h0 : Dv F.r u 0 / F.Om u 0 = 0 := by
    rw [Dv_r_cap_eq_zero heq hdata hC2r ha ha2 hu hb0]
    simp
  rw [h0] at hlt
  have hOmv : 0 < F.Om u v := hOm u hu v hv
  have hlt2 : Dv F.r u v < 0 * F.Om u v := (div_lt_iff₀ hOmv).mp hlt
  simpa using hlt2

/-- Du W ≠ 0 の点では、u ↦ Du r/Ω の微分は真に負。 -/
theorem Du_r_div_Om_deriv_neg_of_DuW_ne_zero {F : WedgeFields} {a b u₁ v : ℝ}
    (hcon : WedgeConstraints F) (hC2Om : C2On a b F.Om)
    (hu₁ : u₁ ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : 0 < F.Om u₁ v) (hr : 0 < F.r u₁ v)
    (hW : Du F.W u₁ v ≠ 0)
    (hruu : HasDerivAt (fun u' => Du F.r u' v) (Duu F.r u₁ v) u₁) :
    deriv (fun u' => Du F.r u' v / F.Om u' v) u₁ < 0 := by
  rw [(Du_r_div_Om_hasDerivAt hcon hC2Om hu₁ hv hOm.ne' hr.ne' hruu).deriv]
  have hsq : (0 : ℝ) < (Du F.W u₁ v) ^ 2 := sq_pos_of_ne_zero hW
  have hpos : (0 : ℝ) < 2 * (Du F.W u₁ v) ^ 2 / (F.r u₁ v * F.Om u₁ v) :=
    div_pos (by linarith) (mul_pos hr hOm)
  have h4 : -2 * (Du F.W u₁ v) ^ 2 / (F.r u₁ v * F.Om u₁ v)
      = -(2 * (Du F.W u₁ v) ^ 2 / (F.r u₁ v * F.Om u₁ v)) := by ring
  rw [h4]
  linarith [hpos]

/-- u ↦ Du r/Ω の微分は、C² 級の場では内点で連続（明示形による）。 -/
theorem Du_r_div_Om_deriv_continuousAt {F : WedgeFields} {a b u₁ v : ℝ}
    (hcon : WedgeConstraints F) (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (hC2W : C2On a b F.W)
    (hv : v ∈ Icc (0 : ℝ) b) (hu₁ : u₁ ∈ Ioo (0 : ℝ) a)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, F.Om u' v ≠ 0)
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, F.r u' v ≠ 0)
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a,
      HasDerivAt (fun u'' => Du F.r u'' v) (Duu F.r u' v) u') :
    ContinuousAt (deriv (fun u' => Du F.r u' v / F.Om u' v)) u₁ := by
  have hu₁Icc : Icc (0 : ℝ) a ∈ 𝓝 u₁ := Icc_mem_nhds hu₁.1 hu₁.2
  have hWc : ContinuousOn (fun t => Du F.W t v) (Icc (0 : ℝ) a) :=
    sliceOn2 hC2W.cont_u hv
  have hrc : ContinuousOn (fun t => F.r t v) (Icc (0 : ℝ) a) :=
    sliceOn2 hC2r.cont hv
  have hOmc : ContinuousOn (fun t => F.Om t v) (Icc (0 : ℝ) a) :=
    sliceOn2 hC2Om.cont hv
  have hnum : ContinuousOn (fun t => -2 * (Du F.W t v * Du F.W t v)) (Icc (0 : ℝ) a) :=
    continuousOn_const.mul (hWc.mul hWc)
  have hden : ContinuousOn (fun t => F.r t v * F.Om t v) (Icc (0 : ℝ) a) :=
    hrc.mul hOmc
  have hcont_e : ContinuousOn
      (fun t => -2 * (Du F.W t v * Du F.W t v) / (F.r t v * F.Om t v))
      (Icc (0 : ℝ) a) :=
    hnum.div hden (fun t ht => mul_ne_zero (hr t ht) (hOm t ht))
  have heq : (fun t => -2 * (Du F.W t v * Du F.W t v) / (F.r t v * F.Om t v))
      =ᶠ[𝓝 u₁] deriv (fun u' => Du F.r u' v / F.Om u' v) := by
    filter_upwards [Ioo_mem_nhds hu₁.1 hu₁.2] with t ht
    have htI : t ∈ Icc (0 : ℝ) a := ⟨ht.1.le, ht.2.le⟩
    show -2 * (Du F.W t v * Du F.W t v) / (F.r t v * F.Om t v)
      = deriv (fun u' => Du F.r u' v / F.Om u' v) t
    rw [(Du_r_div_Om_hasDerivAt hcon hC2Om htI hv (hOm t htI) (hr t htI)
      (hruu t htI)).deriv, pow_two]
  exact (hcont_e.continuousAt hu₁Icc).congr heq

/-- Du W が区間内のどこかで非ゼロなら、その先では r_u < 0（厳密）。 -/
theorem Du_r_lt_zero_of_exists_DuW_ne_zero {F : WedgeFields} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun u'' => Du F.r u'' v') (Duu F.r u' v') u')
    {u₁ : ℝ} (hu₁ : u₁ ∈ Ioo (0 : ℝ) a) (hu₁u : u₁ < u)
    (hW : Du F.W u₁ v ≠ 0) :
    Du F.r u v < 0 := by
  have hu0 : (0 : ℝ) < u := hu₁.1.trans hu₁u
  have ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a := ⟨le_rfl, ha.le⟩
  have hlt : Du F.r u v / F.Om u v < Du F.r 0 v / F.Om 0 v := by
    have h := lt_of_deriv_nonpos_of_exists_deriv_neg
      (f := fun u' => Du F.r u' v / F.Om u' v)
      (a := (0 : ℝ)) (b := u) hu0
      (hcont := (Du_r_div_Om_continuousOn hC2r hC2Om hv
        (fun u' hu' => (hOm u' hu' v hv).ne')).mono (Icc_subset_Icc le_rfl hu.2))
      (hdiff := by
        intro x hx
        rw [interior_Icc] at hx
        have hxI : x ∈ Icc (0 : ℝ) a := ⟨hx.1.le, hx.2.le.trans hu.2⟩
        have hd : DifferentiableAt ℝ (fun u' => Du F.r u' v / F.Om u' v) x :=
          (Du_r_div_Om_hasDerivAt hcon hC2Om hxI hv
            (hOm x hxI v hv).ne' (hr x hxI v hv).ne' (hruu x hxI v hv)).differentiableAt
        exact hd.differentiableWithinAt)
      (hder := by
        intro x hx
        rw [interior_Icc] at hx
        have hxI : x ∈ Icc (0 : ℝ) a := ⟨hx.1.le, hx.2.le.trans hu.2⟩
        exact Du_r_div_Om_deriv_nonpos hcon hC2Om hxI hv
          (hOm x hxI v hv) (hr x hxI v hv) (hruu x hxI v hv))
      (t₀ := u₁) (ht₀ := ⟨hu₁.1, hu₁u⟩)
      (hneg := Du_r_div_Om_deriv_neg_of_DuW_ne_zero hcon hC2Om
        ⟨hu₁.1.le, hu₁.2.le⟩ hv (hOm u₁ ⟨hu₁.1.le, hu₁.2.le⟩ v hv)
        (hr u₁ ⟨hu₁.1.le, hu₁.2.le⟩ v hv) hW
        (hruu u₁ ⟨hu₁.1.le, hu₁.2.le⟩ v hv))
      (hcontderiv := Du_r_div_Om_deriv_continuousAt hcon hC2r hC2Om hC2W hv hu₁
        (fun u' hu' => (hOm u' hu' v hv).ne')
        (fun u' hu' => (hr u' hu' v hv).ne')
        (fun u' hu' => hruu u' hu' v hv))
    exact h
  have h0 : Du F.r 0 v / F.Om 0 v = 0 := by
    rw [Du_r_neck_eq_zero heq hdata hC2r hb hv ha0]
    simp
  rw [h0] at hlt
  have hOmu : 0 < F.Om u v := hOm u hu v hv
  have hlt2 : Du F.r u v < 0 * F.Om u v := (div_lt_iff₀ hOmu).mp hlt
  simpa using hlt2

/-- まとめ：W の両微分が区間内のどこかで非ゼロなら、内部では r_u·r_v > 0（厳密）。 -/
theorem rProduct_pos_of_exists_DW_ne_zero {F : WedgeFields} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hrvv : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u' v'') (Dvv F.r u' v') v')
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun u'' => Du F.r u'' v') (Duu F.r u' v') u')
    {u₁ : ℝ} (hu₁ : u₁ ∈ Ioo (0 : ℝ) a) (hu₁u : u₁ < u) (hWu : Du F.W u₁ v ≠ 0)
    {v₁ : ℝ} (hv₁ : v₁ ∈ Ioo (0 : ℝ) b) (hv₁v : v₁ < v) (hWv : Dv F.W u v₁ ≠ 0) :
    0 < Du F.r u v * Dv F.r u v :=
  mul_pos_of_neg_of_neg
    (Du_r_lt_zero_of_exists_DuW_ne_zero heq hdata hcon hC2r hC2Om hC2W ha hb
      hu hv hOm hr hruu hu₁ hu₁u hWu)
    (Dv_r_lt_zero_of_exists_DvW_ne_zero heq hdata hcon hC2r hC2Om hC2W ha hb ha2
      hu hv hOm hr hrvv hv₁ hv₁v hWv)

end CFT.WedgeRProductStrict
