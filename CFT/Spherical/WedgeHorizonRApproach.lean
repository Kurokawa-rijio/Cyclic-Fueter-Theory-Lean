/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **地平線への接近 r → r₊（第一段）**。前段までで、対応仮説
  Ω(u, v) = c · f(ρ(u)) のもとで最初の地平線が f の最初のゼロに移ること
  （`corr_wedge_first_horizon`）と、ρ := r が再パラメータ化の候補になる
  こと（`WedgeHorizonRhoCandidate`）が閉じた。ここでは ρ = r の場合に、
  最初の地平線の手前では r > r₊ であり、地平線では r = r₊ になること
  （`wedge_r_gt_rp_before_horizon`・`wedge_r_eq_rp_at_horizon`）と、
  u → c⁻ で r(u, v) → r₊ であること（`wedge_r_tendsto_rp_at_horizon`）
  を証明し、まとめ（`wedge_first_horizon_r_approach`）として組み立てる。
  RN 側の符号補題（`rnF_pos_of_gt`・`rnF_neg_of_between`・
  `rnF_eq_zero_iff_of_gt_rm`）も証明する。すなわち「地平線への接近
  r → r₊」が、対応仮説（ρ = r）と C² 級の場・特性データからの定理に
  なった。残りは r_u·r_v の正の下界、Ω 項の下界の検証と ρ そのものの
  構成（対応仮説そのものの証明）である。

  正直な限定：対応仮説そのもの（Ω = c · f(r) の形）はここでも仮定の
  ままであり、証明されたのはその仮定のもとでの r の振る舞いである。
  また r > r₋ は切片上の条件つきの仮定（`hrmr`）として残る。
-/
import Mathlib
import CFT.Spherical.WedgeHorizonCorrespondence
import CFT.Spherical.WedgeHorizonFirstExit
import CFT.Quantum.RNExtremalDoubleZero

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeExist CFT.WedgeCont
open CFT.WedgeFirstZero CFT.WedgeFirstExit CFT.WedgeHorizonCorr CFT.RNExtremalZero

namespace CFT.WedgeHorizonRApproach

/-- RN の計量関数 f は地平線の外側（r > r₊）で正。 -/
theorem rnF_pos_of_gt {rp rm r : ℝ} (hrp : 0 < rp) (hrm : rm < rp) (hr : rp < r) :
    0 < rnF rp rm r := by
  unfold rnF
  apply div_pos
  · exact mul_pos (sub_pos.mpr hr) (sub_pos.mpr (lt_trans hrm hr))
  · exact pow_pos (lt_trans hrp hr) 2

/-- RN の計量関数 f は二つの地平線の間（r₋ < r < r₊）で負。 -/
theorem rnF_neg_of_between {rp rm r : ℝ} (hr : 0 < r) (hrm : rm < r) (hrp : r < rp) :
    rnF rp rm r < 0 := by
  unfold rnF
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr hrp) (sub_pos.mpr hrm)
  · exact pow_pos hr 2

/-- r > r₋ のもとでは、f(r) = 0 ⟺ r = r₊。 -/
theorem rnF_eq_zero_iff_of_gt_rm {rp rm r : ℝ} (hr : 0 < r) (hrm : rm < r) :
    rnF rp rm r = 0 ↔ r = rp := by
  unfold rnF
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact sub_eq_zero.mp h1
      · exact absurd (sub_eq_zero.mp h1) (ne_of_gt hrm)
    · exact absurd h (pow_ne_zero 2 (ne_of_gt hr))
  · intro h
    left
    rw [h]
    simp

/-- 対応仮説（ρ = r）のもとでは、最初の地平線の手前では r > r₊ である：
    Ω > 0 から f(r) > 0 が従い、r > r₋ と合わせると r − r₊ > 0 が出る。 -/
theorem wedge_r_gt_rp_before_horizon {a : ℝ} {F : WedgeFields} {v rp rm : ℝ}
    (H : HorizonCorrespondence F.Om v rp rm) (hρ : H.ρ = fun u => F.r u v)
    (hm : 0 ≤ rm) (hrp : 0 < rp) (hrm : rm < rp)
    (hrmr : ∀ u ∈ Icc (0 : ℝ) a, rm < F.r u v)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) a)
    (hpos : ∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) :
    ∀ u ∈ Ico (0 : ℝ) c, rp < F.r u v := by
  intro u hu
  have huIcc : u ∈ Icc (0 : ℝ) a := ⟨hu.1, hu.2.le.trans hc.2⟩
  have hfu : 0 < rnF rp rm (F.r u v) := by
    have h := (corr_pos_iff H u).mp (hpos u hu)
    rwa [hρ] at h
  have hr0 : 0 < F.r u v := lt_of_le_of_lt hm (hrmr u huIcc)
  by_contra hle
  push_neg at hle
  have hnonpos : rnF rp rm (F.r u v) ≤ 0 := by
    unfold rnF
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle)
        (sub_nonneg.mpr (hrmr u huIcc).le)
    · exact pow_nonneg hr0.le 2
  exact absurd hfu (not_lt_of_ge hnonpos)

/-- 対応仮説（ρ = r）のもとでは、最初の地平線では r = r₊ である：
    Ω = 0 から f(r) = 0 が従い、r > r₋ と合わせると r = r₊ が出る。 -/
theorem wedge_r_eq_rp_at_horizon {F : WedgeFields} {v rp rm : ℝ}
    (H : HorizonCorrespondence F.Om v rp rm) (hρ : H.ρ = fun u => F.r u v)
    (hm : 0 ≤ rm) {c : ℝ} (hfc : F.Om c v = 0) (hrc : rm < F.r c v) :
    F.r c v = rp := by
  have h0 : rnF rp rm (F.r c v) = 0 := by
    have h := (corr_zero_iff H c).mp hfc
    rwa [hρ] at h
  have hr0 : 0 < F.r c v := lt_of_le_of_lt hm hrc
  exact (rnF_eq_zero_iff_of_gt_rm hr0 hrc).mp h0

/-- C² 級の場では、切片上で r(u, v) → r(c, v)（u → c⁻、区間 [0, a] の中での
    左からの接近）。`C2On` から切片の連続性を引き出す。 -/
theorem wedge_r_tendsto_rp_at_horizon {a b : ℝ} {F : WedgeFields} {v rp : ℝ}
    (hC2 : C2On a b F.r) (hv : v ∈ Icc (0 : ℝ) b)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) a) (hc0 : 0 < c) (hrc : F.r c v = rp) :
    Tendsto (fun u => F.r u v) (𝓝[<] c) (𝓝 rp) := by
  have hcont : ContinuousOn (fun t => F.r t v) (Icc (0 : ℝ) a) :=
    CFT.CharUniqueness.sliceOn2 hC2.cont hv
  have hwithin : ContinuousWithinAt (fun t => F.r t v) (Ico (0 : ℝ) c) c :=
    (hcont.continuousWithinAt hc).mono (fun x hx => ⟨hx.1, hx.2.le.trans hc.2⟩)
  have hfilter : 𝓝[Set.Ico (0 : ℝ) c] c = 𝓝[<] c := by
    rw [← Set.Ici_inter_Iio]
    exact nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds
        (mem_of_superset (Ioi_mem_nhds hc0) Set.Ioi_subset_Ici_self))
  rw [← hrc, ← hfilter]
  exact hwithin

/-- まとめ：対応仮説（ρ = r）のもとで、最初の地平線では r が r₊ に
    上から接近する — 地平線では r = r₊、その手前では r > r₊、
    u → c⁻ で r(u, v) → r₊。 -/
theorem wedge_first_horizon_r_approach {a b : ℝ} {F : WedgeFields} {v rp rm : ℝ}
    (ha : 0 ≤ a) (hv : v ∈ Icc (0 : ℝ) b) (hdata : WedgeDataOn a b F)
    (hC2Om : C2On a b F.Om) (hC2r : C2On a b F.r)
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (H : HorizonCorrespondence F.Om v rp rm) (hρ : H.ρ = fun u => F.r u v)
    (hm : 0 ≤ rm) (hrp : 0 < rp) (hrm : rm < rp)
    (hrmr : ∀ u ∈ Icc (0 : ℝ) a, rm < F.r u v) :
    ∃ c ∈ Icc (0 : ℝ) a, F.r c v = rp ∧ (∀ u ∈ Ico (0 : ℝ) c, rp < F.r u v) ∧
      Tendsto (fun u => F.r u v) (𝓝[<] c) (𝓝 rp) := by
  obtain ⟨c, hc, hfc, hpos, _hmin⟩ := wedge_first_horizon_of_data ha hdata hv hC2Om hneg
  have hc0 : 0 < c := by
    have h0 : 0 < F.Om 0 v := wedge_Om_zero_pos_of_data hdata hv
    rcases eq_or_lt_of_le hc.1 with h | h
    · exfalso
      rw [← h] at hfc
      exact absurd hfc (ne_of_gt h0)
    · exact h
  have hrc : F.r c v = rp :=
    wedge_r_eq_rp_at_horizon H hρ hm hfc (hrmr c hc)
  refine ⟨c, hc, hrc, ?_, ?_⟩
  · exact wedge_r_gt_rp_before_horizon H hρ hm hrp hrm hrmr hc hpos
  · exact wedge_r_tendsto_rp_at_horizon hC2r hv hc hc0 hrc

end CFT.WedgeHorizonRApproach
