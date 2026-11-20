/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) のくさび EYM 系の形での分類の本体への第一段：

  **地平線は Ω の最初のゼロとして現れる**。`WedgeContinuationNoZero` で
  閉じたのは「箱の中では Ω はゼロを持たない」こと、すなわち地平線は箱の
  外でしか現れないことだった。ここではその先の一段として、固定した v で
  のヌル切片上で Ω が負になる点があれば、ゼロの集合の**下限が実際にゼロ**
  であり、その手前では Ω > 0 であること（`first_zero`）、およびその
  ゼロが単純ゼロ（`Du F.Om c v ≠ 0`）なら Ω はそこで実際に符号を変える
  こと（`sign_change_of_hasDerivAt`・`wedge_first_horizon_crossing`）
  を証明する。すなわち対応仮説（Ω(u, v) = c · f(ρ(u))）の証明に要る
  「地平線の位置」の厳密な意味 — 最初のゼロ — と、単純ゼロが真の交差で
  あることが、くさび解の側で閉じた。残りは、実際のくさび解の Ω と RN
  側の f との対応づけそのもの（対応仮説の証明）である。

  抽象部分は連続関数 f : ℝ → ℝ についての実解析の補題で、くさびへの
  適用は `C2On` から切片の連続性を引き出す形で条件つきに述べる。
-/
import Mathlib
import CFT.Spherical.WedgeContinuationNoZero
import CFT.Spherical.WedgeHorizonClassification

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeExist CFT.WedgeCont CFT.WedgeOmegaZero
  CFT.WedgeBalance CFT.WedgeHorizon

namespace CFT.WedgeFirstZero

/-- 符号変化があればゼロがある（中間値の定理）。 -/
theorem exists_zero_of_sign_change {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : 0 < f a) (hb : f b < 0) :
    ∃ c ∈ Ioo a b, f c = 0 := by
  have h0 : (0 : ℝ) ∈ Icc (f b) (f a) := ⟨le_of_lt hb, le_of_lt ha⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' (le_of_lt hab) hf h0
  refine ⟨c, ⟨?_, ?_⟩, hfc⟩
  · rcases eq_or_lt_of_le hc.1 with h | h
    · exfalso
      rw [← h] at hfc
      exact absurd hfc (ne_of_gt ha)
    · exact h
  · rcases eq_or_lt_of_le hc.2 with h | h
    · exfalso
      rw [h] at hfc
      exact absurd hfc (ne_of_lt hb)
    · exact h

/-- 最初のゼロ：符号変化があれば、ゼロの集合の下限が実際にゼロであり、
    その手前では関数は正で、すべてのゼロはその下限以上にある。 -/
theorem first_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : 0 < f a) (hb : f b < 0) :
    ∃ c ∈ Icc a b, f c = 0 ∧ (∀ x ∈ Ico a c, 0 < f x) ∧
      ∀ z ∈ Icc a b, f z = 0 → c ≤ z := by
  set S : Set ℝ := Icc a b ∩ f ⁻¹' {0} with hS
  have hne : S.Nonempty := by
    obtain ⟨c, hc, hfc⟩ := exists_zero_of_sign_change hab hf ha hb
    exact ⟨c, ⟨⟨le_of_lt hc.1, le_of_lt hc.2⟩, hfc⟩⟩
  have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hclosed : IsClosed S :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  set c₀ := sInf S with hc₀
  have hc₀mem : c₀ ∈ S := hclosed.csInf_mem hne hbdd
  refine ⟨c₀, hc₀mem.1, hc₀mem.2, ?_, ?_⟩
  · intro x hx
    rcases lt_or_eq_of_le hx.1 with hax | hax
    · by_contra hle
      push_neg at hle
      rcases hle.lt_or_eq with hneg | hzero
      · have hxb : x ≤ b := (hx.2.trans_le hc₀mem.1.2).le
        have hf' : ContinuousOn f (Icc a x) :=
          hf.mono (Icc_subset_Icc_right hxb)
        obtain ⟨c₁, hc₁, hfc₁⟩ := exists_zero_of_sign_change hax hf' ha hneg
        have hc₁S : c₁ ∈ S :=
          ⟨⟨le_of_lt hc₁.1, (hc₁.2.trans hx.2).le.trans hc₀mem.1.2⟩, hfc₁⟩
        exact absurd (csInf_le hbdd hc₁S) (not_le_of_gt (hc₁.2.trans hx.2))
      · have hxS : x ∈ S :=
          ⟨⟨le_of_lt hax, hx.2.le.trans hc₀mem.1.2⟩, hzero⟩
        exact absurd (csInf_le hbdd hxS) (not_le_of_gt hx.2)
    · rw [← hax]
      exact ha
  · intro z hz hfz
    exact csInf_le hbdd ⟨hz, hfz⟩

/-- 単純ゼロは符号変化：導関数が ≠ 0 なら、ゼロの左側と右側で関数の符号が
    導関数の符号と反対・一致する。 -/
theorem sign_change_of_hasDerivAt {f : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hd : d ≠ 0) (hfc : f c = 0) :
    ∃ δ > 0, (∀ x ∈ Ioo (c - δ) c, f x * d < 0) ∧
      ∀ x ∈ Ioo c (c + δ), 0 < f x * d := by
  have hlim : Tendsto (slope f c) (𝓝[≠] c) (𝓝 d) :=
    hasDerivAt_iff_tendsto_slope.mp hf
  have hpos : ∀ᶠ x in 𝓝[≠] c, 0 < slope f c x * d :=
    hlim.eventually (by
      have hcont : ContinuousAt (fun y : ℝ => y * d) d :=
        continuousAt_id.mul continuousAt_const
      exact hcont.eventually (eventually_gt_nhds (mul_self_pos.mpr hd)))
  rw [eventually_nhdsWithin_iff] at hpos
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hpos
  refine ⟨δ, hδpos, ?_, ?_⟩
  · intro x hx
    have hxc : x ≠ c := ne_of_lt hx.2
    have hdist : dist x c < δ := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hx.2)]
      linarith [hx.1]
    have hs : 0 < slope f c x * d := hδ hdist hxc
    have hne : x - c ≠ 0 := sub_ne_zero.mpr hxc
    have hslope : slope f c x = (x - c)⁻¹ * f x := by
      simp [slope, hfc, smul_eq_mul]
    have hkey : f x * d = (slope f c x * d) * (x - c) := by
      rw [hslope]
      field_simp
    rw [hkey]
    exact mul_neg_of_pos_of_neg hs (sub_neg.mpr hx.2)
  · intro x hx
    have hxc : x ≠ c := ne_of_gt hx.1
    have hdist : dist x c < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hx.1)]
      linarith [hx.2]
    have hs : 0 < slope f c x * d := hδ hdist hxc
    have hne : x - c ≠ 0 := sub_ne_zero.mpr hxc
    have hslope : slope f c x = (x - c)⁻¹ * f x := by
      simp [slope, hfc, smul_eq_mul]
    have hkey : f x * d = (slope f c x * d) * (x - c) := by
      rw [hslope]
      field_simp
    rw [hkey]
    exact mul_pos hs (sub_pos.mpr hx.1)

/-- 単純ゼロ（`WedgeHorizonClassification` の意味）での符号変化。 -/
theorem sign_change_of_simpleZero {g : ℝ → ℝ} {c : ℝ}
    (hdiff : DifferentiableAt ℝ g c) (hs : SimpleZero g c) :
    ∃ δ > 0, (∀ x ∈ Ioo (c - δ) c, g x * deriv g c < 0) ∧
      ∀ x ∈ Ioo c (c + δ), 0 < g x * deriv g c :=
  sign_change_of_hasDerivAt hdiff.hasDerivAt hs.2 hs.1

/-- くさび解のヌル切片上で Ω が負になる点があれば、最初の地平線が存在する：
    その手前では Ω > 0 であり、すべてのゼロはその地平線以上にある。
    角での値は `WedgeDataOn` から `F.Om 0 v = neckOm v > 0` の形で入る。 -/
theorem wedge_first_horizon {a b : ℝ} {F : WedgeFields} {v : ℝ}
    (ha : 0 ≤ a) (hv : v ∈ Icc (0 : ℝ) b) (hC2 : C2On a b F.Om)
    (hpos : 0 < F.Om 0 v) (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
      ∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z := by
  obtain ⟨u, hu, hfu⟩ := hneg
  have hu0 : 0 < u :=
    lt_of_le_of_ne hu.1 (fun h => by rw [← h] at hfu; exact absurd hfu (not_lt_of_gt hpos))
  have hcont : ContinuousOn (fun t => F.Om t v) (Icc (0 : ℝ) u) := by
    have h : ContinuousOn (Function.uncurry F.Om ∘ fun t => (t, v)) (Icc (0 : ℝ) u) :=
      hC2.cont.comp (continuous_id.prod_mk continuous_const).continuousOn
        (fun t ht => ⟨⟨ht.1, ht.2.trans hu.2⟩, hv⟩)
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h
  obtain ⟨c, hc, hfc, hpos', hmin⟩ := first_zero hu0 hcont hpos hfu
  exact ⟨c, ⟨hc.1, hc.2.trans hu.2⟩, hfc, hpos',
    fun z hz hfz => by
      rcases le_or_lt z u with hzu | hzu
      · exact hmin z ⟨hz.1, hzu⟩ hfz
      · exact hc.2.trans hzu.le⟩

/-- 最初の地平線が単純ゼロなら、そこで Ω は実際に符号を変える
    （`Du F.Om c v ≠ 0` は `deriv` の意味での単純性）。 -/
theorem wedge_first_horizon_crossing {a b : ℝ} {F : WedgeFields} {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) b) (hC2 : C2On a b F.Om)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) a) (hfc : F.Om c v = 0)
    (hd : Du F.Om c v ≠ 0) :
    ∃ δ > 0, (∀ x ∈ Ioo (c - δ) c, F.Om x v * Du F.Om c v < 0) ∧
      ∀ x ∈ Ioo c (c + δ), 0 < F.Om x v * Du F.Om c v := by
  have hder : HasDerivAt (fun u => F.Om u v) (Du F.Om c v) c :=
    hC2.deriv_u c hc v hv
  exact sign_change_of_hasDerivAt hder hd hfc

end CFT.WedgeFirstZero
