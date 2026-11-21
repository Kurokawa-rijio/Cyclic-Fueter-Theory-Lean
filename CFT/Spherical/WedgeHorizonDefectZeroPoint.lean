/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **S = 0 になる一点の実際の構成（中間値の定理による）**。前段
  （`WedgeHorizonDefectPropagation`）では、v 区間上で R = 0 かつ一点で
  S = 0 なら区間全体で S = 0 になること（v 方向への伝播）と、R = 0 の判定が
  B1|_{W=0} の唯一の零点 r₀ による精密な位置の決定になることが示された。
  残るのは S = 0 になる一点そのものの構成である。ここではそれを、固定した
  ヌル切片（v = const）上での中間値の定理として構成する：

  - 切片の左端での値 S(0, v) < 0 は仮定として置く（v = 0 では角の値
    S(0, 0) = −1 そのもの、`defectSource_corner_eq`）。
  - 最初の地平線 u₀（Ω = 0）に近づくと、r → r₊ のもとで r_u·r_v 項の係数
    c(r) = 1/(r−r₊)² + 1/(r−r₋)² + g/r は +∞ に発散する（極端版：
    `rnLogDerivCoeffC_extremal_tendsto_atTop`）。r_u·r_v が正の下界を
    持ち、Ω 項が下から抑えられれば、S は切片上で +∞ に発散する
    （`defectSource_tendsto_atTop_of_horizon`）。
  - したがって S > 0 になる点 u* が存在し、S の切片上の連続性と合わせると
    中間値の定理から S(u₁, v) = 0 になる点 u₁ ∈ (0, u₀) が存在する
    （`defectSource_eq_zero_of_horizon_blowup`）。
  - その一点を種として、前段の伝播定理により S = 0 は R = 0 の v 区間全体に
    広がる（`defectSource_eq_zero_on_Icc_of_point` とその組み立て
    `defectSource_eq_zero_on_Icc_of_horizon_blowup`）。

  仮定の位置づけ：S(0, v) < 0、r → r₊、r_u·r_v ≥ m > 0、Ω 項の下界は、
  実際のくさび解のデータから検証すべき条件として残る（対応仮説そのものの
  証明には、さらに ρ の構成が要る）。この段で閉じたのは、一点の構成が
  「切片の左端での負値＋地平線での発散」という二つの検証可能な条件に
  帰着することである。
-/
import CFT.Spherical.WedgeHorizonDefectPropagation
import CFT.Spherical.WedgeHorizonDefectSource
import CFT.Quantum.RNLogDerivative
import CFT.Spherical.WedgeHorizonDefectTransport
import CFT.Spherical.WedgeHorizonDefectSourceDeriv

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource
open CFT.WedgeDefectSourceDeriv CFT.WedgeDefectPropagation CFT.RNLogDeriv
open CFT.WedgeDefectSourceDerivClosed

namespace CFT.WedgeDefectZeroPoint

/-- 極端 RN での r_u·r_v の係数 c(r) の明示形（和の形）。
    g = 2/(r−r₊) − 2/r、g′ = −2/(r−r₊)² + 2/r² を代入すると
    c(r) = 2/r² − g′ + g/r = 2/(r−r₊)² + 2/(r(r−r₊)) − 2/r²。 -/
theorem rnLogDerivCoeffC_extremal_eq {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    1 / (r - rp) ^ 2 + 1 / (r - rp) ^ 2 + rnLogDeriv rp rp r / r
      = 2 / (r - rp) ^ 2 + 2 / (r * (r - rp)) - 2 / r ^ 2 := by
  have hrp' : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [rnLogDeriv]
  field_simp
  ring

/-- 極端 RN での r_u·r_v の係数 c(r) の明示形（因数分解形）。
    c(r) = 2(r² + r·r₊ − r₊²)/(r²(r−r₊)²)。 -/
theorem rnLogDerivCoeffC_extremal_eq_factored {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    1 / (r - rp) ^ 2 + 1 / (r - rp) ^ 2 + rnLogDeriv rp rp r / r
      = 2 * (r ^ 2 + r * rp - rp ^ 2) / (r ^ 2 * (r - rp) ^ 2) := by
  rw [rnLogDerivCoeffC_extremal_eq hr hrp]
  have hrp' : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  field_simp
  ring

/-- 極端 RN での係数 c(r) は地平線の外側（r > r₊ > 0）で正。
    分子 r² + r·r₊ − r₊² は r² > r₊² と r·r₊ > 0 から正。 -/
theorem rnLogDerivCoeffC_extremal_pos {rp r : ℝ} (hrp : 0 < rp) (hr : rp < r) :
    0 < 1 / (r - rp) ^ 2 + 1 / (r - rp) ^ 2 + rnLogDeriv rp rp r / r := by
  rw [rnLogDerivCoeffC_extremal_eq_factored (ne_of_gt (lt_trans hrp hr)) (ne_of_gt hr)]
  apply div_pos _ (mul_pos (pow_pos (lt_trans hrp hr) 2) (pow_pos (sub_pos.mpr hr) 2))
  have hsq : rp ^ 2 < r ^ 2 := by
    have h := mul_pos (sub_pos.mpr hr) (show (0:ℝ) < r + rp by linarith)
    nlinarith
  have hpos : 0 < r * rp := mul_pos (lt_trans hrp hr) hrp
  nlinarith

/-- 極端 RN での係数 c(r) は r → r₊⁺ で +∞ に発散する。
    下界 c(r) ≥ 2/(r−r₊)² − 2/r₊² による（2/(r(r−r₊)) > 0 と
    −2/r² ≥ −2/r₊² を使う）。 -/
theorem rnLogDerivCoeffC_extremal_tendsto_atTop {rp : ℝ} (hrp : 0 < rp) :
    Tendsto (fun r => 1 / (r - rp) ^ 2 + 1 / (r - rp) ^ 2
        + rnLogDeriv rp rp r / r) (𝓝[>] rp) atTop := by
  have hsub : Tendsto (fun r : ℝ => r - rp) (𝓝[>] rp) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using (continuous_sub_right rp).tendsto rp)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (Set.mem_Ioi.mp hr)
  have hinv : Tendsto (fun r : ℝ => (r - rp)⁻¹) (𝓝[>] rp) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hpow : Tendsto (fun r : ℝ => ((r - rp)⁻¹) ^ 2) (𝓝[>] rp) atTop :=
    (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp hinv
  have h2 : Tendsto (fun r : ℝ => 2 * ((r - rp)⁻¹) ^ 2) (𝓝[>] rp) atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hpow
  have h2' : Tendsto (fun r : ℝ => 2 / (r - rp) ^ 2 - 2 / rp ^ 2) (𝓝[>] rp) atTop := by
    have h := tendsto_atTop_add_const_right _ (-(2 / rp ^ 2)) h2
    refine h.congr' ?_
    filter_upwards with r
    have hform : (2:ℝ) / (r - rp) ^ 2 = 2 * ((r - rp)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]
    rw [hform]
    ring
  refine tendsto_atTop_mono' _ ?_ h2'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := lt_trans hrp hr
  have h1 : (0:ℝ) < 2 / (r * (r - rp)) :=
    div_pos (by norm_num) (mul_pos hrpos (sub_pos.mpr hr))
  have hsq : rp ^ 2 ≤ r ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hr.le) (show (0:ℝ) ≤ r + rp by linarith)
    nlinarith
  have h2le : 2 / r ^ 2 ≤ 2 / rp ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hrpos 2) (pow_pos hrp 2)]
    linarith [hsq]
  rw [rnLogDerivCoeffC_extremal_eq (ne_of_gt hrpos) (ne_of_gt hr)]
  linarith

/-- +∞ に発散する関数に、下から抑えられた関数を足しても +∞ に発散する。 -/
theorem tendsto_atTop_add_of_eventually_bddBelow_of_tendsto_atTop {f g : ℝ → ℝ}
    {l : Filter ℝ} (hg : ∃ m, ∀ᶠ x in l, m ≤ g x) (hf : Tendsto f l atTop) :
    Tendsto (fun x => g x + f x) l atTop := by
  obtain ⟨m, hm⟩ := hg
  rw [tendsto_atTop]
  intro B
  filter_upwards [hf.eventually (eventually_gt_atTop (B - m)), hm] with x hfx hgx
  linarith

/-- +∞ に発散する関数に、正の下界を持つ関数を掛けても +∞ に発散する。 -/
theorem tendsto_atTop_mul_of_tendsto_atTop_of_eventually_ge {f g : ℝ → ℝ}
    {l : Filter ℝ} {m : ℝ} (hm : 0 < m) (hf : Tendsto f l atTop)
    (hf0 : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, m ≤ g x) :
    Tendsto (fun x => g x * f x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (Filter.Tendsto.const_mul_atTop hm hf)
  filter_upwards [hf0, hg] with x h0 hgm
  exact mul_le_mul_of_nonneg_right hgm h0

/-- 切片上での S の発散：固定した v に対して、r → r₊（u → u₀⁻）、
    r_u·r_v ≥ m > 0（u₀ の近く）、Ω 項が下から抑えられていれば、
    S(u, v) は u → u₀⁻ で +∞ に発散する。 -/
theorem defectSource_tendsto_atTop_of_horizon {F : WedgeFields} {rp u₀ v : ℝ}
    (hrp : 0 < rp) (hu₀ : 0 < u₀)
    (hr0 : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ 0)
    (hrne : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ rp)
    (hrlim : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝[>] rp))
    (hOm : ∃ M, ∀ᶠ u in 𝓝[<] u₀,
      M ≤ F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
            * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
          + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)))
    (hDuDv : ∃ m, 0 < m ∧ ∀ᶠ u in 𝓝[<] u₀, m ≤ Du F.r u v * Dv F.r u v) :
    Tendsto (fun u => defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u v)
      (𝓝[<] u₀) atTop := by
  have hc : Tendsto (fun u => 1 / (F.r u v - rp) ^ 2 + 1 / (F.r u v - rp) ^ 2
        + rnLogDeriv rp rp (F.r u v) / F.r u v) (𝓝[<] u₀) atTop :=
    (rnLogDerivCoeffC_extremal_tendsto_atTop hrp).comp hrlim
  obtain ⟨m, hm, hDuDv'⟩ := hDuDv
  have hc0 : ∀ᶠ u in 𝓝[<] u₀, 0 ≤ 1 / (F.r u v - rp) ^ 2 + 1 / (F.r u v - rp) ^ 2
        + rnLogDeriv rp rp (F.r u v) / F.r u v := by
    have h := hc.eventually (eventually_gt_atTop (0 : ℝ))
    exact h.mono (fun u hu => hu.le)
  have hprod : Tendsto (fun u => (Du F.r u v * Dv F.r u v)
        * (1 / (F.r u v - rp) ^ 2 + 1 / (F.r u v - rp) ^ 2
          + rnLogDeriv rp rp (F.r u v) / F.r u v)) (𝓝[<] u₀) atTop :=
    tendsto_atTop_mul_of_tendsto_atTop_of_eventually_ge hm hc hc0 hDuDv'
  have hsum : Tendsto (fun u => (F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
            * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
          + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)))
        + (Du F.r u v * Dv F.r u v)
          * (1 / (F.r u v - rp) ^ 2 + 1 / (F.r u v - rp) ^ 2
            + rnLogDeriv rp rp (F.r u v) / F.r u v)) (𝓝[<] u₀) atTop :=
    tendsto_atTop_add_of_eventually_bddBelow_of_tendsto_atTop hOm hprod
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
  rw [defectSource_rn_eq (hr0 u hu) (hrne u hu) (hrne u hu)]

/-- 中間値の定理の零点版：連続関数が左端で負、右端で正なら、その間で 0 になる。 -/
theorem exists_eq_zero_of_neg_of_pos {S : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn S (Icc a b)) (hSa : S a < 0) (hSb : 0 < S b) :
    ∃ u₁ ∈ Ioo a b, S u₁ = 0 := by
  have hmem : (0 : ℝ) ∈ Icc (S a) (S b) := ⟨hSa.le, hSb.le⟩
  obtain ⟨u₁, hu₁, hSu₁⟩ := intermediate_value_Icc hab.le hcont hmem
  have hua : a < u₁ := by
    rcases hu₁.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hSa0 : S a = 0 := by rw [h]; exact hSu₁
      exact ne_of_lt hSa hSa0
  have hub : u₁ < b := by
    rcases hu₁.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have hSb0 : S b = 0 := by rw [← h]; exact hSu₁
      exact ne_of_gt hSb hSb0
  exact ⟨u₁, ⟨hua, hub⟩, hSu₁⟩

/-- S = 0 になる一点の構成：切片の左端で S < 0、S が切片上で連続で、
    地平線に向かって S → +∞ なら、切片上に S = 0 になる点が存在する。 -/
theorem defectSource_eq_zero_of_horizon_blowup {F : WedgeFields} {rp u₀ v : ℝ}
    (hrp : 0 < rp) (hu₀ : 0 < u₀)
    (hr0 : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ 0)
    (hrne : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ rp)
    (hrlim : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝[>] rp))
    (hOm : ∃ M, ∀ᶠ u in 𝓝[<] u₀,
      M ≤ F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
            * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
          + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)))
    (hDuDv : ∃ m, 0 < m ∧ ∀ᶠ u in 𝓝[<] u₀, m ≤ Du F.r u v * Dv F.r u v)
    (hScont : ContinuousOn (fun u => defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u v)
      (Icc 0 u₀))
    (hS0 : defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) 0 v < 0) :
    ∃ u₁ ∈ Ioo 0 u₀, defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u₁ v = 0 := by
  have hblow := defectSource_tendsto_atTop_of_horizon hrp hu₀ hr0 hrne hrlim hOm hDuDv
  have hIoo : ∀ᶠ u in 𝓝[<] u₀, u ∈ Ioo 0 u₀ := Ioo_mem_nhdsLT hu₀
  have hev : ∀ᶠ u in 𝓝[<] u₀, 0 < defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u v :=
    hblow.eventually (eventually_gt_atTop 0)
  obtain ⟨us, hus⟩ := (hIoo.and hev).exists
  obtain ⟨u₁, hu₁, hSu₁⟩ := exists_eq_zero_of_neg_of_pos hus.1.1
    (hScont.mono (Icc_subset_Icc_right hus.1.2.le)) hS0 hus.2
  exact ⟨u₁, ⟨hu₁.1, hu₁.2.trans hus.1.2⟩, hSu₁⟩

/-- S = 0 の一点からの v 方向への伝播（RN 版）：S(u₁, v) = 0 かつ
    v 区間上で R = 0 なら、S(u₁, ·) = 0 が区間全体で成り立つ。 -/
theorem defectSource_eq_zero_on_Icc_of_point {F : WedgeFields}
    {rp u₁ v v₀ v₁ M : ℝ}
    (hS : defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u₁ v = 0)
    (hv : v ∈ Icc v₀ v₁)
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : ∀ v' ∈ Icc v₀ v₁, F.Om u₁ v' ≠ 0)
    (hr : ∀ v' ∈ Icc v₀ v₁, F.r u₁ v' ≠ 0)
    (hrp' : ∀ v' ∈ Icc v₀ v₁, F.r u₁ v' ≠ rp)
    (hOmv : ∀ v' ∈ Icc v₀ v₁, HasDerivAt (fun w => F.Om u₁ w) (Dv F.Om u₁ v') v')
    (hWv : ∀ v' ∈ Icc v₀ v₁, HasDerivAt (fun w => F.W u₁ w) (Dv F.W u₁ v') v')
    (hrv : ∀ v' ∈ Icc v₀ v₁, HasDerivAt (fun w => F.r u₁ w) (Dv F.r u₁ v') v')
    (hru : ∀ v' ∈ Icc v₀ v₁, HasDerivAt (fun w => Du F.r u₁ w) (Duv F.r u₁ v') v')
    (hrvv : ∀ v' ∈ Icc v₀ v₁, HasDerivAt (fun w => Dv F.r u₁ w) (Dvv F.r u₁ v') v')
    (hR : ∀ v' ∈ Icc v₀ v₁,
      defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u₁ v' = 0)
    (hM : ∀ v' ∈ Ioo v₀ v₁, |Dv F.Om u₁ v' / F.Om u₁ v'| ≤ M)
    {v' : ℝ} (hv' : v' ∈ Icc v₀ v₁) :
    defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u₁ v' = 0 :=
  defectSource_eq_zero_on_Icc_of_remainder_zero heq hcon hOm hr
    (fun w hw => rnLogDeriv_hasDerivAt (hr w hw) (hrp' w hw) (hrp' w hw))
    (fun w hw => rnLogDeriv'_hasDerivAt (hr w hw) (hrp' w hw) (hrp' w hw))
    hOmv hWv hrv hru hrvv hR hM ⟨v, hv, hS⟩ hv'

/-- S = 0 の一点の構成と v 方向への伝播の組み立て：地平線での発散の仮定と
    v 区間上の伝播のデータが u ∈ (0, u₀) で一様に成り立てば、S = 0 は
    その v 区間全体に広がる（u₁ は切片上の一点）。 -/
theorem defectSource_eq_zero_on_Icc_of_horizon_blowup {F : WedgeFields}
    {rp u₀ v v₀ v₁ M : ℝ}
    (hrp : 0 < rp) (hu₀ : 0 < u₀)
    (hr0 : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ 0)
    (hrne : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ rp)
    (hrlim : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝[>] rp))
    (hOm : ∃ M', ∀ᶠ u in 𝓝[<] u₀,
      M' ≤ F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
            * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
          + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)))
    (hDuDv : ∃ m, 0 < m ∧ ∀ᶠ u in 𝓝[<] u₀, m ≤ Du F.r u v * Dv F.r u v)
    (hScont : ContinuousOn (fun u => defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u v)
      (Icc 0 u₀))
    (hS0 : defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) 0 v < 0)
    (hv : v ∈ Icc v₀ v₁)
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOmv' : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁, F.Om u₁ v' ≠ 0)
    (hrv' : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁, F.r u₁ v' ≠ 0)
    (hrp'' : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁, F.r u₁ v' ≠ rp)
    (hOmv : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁,
      HasDerivAt (fun w => F.Om u₁ w) (Dv F.Om u₁ v') v')
    (hWv : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁,
      HasDerivAt (fun w => F.W u₁ w) (Dv F.W u₁ v') v')
    (hrv : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁,
      HasDerivAt (fun w => F.r u₁ w) (Dv F.r u₁ v') v')
    (hru : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁,
      HasDerivAt (fun w => Du F.r u₁ w) (Duv F.r u₁ v') v')
    (hrvv : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁,
      HasDerivAt (fun w => Dv F.r u₁ w) (Dvv F.r u₁ v') v')
    (hR : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Icc v₀ v₁,
      defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u₁ v' = 0)
    (hM : ∀ u₁ ∈ Ioo 0 u₀, ∀ v' ∈ Ioo v₀ v₁, |Dv F.Om u₁ v' / F.Om u₁ v'| ≤ M)
    {v' : ℝ} (hv' : v' ∈ Icc v₀ v₁) :
    ∃ u₁ ∈ Ioo 0 u₀, defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u₁ v' = 0 := by
  obtain ⟨u₁, hu₁, hSu₁⟩ :=
    defectSource_eq_zero_of_horizon_blowup hrp hu₀ hr0 hrne hrlim hOm hDuDv hScont hS0
  exact ⟨u₁, hu₁, defectSource_eq_zero_on_Icc_of_point hSu₁ hv heq hcon
    (hOmv' u₁ hu₁) (hrv' u₁ hu₁) (hrp'' u₁ hu₁)
    (hOmv u₁ hu₁) (hWv u₁ hu₁) (hrv u₁ hu₁) (hru u₁ hu₁) (hrvv u₁ hu₁)
    (hR u₁ hu₁) (hM u₁ hu₁) hv'⟩

end CFT.WedgeDefectZeroPoint
