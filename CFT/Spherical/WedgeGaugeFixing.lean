/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (a)：特性データと角条件による二重ヌルゲージの固定。

  二重ヌル座標の残余自由度は各方向の再パラメータ化
  u → ũ(u)、v → ṽ(v) である。ここではそのうち特性データで消える部分、
  すなわち帽子データと首データが再パラメータ化を恒等写像に固定すること
  を証明する。

  帽子（v = 0 面）では r(u, 0) = capR u = cos²(u/√2)、
  W(u, 0) = capW u = sin(u/√2)。cos² は [0, π/2] 上で単射
  （cos が [0, π] 上で狭義単調減少し、[0, π/2] では cos ≥ 0 なので
  平方を取っても単射性が残る）であり、sin は [-π/2, π/2] 上で狭義単調
  増加である。したがって u/√2 ∈ [0, π/2] となるキャップ区間
  u ∈ [0, π/√2] 上では capR も capW も単射で、データを保つ ũ は
  恒等写像になる（`cap_gauge_id`）。

  首（u = 0 面）では Ω(0, v) = neckOm v = (cosh(v/√2))² ⁻¹。
  cosh は [0, ∞) 上で狭義単調増加かつ正なので、neckOm も [0, ∞) 上で
  単射であり、データを保つ ṽ は恒等写像になる（`neck_gauge_id`）。

  最後に `HasWedgeData` を満たす二つの場 F, F' に対して、F' のデータが
  F のデータを再パラメータ化で引き戻したものなら、その再パラメータ化は
  両方向とも恒等写像であること（`wedgeData_gauge_id`）を証明する。
  これが 12-8 (a) の特性データによる部分である。角条件（W_u = 1/√2 など）
  による残りの固定は別葉として残る。

  残り：(a) の角条件による部分、(b) のくさび EYM 系の形での分類
  （近地平線極限 AdS₂ × S² など。温度の側は 6-2・9-3・
  `RNExtremalDoubleZero` で証明済み）。
-/
import Mathlib
import CFT.Spherical.WedgeEYMSystem

open Real Set

namespace CFT.WedgeGaugeFixing

/-- cos² は [0, π/2] 上で単射。cos はそこで非負なので、平方の等式から
    cos 自身の等式が戻り、cos の [0, π] での狭義単調減少が効く。 -/
theorem cos_sq_injOn :
    Set.InjOn (fun x : ℝ => (Real.cos x) ^ 2) (Set.Icc 0 (Real.pi / 2)) := by
  intro a ha b hb h
  have hpi := Real.pi_pos
  have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ha.1], ha.2⟩
  have hcb : 0 ≤ Real.cos b := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1], hb.2⟩
  have habs : |Real.cos a| = |Real.cos b| := by
    rw [← sq_eq_sq_iff_abs_eq_abs]; exact h
  rw [abs_of_nonneg hca, abs_of_nonneg hcb] at habs
  exact Real.strictAntiOn_cos.injOn
    ⟨ha.1, by linarith [ha.2]⟩ ⟨hb.1, by linarith [hb.2]⟩ habs

/-- 補助：u ∈ [0, π/√2] なら u/√2 ∈ [0, π/2]。 -/
theorem div_sqrt_two_mem_Icc {u : ℝ}
    (hu : u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2)) :
    u / Real.sqrt 2 ∈ Set.Icc 0 (Real.pi / 2) := by
  refine ⟨div_nonneg hu.1 (Real.sqrt_nonneg 2), ?_⟩
  have hle := div_le_div_of_nonneg_right hu.2 (Real.sqrt_nonneg 2)
  rwa [div_div, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hle

/-- capR はキャップ区間 [0, π/√2] 上で単射。
    （区間の右端は cos²(u/√2) = 0 となる点で、帽子の端である。） -/
theorem capR_injOn :
    Set.InjOn CFT.Wedge.capR (Set.Icc 0 (Real.pi / Real.sqrt 2)) := by
  intro a ha b hb h
  have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h' : a / Real.sqrt 2 = b / Real.sqrt 2 :=
    cos_sq_injOn (div_sqrt_two_mem_Icc ha) (div_sqrt_two_mem_Icc hb)
      (by simpa [CFT.Wedge.capR] using h)
  exact (div_left_inj' h2).mp h'

/-- capW はキャップ区間 [0, π/√2] 上で単射
    （sin の [-π/2, π/2] での狭義単調増加による）。 -/
theorem capW_injOn :
    Set.InjOn CFT.Wedge.capW (Set.Icc 0 (Real.pi / Real.sqrt 2)) := by
  intro a ha b hb h
  have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hpi := Real.pi_pos
  have ha' := div_sqrt_two_mem_Icc ha
  have hb' := div_sqrt_two_mem_Icc hb
  have h' : a / Real.sqrt 2 = b / Real.sqrt 2 := by
    apply Real.strictMonoOn_sin.injOn
    · exact ⟨by linarith [ha'.1], by linarith [ha'.2]⟩
    · exact ⟨by linarith [hb'.1], by linarith [hb'.2]⟩
    · simpa [CFT.Wedge.capW] using h
  exact (div_left_inj' h2).mp h'

/-- neckOm は [0, ∞) 上で単射（cosh の [0, ∞) での狭義単調増加と正値性による）。 -/
theorem neckOm_injOn : Set.InjOn CFT.Wedge.neckOm (Set.Ici 0) := by
  intro a ha b hb h
  have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h' : (Real.cosh (a / Real.sqrt 2)) ^ 2 = (Real.cosh (b / Real.sqrt 2)) ^ 2 := by
    have hh := h
    simp only [CFT.Wedge.neckOm] at hh
    exact inv_inj.mp hh
  have habs : |Real.cosh (a / Real.sqrt 2)| = |Real.cosh (b / Real.sqrt 2)| := by
    rw [← sq_eq_sq_iff_abs_eq_abs]; exact h'
  rw [abs_of_pos (Real.cosh_pos _), abs_of_pos (Real.cosh_pos _)] at habs
  have h'' : a / Real.sqrt 2 = b / Real.sqrt 2 :=
    Real.cosh_strictMonoOn.injOn
      (mem_Ici.mpr (div_nonneg (mem_Ici.mp ha) (Real.sqrt_nonneg 2)))
      (mem_Ici.mpr (div_nonneg (mem_Ici.mp hb) (Real.sqrt_nonneg 2))) habs
  exact (div_left_inj' h2).mp h''

/-- キャップ側のゲージ固定：帽子データ capR を保つ再パラメータ化は
    キャップ区間上で恒等写像である。 -/
theorem cap_gauge_id (φ : ℝ → ℝ)
    (hφ : ∀ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2),
      φ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2)
        ∧ CFT.Wedge.capR (φ u) = CFT.Wedge.capR u) :
    ∀ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2), φ u = u := by
  intro u hu
  exact capR_injOn (hφ u hu).1 hu (hφ u hu).2

/-- キャップ側のゲージ固定（W データ版）：帽子データ capW を保つ
    再パラメータ化もキャップ区間上で恒等写像である。 -/
theorem capW_gauge_id (φ : ℝ → ℝ)
    (hφ : ∀ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2),
      φ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2)
        ∧ CFT.Wedge.capW (φ u) = CFT.Wedge.capW u) :
    ∀ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2), φ u = u := by
  intro u hu
  exact capW_injOn (hφ u hu).1 hu (hφ u hu).2

/-- 首側のゲージ固定：首データ neckOm を保つ再パラメータ化は
    [0, ∞) 上で恒等写像である。 -/
theorem neck_gauge_id (ψ : ℝ → ℝ)
    (hψ : ∀ v ∈ Set.Ici (0:ℝ),
      ψ v ∈ Set.Ici (0:ℝ) ∧ CFT.Wedge.neckOm (ψ v) = CFT.Wedge.neckOm v) :
    ∀ v ∈ Set.Ici (0:ℝ), ψ v = v := by
  intro v hv
  exact neckOm_injOn (hψ v hv).1 hv (hψ v hv).2

/-- 特性データによる二重ヌルゲージの固定（12-8 (a) のデータ部分）：
    `HasWedgeData` を満たす二つの場 F, F' について、F' の帽子・首データが
    F のデータを再パラメータ化 φ, ψ で引き戻したものなら、φ は
    キャップ区間上で、ψ は [0, ∞) 上で恒等写像である。 -/
theorem wedgeData_gauge_id (F F' : CFT.Wedge.WedgeFields)
    (hF : CFT.Wedge.HasWedgeData F) (hF' : CFT.Wedge.HasWedgeData F')
    (φ ψ : ℝ → ℝ)
    (hφ : ∀ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2),
      φ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2) ∧ F'.r u 0 = F.r (φ u) 0)
    (hψ : ∀ v ∈ Set.Ici (0:ℝ),
      ψ v ∈ Set.Ici (0:ℝ) ∧ F'.Om 0 v = F.Om 0 (ψ v)) :
    (∀ u ∈ Set.Icc 0 (Real.pi / Real.sqrt 2), φ u = u)
      ∧ (∀ v ∈ Set.Ici (0:ℝ), ψ v = v) := by
  constructor
  · intro u hu
    apply capR_injOn (hφ u hu).1 hu
    have h1 : F'.r u 0 = CFT.Wedge.capR u := (hF'.1 u).1
    have h2 : F.r (φ u) 0 = CFT.Wedge.capR (φ u) := (hF.1 (φ u)).1
    rw [← h1, ← h2, (hφ u hu).2]
  · intro v hv
    apply neckOm_injOn (hψ v hv).1 hv
    have h1 : F'.Om 0 v = CFT.Wedge.neckOm v := (hF'.2 v).2.1
    have h2 : F.Om 0 (ψ v) = CFT.Wedge.neckOm (ψ v) := (hF.2 (ψ v)).2.1
    rw [← h1, ← h2, (hψ v hv).2]

end CFT.WedgeGaugeFixing
