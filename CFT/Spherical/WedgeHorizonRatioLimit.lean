/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **c の候補の地平線での極限**。対応仮説 Ω(u, v) = c · f(ρ(u)) は、
  くさび解の側の Ω と RN 側の計量関数 f を結ぶが、その定数 c と再パラメー
  タ化 ρ を実際の解から構成することはまだ残っている。ここではその構成に
  要る解析的な核を証明する：Ω が切片上で単純ゼロを持ち、ρ がその点で
  C¹ かつ ρ′(u₀) ≠ 0 で、f が r₊ で単純ゼロなら、比 Ω(u, v)/f(ρ(u)) は
  u → u₀（穿孔近傍）で有限の非ゼロ極限
    dOm / (f′(r₊) · ρ′(u₀))
  を持つ（`wedgeOmega_ratio_tendsto`・`wedgeOmega_ratio_tendsto_rn`）。
  すなわち比を c の候補とみなすとき、地平線での値は連続的に定まり、
  0 にはならない。極限が正なら、地平線の穿孔近傍では比は正で、
  Ω と f(ρ) は同じ符号を持つ（`wedgeOmega_ratio_eventually_pos`、
  `wedgeOmega_ratio_eventually_pos_rn`）—— 出口をまたぐ対応の片側の
  定式化の一歩である。最後に最初の出口での版
  （`wedge_first_exit_ratio_limit`）で、この極限が実際の延長解の
  最初の出口においても成り立つことを示す。

  抽象部分は実解析の補題（`tendsto_div_of_hasDerivAt_zero`）：0 になる
  二つの関数の比の極限は導関数の比で、傾きの極限（`slope`）による。
  残り：ρ そのものの構成（r の単調性からの候補づけ）と、比が地平線の
  近傍全体で定数 c に等しいことの証明（対応仮説そのもの）。
-/
import Mathlib
import CFT.Quantum.RNExtremalDoubleZero
import CFT.Spherical.WedgeHorizonFirstExit

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeCont

namespace CFT.WedgeHorizonRatio

/-- 0 になる二つの関数の比の極限は導関数の比（傾きの極限による）。 -/
theorem tendsto_div_of_hasDerivAt_zero {f g : ℝ → ℝ} {x₀ f' g' : ℝ}
    (hf : HasDerivAt f f' x₀) (hg : HasDerivAt g g' x₀)
    (hf0 : f x₀ = 0) (hg0 : g x₀ = 0) (hg' : g' ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] x₀) (𝓝 (f' / g')) := by
  have hfs := hasDerivAt_iff_tendsto_slope.mp hf
  have hgs := hasDerivAt_iff_tendsto_slope.mp hg
  have hdiv := hfs.div hgs hg'
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ x₀ := hx
  show (x - x₀)⁻¹ * (f x - f x₀) / ((x - x₀)⁻¹ * (g x - g x₀)) = f x / g x
  rw [hf0, hg0, sub_zero, sub_zero]
  exact mul_div_mul_left _ _ (inv_ne_zero (sub_ne_zero.mpr hx'))

section Wedge

variable {Om : ℝ → ℝ → ℝ} {v u₀ rp rm : ℝ} {ρ : ℝ → ℝ} {f : ℝ → ℝ}

/-- くさび切片上の Ω と再パラメータ化された f の比は、地平線で
    導関数の比に収束する。 -/
theorem wedgeOmega_ratio_tendsto {dOm df dρ : ℝ}
    (hOm : HasDerivAt (fun u => Om u v) dOm u₀) (hOm0 : Om u₀ v = 0)
    (hρ : HasDerivAt ρ dρ u₀) (hρ0 : ρ u₀ = rp) (hdρ : dρ ≠ 0)
    (hf : HasDerivAt f df rp) (hf0 : f rp = 0) (hdf : df ≠ 0) :
    Tendsto (fun u => Om u v / f (ρ u)) (𝓝[≠] u₀) (𝓝 (dOm / (df * dρ))) := by
  have hf' : HasDerivAt f df (ρ u₀) := by rw [hρ0]; exact hf
  have hg : HasDerivAt (fun u => f (ρ u)) (df * dρ) u₀ := hf'.comp u₀ hρ
  have hg0 : f (ρ u₀) = 0 := by rw [hρ0]; exact hf0
  exact tendsto_div_of_hasDerivAt_zero hOm hg hOm0 hg0 (mul_ne_zero hdf hdρ)

/-- 比の極限は 0 でない（Ω の単純ゼロと f・ρ の非退化のもとで）。 -/
theorem wedgeOmega_ratio_limit_ne_zero {dOm df dρ : ℝ}
    (hdOm : dOm ≠ 0) (hdf : df ≠ 0) (hdρ : dρ ≠ 0) :
    dOm / (df * dρ) ≠ 0 :=
  div_ne_zero hdOm (mul_ne_zero hdf hdρ)

/-- RN の計量関数への版：極限は dOm / (((r₊ − r₋)/r₊²) · ρ′(u₀))。 -/
theorem wedgeOmega_ratio_tendsto_rn {dOm dρ : ℝ}
    (hOm : HasDerivAt (fun u => Om u v) dOm u₀) (hOm0 : Om u₀ v = 0)
    (hρ : HasDerivAt ρ dρ u₀) (hρ0 : ρ u₀ = rp) (hdρ : dρ ≠ 0)
    (hp : rp ≠ 0) (hm : rp ≠ rm) :
    Tendsto (fun u => Om u v / CFT.RNExtremalZero.rnF rp rm (ρ u)) (𝓝[≠] u₀)
      (𝓝 (dOm / ((rp - rm) / rp ^ 2 * dρ))) := by
  have hf : HasDerivAt (CFT.RNExtremalZero.rnF rp rm) ((rp - rm) / rp ^ 2) (ρ u₀) := by
    rw [hρ0]
    exact CFT.RNExtremalZero.rnF_hasDerivAt rp rm hp
  have hf' : HasDerivAt (CFT.RNExtremalZero.rnF rp rm) ((rp - rm) / rp ^ 2) rp :=
    hρ0 ▸ hf
  exact wedgeOmega_ratio_tendsto hOm hOm0 hρ hρ0 hdρ hf'
    (CFT.RNExtremalZero.rnF_at_rp rp rm)
    (div_ne_zero (sub_ne_zero.mpr hm) (pow_ne_zero 2 hp))

/-- 極限が正なら、地平線の穿孔近傍では比は正：Ω と f(ρ) は同じ符号。 -/
theorem wedgeOmega_ratio_eventually_pos {dOm df dρ : ℝ}
    (hOm : HasDerivAt (fun u => Om u v) dOm u₀) (hOm0 : Om u₀ v = 0)
    (hρ : HasDerivAt ρ dρ u₀) (hρ0 : ρ u₀ = rp) (hdρ : dρ ≠ 0)
    (hf : HasDerivAt f df rp) (hf0 : f rp = 0) (hdf : df ≠ 0)
    (hlim : 0 < dOm / (df * dρ)) :
    ∀ᶠ u in 𝓝[≠] u₀, 0 < Om u v / f (ρ u) :=
  (wedgeOmega_ratio_tendsto hOm hOm0 hρ hρ0 hdρ hf hf0 hdf).eventually
    (Ioi_mem_nhds hlim)

/-- RN 版：非極端（r₋ < r₊）で dOm > 0、ρ′(u₀) > 0 なら、地平線の
    穿孔近傍では Ω/f(ρ(u)) > 0。 -/
theorem wedgeOmega_ratio_eventually_pos_rn {dOm dρ : ℝ}
    (hOm : HasDerivAt (fun u => Om u v) dOm u₀) (hOm0 : Om u₀ v = 0)
    (hρ : HasDerivAt ρ dρ u₀) (hρ0 : ρ u₀ = rp) (hdρ : dρ ≠ 0)
    (hp : 0 < rp) (hm : rm < rp) (hdOm : 0 < dOm) (hdρpos : 0 < dρ) :
    ∀ᶠ u in 𝓝[≠] u₀, 0 < Om u v / CFT.RNExtremalZero.rnF rp rm (ρ u) := by
  have hdf : (0 : ℝ) < (rp - rm) / rp ^ 2 := div_pos (sub_pos.mpr hm) (pow_pos hp 2)
  have hlim : 0 < dOm / ((rp - rm) / rp ^ 2 * dρ) :=
    div_pos hdOm (mul_pos hdf hdρpos)
  exact (wedgeOmega_ratio_tendsto_rn hOm hOm0 hρ hρ0 hdρ (ne_of_gt hp)
    (ne_of_gt hm)).eventually (Ioi_mem_nhds hlim)

/-- 最初の出口での比の極限：Ω が負になる点があれば、最初の出口 c では
    比 Ω/f(ρ) が有限の非ゼロ極限を持つ。ρ と Ω の微分可能性・非退化は、
    最初のゼロに対する条件つきの仮定として残る（`wedge_first_exit_crossing`
    の `hd` と同じ形）。 -/
theorem wedge_first_exit_ratio_limit {a b B m : ℝ} {F : WedgeFields} {v : ℝ}
    {rp rm : ℝ} {ρ : ℝ → ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om)
    (hexit : ∀ u ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' = 0 →
      ¬ Inside B m (ptOf F u v'))
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (hρ : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 →
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) →
      ∃ dρ : ℝ, HasDerivAt ρ dρ c ∧ ρ c = rp ∧ dρ ≠ 0)
    (hOm : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 →
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) →
      ∃ dOm : ℝ, HasDerivAt (fun u => F.Om u v) dOm c ∧ dOm ≠ 0)
    (hp : rp ≠ 0) (hm : rp ≠ rm) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧
      (∃ dOm dρ : ℝ, dOm ≠ 0 ∧ dρ ≠ 0 ∧
        Tendsto (fun u => F.Om u v / CFT.RNExtremalZero.rnF rp rm (ρ u)) (𝓝[≠] c)
          (𝓝 (dOm / ((rp - rm) / rp ^ 2 * dρ)))) ∧
      ¬ Inside B m (ptOf F c v) := by
  obtain ⟨c, hc, hfc, _hpos, hmin, hout⟩ :=
    CFT.WedgeFirstExit.wedge_first_exit ha hdata hv hC2 hexit hneg
  obtain ⟨dρ, hρd, hρ0, hdρ⟩ := hρ c hc hfc hmin
  obtain ⟨dOm, hOmd, hdOm⟩ := hOm c hc hfc hmin
  exact ⟨c, hc, hfc, ⟨dOm, dρ, hdOm, hdρ,
    wedgeOmega_ratio_tendsto_rn hOmd hfc hρd hρ0 hdρ hp hm⟩, hout⟩

end Wedge

end CFT.WedgeHorizonRatio
