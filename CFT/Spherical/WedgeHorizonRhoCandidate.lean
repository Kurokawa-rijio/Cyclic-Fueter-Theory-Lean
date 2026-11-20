/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **ρ の候補としての r の単調性と、比が定数になるための十分条件**。
  前段（`WedgeHorizonRatioLimit`）では、比 Ω(u, v)/f(ρ(u)) が地平線で
  有限の非ゼロ極限 dOm/(f′(r₊)·ρ′(u₀)) を持つことを、ρ を抽象的な
  再パラメータ化として証明した。ここでは ρ の候補を具体化する第一歩と
  して、面積半径 r 自身を取る：固定したヌル切片上で r の u 微分が
  正なら、r はその区間上で狭義単調（したがって単射で、像は区間）であり、
  ρ := r は ρ(u₀) = r₊ と ρ′(u₀) ≠ 0 を満たす再パラメータ化の候補になる。
  そのもとで比 Ω/f(r) の地平線での極限（`wedgeOmega_ratio_tendsto_rho_eq_r`、
  RN 版 `wedgeOmega_ratio_tendsto_rho_eq_r_rn`）と、最初の出口での版
  （`wedge_first_exit_rho_limit`）を証明する。さらに、比が区間上で
  定数になるための十分条件 — 比の関数がその区間上で微分 0 を持つこと —
  を抽象補題（`const_of_hasDerivAt_zero_Icc`）とくさびへの適用
  （`wedge_ratio_const_of_deriv_zero`）として定式化する。

  抽象部分は実解析の補題：導関数が正なら狭義単調
  （`strictMonoOn_of_deriv_pos_Icc`）、その像は区間
  （`image_Icc_of_deriv_pos`、中間値の定理による）、微分 0 なら定数
  （`const_of_hasDerivAt_zero_Icc`）。
  残り：ρ そのものの構成（r の単調性だけでは ρ = r が対応仮説の
  ρ であることの証明にはならず、Ω = c·f(r) の形そのものは未証明）と、
  比が地平線の近傍全体で定数 c に等しいことの証明（対応仮説そのもの）。
-/
import CFT.Spherical.WedgeHorizonRatioLimit

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeCont CFT.WedgeFirstExit

namespace CFT.WedgeHorizonRho

/-- 導関数が区間の内部で正なら、関数はその閉区間上で狭義単調。 -/
theorem strictMonoOn_of_deriv_pos_Icc {r : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn r (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv r x) :
    StrictMonoOn r (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcont
  intro x hx
  rw [interior_Icc] at hx
  exact hpos x hx

/-- 導関数が正なら、関数は区間上で単射。 -/
theorem injOn_of_deriv_pos_Icc {r : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn r (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv r x) :
    Set.InjOn r (Icc a b) :=
  (strictMonoOn_of_deriv_pos_Icc hcont hpos).injOn

/-- 導関数が正なら、関数は閉区間を閉区間に写す（中間値の定理による）。 -/
theorem image_Icc_of_deriv_pos {r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn r (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv r x) :
    r '' Icc a b = Icc (r a) (r b) := by
  have hsm : StrictMonoOn r (Icc a b) := strictMonoOn_of_deriv_pos_Icc hcont hpos
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨hsm.monotoneOn (left_mem_Icc.mpr hab) hx hx.1,
      hsm.monotoneOn hx (right_mem_Icc.mpr hab) hx.2⟩
  · exact intermediate_value_Icc hab hcont

/-- 微分が 0 なら、関数は閉区間上で定数（平均値の定理による）。 -/
theorem const_of_hasDerivAt_zero_Icc {R : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn R (Icc a b))
    (hdiff : ∀ x ∈ Icc a b, HasDerivAt R 0 x) :
    ∀ x ∈ Icc a b, R x = R a := by
  apply constant_of_has_deriv_right_zero hcont
  intro x hx
  exact (hdiff x (Ico_subset_Icc_self hx)).hasDerivWithinAt

section Wedge

variable {F : WedgeFields} {v : ℝ}

/-- くさび切片上の面積半径 r は、u 微分が正なら区間上で狭義単調。
    すなわち r は再パラメータ化 ρ の候補になる。 -/
theorem wedge_r_slice_strictMonoOn {a b : ℝ}
    (hcont : ContinuousOn (fun u => F.r u v) (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv (fun u => F.r u v) x) :
    StrictMonoOn (fun u => F.r u v) (Icc a b) :=
  strictMonoOn_of_deriv_pos_Icc hcont hpos

/-- C² 級の場では、切片の連続性は `C2On` から引き出せる。 -/
theorem wedge_r_slice_strictMonoOn_of_C2 {A b : ℝ}
    (hC2 : C2On A b F.r) (hv : v ∈ Icc (0 : ℝ) b)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) A, 0 < deriv (fun u => F.r u v) x) :
    StrictMonoOn (fun u => F.r u v) (Icc (0 : ℝ) A) := by
  have hcont : ContinuousOn (fun t => F.r t v) (Icc (0 : ℝ) A) := by
    have h : ContinuousOn (Function.uncurry F.r ∘ fun t => (t, v)) (Icc (0 : ℝ) A) :=
      hC2.cont.comp (continuous_id.prod_mk continuous_const).continuousOn
        (fun t ht => ⟨ht, hv⟩)
    simpa [Function.comp_def, Function.uncurry_apply_pair] using h
  exact strictMonoOn_of_deriv_pos_Icc hcont hpos

/-- r の単調性のもとで、r は区間を区間に写す。 -/
theorem wedge_r_slice_image_Icc {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun u => F.r u v) (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv (fun u => F.r u v) x) :
    (fun u => F.r u v) '' Icc a b = Icc (F.r a v) (F.r b v) :=
  image_Icc_of_deriv_pos hab hcont hpos

/-- ρ := r の候補：Ω と面積半径の比は、地平線で導関数の比に収束する。 -/
theorem wedgeOmega_ratio_tendsto_rho_eq_r {u₀ rp : ℝ} {f : ℝ → ℝ}
    {dOm df dr : ℝ}
    (hOm : HasDerivAt (fun u => F.Om u v) dOm u₀) (hOm0 : F.Om u₀ v = 0)
    (hr : HasDerivAt (fun u => F.r u v) dr u₀) (hr0 : F.r u₀ v = rp) (hdr : dr ≠ 0)
    (hf : HasDerivAt f df rp) (hf0 : f rp = 0) (hdf : df ≠ 0) :
    Tendsto (fun u => F.Om u v / f (F.r u v)) (𝓝[≠] u₀) (𝓝 (dOm / (df * dr))) :=
  CFT.WedgeHorizonRatio.wedgeOmega_ratio_tendsto hOm hOm0 hr hr0 hdr hf hf0 hdf

/-- ρ := r の候補の RN 版：極限は dOm / (((r₊ − r₋)/r₊²) · r′(u₀))。 -/
theorem wedgeOmega_ratio_tendsto_rho_eq_r_rn {u₀ rp rm : ℝ}
    {dOm dr : ℝ}
    (hOm : HasDerivAt (fun u => F.Om u v) dOm u₀) (hOm0 : F.Om u₀ v = 0)
    (hr : HasDerivAt (fun u => F.r u v) dr u₀) (hr0 : F.r u₀ v = rp) (hdr : dr ≠ 0)
    (hp : rp ≠ 0) (hm : rp ≠ rm) :
    Tendsto (fun u => F.Om u v / CFT.RNExtremalZero.rnF rp rm (F.r u v)) (𝓝[≠] u₀)
      (𝓝 (dOm / ((rp - rm) / rp ^ 2 * dr))) :=
  CFT.WedgeHorizonRatio.wedgeOmega_ratio_tendsto_rn hOm hOm0 hr hr0 hdr hp hm

/-- ρ := r の候補のもとで、比の極限は 0 でない。 -/
theorem wedgeOmega_ratio_limit_ne_zero_rho_eq_r {dOm df dr : ℝ}
    (hdOm : dOm ≠ 0) (hdf : df ≠ 0) (hdr : dr ≠ 0) :
    dOm / (df * dr) ≠ 0 :=
  CFT.WedgeHorizonRatio.wedgeOmega_ratio_limit_ne_zero hdOm hdf hdr

/-- 比が定数になるための十分条件：比の関数が区間上で微分 0 を持てば、
    比はその区間上で定数（地平線を含まない区間での形。比の微分可能性
    自体が仮定に入る）。 -/
theorem wedge_ratio_const_of_deriv_zero {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn (fun u => F.Om u v / f (F.r u v)) (Icc a b))
    (hdiff : ∀ x ∈ Icc a b,
      HasDerivAt (fun u => F.Om u v / f (F.r u v)) 0 x) :
    ∀ x ∈ Icc a b, F.Om x v / f (F.r x v) = F.Om a v / f (F.r a v) :=
  const_of_hasDerivAt_zero_Icc hcont hdiff

/-- 最初の出口での比の極限（ρ := r の候補）：出口で r の微分が正なら、
    比 Ω/rnF(r) は有限の非ゼロ極限を持つ。r の微分可能性・非退化は、
    最初のゼロに対する条件つきの仮定として残る。 -/
theorem wedge_first_exit_rho_limit {a b B m : ℝ} {F : WedgeFields} {v : ℝ}
    {rp rm : ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om)
    (hexit : ∀ u ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' = 0 →
      ¬ Inside B m (ptOf F u v'))
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (hr : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 →
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) →
      ∃ dr : ℝ, HasDerivAt (fun u => F.r u v) dr c ∧ F.r c v = rp ∧ 0 < dr)
    (hOm : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 →
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) →
      ∃ dOm : ℝ, HasDerivAt (fun u => F.Om u v) dOm c ∧ dOm ≠ 0)
    (hp : rp ≠ 0) (hm : rp ≠ rm) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧
      (∃ dOm dr : ℝ, dOm ≠ 0 ∧ dr ≠ 0 ∧
        Tendsto (fun u => F.Om u v / CFT.RNExtremalZero.rnF rp rm (F.r u v)) (𝓝[≠] c)
          (𝓝 (dOm / ((rp - rm) / rp ^ 2 * dr)))) ∧
      ¬ Inside B m (ptOf F c v) := by
  obtain ⟨c, hc, hfc, _hpos, hmin, hout⟩ :=
    CFT.WedgeFirstExit.wedge_first_exit ha hdata hv hC2 hexit hneg
  obtain ⟨dr, hrd, hr0, hdrpos⟩ := hr c hc hfc hmin
  obtain ⟨dOm, hOmd, hdOm⟩ := hOm c hc hfc hmin
  exact ⟨c, hc, hfc, ⟨dOm, dr, hdOm, ne_of_gt hdrpos,
    wedgeOmega_ratio_tendsto_rho_eq_r_rn hOmd hfc hrd hr0 (ne_of_gt hdrpos) hp hm⟩,
    hout⟩

end Wedge

end CFT.WedgeHorizonRho
