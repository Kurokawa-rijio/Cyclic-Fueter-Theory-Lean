import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 4-5（エネルギー恒等式）の残り：矩形上の積分収支。

  `WedgeEnergyIdentity.lean` のフラックス恒等式
    ∂_u F^u + ∂_v F^v = -V (∂_u A + ∂_v A)
  （導分代数の流儀）は微分形だった。ここでは解析版として、矩形
  [u0, u1] × [v0, v1] 上で積分した収支
    ∫ (F^u(u1, ·) - F^u(u0, ·)) + ∫ (F^v(·, v1) - F^v(·, v0))
      = ∬ -(V (∂_u A + ∂_v A))
  を証明する。すなわち矩形上の発散定理（グリーンの定理の積分形）である。
  証明は FTC とフビニ（区間積分の順序交換）の組み立てで、Clairaut は使わない。
  残り：フラックス恒等式そのものの解析的 `deriv` 版への移行（導分代数版は
  `WedgeEnergyIdentity.wedge_energy_flux` で証明済み）。このモジュールでは
  フラックス恒等式を各点の仮定として受け取る。
-/

namespace CFT.WedgeBalance

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- 区間積分の順序交換（フビニ）。`MeasureTheory.integral_integral_swap` の区間版。
    `CFT.WDWMix.intervalIntegral_swap` と同じもの（こちらは Spherical 側で使うため再掲）。 -/
theorem intervalIntegral_swap {F : ℝ → ℝ → ℝ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D)))) :
    ∫ x in A..B, ∫ y in C..D, F x y = ∫ y in C..D, ∫ x in A..B, F x y := by
  simp only [intervalIntegral.integral_of_le hAB, intervalIntegral.integral_of_le hCD]
  exact MeasureTheory.integral_integral_swap hF

/-- 矩形上で連続な関数は、区間の積に対する制限測度の積に関して可積分である。
    `CFT.WDWMix.integrable_prod_restrict_of_continuousOn` と同じもの。 -/
theorem integrable_prod_restrict_of_continuousOn {F : ℝ → ℝ → ℝ} {A B C D : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc A B ×ˢ Set.Icc C D)) :
    Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc A B)).prod (volume.restrict (Set.Ioc C D))) := by
  have h1 : IntegrableOn (Function.uncurry F) (Set.Icc A B ×ˢ Set.Icc C D)
      (volume : Measure (ℝ × ℝ)) :=
    hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h2 : IntegrableOn (Function.uncurry F) (Set.Ioc A B ×ˢ Set.Ioc C D)
      (volume : Measure (ℝ × ℝ)) :=
    h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  rw [MeasureTheory.Measure.prod_restrict]
  exact h2

/-- 矩形上の発散定理（グリーンの定理の積分形）。
    Fu の u 偏微分と Fv の v 偏微分の二重積分は、矩形の境界フラックスに等しい。 -/
theorem rect_divergence {Fu Fv dFu dFv : ℝ → ℝ → ℝ} {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hFu : ∀ v, ∀ u, HasDerivAt (fun u' => Fu u' v) (dFu u v) u)
    (hFv : ∀ u, ∀ v, HasDerivAt (fun v' => Fv u v') (dFv u v) v)
    (hdFu_c : Continuous (Function.uncurry dFu))
    (hdFv_c : Continuous (Function.uncurry dFv)) :
    (∫ v in v0..v1, (Fu u1 v - Fu u0 v)) + (∫ u in u0..u1, (Fv u v1 - Fv u v0))
      = ∫ u in u0..u1, ∫ v in v0..v1, (dFu u v + dFv u v) := by
  have cont_u : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ v : ℝ,
      Continuous fun u => F u v := by
    intro F hF v
    exact hF.comp (continuous_id.prod_mk continuous_const)
  have cont_v : ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ u : ℝ,
      Continuous fun v => F u v := by
    intro F hF u
    exact hF.comp (continuous_const.prod_mk continuous_id)
  have hJointFu : Integrable (Function.uncurry dFu)
      ((volume.restrict (Set.Ioc u0 u1)).prod (volume.restrict (Set.Ioc v0 v1))) :=
    integrable_prod_restrict_of_continuousOn hdFu_c.continuousOn
  have hJointFv : Integrable (Function.uncurry dFv)
      ((volume.restrict (Set.Ioc u0 u1)).prod (volume.restrict (Set.Ioc v0 v1))) :=
    integrable_prod_restrict_of_continuousOn hdFv_c.continuousOn
  have iFu_v : ∀ u, IntervalIntegrable (fun v => dFu u v) volume v0 v1 := fun u =>
    (cont_v dFu hdFu_c u).intervalIntegrable v0 v1
  have iFv_v : ∀ u, IntervalIntegrable (fun v => dFv u v) volume v0 v1 := fun u =>
    (cont_v dFv hdFv_c u).intervalIntegrable v0 v1
  have iFu_u : ∀ v, IntervalIntegrable (fun u => dFu u v) volume u0 u1 := fun v =>
    (cont_u dFu hdFu_c v).intervalIntegrable u0 u1
  have hIntA : IntervalIntegrable (fun u => ∫ v in v0..v1, dFu u v) volume u0 u1 := by
    have h := hJointFu.integral_prod_left
    have heq : (fun u => ∫ v, Function.uncurry dFu (u, v) ∂(volume.restrict (Set.Ioc v0 v1)))
        = (fun u => ∫ v in v0..v1, dFu u v) := by
      funext u
      show (∫ v in Set.Ioc v0 v1, dFu u v) = ∫ v in v0..v1, dFu u v
      exact (intervalIntegral.integral_of_le hv).symm
    rw [heq] at h
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hu]
  have hIntB : IntervalIntegrable (fun u => ∫ v in v0..v1, dFv u v) volume u0 u1 := by
    have h := hJointFv.integral_prod_left
    have heq : (fun u => ∫ v, Function.uncurry dFv (u, v) ∂(volume.restrict (Set.Ioc v0 v1)))
        = (fun u => ∫ v in v0..v1, dFv u v) := by
      funext u
      show (∫ v in Set.Ioc v0 v1, dFv u v) = ∫ v in v0..v1, dFv u v
      exact (intervalIntegral.integral_of_le hv).symm
    rw [heq] at h
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hu]
  have h1 : ∫ u in u0..u1, ∫ v in v0..v1, dFu u v
      = ∫ v in v0..v1, (Fu u1 v - Fu u0 v) := by
    rw [intervalIntegral_swap hu hv hJointFu]
    apply intervalIntegral.integral_congr
    intro v _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hFu v u) (iFu_u v)
  have h2 : ∫ u in u0..u1, ∫ v in v0..v1, dFv u v
      = ∫ u in u0..u1, (Fv u v1 - Fv u v0) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hFv u v) (iFv_v u)
  have hsum : ∫ u in u0..u1, ∫ v in v0..v1, (dFu u v + dFv u v)
      = (∫ u in u0..u1, ∫ v in v0..v1, dFu u v)
        + (∫ u in u0..u1, ∫ v in v0..v1, dFv u v) := by
    rw [← intervalIntegral.integral_add hIntA hIntB]
    apply intervalIntegral.integral_congr
    intro u _
    exact intervalIntegral.integral_add (iFu_v u) (iFv_v u)
  rw [hsum, h1, h2]

/-- ポテンシャル V(W) = W²/2 - W⁴/4 の解析版（`WedgeEnergyIdentity.wedgePot` に対応）。 -/
noncomputable def wedgePotFun (W : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (W u v) ^ 2 / 2 - (W u v) ^ 4 / 4

/-- 係数 A = Ω/(2r²) の解析版（`WedgeEnergyIdentity.wedgeA` に対応）。 -/
noncomputable def wedgeAFun (Om r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  Om u v / (2 * (r u v) ^ 2)

/-- 4-5（矩形上のエネルギー収支）：フラックス恒等式
    ∂_u F^u + ∂_v F^v = -V (∂_u A + ∂_v A)
  を各点の仮定として受け取り、矩形上で積分した収支（境界フラックス = 源の二重積分）
  を得る。dAu・dAv は A の u・v 偏微分として仮定した関数。 -/
theorem wedge_energy_balance {Fu Fv dFu dFv dAu dAv : ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ} {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hFu : ∀ v, ∀ u, HasDerivAt (fun u' => Fu u' v) (dFu u v) u)
    (hFv : ∀ u, ∀ v, HasDerivAt (fun v' => Fv u v') (dFv u v) v)
    (hdFu_c : Continuous (Function.uncurry dFu))
    (hdFv_c : Continuous (Function.uncurry dFv))
    (hflux : ∀ u v, dFu u v + dFv u v
      = -(wedgePotFun W u v) * (dAu u v + dAv u v)) :
    (∫ v in v0..v1, (Fu u1 v - Fu u0 v)) + (∫ u in u0..u1, (Fv u v1 - Fv u v0))
      = ∫ u in u0..u1, ∫ v in v0..v1, -(wedgePotFun W u v) * (dAu u v + dAv u v) := by
  rw [rect_divergence hu hv hFu hFv hdFu_c hdFv_c]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  exact hflux u v

/-- 4-5（エネルギー・フラックスの保存形）：源が消える場合（∂_u A + ∂_v A = 0）、
    矩形の境界を出入りするフラックスの合計は 0 になる。 -/
theorem wedge_energy_balance_conserved {Fu Fv dFu dFv dAu dAv : ℝ → ℝ → ℝ}
    {W : ℝ → ℝ → ℝ} {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hFu : ∀ v, ∀ u, HasDerivAt (fun u' => Fu u' v) (dFu u v) u)
    (hFv : ∀ u, ∀ v, HasDerivAt (fun v' => Fv u v') (dFv u v) v)
    (hdFu_c : Continuous (Function.uncurry dFu))
    (hdFv_c : Continuous (Function.uncurry dFv))
    (hflux : ∀ u v, dFu u v + dFv u v
      = -(wedgePotFun W u v) * (dAu u v + dAv u v))
    (hA : ∀ u v, dAu u v + dAv u v = 0) :
    (∫ v in v0..v1, (Fu u1 v - Fu u0 v)) + (∫ u in u0..u1, (Fv u v1 - Fv u v0)) = 0 := by
  have hz : ∀ u v, -(wedgePotFun W u v) * (dAu u v + dAv u v) = 0 := by
    intro u v
    simp [hA u v]
  rw [wedge_energy_balance hu hv hFu hFv hdFu_c hdFv_c hflux]
  simp only [hz, intervalIntegral.integral_zero]

end

end CFT.WedgeBalance
