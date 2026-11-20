/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **RN の計量関数 f の対数微分 f′/f の明示形（部分分数表示）と、地平線での留数**。
  前段（`WedgeHorizonRatioODE`）では、対応仮説 Ω = c·f(r) が切片上の
  対数微分の一致 dOm/Ω = (f′/f)·dr という一階の微分方程式の条件に帰着
  された。ここでは RN の f(r) = (r − r₊)(r − r₋)/r² に対してその右辺を
  明示する：f′/f = 1/(r − r₊) + 1/(r − r₋) − 2/r。したがって一致条件は
  dOm/Ω = (1/(r − r₊) + 1/(r − r₋) − 2/r)·dr という、r の有理関数との
  比較になる。さらに (r − r₊)·(f′/f) の r → r₊ での極限は、非極限では 1、
  極限（r₊ = r₋）では 2 であり、留数がゼロの位数（一次ゼロ ↔ 1、
  二重ゼロ ↔ 2）を読み取る。すなわち対数微分の一致条件は、地平線の近く
  では Ω′/Ω の留数が 1 か 2 かという形で剛性分類と直結する。
  くさびへの適用として、一致条件を RN の明示形で書いた版の対応定理
  `wedge_correspondence_rn_logDeriv`（と極限版）を証明する。

  抽象部分は RN の f についての補題：商の微分公式からの導関数の値
  （`rnF_deriv_value`・`rnF_hasDerivAt_logDeriv`）、f′/f の明示形
  （`rnF_logDeriv_eq`）、極限形（`rnLogDeriv_extremal`）、留数の極限
  （`rnLogDeriv_mul_sub_tendsto_one`・`rnLogDeriv_mul_sub_tendsto_two`）。
  残り：対数微分の一致そのものが実際のくさび解で成り立つことの証明
  （発展方程式からの導出）と、ρ そのものの構成（対応仮説そのもの）。
-/
import CFT.Quantum.RNExtremalDoubleZero
import CFT.Spherical.WedgeHorizonRatioODE

open Real Set Filter Topology
open CFT.RNExtremalZero

namespace CFT.RNLogDeriv

/-- RN の計量関数 f の対数微分 f′/f の明示形（部分分数表示）。 -/
noncomputable def rnLogDeriv (rp rm r : ℝ) : ℝ := 1 / (r - rp) + 1 / (r - rm) - 2 / r

/-- 商の微分公式による f′(r) の値。 -/
theorem rnF_deriv_value {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) (hrm : r ≠ rm) :
    ((2 * r - rp - rm) * r ^ 2 - (r - rp) * (r - rm) * (2 * r)) / (r ^ 2) ^ 2
      = rnF rp rm r * rnLogDeriv rp rm r := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  have h2 : r - rm ≠ 0 := sub_ne_zero.mpr hrm
  simp only [rnF, rnLogDeriv]
  field_simp
  ring

/-- f′(r) = f(r) · (f′/f)(r)：対数微分の形での微分可能性。 -/
theorem rnF_hasDerivAt_logDeriv {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp)
    (hrm : r ≠ rm) :
    HasDerivAt (rnF rp rm) (rnF rp rm r * rnLogDeriv rp rm r) r := by
  have hN : HasDerivAt (fun x => (x - rp) * (x - rm)) (2 * r - rp - rm) r := by
    have h := ((hasDerivAt_id r).sub_const rp).mul ((hasDerivAt_id r).sub_const rm)
    simp only [id_eq] at h
    convert h using 1
    ring
  have hD : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := hN.div hD (pow_ne_zero 2 hr)
  rwa [rnF_deriv_value hr hrp hrm] at h

/-- f′(r) の `deriv` 形。 -/
theorem rnF_deriv_eq {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) (hrm : r ≠ rm) :
    deriv (rnF rp rm) r = rnF rp rm r * rnLogDeriv rp rm r :=
  (rnF_hasDerivAt_logDeriv hr hrp hrm).deriv

/-- r ≠ 0、r ≠ r₊、r ≠ r₋ なら f(r) ≠ 0。 -/
theorem rnF_ne_zero_of_ne {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) (hrm : r ≠ rm) :
    rnF rp rm r ≠ 0 := by
  simp only [rnF]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hrp) (sub_ne_zero.mpr hrm))
    (pow_ne_zero 2 hr)

/-- f′(r)/f(r) の明示形：部分分数表示。 -/
theorem rnF_logDeriv_eq {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) (hrm : r ≠ rm) :
    deriv (rnF rp rm) r / rnF rp rm r = rnLogDeriv rp rm r := by
  rw [(rnF_hasDerivAt_logDeriv hr hrp hrm).deriv,
    mul_div_cancel_left₀ _ (rnF_ne_zero_of_ne hr hrp hrm)]

/-- 極限（r₊ = r₋）での対数微分：2/(r − r₊) − 2/r。 -/
theorem rnLogDeriv_extremal {rp r : ℝ} :
    rnLogDeriv rp rp r = 2 / (r - rp) - 2 / r := by
  simp only [rnLogDeriv, ← two_mul, mul_one_div]

/-- 非極限での留数：(r − r₊)·(f′/f) → 1（r → r₊⁺）。一次ゼロの留数は 1。 -/
theorem rnLogDeriv_mul_sub_tendsto_one {rp rm : ℝ} (hrp0 : rp ≠ 0) (hne : rp ≠ rm) :
    Tendsto (fun r => (r - rp) * rnLogDeriv rp rm r) (𝓝[>] rp) (𝓝 1) := by
  have hev : (fun r => (r - rp) * rnLogDeriv rp rm r) =ᶠ[𝓝[>] rp]
      (fun r => (r * rm + r * rp - 2 * rm * rp) / (r * (r - rm))) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hne),
      eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hrp0)] with
      r hr hrne hrne0
    have hrp' : r ≠ rp := ne_of_gt hr
    have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp'
    have h2 : r - rm ≠ 0 := sub_ne_zero.mpr hrne
    simp only [rnLogDeriv]
    field_simp
    ring
  have hcont : ContinuousAt
      (fun r => (r * rm + r * rp - 2 * rm * rp) / (r * (r - rm))) rp := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero hrp0 (sub_ne_zero.mpr hne)
  have hval : (rp * rm + rp * rp - 2 * rm * rp) / (rp * (rp - rm)) = 1 := by
    rw [div_eq_one_iff_eq (mul_ne_zero hrp0 (sub_ne_zero.mpr hne))]
    ring
  have htend : Tendsto (fun r => (r * rm + r * rp - 2 * rm * rp) / (r * (r - rm)))
      (𝓝[>] rp) (𝓝 1) := by
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi rp) hcont.tendsto
    rwa [hval] at h
  exact htend.congr' hev.symm

/-- 極限での留数：(r − r₊)·(f′/f) → 2（r → r₊⁺）。二重ゼロの留数は 2。 -/
theorem rnLogDeriv_mul_sub_tendsto_two {rp : ℝ} (hrp0 : rp ≠ 0) :
    Tendsto (fun r => (r - rp) * rnLogDeriv rp rp r) (𝓝[>] rp) (𝓝 2) := by
  have hev : (fun r => (r - rp) * rnLogDeriv rp rp r) =ᶠ[𝓝[>] rp]
      (fun r => 2 * rp / r) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds hrp0)] with
      r hr hrne0
    have hrp' : r ≠ rp := ne_of_gt hr
    have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp'
    simp only [rnLogDeriv]
    field_simp
    ring
  have hcont : ContinuousAt (fun r => 2 * rp / r) rp := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hrp0
  have hval : 2 * rp / rp = 2 := mul_div_cancel_right₀ 2 hrp0
  have htend : Tendsto (fun r => 2 * rp / r) (𝓝[>] rp) (𝓝 2) := by
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi rp) hcont.tendsto
    rwa [hval] at h
  exact htend.congr' hev.symm

section Wedge

open CFT.Wedge

variable {F : WedgeFields} {v : ℝ}

/-- くさび版（RN の明示形）：切片上で対数微分が RN の明示形に一致すれば、
    区間上で Ω(u, v) = c * f(r(u, v))。 -/
theorem wedge_correspondence_rn_logDeriv {a b rp rm : ℝ}
    (hcont : ContinuousOn (fun u => F.Om u v / rnF rp rm (F.r u v)) (Icc a b))
    (hOm : ∀ x ∈ Icc a b, ∃ dOm, HasDerivAt (fun u => F.Om u v) dOm x)
    (hr : ∀ x ∈ Icc a b, ∃ dr, HasDerivAt (fun u => F.r u v) dr x)
    (hr0 : ∀ x ∈ Icc a b, F.r x v ≠ 0)
    (hrp : ∀ x ∈ Icc a b, F.r x v ≠ rp)
    (hrm : ∀ x ∈ Icc a b, F.r x v ≠ rm)
    (hmatch : ∀ x ∈ Icc a b, ∀ dOm dr,
      HasDerivAt (fun u => F.Om u v) dOm x →
      HasDerivAt (fun u => F.r u v) dr x →
      dOm = F.Om x v * (rnLogDeriv rp rm (F.r x v) * dr)) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, F.Om x v = c * rnF rp rm (F.r x v) := by
  apply CFT.WedgeHorizonRatioODE.wedge_correspondence_of_logDeriv_match hcont hOm hr
  · intro x hx
    exact ⟨rnF rp rm (F.r x v) * rnLogDeriv rp rm (F.r x v),
      rnF_hasDerivAt_logDeriv (hr0 x hx) (hrp x hx) (hrm x hx)⟩
  · intro x hx
    exact rnF_ne_zero_of_ne (hr0 x hx) (hrp x hx) (hrm x hx)
  · intro x hx dOm df dr hdOm hdf hdr
    have hdfv : df = rnF rp rm (F.r x v) * rnLogDeriv rp rm (F.r x v) :=
      ((rnF_hasDerivAt_logDeriv (hr0 x hx) (hrp x hx) (hrm x hx)).unique hdf).symm
    rw [hdfv, hmatch x hx dOm dr hdOm hdr]
    ring

/-- くさび版（極限、RN の明示形）：r₊ = r₋ のとき、一致条件は
    dOm/Ω = (2/(r − r₊) − 2/r)·dr という形になる。 -/
theorem wedge_correspondence_rn_logDeriv_extremal {a b rp : ℝ}
    (hcont : ContinuousOn (fun u => F.Om u v / rnF rp rp (F.r u v)) (Icc a b))
    (hOm : ∀ x ∈ Icc a b, ∃ dOm, HasDerivAt (fun u => F.Om u v) dOm x)
    (hr : ∀ x ∈ Icc a b, ∃ dr, HasDerivAt (fun u => F.r u v) dr x)
    (hr0 : ∀ x ∈ Icc a b, F.r x v ≠ 0)
    (hrp : ∀ x ∈ Icc a b, F.r x v ≠ rp)
    (hmatch : ∀ x ∈ Icc a b, ∀ dOm dr,
      HasDerivAt (fun u => F.Om u v) dOm x →
      HasDerivAt (fun u => F.r u v) dr x →
      dOm = F.Om x v * ((2 / (F.r x v - rp) - 2 / F.r x v) * dr)) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, F.Om x v = c * rnF rp rp (F.r x v) := by
  apply wedge_correspondence_rn_logDeriv hcont hOm hr hr0 hrp hrp
  intro x hx dOm dr hdOm hdr
  rw [rnLogDeriv_extremal]
  exact hmatch x hx dOm dr hdOm hdr

end Wedge

end CFT.RNLogDeriv
