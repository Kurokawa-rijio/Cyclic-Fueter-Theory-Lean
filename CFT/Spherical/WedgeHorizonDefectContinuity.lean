/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **切片上の S の連続性**。前段（`WedgeHorizonDefectZeroPoint`）では、
  固定したヌル切片（v = const）上で S = 0 になる一点が中間値の定理から
  構成されたが、その仮定の一つは S の切片上の連続性
    ContinuousOn (fun u => defectSource F g g' u v) (Icc 0 u₀)
  であった。ここではそれを、C² 級の場（`C2On`）から導く。`defectSource`
  は Ω, r, W とその 1 階微分 Du r, Dv r および g(r), g′(r) と rhsR の
  代数式なので、切片上の各成分の連続性（`C2Data.cont`・`cont_u`・
  `cont_v` を `sliceOn2` で切片に制限したもの）と r ≠ 0、g, g′ の
  r での連続性から、連続性の代数で組み立てる
  （`defectSource_continuousOn`）。C² 級の場への適用版
  （`defectSource_continuousOn_of_C2`）と RN 版
  （`defectSource_continuousOn_rn_of_C2`・極端版
  `defectSource_continuousOn_rn_extremal_of_C2`）も証明する。RN 版では
  g = rnLogDeriv、g′ = rnLogDeriv′ の連続性は `HasDerivAt` から得る。
  さらに前段の左端の負値（`defectSource_zero_slice_rn_neg`）と組み合わせて、
  一点の構成の仮定のうち連続性と左端の負値を C² データ＋特性データからの
  定理に置き換えた版（`defectSource_eq_zero_of_horizon_blowup_of_C2`）
  を証明する。残る仮定は地平線への接近 r → r₊、r_u·r_v の正の下界、
  Ω 項の下界と、ρ そのものの構成である。
-/
import CFT.Spherical.WedgeHorizonDefectTransport
import CFT.Spherical.WedgeHorizonDefectSourceDeriv
import CFT.Spherical.WedgeHorizonDefectZeroPoint
import CFT.Spherical.WedgeHorizonDefectZeroPointData

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeDefectTransport CFT.WedgeDefectSourceDeriv
open CFT.WedgeDefectZeroPoint CFT.WedgeDefectZeroPointData CFT.RNLogDeriv

namespace CFT.WedgeDefectContinuity

/-- r の発展方程式の右辺 `rhsR` は、r ≠ 0 のもとで引数の連続関数として
    連続である（有理式の連続性の代数）。 -/
theorem continuousOn_rhsR {s : Set ℝ} {Om W ru rv r : ℝ → ℝ}
    (hOm : ContinuousOn Om s) (hW : ContinuousOn W s) (hru : ContinuousOn ru s)
    (hrv : ContinuousOn rv s) (hr : ContinuousOn r s)
    (hr0 : ∀ x ∈ s, r x ≠ 0) :
    ContinuousOn (fun x => rhsR (Om x) (W x) (ru x) (rv x) (r x)) s := by
  have hr2 : ∀ x ∈ s, (r x) ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (hr0 x hx)
  have hW2 : ContinuousOn (fun x => (W x) ^ 2) s := hW.pow 2
  have h1m : ContinuousOn (fun x => 1 - (W x) ^ 2) s := continuousOn_const.sub hW2
  have hsq : ContinuousOn (fun x => (1 - (W x) ^ 2) ^ 2) s := h1m.pow 2
  have hdiv : ContinuousOn (fun x => (1 - (W x) ^ 2) ^ 2 / (r x) ^ 2) s :=
    hsq.div (hr.pow 2) hr2
  have hsub : ContinuousOn (fun x => (1 - (W x) ^ 2) ^ 2 / (r x) ^ 2 - 1) s :=
    hdiv.sub continuousOn_const
  have hfirst : ContinuousOn
      (fun x => (1 / 2) * Om x * ((1 - (W x) ^ 2) ^ 2 / (r x) ^ 2 - 1) / r x) s :=
    ((continuousOn_const.mul hOm).mul hsub).div hr hr0
  have hsecond : ContinuousOn (fun x => ru x * rv x / r x) s :=
    (hru.mul hrv).div hr hr0
  have h := hfirst.sub hsecond
  unfold rhsR
  exact h

/-- ソース項 S の切片上の連続性：場とその 1 階微分の切片上の連続性と、
    r ≠ 0、g, g′ の r での連続性から従う。 -/
theorem defectSource_continuousOn {F : WedgeFields} {g g' : ℝ → ℝ} {u₀ v : ℝ}
    (hOm : ContinuousOn (fun u => F.Om u v) (Icc 0 u₀))
    (hr : ContinuousOn (fun u => F.r u v) (Icc 0 u₀))
    (hW : ContinuousOn (fun u => F.W u v) (Icc 0 u₀))
    (hru : ContinuousOn (fun u => Du F.r u v) (Icc 0 u₀))
    (hrv : ContinuousOn (fun u => Dv F.r u v) (Icc 0 u₀))
    (hr0 : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ 0)
    (hg : ∀ u ∈ Icc (0:ℝ) u₀, ContinuousAt g (F.r u v))
    (hg' : ∀ u ∈ Icc (0:ℝ) u₀, ContinuousAt g' (F.r u v)) :
    ContinuousOn (fun u => defectSource F g g' u v) (Icc 0 u₀) := by
  have hr2 : ∀ u ∈ Icc (0:ℝ) u₀, (F.r u v) ^ 2 ≠ 0 :=
    fun u hu => pow_ne_zero 2 (hr0 u hu)
  have hr4 : ∀ u ∈ Icc (0:ℝ) u₀, (F.r u v) ^ 4 ≠ 0 :=
    fun u hu => pow_ne_zero 4 (hr0 u hu)
  have hgc : ContinuousOn (fun u => g (F.r u v)) (Icc 0 u₀) := by
    intro u hu
    exact Filter.Tendsto.comp (hg u hu) (hr.continuousWithinAt hu)
  have hgc' : ContinuousOn (fun u => g' (F.r u v)) (Icc 0 u₀) := by
    intro u hu
    exact Filter.Tendsto.comp (hg' u hu) (hr.continuousWithinAt hu)
  have hRHS : ContinuousOn
      (fun u => rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v))
      (Icc 0 u₀) :=
    continuousOn_rhsR hOm hW hru hrv hr hr0
  have hA : ContinuousOn (fun u => F.Om u v / (F.r u v) ^ 2) (Icc 0 u₀) :=
    hOm.div (hr.pow 2) hr2
  have hB : ContinuousOn
      (fun u => 2 * Du F.r u v * Dv F.r u v / (F.r u v) ^ 2) (Icc 0 u₀) :=
    ((continuousOn_const.mul hru).mul hrv).div (hr.pow 2) hr2
  have hW2 : ContinuousOn (fun u => (F.W u v) ^ 2) (Icc 0 u₀) := hW.pow 2
  have h1m : ContinuousOn (fun u => 1 - (F.W u v) ^ 2) (Icc 0 u₀) :=
    continuousOn_const.sub hW2
  have hsq : ContinuousOn (fun u => (1 - (F.W u v) ^ 2) ^ 2) (Icc 0 u₀) := h1m.pow 2
  have hC : ContinuousOn
      (fun u => 2 * F.Om u v * (1 - (F.W u v) ^ 2) ^ 2 / (F.r u v) ^ 4) (Icc 0 u₀) :=
    ((continuousOn_const.mul hOm).mul hsq).div (hr.pow 4) hr4
  have hD : ContinuousOn
      (fun u => g' (F.r u v) * Dv F.r u v * Du F.r u v) (Icc 0 u₀) :=
    (hgc'.mul hrv).mul hru
  have hE : ContinuousOn
      (fun u => g (F.r u v)
        * rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v))
      (Icc 0 u₀) :=
    hgc.mul hRHS
  have h := ((hA.add hB).sub hC).sub (hD.add hE)
  unfold defectSource
  exact h

/-- C² 級の場への適用版：`C2Data` の連続性（値・∂_u・∂_v）を `sliceOn2`
    で切片に制限して `defectSource_continuousOn` に入れる。 -/
theorem defectSource_continuousOn_of_C2 {F : WedgeFields} {g g' : ℝ → ℝ} {a b u₀ v : ℝ}
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (hu₀ : u₀ ≤ a) (hv : v ∈ Icc (0:ℝ) b)
    (hr0 : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ 0)
    (hg : ∀ u ∈ Icc (0:ℝ) u₀, ContinuousAt g (F.r u v))
    (hg' : ∀ u ∈ Icc (0:ℝ) u₀, ContinuousAt g' (F.r u v)) :
    ContinuousOn (fun u => defectSource F g g' u v) (Icc 0 u₀) := by
  have hsub : Icc (0:ℝ) u₀ ⊆ Icc (0:ℝ) a := Icc_subset_Icc le_rfl hu₀
  exact defectSource_continuousOn
    ((CFT.CharUniqueness.sliceOn2 hC2Om.cont hv).mono hsub)
    ((CFT.CharUniqueness.sliceOn2 hC2r.cont hv).mono hsub)
    ((CFT.CharUniqueness.sliceOn2 hC2W.cont hv).mono hsub)
    ((CFT.CharUniqueness.sliceOn2 hC2r.cont_u hv).mono hsub)
    ((CFT.CharUniqueness.sliceOn2 hC2r.cont_v hv).mono hsub)
    hr0 hg hg'

/-- RN 版：g = rnLogDeriv、g′ = rnLogDeriv′ の連続性は `HasDerivAt`
    から得る（r ≠ 0, r ≠ r₊, r ≠ r₋ のもと）。 -/
theorem defectSource_continuousOn_rn_of_C2 {F : WedgeFields} {rp rm a b u₀ v : ℝ}
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (hu₀ : u₀ ≤ a) (hv : v ∈ Icc (0:ℝ) b)
    (hr0 : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ 0)
    (hrp : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ rp)
    (hrm : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ rm) :
    ContinuousOn (fun u => defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v)
      (Icc 0 u₀) :=
  defectSource_continuousOn_of_C2 hC2r hC2Om hC2W hu₀ hv hr0
    (fun u hu => (rnLogDeriv_hasDerivAt (hr0 u hu) (hrp u hu) (hrm u hu)).continuousAt)
    (fun u hu => (rnLogDeriv'_hasDerivAt (hr0 u hu) (hrp u hu) (hrm u hu)).continuousAt)

/-- RN 極端版（r₊ = r₋）：一点の構成で使う形。 -/
theorem defectSource_continuousOn_rn_extremal_of_C2 {F : WedgeFields} {rp a b u₀ v : ℝ}
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (hu₀ : u₀ ≤ a) (hv : v ∈ Icc (0:ℝ) b)
    (hr0 : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ 0)
    (hrp : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ rp) :
    ContinuousOn (fun u => defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u v)
      (Icc 0 u₀) :=
  defectSource_continuousOn_rn_of_C2 hC2r hC2Om hC2W hu₀ hv hr0 hrp hrp

/-- S = 0 の一点の構成（C² データ＋特性データ版）：連続性の仮定と
    左端の負値の仮定を、C² 級の場と特性データからの定理に置き換えたもの。
    残る仮定は地平線への接近 r → r₊、r_u·r_v の正の下界、Ω 項の下界である。 -/
theorem defectSource_eq_zero_of_horizon_blowup_of_C2 {F : WedgeFields} {rp a b u₀ v : ℝ}
    (hrp : 0 < rp) (hu₀ : 0 < u₀)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (hu₀a : u₀ ≤ a) (hv : v ∈ Icc (0:ℝ) b)
    (hdata : HasWedgeData F)
    (hr0 : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ 0)
    (hr0' : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ 0)
    (hrne : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ rp)
    (hrne' : ∀ u ∈ Icc (0:ℝ) u₀, F.r u v ≠ rp)
    (hrlim : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝[>] rp))
    (hOm : ∃ M, ∀ᶠ u in 𝓝[<] u₀,
      M ≤ F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
            * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
          + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)))
    (hDuDv : ∃ m, 0 < m ∧ ∀ᶠ u in 𝓝[<] u₀, m ≤ Du F.r u v * Dv F.r u v) :
    ∃ u₁ ∈ Ioo 0 u₀, defectSource F (rnLogDeriv rp rp) (rnLogDeriv' rp rp) u₁ v = 0 :=
  defectSource_eq_zero_of_horizon_blowup hrp hu₀ hr0 hrne hrlim hOm hDuDv
    (defectSource_continuousOn_rn_extremal_of_C2 hC2r hC2Om hC2W hu₀a hv hr0' hrne')
    (defectSource_zero_slice_rn_neg hdata v)

end CFT.WedgeDefectContinuity
