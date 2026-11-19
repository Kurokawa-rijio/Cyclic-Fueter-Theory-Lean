/-
  9-3 極限（エクストリーマル）極限の残り：非極端の場合の固有距離の有限性

  非極端 RN（0 < r₋ < r₊）では計量関数 f(r) = (r − r₊)(r − r₋)/r² が
  r = r₊ に一次ゼロを持ち、t 一定の動径固有距離の被積分関数は
    1/√f(r) = r/√((r − r₊)(r − r₋))。
  r ∈ [r₊, r₊ + R] では r − r₋ ≥ r₊ − r₋ > 0 なので
    1/√f(r) ≤ ((r₊ + R)/√(r₊ − r₋)) · (r − r₊)^(-1/2)
  とモデル関数で上から抑えられ、モデル積分
    ∫_{r₊+ε}^{r₊+R} (x − r₊)^(-1/2) dx = 2(√R − √ε)
  は ε → 0⁺ で 2√R に留まる。よって切り捨てた喉の長さ L(ε) は
  ε → 0⁺ で有界のままであり、極端の場合（L(ε) → +∞、無限の喉）と
  対照的に非極端地平線までの固有距離は有限である。
  すなわち「一次ゼロ ↔ 有限距離／二重ゼロ ↔ 無限の喉」の分類の
  有限側が閉じたことになる。
  残り：くさび EYM 系の形での喉への接続（12-8 (b) の本体）。
-/
import CFT.Quantum.RNExtremalDoubleZero
import Mathlib.Analysis.SpecialFunctions.Integrals

open Real Filter Topology intervalIntegral

namespace CFT.NonextremalThroat

/-- モデル積分：∫_{r₊+ε}^{r₊+R} (x − r₊)^(-1/2) dx = 2(√R − √ε)。
    原始関数は 2√(x − r₊)。 -/
theorem model_sqrt_integral (rp ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    ∫ x in (rp + ε)..(rp + R), (Real.sqrt (x - rp))⁻¹
      = 2 * (Real.sqrt R - Real.sqrt ε) := by
  have hab : rp + ε ≤ rp + R := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (rp + ε) (rp + R),
      HasDerivAt (fun x => 2 * Real.sqrt (x - rp)) ((Real.sqrt (x - rp))⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxrp : 0 < x - rp := by linarith [hx.1]
    have hne : x - rp ≠ 0 := ne_of_gt hxrp
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (x - rp))) (x - rp) :=
      Real.hasDerivAt_sqrt hne
    have hcomp : HasDerivAt (fun x => Real.sqrt (x - rp))
        ((1 / (2 * Real.sqrt (x - rp))) * 1) x := by
      have h := hsqrt.comp x ((hasDerivAt_id x).sub_const rp)
      simpa using h
    have h2 : HasDerivAt (fun x => 2 * Real.sqrt (x - rp))
        (2 * ((1 / (2 * Real.sqrt (x - rp))) * 1)) x := hcomp.const_mul 2
    have h3 : 2 * ((1 / (2 * Real.sqrt (x - rp))) * 1) = (Real.sqrt (x - rp))⁻¹ := by
      have hs : Real.sqrt (x - rp) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hxrp)
      field_simp
    rw [h3] at h2
    exact h2
  have hint : IntervalIntegrable (fun x => (Real.sqrt (x - rp))⁻¹)
      MeasureTheory.volume (rp + ε) (rp + R) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · have h : Continuous (fun x => Real.sqrt (x - rp)) :=
        Real.continuous_sqrt.comp (continuous_id.sub continuous_const)
      exact h.continuousOn
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1] : 0 < x - rp))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have e1 : rp + R - rp = R := by ring
  have e2 : rp + ε - rp = ε := by ring
  rw [e1, e2]
  ring

/-- 非極端の場合の √f：r > r₊ では √(f(r)) = √((r − r₊)(r − r₋))/r。 -/
theorem nonextremal_sqrt_rnF (rm rp r : ℝ) (hm : rm < rp) (hr : rp < r) (hp : 0 < rp) :
    Real.sqrt (CFT.RNExtremalZero.rnF rp rm r)
      = Real.sqrt ((r - rp) * (r - rm)) / r := by
  simp only [CFT.RNExtremalZero.rnF]
  have hnum : 0 ≤ (r - rp) * (r - rm) := mul_nonneg (by linarith) (by linarith)
  rw [Real.sqrt_div hnum, Real.sqrt_sq (by linarith : (0:ℝ) ≤ r)]

/-- 固有距離の被積分関数：1/√f(r) = r/√((r − r₊)(r − r₋))（r > r₊）。 -/
theorem nonextremal_properLength_integrand (rm rp r : ℝ) (hm : rm < rp) (hr : rp < r)
    (hp : 0 < rp) :
    (Real.sqrt (CFT.RNExtremalZero.rnF rp rm r))⁻¹
      = r / Real.sqrt ((r - rp) * (r - rm)) := by
  rw [nonextremal_sqrt_rnF rm rp r hm hr hp, inv_div]

/-- 被積分関数のモデルによる上界：r ∈ [r₊+ε, r₊+R] では
    r/√((r − r₊)(r − r₋)) ≤ ((r₊+R)/√(r₊−r₋)) · (√(r − r₊))⁻¹。 -/
theorem nonextremal_integrand_le (rm rp ε R r : ℝ) (hε : 0 < ε) (hm : 0 < rm)
    (hmp : rm < rp) (hr : rp + ε ≤ r) (hrR : r ≤ rp + R) :
    r / Real.sqrt ((r - rp) * (r - rm))
      ≤ ((rp + R) / Real.sqrt (rp - rm)) * (Real.sqrt (r - rp))⁻¹ := by
  have hrp : 0 < r - rp := by linarith
  have hrm : 0 < r - rm := by linarith
  have hsub : 0 < rp - rm := by linarith
  have hden : Real.sqrt ((r - rp) * (r - rm))
      = Real.sqrt (r - rp) * Real.sqrt (r - rm) :=
    Real.sqrt_mul (le_of_lt hrp) _
  have hden_le : Real.sqrt (r - rp) * Real.sqrt (rp - rm)
      ≤ Real.sqrt (r - rp) * Real.sqrt (r - rm) := by
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt (by linarith : rp - rm ≤ r - rm)
  have hmain : r / (Real.sqrt (r - rp) * Real.sqrt (r - rm))
      ≤ (rp + R) / (Real.sqrt (r - rp) * Real.sqrt (rp - rm)) :=
    div_le_div₀ (by linarith : (0:ℝ) ≤ rp + R) (by linarith : r ≤ rp + R)
      (mul_pos (Real.sqrt_pos.mpr hrp) (Real.sqrt_pos.mpr hsub)) hden_le
  have hs1 : Real.sqrt (r - rp) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrp)
  have hs2 : Real.sqrt (rp - rm) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsub)
  have hsplit : (rp + R) / (Real.sqrt (r - rp) * Real.sqrt (rp - rm))
      = ((rp + R) / Real.sqrt (rp - rm)) * (Real.sqrt (r - rp))⁻¹ := by
    rw [div_eq_iff (mul_ne_zero hs1 hs2), mul_assoc,
      ← mul_assoc (Real.sqrt (r - rp))⁻¹ (Real.sqrt (r - rp)) (Real.sqrt (rp - rm)),
      inv_mul_cancel₀ hs1, one_mul, div_mul_cancel₀ _ hs2]
  rw [hden]
  rw [hsplit] at hmain
  exact hmain

/-- 切り捨てた喉の長さの上界：
    ∫_{r₊+ε}^{r₊+R} dr/√f(r) ≤ ((r₊+R)/√(r₊−r₋)) · 2(√R − √ε)。 -/
theorem nonextremal_throatLength_le (rm rp ε R : ℝ) (hε : 0 < ε) (hεR : ε < R)
    (hm : 0 < rm) (hmp : rm < rp) (hp : 0 < rp) :
    ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
      ≤ ((rp + R) / Real.sqrt (rp - rm)) * (2 * (Real.sqrt R - Real.sqrt ε)) := by
  have hab : rp + ε ≤ rp + R := by linarith
  have hrnF : ContinuousOn (fun x => CFT.RNExtremalZero.rnF rp rm x)
      (Set.uIcc (rp + ε) (rp + R)) := by
    simp only [CFT.RNExtremalZero.rnF]
    apply ContinuousOn.div
    · exact ((continuous_id.sub continuous_const).mul
        (continuous_id.sub continuous_const)).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hx0 : x ≠ 0 := ne_of_gt (by linarith [hx.1] : 0 < x)
      exact pow_ne_zero 2 hx0
  have hcontRN : ContinuousOn
      (fun x => (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹)
      (Set.uIcc (rp + ε) (rp + R)) := by
    apply ContinuousOn.inv₀
    · have h := Real.continuous_sqrt.comp_continuousOn hrnF
      simpa only [Function.comp_apply] using h
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have h1 : 0 < x - rp := by linarith [hx.1]
      have h2 : 0 < x - rm := by linarith [hx.1]
      have hpos : 0 < CFT.RNExtremalZero.rnF rp rm x := by
        simp only [CFT.RNExtremalZero.rnF]
        apply div_pos (mul_pos h1 h2)
        have hx0 : 0 < x := by linarith [hx.1]
        positivity
      exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hf : IntervalIntegrable
      (fun x => (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹)
      MeasureTheory.volume (rp + ε) (rp + R) := hcontRN.intervalIntegrable
  have hcontM : ContinuousOn (fun x => (Real.sqrt (x - rp))⁻¹)
      (Set.uIcc (rp + ε) (rp + R)) := by
    apply ContinuousOn.inv₀
    · have h : Continuous (fun x => Real.sqrt (x - rp)) :=
        Real.continuous_sqrt.comp (continuous_id.sub continuous_const)
      exact h.continuousOn
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1] : 0 < x - rp))
  have hcontR2 : ContinuousOn (fun x => x / Real.sqrt ((x - rp) * (x - rm)))
      (Set.uIcc (rp + ε) (rp + R)) := by
    apply ContinuousOn.div continuousOn_id
    · have h : Continuous (fun x => Real.sqrt ((x - rp) * (x - rm))) :=
        Real.continuous_sqrt.comp
          ((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const))
      exact h.continuousOn
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have h1 : 0 < x - rp := by linarith [hx.1]
      have h2 : 0 < x - rm := by linarith [hx.1]
      exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos h1 h2))
  have hf2 : IntervalIntegrable (fun x => x / Real.sqrt ((x - rp) * (x - rm)))
      MeasureTheory.volume (rp + ε) (rp + R) := hcontR2.intervalIntegrable
  have hg : IntervalIntegrable
      (fun x => ((rp + R) / Real.sqrt (rp - rm)) * (Real.sqrt (x - rp))⁻¹)
      MeasureTheory.volume (rp + ε) (rp + R) :=
    hcontM.intervalIntegrable.const_mul _
  calc ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
      = ∫ x in (rp + ε)..(rp + R), x / Real.sqrt ((x - rp) * (x - rm)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        exact nonextremal_properLength_integrand rm rp x hmp (by linarith [hx.1]) hp
    _ ≤ ∫ x in (rp + ε)..(rp + R),
          ((rp + R) / Real.sqrt (rp - rm)) * (Real.sqrt (x - rp))⁻¹ := by
        apply intervalIntegral.integral_mono_on hab hf2 hg
        intro x hx
        exact nonextremal_integrand_le rm rp ε R x hε hm hmp hx.1 hx.2
    _ = ((rp + R) / Real.sqrt (rp - rm)) * (2 * (Real.sqrt R - Real.sqrt ε)) := by
        rw [intervalIntegral.integral_const_mul, model_sqrt_integral rp ε R hε hεR]

/-- 切り捨てた喉の長さは非負。 -/
theorem nonextremal_throatLength_nonneg (rm rp ε R : ℝ) (hε : 0 < ε) (hεR : ε < R)
    (hmp : rm < rp) (hp : 0 < rp) :
    0 ≤ ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹ := by
  apply intervalIntegral.integral_nonneg (by linarith : rp + ε ≤ rp + R)
  intro u _
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- まとめ：非極端 RN の喉の固有距離は有限である。切り捨てた長さ L(ε) は
    ε ∈ (0, R) の範囲で 0 ≤ L(ε) ≤ ((r₊+R)/√(r₊−r₋)) · 2√R と一様に
    有界であり、ε → 0⁺ で発散しない（極端の場合と対照的）。 -/
theorem nonextremal_throat_finite (rm rp R : ℝ) (hm : 0 < rm) (hmp : rm < rp)
    (hp : 0 < rp) (hR : 0 < R) :
    ∀ ε ∈ Set.Ioo 0 R,
      0 ≤ ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
        ∧ ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
          ≤ ((rp + R) / Real.sqrt (rp - rm)) * (2 * Real.sqrt R) := by
  intro ε hε
  obtain ⟨hε0, hεR⟩ := hε
  refine ⟨nonextremal_throatLength_nonneg rm rp ε R hε0 hεR hmp hp, ?_⟩
  have hle := nonextremal_throatLength_le rm rp ε R hε0 hεR hm hmp hp
  have hC : 0 ≤ (rp + R) / Real.sqrt (rp - rm) :=
    div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have h2 : (2:ℝ) * (Real.sqrt R - Real.sqrt ε) ≤ 2 * Real.sqrt R := by
    have h := Real.sqrt_nonneg ε
    linarith
  calc ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
      ≤ ((rp + R) / Real.sqrt (rp - rm)) * (2 * (Real.sqrt R - Real.sqrt ε)) := hle
    _ ≤ ((rp + R) / Real.sqrt (rp - rm)) * (2 * Real.sqrt R) :=
        mul_le_mul_of_nonneg_left h2 hC

/-- 対比：非極端の場合、切り捨てた喉の長さは ε → 0⁺ で +∞ に発散しない
    （極端の場合は `CFT.ExtremalThroat.extremal_throat_infinite` により +∞）。 -/
theorem nonextremal_throat_not_tendsto_atTop (rm rp R : ℝ) (hm : 0 < rm) (hmp : rm < rp)
    (hp : 0 < rp) (hR : 0 < R) :
    ¬ Tendsto (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R),
      (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹) (𝓝[>] 0) atTop := by
  intro h
  have hev := h.eventually (eventually_gt_atTop
    (((rp + R) / Real.sqrt (rp - rm)) * (2 * Real.sqrt R)))
  have hIoo : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ∈ Set.Ioo 0 R := Ioo_mem_nhdsGT hR
  obtain ⟨ε, hεbig, hεIoo⟩ := (hev.and hIoo).exists
  have hle := (nonextremal_throat_finite rm rp R hm hmp hp hR ε hεIoo).2
  linarith

end CFT.NonextremalThroat
