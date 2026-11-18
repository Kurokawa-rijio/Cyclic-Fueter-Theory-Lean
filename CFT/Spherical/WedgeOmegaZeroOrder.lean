/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) のくさび EYM 系の形での分類への一段：

  結合 A = Ω/(2r²) について、Ω のゼロの位数が A のゼロの位数にそのまま
  移ること。すなわち r ≠ 0 のもとでは、u 方向・v 方向のそれぞれについて

  * A = 0 ⟺ Ω = 0（ゼロ集合の一致）、
  * A の単純ゼロ ⟺ Ω の単純ゼロ（値が 0 で 1 階微分が ≠ 0）、
  * A の値と 1 階微分がともに 0 ⟺ Ω の値と 1 階微分がともに 0
    （二重以上のゼロの一致）。

  鍵は、Ω = 0 の点での A の微分公式
    Du A = Du Ω / (2r²)（Ω = 0 の項が落ちる）
  で、因子 1/(2r²) が r ≠ 0 のもとで滑らかかつ非ゼロだからである。
  これにより、RN 側で既に証明済みの分類（`RNExtremalDoubleZero`：
  f の一次ゼロ ⟺ T > 0、f の二重ゼロ ⟺ 極端・T = 0）の「ゼロの位数による
  区別」が、くさび系の結合 A についても Ω と同じになる。残りは、
  実際のくさび解の Ω のゼロと地平線・喉との対応づけ（4-17 の局所解と
  9-3 の喉の発散への接続）。
-/
import Mathlib
import CFT.Spherical.WedgeEYMSystem
import CFT.Spherical.WedgeEnergyBalance

open CFT.Wedge
open CFT.WedgeBalance

namespace CFT.WedgeOmegaZero

/-- A = 0 ⟺ Ω = 0（r ≠ 0 のもと）。ゼロ集合の一致。 -/
theorem wedgeA_eq_zero_iff {Om r : ℝ → ℝ → ℝ} {u v : ℝ} (hr : r u v ≠ 0) :
    wedgeAFun Om r u v = 0 ↔ Om u v = 0 := by
  show Om u v / (2 * (r u v) ^ 2) = 0 ↔ Om u v = 0
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero (pow_ne_zero 2 hr))
  · intro h
    exact Or.inl h

/-- A の u 微分の明示公式：Du A = Du Ω/(2r²) − Ω·Du r/r³。 -/
theorem wedgeA_deriv_u {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun u' => Om u' v) u)
    (hr : DifferentiableAt ℝ (fun u' => r u' v) u)
    (hr0 : r u v ≠ 0) :
    deriv (fun u' => wedgeAFun Om r u' v) u
      = Du Om u v / (2 * (r u v) ^ 2) - Om u v * Du r u v / (r u v) ^ 3 := by
  have hr2 : (2 : ℝ) * (r u v) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)
  have h1 : HasDerivAt (fun u' => Om u' v) (Du Om u v) u := hOm.hasDerivAt
  have h2 : HasDerivAt (fun u' => 2 * (r u' v) ^ 2)
      (2 * ((2 : ℝ) * (r u v) ^ (2 - 1) * Du r u v)) u :=
    (hr.hasDerivAt.pow 2).const_mul 2
  have h3 := h1.div h2 hr2
  show deriv (fun u' => Om u' v / (2 * (r u' v) ^ 2)) u
      = Du Om u v / (2 * (r u v) ^ 2) - Om u v * Du r u v / (r u v) ^ 3
  rw [h3.deriv]
  have hr3 : (r u v) ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  field_simp
  ring

/-- Ω = 0 の点での A の u 微分：Du A = Du Ω/(2r²)。 -/
theorem wedgeA_deriv_u_at_zero {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun u' => Om u' v) u)
    (hr : DifferentiableAt ℝ (fun u' => r u' v) u)
    (hr0 : r u v ≠ 0) (h0 : Om u v = 0) :
    deriv (fun u' => wedgeAFun Om r u' v) u
      = Du Om u v / (2 * (r u v) ^ 2) := by
  rw [wedgeA_deriv_u hOm hr hr0, h0]
  simp

/-- A の単純ゼロ ⟺ Ω の単純ゼロ（u 方向）。 -/
theorem wedgeA_simple_zero_u {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun u' => Om u' v) u)
    (hr : DifferentiableAt ℝ (fun u' => r u' v) u)
    (hr0 : r u v ≠ 0) :
    (wedgeAFun Om r u v = 0 ∧ Du (wedgeAFun Om r) u v ≠ 0)
      ↔ (Om u v = 0 ∧ Du Om u v ≠ 0) := by
  have hr2 : (2 : ℝ) * (r u v) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)
  have hA : Du (wedgeAFun Om r) u v = deriv (fun u' => wedgeAFun Om r u' v) u := rfl
  constructor
  · rintro ⟨hAz, hAd⟩
    have h0 : Om u v = 0 := (wedgeA_eq_zero_iff hr0).mp hAz
    refine ⟨h0, ?_⟩
    intro hd
    apply hAd
    rw [hA, wedgeA_deriv_u_at_zero hOm hr hr0 h0, hd]
    simp
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeA_eq_zero_iff hr0).mpr h0, ?_⟩
    rw [hA, wedgeA_deriv_u_at_zero hOm hr hr0 h0]
    exact div_ne_zero hd hr2

/-- A の値と u 微分がともに 0 ⟺ Ω の値と u 微分がともに 0（二重以上のゼロの一致）。 -/
theorem wedgeA_zero_deriv_zero_u {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun u' => Om u' v) u)
    (hr : DifferentiableAt ℝ (fun u' => r u' v) u)
    (hr0 : r u v ≠ 0) :
    (wedgeAFun Om r u v = 0 ∧ Du (wedgeAFun Om r) u v = 0)
      ↔ (Om u v = 0 ∧ Du Om u v = 0) := by
  have hr2 : (2 : ℝ) * (r u v) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)
  have hA : Du (wedgeAFun Om r) u v = deriv (fun u' => wedgeAFun Om r u' v) u := rfl
  constructor
  · rintro ⟨hAz, hAd⟩
    have h0 : Om u v = 0 := (wedgeA_eq_zero_iff hr0).mp hAz
    refine ⟨h0, ?_⟩
    have h : Du Om u v / (2 * (r u v) ^ 2) = 0 := by
      rw [← wedgeA_deriv_u_at_zero hOm hr hr0 h0, ← hA]
      exact hAd
    rcases (div_eq_zero_iff).mp h with hd | hd
    · exact hd
    · exact absurd hd hr2
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeA_eq_zero_iff hr0).mpr h0, ?_⟩
    rw [hA, wedgeA_deriv_u_at_zero hOm hr hr0 h0, hd]
    simp

/-- A の v 微分の明示公式：Dv A = Dv Ω/(2r²) − Ω·Dv r/r³。 -/
theorem wedgeA_deriv_v {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun v' => Om u v') v)
    (hr : DifferentiableAt ℝ (fun v' => r u v') v)
    (hr0 : r u v ≠ 0) :
    deriv (fun v' => wedgeAFun Om r u v') v
      = Dv Om u v / (2 * (r u v) ^ 2) - Om u v * Dv r u v / (r u v) ^ 3 := by
  have hr2 : (2 : ℝ) * (r u v) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)
  have h1 : HasDerivAt (fun v' => Om u v') (Dv Om u v) v := hOm.hasDerivAt
  have h2 : HasDerivAt (fun v' => 2 * (r u v') ^ 2)
      (2 * ((2 : ℝ) * (r u v) ^ (2 - 1) * Dv r u v)) v :=
    (hr.hasDerivAt.pow 2).const_mul 2
  have h3 := h1.div h2 hr2
  show deriv (fun v' => Om u v' / (2 * (r u v') ^ 2)) v
      = Dv Om u v / (2 * (r u v) ^ 2) - Om u v * Dv r u v / (r u v) ^ 3
  rw [h3.deriv]
  have hr3 : (r u v) ^ 3 ≠ 0 := pow_ne_zero 3 hr0
  field_simp
  ring

/-- Ω = 0 の点での A の v 微分：Dv A = Dv Ω/(2r²)。 -/
theorem wedgeA_deriv_v_at_zero {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun v' => Om u v') v)
    (hr : DifferentiableAt ℝ (fun v' => r u v') v)
    (hr0 : r u v ≠ 0) (h0 : Om u v = 0) :
    deriv (fun v' => wedgeAFun Om r u v') v
      = Dv Om u v / (2 * (r u v) ^ 2) := by
  rw [wedgeA_deriv_v hOm hr hr0, h0]
  simp

/-- A の単純ゼロ ⟺ Ω の単純ゼロ（v 方向）。 -/
theorem wedgeA_simple_zero_v {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun v' => Om u v') v)
    (hr : DifferentiableAt ℝ (fun v' => r u v') v)
    (hr0 : r u v ≠ 0) :
    (wedgeAFun Om r u v = 0 ∧ Dv (wedgeAFun Om r) u v ≠ 0)
      ↔ (Om u v = 0 ∧ Dv Om u v ≠ 0) := by
  have hr2 : (2 : ℝ) * (r u v) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)
  have hA : Dv (wedgeAFun Om r) u v = deriv (fun v' => wedgeAFun Om r u v') v := rfl
  constructor
  · rintro ⟨hAz, hAd⟩
    have h0 : Om u v = 0 := (wedgeA_eq_zero_iff hr0).mp hAz
    refine ⟨h0, ?_⟩
    intro hd
    apply hAd
    rw [hA, wedgeA_deriv_v_at_zero hOm hr hr0 h0, hd]
    simp
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeA_eq_zero_iff hr0).mpr h0, ?_⟩
    rw [hA, wedgeA_deriv_v_at_zero hOm hr hr0 h0]
    exact div_ne_zero hd hr2

/-- A の値と v 微分がともに 0 ⟺ Ω の値と v 微分がともに 0（二重以上のゼロの一致）。 -/
theorem wedgeA_zero_deriv_zero_v {Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hOm : DifferentiableAt ℝ (fun v' => Om u v') v)
    (hr : DifferentiableAt ℝ (fun v' => r u v') v)
    (hr0 : r u v ≠ 0) :
    (wedgeAFun Om r u v = 0 ∧ Dv (wedgeAFun Om r) u v = 0)
      ↔ (Om u v = 0 ∧ Dv Om u v = 0) := by
  have hr2 : (2 : ℝ) * (r u v) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)
  have hA : Dv (wedgeAFun Om r) u v = deriv (fun v' => wedgeAFun Om r u v') v := rfl
  constructor
  · rintro ⟨hAz, hAd⟩
    have h0 : Om u v = 0 := (wedgeA_eq_zero_iff hr0).mp hAz
    refine ⟨h0, ?_⟩
    have h : Dv Om u v / (2 * (r u v) ^ 2) = 0 := by
      rw [← wedgeA_deriv_v_at_zero hOm hr hr0 h0, ← hA]
      exact hAd
    rcases (div_eq_zero_iff).mp h with hd | hd
    · exact hd
    · exact absurd hd hr2
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeA_eq_zero_iff hr0).mpr h0, ?_⟩
    rw [hA, wedgeA_deriv_v_at_zero hOm hr hr0 h0, hd]
    simp

end CFT.WedgeOmegaZero
