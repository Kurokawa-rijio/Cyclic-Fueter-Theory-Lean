import CFT.Spherical.SchwarzschildAnalytic
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 12-7.6（荷電セクター：RN 解の明示）の残り：
  解析的な `deriv` 版への移行。`ReissnerNordstromSolution.lean` は
  導分代数の流儀で、真空方程式に対する残差形・拘束・ミスナー–シャープ質量を
  証明した。このモジュールでは同じ内容を実際の関数 r, Om : ℝ → ℝ → ℝ と
  `CFT.Wedge.Du` / `Dv`（スライスの `deriv`）で述べる：
  トータス関係 2Ω = 1 − 2M/r + Q²/r² と r_u = −Ω、r_v = +Ω を
  `ReissnerNordstromFieldAnalytic` として定義し、Ω の u・v 微分
  （Du Ω = −MΩ/r² + Q²Ω/r³、Dv Ω = +MΩ/r² − Q²Ω/r³、トータス関係の微分）、
  r 方程式・Ω 方程式の残差形（商の微分による HasDerivAt の組み立て）・
  拘束 C_u・C_v・質量 m = M − Q²/(2r) とその u・v 微分を証明し、
  まとめ `rn_electrovacuum_analytic` と Q = 0 での 9-1 への帰着
  `rn_to_schwarzschild_analytic` とする。
  これで 12-7.6 の「解の明示」は導分代数版・解析版ともに閉じた。

  残り：くさび EYM 系への Einstein–Maxwell ソース項の導入＝Abelian 射影、
  地平線 r± の扱い（Ω ≠ 0 を仮定）、W 場側への埋め込み。
  真空方程式を満たすとは主張しない（残差形が正しい到達点）。
-/

open CFT.Wedge

namespace CFT.ReissnerNordstromAnalytic

/-- 解析的な RN 場の条件（トータス関係の `deriv` 版）。M, Q は定数の実数。 -/
def ReissnerNordstromFieldAnalytic (r Om : ℝ → ℝ → ℝ) (M Q : ℝ) : Prop :=
  ∀ u v, 2 * Om u v = 1 - 2 * M / r u v + Q ^ 2 / (r u v) ^ 2
    ∧ Du r u v = -Om u v ∧ Dv r u v = Om u v

/-- 分母を払った形：2 Ω r² = r² − 2Mr + Q²。 -/
theorem rn_Om_mul_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q) (hr : r u v ≠ 0) :
    2 * Om u v * (r u v) ^ 2 = (r u v) ^ 2 - 2 * M * r u v + Q ^ 2 := by
  have hOm := (h u v).1
  have h1 : (2 * Om u v) * (r u v) ^ 2
      = (1 - 2 * M / r u v + Q ^ 2 / (r u v) ^ 2) * (r u v) ^ 2 :=
    congrArg (· * (r u v) ^ 2) hOm
  have h2 : (1 - 2 * M / r u v + Q ^ 2 / (r u v) ^ 2) * (r u v) ^ 2
      = (r u v) ^ 2 - 2 * M * r u v + Q ^ 2 := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- Ω の u 微分：Du Ω = −MΩ/r² + Q²Ω/r³（トータス関係の微分）。 -/
theorem rn_du_Om_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : r u v ≠ 0) :
    Du Om u v = -M * Om u v / (r u v) ^ 2 + Q ^ 2 * Om u v / (r u v) ^ 3 := by
  obtain ⟨hrel, hru, _⟩ := h u v
  have hfun : (fun u' => 2 * Om u' v)
      = (fun u' => 1 - 2 * M / r u' v + Q ^ 2 / (r u' v) ^ 2) := by
    funext u'
    exact (h u' v).1
  have hder : deriv (fun u' => 2 * Om u' v) u
      = deriv (fun u' => 1 - 2 * M / r u' v + Q ^ 2 / (r u' v) ^ 2) u :=
    congrArg (fun F => deriv F u) hfun
  have hL : deriv (fun u' => 2 * Om u' v) u = 2 * Du Om u v := by
    show deriv (fun u' => 2 * Om u' v) u = 2 * deriv (fun u' => Om u' v) u
    exact deriv_const_mul 2 (hOm u)
  have hR : HasDerivAt (fun u' => 1 - 2 * M / r u' v + Q ^ 2 / (r u' v) ^ 2)
      (0 - (2 * M) * (-(Du r u v) / (r u v) ^ 2)
        + Q ^ 2 * (-(((2 : ℕ) : ℝ) * (r u v) ^ (2 - 1) * Du r u v)
          / ((r u v) ^ 2) ^ 2)) u := by
    have h1 := (hr u).hasDerivAt
    have h2 := h1.inv hr0
    have h3 := h2.const_mul (2 * M)
    have h4 := h1.pow 2
    have h5 := h4.inv (pow_ne_zero 2 hr0)
    have h6 := h5.const_mul (Q ^ 2)
    exact ((hasDerivAt_const u (1 : ℝ)).sub h3).add h6
  rw [hL, hR.deriv, hru] at hder
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hder
  linear_combination hder / 2
    + (Om u v * Q ^ 2 * (r u v)⁻¹ ^ 3) * (mul_inv_cancel₀ hr0)

/-- Ω の v 微分：Dv Ω = +MΩ/r² − Q²Ω/r³。 -/
theorem rn_dv_Om_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hr : Differentiable ℝ (fun v' => r u v'))
    (hOm : Differentiable ℝ (fun v' => Om u v'))
    (hr0 : r u v ≠ 0) :
    Dv Om u v = M * Om u v / (r u v) ^ 2 - Q ^ 2 * Om u v / (r u v) ^ 3 := by
  obtain ⟨hrel, _, hrv⟩ := h u v
  have hfun : (fun v' => 2 * Om u v')
      = (fun v' => 1 - 2 * M / r u v' + Q ^ 2 / (r u v') ^ 2) := by
    funext v'
    exact (h u v').1
  have hder : deriv (fun v' => 2 * Om u v') v
      = deriv (fun v' => 1 - 2 * M / r u v' + Q ^ 2 / (r u v') ^ 2) v :=
    congrArg (fun F => deriv F v) hfun
  have hL : deriv (fun v' => 2 * Om u v') v = 2 * Dv Om u v := by
    show deriv (fun v' => 2 * Om u v') v = 2 * deriv (fun v' => Om u v') v
    exact deriv_const_mul 2 (hOm v)
  have hR : HasDerivAt (fun v' => 1 - 2 * M / r u v' + Q ^ 2 / (r u v') ^ 2)
      (0 - (2 * M) * (-(Dv r u v) / (r u v) ^ 2)
        + Q ^ 2 * (-(((2 : ℕ) : ℝ) * (r u v) ^ (2 - 1) * Dv r u v)
          / ((r u v) ^ 2) ^ 2)) v := by
    have h1 := (hr v).hasDerivAt
    have h2 := h1.inv hr0
    have h3 := h2.const_mul (2 * M)
    have h4 := h1.pow 2
    have h5 := h4.inv (pow_ne_zero 2 hr0)
    have h6 := h5.const_mul (Q ^ 2)
    exact ((hasDerivAt_const v (1 : ℝ)).sub h3).add h6
  rw [hL, hR.deriv, hrv] at hder
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hder
  linear_combination hder / 2
    - (Om u v * Q ^ 2 * (r u v)⁻¹ ^ 3) * (mul_inv_cancel₀ hr0)

/-- Duv r = Du Ω（Dv r = Ω を u 方向に微分）。 -/
theorem rn_Duv_r_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q) :
    Duv r u v = Du Om u v := by
  have hfun : (fun u' => Dv r u' v) = (fun u' => Om u' v) := by
    funext u'
    exact (h u' v).2.2
  show deriv (fun u' => Dv r u' v) u = deriv (fun u' => Om u' v) u
  rw [hfun]

/-- r 方程式の残差形の解析版：r_uv = −Ω/(2r) − r_u r_v/r + Q²Ω/(2r³)。 -/
theorem rn_r_eq_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : r u v ≠ 0) :
    Duv r u v = -Om u v / (2 * r u v) - Du r u v * Dv r u v / r u v
      + Q ^ 2 * Om u v / (2 * (r u v) ^ 3) := by
  obtain ⟨hrel, hru, hrv⟩ := h u v
  have hdu := rn_du_Om_analytic h hr hOm hr0
  have hOm' := rn_Om_mul_analytic h hr0
  rw [rn_Duv_r_analytic h, hdu, hru, hrv]
  field_simp
  linear_combination (-2 * Om u v * (r u v) ^ 7) * hOm'

/-- Ω 方程式の残差形の解析版：
    Ω_uv = Ω_u Ω_v/Ω − 2Ω r_uv/r − Q²Ω²/r⁴。 -/
theorem rn_Om_eq_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hru_diff : ∀ u', Differentiable ℝ (fun v' => r u' v'))
    (hOmv_diff : ∀ u', Differentiable ℝ (fun v' => Om u' v'))
    (hr_u : Differentiable ℝ (fun u' => r u' v))
    (hOm_u : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : ∀ u', r u' v ≠ 0)
    (hOm0 : Om u v ≠ 0) :
    Duv Om u v = Du Om u v * Dv Om u v / Om u v
      - 2 * Om u v * Duv r u v / r u v
      - Q ^ 2 * Om u v ^ 2 / (r u v) ^ 4 := by
  have hr0u := hr0 u
  have hdu := rn_du_Om_analytic h hr_u hOm_u hr0u
  have hdv := rn_dv_Om_analytic h (hru_diff u) (hOmv_diff u) hr0u
  have hruv : Duv r u v
      = -M * Om u v / (r u v) ^ 2 + Q ^ 2 * Om u v / (r u v) ^ 3 := by
    rw [rn_Duv_r_analytic h, hdu]
  have hfun : (fun u' => Dv Om u' v)
      = (fun u' => M * Om u' v / (r u' v) ^ 2 - Q ^ 2 * Om u' v / (r u' v) ^ 3) := by
    funext u'
    exact rn_dv_Om_analytic h (hru_diff u') (hOmv_diff u') (hr0 u')
  have hDuv : Duv Om u v
      = deriv (fun u' => M * Om u' v / (r u' v) ^ 2 - Q ^ 2 * Om u' v / (r u' v) ^ 3) u := by
    show deriv (fun u' => Dv Om u' v) u
      = deriv (fun u' => M * Om u' v / (r u' v) ^ 2 - Q ^ 2 * Om u' v / (r u' v) ^ 3) u
    rw [hfun]
  have hg : HasDerivAt (fun u' => M * Om u' v / (r u' v) ^ 2 - Q ^ 2 * Om u' v / (r u' v) ^ 3)
      ((M * deriv (fun u' => Om u' v) u * (r u v) ^ 2
        - M * Om u v * (2 * r u v * deriv (fun u' => r u' v) u)) / ((r u v) ^ 2) ^ 2
      - (Q ^ 2 * deriv (fun u' => Om u' v) u * (r u v) ^ 3
        - Q ^ 2 * Om u v * (3 * (r u v) ^ 2 * deriv (fun u' => r u' v) u)) / ((r u v) ^ 3) ^ 2) u := by
    have h1 := (hOm_u u).hasDerivAt
    have h2 := (hr_u u).hasDerivAt
    have h3 := h1.const_mul M
    have h4 := h2.pow 2
    have h5 := h3.div h4 (pow_ne_zero 2 hr0u)
    have h6 := h1.const_mul (Q ^ 2)
    have h7 := h2.pow 3
    have h8 := h6.div h7 (pow_ne_zero 3 hr0u)
    convert h5.sub h8 using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      show (3 : ℕ) - 1 = 2 from rfl, pow_one]
  rw [hDuv, hg.deriv]
  show ((M * Du Om u v) * (r u v) ^ 2
      - M * Om u v * (2 * r u v * Du r u v)) / ((r u v) ^ 2) ^ 2
    - (Q ^ 2 * Du Om u v * (r u v) ^ 3
      - Q ^ 2 * Om u v * (3 * (r u v) ^ 2 * Du r u v)) / ((r u v) ^ 3) ^ 2
    = Du Om u v * Dv Om u v / Om u v - 2 * Om u v * Duv r u v / r u v
      - Q ^ 2 * Om u v ^ 2 / (r u v) ^ 4
  rw [hdu, hdv, hruv, (h u v).2.1]
  field_simp
  ring

/-- 拘束 C_u の解析版：r_uu − (Ω_u/Ω) r_u = 0。 -/
theorem rn_constraint_u_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hOm0 : Om u v ≠ 0) :
    Duu r u v - Du Om u v / Om u v * Du r u v = 0 := by
  obtain ⟨_, hru, _⟩ := h u v
  have hfun : (fun u' => deriv (fun u'' => r u'' v) u') = (fun u' => -Om u' v) := by
    funext u'
    exact (h u' v).2.1
  have hDuu : Duu r u v = -Du Om u v := by
    show deriv (fun u' => deriv (fun u'' => r u'' v) u') u
      = -deriv (fun u' => Om u' v) u
    rw [hfun]
    exact ((hOm u).hasDerivAt.neg).deriv
  rw [hDuu, hru]
  field_simp

/-- 拘束 C_v の解析版：r_vv − (Ω_v/Ω) r_v = 0。 -/
theorem rn_constraint_v_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hOm0 : Om u v ≠ 0) :
    Dvv r u v - Dv Om u v / Om u v * Dv r u v = 0 := by
  obtain ⟨_, _, hrv⟩ := h u v
  have hfun : (fun v' => deriv (fun v'' => r u v'') v') = (fun v' => Om u v') := by
    funext v'
    exact (h u v').2.2
  have hDvv : Dvv r u v = Dv Om u v := by
    show deriv (fun v' => deriv (fun v'' => r u v'') v') v
      = deriv (fun v' => Om u v') v
    rw [hfun]
  rw [hDvv, hrv]
  field_simp

/-- ミスナー–シャープ質量は M − Q²/(2r)（解析版）。 -/
theorem rn_mass_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hr0 : r u v ≠ 0) (hOm0 : Om u v ≠ 0) :
    CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v
      = M - Q ^ 2 / (2 * r u v) := by
  obtain ⟨_, hru, hrv⟩ := h u v
  have hOm' := rn_Om_mul_analytic h hr0
  show r u v / 2 + r u v * Du r u v * Dv r u v / Om u v = M - Q ^ 2 / (2 * r u v)
  rw [hru, hrv]
  field_simp
  linear_combination (-2 * Om u v) * hOm'

/-- 質量の u 微分：du m = −Q²Ω/(2r²)（解析版）。 -/
theorem rn_mass_u_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hr0 : ∀ u', r u' v ≠ 0) (hOm0 : ∀ u', Om u' v ≠ 0) :
    Du (fun u v => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v) u v
      = -Q ^ 2 * Om u v / (2 * (r u v) ^ 2) := by
  have hfun : (fun u' => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u' v)
      = (fun u' => M - Q ^ 2 / (2 * r u' v)) := by
    funext u'
    exact rn_mass_analytic h (hr0 u') (hOm0 u')
  show deriv (fun u' => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u' v) u
      = -Q ^ 2 * Om u v / (2 * (r u v) ^ 2)
  have hder : deriv (fun u' => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u' v) u
      = deriv (fun u' => M - Q ^ 2 / (2 * r u' v)) u :=
    congrArg (fun F => deriv F u) hfun
  have hR : HasDerivAt (fun u' => M - Q ^ 2 / (2 * r u' v))
      (0 - Q ^ 2 * (-(2 * Du r u v) / (2 * r u v) ^ 2)) u := by
    have h1 := ((hr u).hasDerivAt.const_mul (2 : ℝ)).inv
      (mul_ne_zero (by norm_num) (hr0 u))
    have h2 := h1.const_mul (Q ^ 2)
    exact (hasDerivAt_const u M).sub h2
  rw [hder, hR.deriv]
  obtain ⟨_, hru, _⟩ := h u v
  rw [hru]
  field_simp
  ring

/-- 質量の v 微分：dv m = +Q²Ω/(2r²)（解析版）。 -/
theorem rn_mass_v_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hr : Differentiable ℝ (fun v' => r u v'))
    (hr0 : ∀ v', r u v' ≠ 0) (hOm0 : ∀ v', Om u v' ≠ 0) :
    Dv (fun u v => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v) u v
      = Q ^ 2 * Om u v / (2 * (r u v) ^ 2) := by
  have hfun : (fun v' => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v')
      = (fun v' => M - Q ^ 2 / (2 * r u v')) := by
    funext v'
    exact rn_mass_analytic h (hr0 v') (hOm0 v')
  show deriv (fun v' => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v') v
      = Q ^ 2 * Om u v / (2 * (r u v) ^ 2)
  have hder : deriv (fun v' => CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v') v
      = deriv (fun v' => M - Q ^ 2 / (2 * r u v')) v :=
    congrArg (fun F => deriv F v) hfun
  have hR : HasDerivAt (fun v' => M - Q ^ 2 / (2 * r u v'))
      (0 - Q ^ 2 * (-(2 * Dv r u v) / (2 * r u v) ^ 2)) v := by
    have h1 := ((hr v).hasDerivAt.const_mul (2 : ℝ)).inv
      (mul_ne_zero (by norm_num) (hr0 v))
    have h2 := h1.const_mul (Q ^ 2)
    exact (hasDerivAt_const v M).sub h2
  rw [hder, hR.deriv]
  obtain ⟨_, _, hrv⟩ := h u v
  rw [hrv]
  field_simp
  ring

/-- まとめ：RN 場（解析版）は真空方程式を残差 Q² 項つきで満たし、拘束は 0、
    質量は M − Q²/(2r)。 -/
theorem rn_electrovacuum_analytic {r Om : ℝ → ℝ → ℝ} {M Q u v : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q)
    (hdiff : ∀ u v, Differentiable ℝ (fun u' => r u' v) ∧ Differentiable ℝ (fun v' => r u v')
      ∧ Differentiable ℝ (fun u' => Om u' v) ∧ Differentiable ℝ (fun v' => Om u v'))
    (hr0 : ∀ u v, r u v ≠ 0) (hOm0 : ∀ u v, Om u v ≠ 0) :
    Duv r u v = -Om u v / (2 * r u v) - Du r u v * Dv r u v / r u v
        + Q ^ 2 * Om u v / (2 * (r u v) ^ 3)
      ∧ Duv Om u v = Du Om u v * Dv Om u v / Om u v
          - 2 * Om u v * Duv r u v / r u v - Q ^ 2 * Om u v ^ 2 / (r u v) ^ 4
      ∧ Duu r u v - Du Om u v / Om u v * Du r u v = 0
      ∧ Dvv r u v - Dv Om u v / Om u v * Dv r u v = 0
      ∧ CFT.SchwarzschildAnalytic.misnerSharpMassAnalytic r Om u v
          = M - Q ^ 2 / (2 * r u v) := by
  obtain ⟨hru_d, hrv_d, hOmu_d, hOmv_d⟩ := hdiff u v
  exact ⟨rn_r_eq_analytic h hru_d hOmu_d (hr0 u v),
    rn_Om_eq_analytic h (fun u' => (hdiff u' v).2.1)
      (fun u' => (hdiff u' v).2.2.2) hru_d hOmu_d (fun u' => hr0 u' v) (hOm0 u v),
    rn_constraint_u_analytic h hOmu_d (hOm0 u v),
    rn_constraint_v_analytic h (hOm0 u v),
    rn_mass_analytic h (hr0 u v) (hOm0 u v)⟩

/-- Q = 0 での帰着：RN 場（解析版）はシュワルツシルト場（解析版）になる（9-1）。 -/
theorem rn_to_schwarzschild_analytic {r Om : ℝ → ℝ → ℝ} {M Q : ℝ}
    (h : ReissnerNordstromFieldAnalytic r Om M Q) (hQ : Q = 0) :
    CFT.SchwarzschildAnalytic.SchwarzschildFieldAnalytic r Om M := by
  intro u v
  obtain ⟨ht, hru, hrv⟩ := h u v
  refine ⟨?_, hru, hrv⟩
  rw [hQ] at ht
  simpa using ht

end CFT.ReissnerNordstromAnalytic
