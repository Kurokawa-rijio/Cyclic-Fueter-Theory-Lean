
import CFT.Spherical.WedgeEYMSystem
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 9-1・9-2 の残り：解析的な `deriv` 版への移行。
  `SchwarzschildVacuumSolution.lean`（9-1）と `FlatLimit.lean`（9-2）は
  導分代数の流儀で、真空の発展方程式・拘束・ミスナー–シャープ質量を証明した。
  このモジュールでは同じ内容を実際の関数 r, Om : ℝ → ℝ → ℝ と
  `CFT.Wedge.Du` / `Dv`（スライスの `deriv`）で述べる：
  トータス関係 2Ω = 1 − 2M/r と r_u = −Ω、r_v = +Ω を
  `SchwarzschildFieldAnalytic` として定義し、Ω の u・v 微分
  （Du Ω = −MΩ/r²、Dv Ω = +MΩ/r²、トータス関係の微分）、
  r 方程式・Ω 方程式（商の微分による HasDerivAt の組み立て）・
  拘束 C_u・C_v・質量 = M を証明し、まとめ `schwarzschild_vacuum_analytic`
  とする。M = 0 の場合は平坦極限（Ω = 1/2、r_uv = Ω_uv = 0、質量 0）の
  解析版 `flat_limit_analytic` になる。
  これで 9-1・9-2 は、導分代数版・解析版ともに閉じた。

  残り：トータス ODE を満たす ρ の存在そのもの（陰関数／ODE の存在定理）、
  地平線 r = 2M（Ω = 0）の扱いは本モジュールの範囲外（Ω ≠ 0 を仮定）。
-/

open CFT.Wedge

namespace CFT.SchwarzschildAnalytic

/-- 解析的なシュワルツシルト場の条件（トータス関係の `deriv` 版）。M は定数の実数。 -/
def SchwarzschildFieldAnalytic (r Om : ℝ → ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ u v, 2 * Om u v = 1 - 2 * M / r u v ∧ Du r u v = -Om u v ∧ Dv r u v = Om u v

/-- 分母を払った形：2 Ω r = r − 2M。 -/
theorem schwarzschild_Om_mul_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M) (hr : r u v ≠ 0) :
    2 * Om u v * r u v = r u v - 2 * M := by
  have hOm := (h u v).1
  have h1 : (2 * Om u v) * r u v = (1 - 2 * M / r u v) * r u v := congrArg (· * r u v) hOm
  have h2 : (1 - 2 * M / r u v) * r u v = r u v - 2 * M := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hr]
  rw [h2] at h1
  exact h1

/-- Ω の u 微分：Du Ω = −MΩ/r²（トータス関係の微分）。 -/
theorem schwarzschild_du_Om_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : r u v ≠ 0) :
    Du Om u v = -M * Om u v / (r u v) ^ 2 := by
  obtain ⟨hrel, hru, _⟩ := h u v
  have hfun : (fun u' => 2 * Om u' v) = (fun u' => 1 - 2 * M / r u' v) := by
    funext u'
    exact (h u' v).1
  have hder : deriv (fun u' => 2 * Om u' v) u
      = deriv (fun u' => 1 - 2 * M / r u' v) u :=
    congrArg (fun F => deriv F u) hfun
  have hL : deriv (fun u' => 2 * Om u' v) u = 2 * Du Om u v := by
    show deriv (fun u' => 2 * Om u' v) u = 2 * deriv (fun u' => Om u' v) u
    exact deriv_const_mul 2 (hOm u)
  have hR : HasDerivAt (fun u' => 1 - 2 * M / r u' v)
      (0 - (2 * M) * (-(Du r u v) / (r u v) ^ 2)) u := by
    have h1 := (hr u).hasDerivAt
    have h2 := h1.inv hr0
    have h3 := h2.const_mul (2 * M)
    exact (hasDerivAt_const u (1 : ℝ)).sub h3
  rw [hL, hR.deriv, hru] at hder
  linear_combination hder / 2

/-- Ω の v 微分：Dv Ω = +MΩ/r²。 -/
theorem schwarzschild_dv_Om_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
    (hr : Differentiable ℝ (fun v' => r u v'))
    (hOm : Differentiable ℝ (fun v' => Om u v'))
    (hr0 : r u v ≠ 0) :
    Dv Om u v = M * Om u v / (r u v) ^ 2 := by
  obtain ⟨hrel, _, hrv⟩ := h u v
  have hfun : (fun v' => 2 * Om u v') = (fun v' => 1 - 2 * M / r u v') := by
    funext v'
    exact (h u v').1
  have hder : deriv (fun v' => 2 * Om u v') v
      = deriv (fun v' => 1 - 2 * M / r u v') v :=
    congrArg (fun F => deriv F v) hfun
  have hL : deriv (fun v' => 2 * Om u v') v = 2 * Dv Om u v := by
    show deriv (fun v' => 2 * Om u v') v = 2 * deriv (fun v' => Om u v') v
    exact deriv_const_mul 2 (hOm v)
  have hR : HasDerivAt (fun v' => 1 - 2 * M / r u v')
      (0 - (2 * M) * (-(Dv r u v) / (r u v) ^ 2)) v := by
    have h1 := (hr v).hasDerivAt
    have h2 := h1.inv hr0
    have h3 := h2.const_mul (2 * M)
    exact (hasDerivAt_const v (1 : ℝ)).sub h3
  rw [hL, hR.deriv, hrv] at hder
  linear_combination hder / 2

/-- Duv r = Du Ω（Dv r = Ω を u 方向に微分）。 -/
theorem schwarzschild_Duv_r_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M) :
    Duv r u v = Du Om u v := by
  have hfun : (fun u' => Dv r u' v) = (fun u' => Om u' v) := by
    funext u'
    exact (h u' v).2.2
  show deriv (fun u' => Dv r u' v) u = deriv (fun u' => Om u' v) u
  rw [hfun]

/-- 真空の r 方程式の解析版：r_uv = −Ω/(2r) − r_u r_v/r。 -/
theorem schwarzschild_r_eq_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : r u v ≠ 0) :
    Duv r u v = -Om u v / (2 * r u v) - Du r u v * Dv r u v / r u v := by
  obtain ⟨hrel, hru, hrv⟩ := h u v
  have hdu := schwarzschild_du_Om_analytic h hr hOm hr0
  have hOm' := schwarzschild_Om_mul_analytic h hr0
  rw [schwarzschild_Duv_r_analytic h, hdu, hru, hrv]
  field_simp
  linear_combination (-r u v ^ 2 * Om u v) * hOm'

/-- 真空の Ω 方程式の解析版：Ω_uv = Ω_u Ω_v/Ω − 2Ω r_uv/r。 -/
theorem schwarzschild_Om_eq_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
    (hru_diff : ∀ u', Differentiable ℝ (fun v' => r u' v'))
    (hOmv_diff : ∀ u', Differentiable ℝ (fun v' => Om u' v'))
    (hr_u : Differentiable ℝ (fun u' => r u' v))
    (hOm_u : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : ∀ u', r u' v ≠ 0)
    (hOm0 : Om u v ≠ 0) :
    Duv Om u v = Du Om u v * Dv Om u v / Om u v
      - 2 * Om u v * Duv r u v / r u v := by
  have hr0u := hr0 u
  have hdu := schwarzschild_du_Om_analytic h hr_u hOm_u hr0u
  have hdv := schwarzschild_dv_Om_analytic h (hru_diff u) (hOmv_diff u) hr0u
  have hruv : Duv r u v = -M * Om u v / (r u v) ^ 2 := by
    rw [schwarzschild_Duv_r_analytic h, hdu]
  have hfun : (fun u' => Dv Om u' v) = (fun u' => M * Om u' v / (r u' v) ^ 2) := by
    funext u'
    exact schwarzschild_dv_Om_analytic h (hru_diff u') (hOmv_diff u') (hr0 u')
  have hDuv : Duv Om u v = deriv (fun u' => M * Om u' v / (r u' v) ^ 2) u := by
    show deriv (fun u' => Dv Om u' v) u = deriv (fun u' => M * Om u' v / (r u' v) ^ 2) u
    rw [hfun]
  have hg : HasDerivAt (fun u' => M * Om u' v / (r u' v) ^ 2)
      ((M * deriv (fun u' => Om u' v) u * (r u v) ^ 2
        - M * Om u v * (2 * r u v * deriv (fun u' => r u' v) u)) / ((r u v) ^ 2) ^ 2) u := by
    have h1 := (hOm_u u).hasDerivAt
    have h2 := (hr_u u).hasDerivAt
    have h3 := h1.const_mul M
    have h4 := h2.pow 2
    have h5 := h3.div h4 (pow_ne_zero 2 hr0u)
    convert h5 using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  rw [hDuv, hg.deriv]
  show ((M * Du Om u v) * (r u v) ^ 2
      - M * Om u v * (2 * r u v * Du r u v)) / ((r u v) ^ 2) ^ 2
    = Du Om u v * Dv Om u v / Om u v - 2 * Om u v * Duv r u v / r u v
  rw [hdu, hdv, hruv, (h u v).2.1]
  field_simp
  ring

/-- 拘束 C_u の解析版：r_uu − (Ω_u/Ω) r_u = 0。 -/
theorem schwarzschild_constraint_u_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
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
theorem schwarzschild_constraint_v_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
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

/-- ミスナー–シャープ質量の解析版：m = r/2 + r r_u r_v/Ω。 -/
noncomputable def misnerSharpMassAnalytic (r Om : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  r u v / 2 + r u v * Du r u v * Dv r u v / Om u v

/-- ミスナー–シャープ質量は M。 -/
theorem schwarzschild_mass_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
    (hr0 : r u v ≠ 0) (hOm0 : Om u v ≠ 0) :
    misnerSharpMassAnalytic r Om u v = M := by
  obtain ⟨_, hru, hrv⟩ := h u v
  have hOm' := schwarzschild_Om_mul_analytic h hr0
  show r u v / 2 + r u v * Du r u v * Dv r u v / Om u v = M
  rw [hru, hrv]
  field_simp
  linear_combination (-Om u v) * hOm'

/-- まとめ：シュワルツシルト場（解析版）は真空の発展方程式と拘束を満たし、質量は M。 -/
theorem schwarzschild_vacuum_analytic {r Om : ℝ → ℝ → ℝ} {M u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om M)
    (hdiff : ∀ u v, Differentiable ℝ (fun u' => r u' v) ∧ Differentiable ℝ (fun v' => r u v')
      ∧ Differentiable ℝ (fun u' => Om u' v) ∧ Differentiable ℝ (fun v' => Om u v'))
    (hr0 : ∀ u v, r u v ≠ 0) (hOm0 : ∀ u v, Om u v ≠ 0) :
    Duv r u v = -Om u v / (2 * r u v) - Du r u v * Dv r u v / r u v
      ∧ Duv Om u v = Du Om u v * Dv Om u v / Om u v - 2 * Om u v * Duv r u v / r u v
      ∧ Duu r u v - Du Om u v / Om u v * Du r u v = 0
      ∧ Dvv r u v - Dv Om u v / Om u v * Dv r u v = 0
      ∧ misnerSharpMassAnalytic r Om u v = M := by
  obtain ⟨hru_d, hrv_d, hOmu_d, hOmv_d⟩ := hdiff u v
  exact ⟨schwarzschild_r_eq_analytic h hru_d hOmu_d (hr0 u v),
    schwarzschild_Om_eq_analytic h (fun u' => (hdiff u' v).2.1)
      (fun u' => (hdiff u' v).2.2.2) hru_d hOmu_d (fun u' => hr0 u' v) (hOm0 u v),
    schwarzschild_constraint_u_analytic h hOmu_d (hOm0 u v),
    schwarzschild_constraint_v_analytic h (hOm0 u v),
    schwarzschild_mass_analytic h (hr0 u v) (hOm0 u v)⟩

/-- M = 0 のシュワルツシルト場の値：Ω = 1/2、r_u = −1/2、r_v = +1/2。 -/
theorem flat_field_values_analytic {r Om : ℝ → ℝ → ℝ} {u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om 0) :
    Om u v = 1 / 2 ∧ Du r u v = -(1 / 2 : ℝ) ∧ Dv r u v = 1 / 2 := by
  obtain ⟨hrel, hru, hrv⟩ := h u v
  simp only [mul_zero, zero_div, sub_zero] at hrel
  have hOm : Om u v = 1 / 2 := by linear_combination hrel / 2
  rw [hOm] at hru hrv
  exact ⟨hOm, hru, hrv⟩

/-- r の平坦な波動方程式の解析版：r_uv = 0。 -/
theorem flat_r_uv_analytic {r Om : ℝ → ℝ → ℝ} {u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om 0)
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr0 : r u v ≠ 0) :
    Duv r u v = 0 := by
  have hdu := schwarzschild_du_Om_analytic h hr hOm hr0
  rw [schwarzschild_Duv_r_analytic h, hdu]
  simp

/-- Ω の平坦な波動方程式の解析版：Ω_uv = 0。 -/
theorem flat_Om_uv_analytic {r Om : ℝ → ℝ → ℝ} {u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om 0)
    (hru_diff : ∀ u', Differentiable ℝ (fun v' => r u' v'))
    (hOmv_diff : ∀ u', Differentiable ℝ (fun v' => Om u' v'))
    (hr0 : ∀ u', r u' v ≠ 0) :
    Duv Om u v = 0 := by
  have hfun : (fun u' => Dv Om u' v) = (fun _ => (0 : ℝ)) := by
    funext u'
    have hdv := schwarzschild_dv_Om_analytic h (hru_diff u') (hOmv_diff u') (hr0 u')
    rw [hdv]
    simp
  show deriv (fun u' => Dv Om u' v) u = 0
  rw [hfun]
  exact deriv_const u 0

/-- ミスナー–シャープ質量は 0（平坦極限では質量が消える）。 -/
theorem flat_mass_analytic {r Om : ℝ → ℝ → ℝ} {u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om 0)
    (hr0 : r u v ≠ 0) (hOm0 : Om u v ≠ 0) :
    misnerSharpMassAnalytic r Om u v = 0 := by
  have hm := schwarzschild_mass_analytic h hr0 hOm0
  simpa using hm

/-- まとめ：平坦極限（解析版）。 -/
theorem flat_limit_analytic {r Om : ℝ → ℝ → ℝ} {u v : ℝ}
    (h : SchwarzschildFieldAnalytic r Om 0)
    (hdiff : ∀ u v, Differentiable ℝ (fun u' => r u' v) ∧ Differentiable ℝ (fun v' => r u v')
      ∧ Differentiable ℝ (fun u' => Om u' v) ∧ Differentiable ℝ (fun v' => Om u v'))
    (hr0 : ∀ u v, r u v ≠ 0) (hOm0 : ∀ u v, Om u v ≠ 0) :
    Om u v = 1 / 2 ∧ Du r u v = -(1 / 2 : ℝ) ∧ Dv r u v = 1 / 2 ∧ Duv r u v = 0 ∧
      Duv Om u v = 0 ∧ misnerSharpMassAnalytic r Om u v = 0 := by
  obtain ⟨hru_d, hrv_d, hOmu_d, hOmv_d⟩ := hdiff u v
  obtain ⟨hOm, hru, hrv⟩ := flat_field_values_analytic h
  exact ⟨hOm, hru, hrv,
    flat_r_uv_analytic h hru_d hOmu_d (hr0 u v),
    flat_Om_uv_analytic h (fun u' => (hdiff u' v).2.1)
      (fun u' => (hdiff u' v).2.2.2) (fun u' => hr0 u' v),
    flat_mass_analytic h (hr0 u v) (hOm0 u v)⟩

end CFT.SchwarzschildAnalytic
