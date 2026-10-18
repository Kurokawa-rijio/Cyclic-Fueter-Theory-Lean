/-
  α-VIII.3(Z41)、α-VIII.7(Z44)の線形の部分、α-VIII.5(Z42)の条件つきの算術

  線形のゆらぎの方程式(t = log r、AdS₂ 型の動径座標):φ'' − d φ' − μ φ = 0、μ = m_eff² L₂²。
    * char_root:φ = e^{αt} が解 ⇔ α² − dα − μ = 0
    * real_roots_iff:実根を持つ ⇔ d² + 4μ ≥ 0(Breitenlohner–Freedman 境界 μ ≥ −d²/4)
    * oscillating_solution:μ < −d²/4 なら φ = e^{dt/2} cos(ωt)、ω² = −(μ + d²/4) が解(振動解、BF 違反)
    * AdS₂(d = 1)の境界は μ = −1/4(bf_ads2)
  非線形アトラクターの存在・一意性・安定性(VIII.3 の本体)と、BPS の no-go(VIII.7 の本体)は、
  作用・アトラクター関数・SUSY 変換則が手元になく未形式化。
  VIII.5:採用する規約は ℓ*² = α′/4(Witten の木の近似の縮約 G_N = α_GUT α′/4、AlphaVIII_Z38 の ell_witten)。
  このとき α′/ℓ*² = 4、α′R(S³) = 24、α′R(S⁴) = 48、レベル 1/4 は整数でない(z42_adopted, one_quarter_not_integer)。
  旧規約 ℓ*² = α′/8 の値(z42_conditional, one_eighth_not_integer)は比較のため残す。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Real

namespace CFT.BF

/-- φ = e^{αt} の 1 階・2 階微分 -/
theorem exp_derivs (α t : ℝ) :
    HasDerivAt (fun t => exp (α * t)) (α * exp (α * t)) t ∧
    HasDerivAt (fun t => α * exp (α * t)) (α ^ 2 * exp (α * t)) t := by
  have h := ((hasDerivAt_id t).const_mul α).exp
  constructor
  · convert h using 1; simp; ring
  · convert h.const_mul α using 1; simp; ring

/-- 指数解の条件:φ'' − dφ' − μφ = (α² − dα − μ) e^{αt} -/
theorem char_root (α d μ t : ℝ) :
    α ^ 2 * exp (α * t) - d * (α * exp (α * t)) - μ * exp (α * t) = 0 ↔ α ^ 2 - d * α - μ = 0 := by
  have hp : 0 < exp (α * t) := exp_pos _
  constructor
  · intro h
    have : (α ^ 2 - d * α - μ) * exp (α * t) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right hp.ne'
  · intro h; linear_combination exp (α * t) * h

/-- 実根を持つ ⇔ d² + 4μ ≥ 0(BF 境界) -/
theorem real_roots_iff (d μ : ℝ) : (∃ α : ℝ, α ^ 2 - d * α - μ = 0) ↔ -(d ^ 2 / 4) ≤ μ := by
  constructor
  · rintro ⟨α, h⟩; nlinarith [sq_nonneg (2 * α - d)]
  · intro h
    refine ⟨(d + √(d ^ 2 + 4 * μ)) / 2, ?_⟩
    have hs := Real.sq_sqrt (show 0 ≤ d ^ 2 + 4 * μ by linarith)
    nlinarith [hs]

/-- AdS₂(d = 1)の BF 境界 -/
theorem bf_ads2 (μ : ℝ) : (∃ α : ℝ, α ^ 2 - 1 * α - μ = 0) ↔ -(1 / 4) ≤ μ := by
  have := real_roots_iff 1 μ; norm_num at this ⊢; exact this

/-- BF 境界の下では振動解 e^{dt/2} cos(ωt) がある(ω² = −(μ + d²/4)) -/
theorem oscillating_solution (d μ ω t : ℝ) (hω : ω ^ 2 = -(μ + d ^ 2 / 4)) :
    let φ := fun t => exp (d / 2 * t) * cos (ω * t)
    let φ' := fun t => d / 2 * exp (d / 2 * t) * cos (ω * t) - ω * exp (d / 2 * t) * sin (ω * t)
    let φ'' := (d / 2) ^ 2 * exp (d / 2 * t) * cos (ω * t) - d * ω * exp (d / 2 * t) * sin (ω * t)
      - ω ^ 2 * exp (d / 2 * t) * cos (ω * t)
    HasDerivAt φ (φ' t) t ∧ HasDerivAt φ' φ'' t ∧ φ'' - d * φ' t - μ * φ t = 0 := by
  intro φ φ' φ''
  have he := ((hasDerivAt_id t).const_mul (d / 2)).exp
  have hc := ((hasDerivAt_id t).const_mul ω).cos
  have hs := ((hasDerivAt_id t).const_mul ω).sin
  refine ⟨?_, ?_, ?_⟩
  · convert he.mul hc using 1; simp [φ']; ring
  · have h1 := (he.const_mul (d / 2)).mul hc
    have h2 := (he.const_mul ω).mul hs
    convert h1.sub h2 using 1
    all_goals first | (funext x; simp [φ']; ring) | (simp [φ'']; ring)
  · simp only [φ, φ', φ'']
    linear_combination (-(exp (d / 2 * t) * cos (ω * t))) * hω

/-! ### α-VIII.5(条件つき) -/

theorem z42_conditional (αp : ℝ) (hα : αp ≠ 0) :
    let ell2 := αp / 8
    αp / ell2 = 8 ∧ αp * (6 / ell2) = 48 ∧ αp * (12 / ell2) = 96 := by
  intro ell2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ell2] <;> field_simp <;> ring

theorem one_eighth_not_integer : ¬ ∃ k : ℤ, (k : ℚ) = 1 / 8 := by
  rintro ⟨k, hk⟩
  have h8 : (8 : ℚ) * k = 1 := by rw [hk]; norm_num
  have : (8 * k : ℤ) = 1 := by exact_mod_cast h8
  omega

/-- 採用した規約 ℓ*² = α′/4 での値 -/
theorem z42_adopted (αp : ℝ) (hα : αp ≠ 0) :
    let ell2 := αp / 4
    αp / ell2 = 4 ∧ αp * (6 / ell2) = 24 ∧ αp * (12 / ell2) = 48 := by
  intro ell2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ell2] <;> field_simp <;> ring

theorem one_quarter_not_integer : ¬ ∃ k : ℤ, (k : ℚ) = 1 / 4 := by
  rintro ⟨k, hk⟩
  have h4 : (4 : ℚ) * k = 1 := by rw [hk]; norm_num
  have : (4 * k : ℤ) = 1 := by exact_mod_cast h4
  omega

end CFT.BF
