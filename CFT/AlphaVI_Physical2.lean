/-
  α-VI.6 (Z35)・α-VI.8 (Z37) の補強:物理的な枝、affine 量子化、停留位相の条件

  α-VI.6(物理的な内積)
  * 物理的な枝(b > 0、c > 0、ℓ > 0):Q_C(b) > 0 となる b > 0 がある ⇔ C > 8c²ℓ(`physical_branch`)。
    (全実数の b を許した `domain_nonempty_iff` には C < −8c²ℓ の負の枝が混じるので、こちらを使う。)
  * K の値域:K − 8c²ℓ = (p_a² + 4c²(b − ℓ)²)/b ≥ 0、p_a ≠ 0 なら K > 8c²ℓ(`K_minus_min`、`K_gt_min`)。
    簡約位相空間は半平面 {K > K₀} × ℝ_T(K₀ = 8c²ℓ、{T, K} = 1)。
  * 半平面の上では T̂ = iħ∂_K は自己共役にならない(半直線の微分作用素は不足指数が一致しない)。
    そこで正準群を affine 群にとる(Isham 1984 の正準群量子化):D = (K − K₀)T は
    {D, K} = K − K₀(`affine_bracket`)をみたし、(K − K₀, D) は affine 群の Lie 代数を張る。
  * affine 群の既約ユニタリ表現で K − K₀ > 0 となるものは同値を除いて一つ(Gel'fand–Naimark 1947、外部定理)。
    その実現は L²((0, ∞), dk)(k = K − K₀)で、
      平行移動 ψ(k) ↦ e^{iτk/ħ}ψ(k)(`translation_norm`)、拡大 ψ(k) ↦ √α ψ(αk)(`dilation_isometry`)
    はどちらもノルムを保つ。K̂ − K₀ は掛け算で正、D̂ は拡大の生成子で自己共役(Stone の定理、外部定理)。
    したがって物理的な内積 ⟨f, g⟩ = ∫ f̄ g dK は仮定ではなく、表現の一意性から決まる
    (正値性と非退化性は AlphaVI_Physical の `phys_inner_nonneg`、`phys_inner_eq_zero`)。
    二つの枝(p_a = ±√Q、AlphaIV_WKB2)はそれぞれこの表現を一つずつ持つ。
  * T は内部時計ではなく、Dirac 観測量(軌道のラベル)として扱う。時刻を表す観測量としては共変な POVM を使う
    (Holevo)。ここでは自己共役な時計は要求しない。

  α-VI.8(半古典極限)
  * 波束 Ψ_f(a, b) = ∫ g(C) e^{i(aσ_C(b) − C T₀)/ħ}/σ_C(b) dC(g は C > 8c²ℓ に台をもつなめらかな関数)。
    位相 φ(C) = aσ_C(b) − C T₀ の停留点の条件は ∂_C(aσ_C) = T₀、すなわち T(a, b, p_a = σ_C) = T₀
    (AlphaVI_Physical `dS_dC`)。
  * 非退化:∂_C²(aσ_C) = −a b²/(4 σ_C³) ≠ 0(a, b ≠ 0、`d2S_dC2`、`stationary_nondegenerate`)。
  * 一意性:a, b > 0 なら T(C) = ab/(2σ_C) は {C : Q_C(b) > 0} = (4c²(b² + ℓ²)/b, ∞) で狭義単調減少
    (`T_strictAnti`)。したがって停留点は高々一つ(`stationary_unique`)。
  * 停留位相の定理(Hörmander, Thm 7.7.5、外部定理)の条件(位相がなめらか、停留点が一つで非退化)が
    そろうので、Ψ_f(a, b) = e^{iφ(C*)/ħ} g(C*) √(2πħ/|φ″(C*)|) e^{iπ/4 sgn φ″}/σ_{C*} + O(ħ^{3/2})、
    停留点がなければ O(ħ^∞)。|Ψ_f|² は古典軌道 {K = C*、T = T₀} に集中する。(K, T) は保存する
    (AlphaVI `bracket_KH`、AlphaVI_Physical `bracket_TH_weak`)ので、これは古典の解そのもの。
  * 帽子との接合条件の回復は、最後の課題(代数から実際の場への橋渡し)と同じ形の問題なので、そちらに移す。
-/
import CFT.AlphaVI_Physical

namespace CFT.Phys2

open CFT.AlphaVI CFT.WKB Real MeasureTheory Set

noncomputable section

/-! ### α-VI.6 -/

/-- 【α-VI.6】物理的な枝:c, ℓ > 0 のとき、Q_C(b) > 0 となる b > 0 がある ⇔ C > 8c²ℓ -/
theorem physical_branch (c l C : ℝ) (hc : 0 < c) (hl : 0 < l) :
    (∃ b, 0 < b ∧ 0 < Q c l C b) ↔ 8 * c ^ 2 * l < C := by
  constructor
  · rintro ⟨b, hb, hQ⟩
    have key : (C - 8 * c ^ 2 * l) * b = Q c l C b + 4 * c ^ 2 * (b - l) ^ 2 := by
      simp only [Q]; ring
    by_contra h
    push_neg at h
    have h1 : (C - 8 * c ^ 2 * l) * b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
    have h2 : 0 ≤ 4 * c ^ 2 * (b - l) ^ 2 := by positivity
    linarith
  · intro h
    have hc2 : 0 < c ^ 2 := by positivity
    have hc0 : c ≠ 0 := hc.ne'
    have h0 : 0 < 8 * c ^ 2 * l := by positivity
    have hCpos : 0 < C := by linarith
    refine ⟨C / (8 * c ^ 2), by positivity, ?_⟩
    have key : 16 * c ^ 2 * Q c l C (C / (8 * c ^ 2)) = C ^ 2 - 64 * c ^ 4 * l ^ 2 := by
      simp only [Q]
      field_simp <;> ring
    have hprod := mul_pos (sub_pos.mpr h) (show 0 < C + 8 * c ^ 2 * l by linarith)
    have hC : 64 * c ^ 4 * l ^ 2 < C ^ 2 := by nlinarith [hprod]
    nlinarith [key, hC, hc2]

/-- K − 8c²ℓ = (p_a² + 4c²(b − ℓ)²)/b -/
theorem K_minus_min (b pa c l : ℝ) (hb : b ≠ 0) :
    (pa ^ 2 + 4 * c ^ 2 * (b ^ 2 + l ^ 2)) / b - 8 * c ^ 2 * l
      = (pa ^ 2 + 4 * c ^ 2 * (b - l) ^ 2) / b := by
  field_simp <;> ring

/-- 【α-VI.6】b > 0、p_a ≠ 0 なら K > K₀ = 8c²ℓ(簡約位相空間は半平面) -/
theorem K_gt_min (b pa c l : ℝ) (hb : 0 < b) (hpa : pa ≠ 0) :
    8 * c ^ 2 * l < (pa ^ 2 + 4 * c ^ 2 * (b ^ 2 + l ^ 2)) / b := by
  have h := K_minus_min b pa c l hb.ne'
  have hp : 0 < pa ^ 2 := sq_pos_of_ne_zero hpa
  have hnum : 0 < pa ^ 2 + 4 * c ^ 2 * (b - l) ^ 2 :=
    add_pos_of_pos_of_nonneg hp (by positivity)
  have : 0 < (pa ^ 2 + 4 * c ^ 2 * (b - l) ^ 2) / b := div_pos hnum hb
  linarith

/-- 【α-VI.6】affine の括弧:D = (K − K₀)T の勾配を Leibniz 則で作ると {D, K} = K − K₀
({T, K} = 1 は AlphaVI `bracket_TK`) -/
theorem affine_bracket (a b pa c l K K0 T : ℝ) (hb : b ≠ 0) (hpa : pa ≠ 0) :
    (Ka * T + (K - K0) * Ta b pa) * Kpa b pa - (Kpa b pa * T + (K - K0) * Tpa a b pa) * Ka
      + (Kb b pa c l * T + (K - K0) * Tb a pa) * Kpb - (Kpb * T + (K - K0) * Tpb) * Kb b pa c l
      = K - K0 := by
  have h := bracket_TK a b pa c l hb hpa
  linear_combination (K - K0) * h

/-- 平行移動 ψ ↦ e^{iτk/ħ}ψ は各点で絶対値を保つ -/
theorem translation_norm (ψ : ℝ → ℂ) (τ κ k : ℝ) :
    ‖Complex.exp (((τ * k * κ : ℝ) : ℂ) * Complex.I) * ψ k‖ = ‖ψ k‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- 【α-VI.6】拡大 ψ(k) ↦ √α ψ(αk)(α > 0)は L²((0, ∞), dk) のノルムを保つ -/
theorem dilation_isometry (ψ : ℝ → ℂ) (α : ℝ) (hα : 0 < α) :
    ∫ k in Ioi (0 : ℝ), ‖(Real.sqrt α : ℂ) * ψ (α * k)‖ ^ 2 = ∫ k in Ioi (0 : ℝ), ‖ψ k‖ ^ 2 := by
  have h1 : ∀ k, ‖(Real.sqrt α : ℂ) * ψ (α * k)‖ ^ 2 = α * ‖ψ (α * k)‖ ^ 2 := by
    intro k
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hα.le]
  simp_rw [h1]
  rw [integral_mul_left]
  have h2 := integral_comp_mul_left_Ioi (fun k => ‖ψ k‖ ^ 2) 0 hα
  simp only [mul_zero] at h2
  rw [h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]

/-! ### α-VI.8 -/

/-- Q の C についての微分は b -/
theorem hasDerivAt_Q_C (c l b C : ℝ) : HasDerivAt (fun C' => Q c l C' b) b C := by
  have h := ((hasDerivAt_id C).mul_const b).sub_const (4 * c ^ 2 * (b ^ 2 + l ^ 2))
  exact h.congr_deriv (one_mul b)

/-- 【α-VI.8】∂_C²(aσ_C) = ∂_C(ab/(2σ_C)) = −ab²/(4σ_C³) -/
theorem d2S_dC2 (a b c l C : ℝ) (hQ : 0 < Q c l C b) :
    HasDerivAt (fun C' => a * b / (2 * Real.sqrt (Q c l C' b)))
      (-(a * b ^ 2) / (4 * Real.sqrt (Q c l C b) ^ 3)) C := by
  have hs := (hasDerivAt_Q_C c l b C).sqrt hQ.ne'
  have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
  have hne : (fun C' => 2 * Real.sqrt (Q c l C' b)) C ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]; exact hspos.ne'
  have h := (hasDerivAt_const C (a * b)).div (hs.const_mul 2) hne
  refine h.congr_deriv ?_
  have hsq : Real.sqrt (Q c l C b) ^ 2 = Q c l C b := Real.sq_sqrt hQ.le
  have hs0 : Real.sqrt (Q c l C b) ≠ 0 := hspos.ne'
  field_simp <;> ring

/-- 【α-VI.8】非退化:a, b ≠ 0 なら停留点での 2 階微分は 0 でない -/
theorem stationary_nondegenerate (a b c l C : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hQ : 0 < Q c l C b) :
    -(a * b ^ 2) / (4 * Real.sqrt (Q c l C b) ^ 3) ≠ 0 := by
  have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero ha (pow_ne_zero 2 hb)))
    (mul_pos four_pos (pow_pos hspos 3)).ne'

/-- 定義域 {C : Q_C(b) > 0} は半直線 (4c²(b² + ℓ²)/b, ∞)(b > 0) -/
theorem domain_Ioi (b c l : ℝ) (hb : 0 < b) :
    {C | 0 < Q c l C b} = Ioi (4 * c ^ 2 * (b ^ 2 + l ^ 2) / b) := by
  ext C
  simp only [mem_setOf_eq, mem_Ioi, Q]
  rw [div_lt_iff₀ hb]
  constructor <;> intro h <;> linarith

/-- 【α-VI.8】a, b > 0 なら T(C) = ab/(2σ_C) は定義域で狭義単調減少 -/
theorem T_strictAnti (a b c l : ℝ) (ha : 0 < a) (hb : 0 < b) :
    StrictAntiOn (fun C => a * b / (2 * Real.sqrt (Q c l C b))) {C | 0 < Q c l C b} := by
  rw [domain_Ioi b c l hb]
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro C hC
    have hQ : 0 < Q c l C b := by
      have h' := hC
      rw [mem_Ioi, div_lt_iff₀ hb] at h'
      simp only [Q]; linarith
    exact (d2S_dC2 a b c l C hQ).continuousAt.continuousWithinAt
  · intro C hC
    rw [interior_Ioi] at hC
    have hQ : 0 < Q c l C b := by
      have h' := hC
      rw [mem_Ioi, div_lt_iff₀ hb] at h'
      simp only [Q]; linarith
    rw [(d2S_dC2 a b c l C hQ).deriv]
    have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
    apply div_neg_of_neg_of_pos
    · have : 0 < a * b ^ 2 := by positivity
      linarith
    · exact mul_pos four_pos (pow_pos hspos 3)

/-- 【α-VI.8】停留点は高々一つ:T(C₁) = T(C₂) = T₀ なら C₁ = C₂ -/
theorem stationary_unique (a b c l C₁ C₂ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 0 < Q c l C₁ b) (h2 : 0 < Q c l C₂ b)
    (h : a * b / (2 * Real.sqrt (Q c l C₁ b)) = a * b / (2 * Real.sqrt (Q c l C₂ b))) : C₁ = C₂ :=
  (T_strictAnti a b c l ha hb).injOn h1 h2 h

end

end CFT.Phys2
