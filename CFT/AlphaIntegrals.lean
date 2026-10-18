/-
  積分を使う項目(添付の統合計算スクリプト Z1_Z46_integrated_calculations_2026-10-14.py の式による)

  * α-IV.1 (Z1)   キャップ r = ℓ sin(s/ℓ) と首 r = ℓ の初期データ(W = r′)は
                   Hamilton/YM 拘束 2/r²(1 − r′² − 2rr″) = 4ℓ²(W′²/r² + (1−W²)²/(2r⁴)) を満たす。
                   接合 s = πℓ/2 で [r] = 0、[r′] = 0、[r″] = 1/ℓ(計量は C^{1,1})。
                   YM エネルギー:キャップ 3π/(8ℓ)、長さ L の首 L/(2ℓ²)(単位 4π/g²)
  * α-V.5 (Z29)   端点付近の動径 Dirac 方程式の主要項:F = s^{−κ}、G = s^{κ} が解。
                   κ ≥ 1/2 では s^{−κ} は L² でない:∫_ε^1 s^{−2κ} ds → ∞(ε → 0+)
  * α-VII.4 (Z28-d) Beta(2,3) の積率 E[X] = 2/5、E[X²] = 1/5、A = Var X = 1/25。
                   n = 9、k = 2、L_k = k(k + n − 1) = 20 の摂動公式で
                   λ₂ = −207/500、係数 = 99/250(摂動公式そのものは入力)
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real intervalIntegral Filter Topology

namespace CFT.AlphaIntegrals

/-! ### α-IV.1 (Z1) 弱い初期データ -/

/-- キャップの拘束:u = s/ℓ、S = sin u ≠ 0、C = cos u のとき
    r = ℓS、r′ = C、r″ = −S/ℓ、W = r′、W′ = −S/ℓ で両辺は 6/ℓ² -/
theorem cap_constraint (l S C : ℝ) (hl : l ≠ 0) (hS : S ≠ 0) (hSC : S ^ 2 + C ^ 2 = 1) :
    2 / (l * S) ^ 2 * (1 - C ^ 2 - 2 * (l * S) * (-S / l))
      = 4 * l ^ 2 * ((-S / l) ^ 2 / (l * S) ^ 2 + (1 - C ^ 2) ^ 2 / (2 * (l * S) ^ 4)) := by
  have hC : 1 - C ^ 2 = S ^ 2 := by linarith
  rw [hC]
  field_simp
  ring

/-- 首の拘束:r = ℓ、r′ = 0、r″ = 0、W = 0 で両辺は 2/ℓ² -/
theorem neck_constraint (l : ℝ) (hl : l ≠ 0) :
    2 / l ^ 2 * (1 - 0 ^ 2 - 2 * l * 0) = 4 * l ^ 2 * (0 ^ 2 / l ^ 2 + (1 - 0 ^ 2) ^ 2 / (2 * l ^ 4)) := by
  field_simp
  ring

/-- キャップの r と r′ の導関数 -/
theorem cap_r_deriv (l s : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun s => l * sin (s / l)) (cos (s / l)) s := by
  have h := ((hasDerivAt_sin (s / l)).comp s ((hasDerivAt_id s).div_const l)).const_mul l
  convert h using 1
  field_simp

theorem cap_rp_deriv (l s : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun s => cos (s / l)) (-sin (s / l) / l) s := by
  have h := (hasDerivAt_cos (s / l)).comp s ((hasDerivAt_id s).div_const l)
  convert h using 1
  simp [div_eq_mul_inv]

/-- 接合 s = πℓ/2 での跳び(首 − キャップ):[r] = 0、[r′] = 0、[r″] = 1/ℓ -/
theorem junction_jumps (l : ℝ) (hl : l ≠ 0) :
    l - l * sin (π * l / 2 / l) = 0 ∧ (0 : ℝ) - cos (π * l / 2 / l) = 0 ∧
      (0 : ℝ) - (-sin (π * l / 2 / l) / l) = 1 / l := by
  have h : π * l / 2 / l = π / 2 := by field_simp; ring
  rw [h, sin_pi_div_two, cos_pi_div_two]
  refine ⟨by ring, by ring, by ring⟩

/-- キャップの YM エネルギー ∫₀^{πℓ/2} [r″² + (1 − r′²)²/(2r²)] ds = 3π/(8ℓ) -/
theorem cap_energy (l : ℝ) (hl : 0 < l) :
    ∫ s in (0 : ℝ)..(π * l / 2),
        ((-sin (s / l) / l) ^ 2 + (1 - cos (s / l) ^ 2) ^ 2 / (2 * (l * sin (s / l)) ^ 2))
      = 3 * π / (8 * l) := by
  have hl0 : l ≠ 0 := hl.ne'
  have hpt : ∀ s : ℝ, (-sin (s / l) / l) ^ 2 + (1 - cos (s / l) ^ 2) ^ 2 / (2 * (l * sin (s / l)) ^ 2)
      = 3 / (2 * l ^ 2) * sin (s / l) ^ 2 := by
    intro s
    have hC : 1 - cos (s / l) ^ 2 = sin (s / l) ^ 2 := by linarith [sin_sq_add_cos_sq (s / l)]
    rw [hC]
    by_cases hS : sin (s / l) = 0
    · simp [hS]
    · field_simp
      ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_div (fun x => sin x ^ 2) hl0, integral_sin_sq]
  have h1 : π * l / 2 / l = π / 2 := by field_simp; ring
  rw [h1, zero_div, sin_zero, cos_zero, sin_pi_div_two, cos_pi_div_two]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- 首の YM エネルギー:∫₀^L (1/(2ℓ²)) ds = L/(2ℓ²) -/
theorem neck_energy (l L : ℝ) :
    ∫ _s in (0 : ℝ)..L, (0 ^ 2 + (1 - 0 ^ 2) ^ 2 / (2 * l ^ 2) : ℝ) = L / (2 * l ^ 2) := by
  simp [integral_const]
  ring

/-! ### α-V.5 (Z29) 端点の limit-point 判定の局所部分 -/

/-- F = s^{−κ} は F′ + (κ/s)F = 0 を満たす(s > 0) -/
theorem endpoint_F (κ s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => s ^ (-κ)) (-κ * s ^ (-κ - 1)) s ∧
      -κ * s ^ (-κ - 1) + κ / s * s ^ (-κ) = 0 := by
  constructor
  · simpa using Real.hasDerivAt_rpow_const (p := -κ) (Or.inl hs.ne')
  · rw [Real.rpow_sub_one hs.ne']
    field_simp

/-- G = s^{κ} は −G′ + (κ/s)G = 0 を満たす(s > 0) -/
theorem endpoint_G (κ s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => s ^ κ) (κ * s ^ (κ - 1)) s ∧
      -(κ * s ^ (κ - 1)) + κ / s * s ^ κ = 0 := by
  constructor
  · exact Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  · rw [Real.rpow_sub_one hs.ne']
    field_simp

/-- κ = 1/2:∫_ε^1 s^{−1} ds = log(1/ε) → ∞(ε → 0+) -/
theorem not_L2_half :
    Tendsto (fun ε : ℝ => ∫ s in ε..1, s⁻¹) (𝓝[>] 0) atTop := by
  have h : ∀ ε : ℝ, 0 < ε → ∫ s in ε..1, s⁻¹ = -log ε := by
    intro ε hε
    rw [integral_inv_of_pos hε one_pos, log_div one_ne_zero hε.ne', log_one, zero_sub]
  have hlog : Tendsto (fun ε : ℝ => -log ε) (𝓝[>] 0) atTop := by
    have := tendsto_log_nhdsWithin_zero.mono_left (nhdsWithin_mono 0 (fun x (hx : 0 < x) => hx.ne'))
    exact tendsto_neg_atBot_atTop.comp this
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (h ε hε).symm

/-- κ > 1/2:∫_ε^1 s^{−2κ} ds = ((1/ε)^{2κ−1} − 1)/(2κ − 1) → ∞(ε → 0+) -/
theorem not_L2_gt (κ : ℝ) (hκ : 1 / 2 < κ) :
    Tendsto (fun ε : ℝ => ∫ s in ε..1, s ^ (-2 * κ)) (𝓝[>] 0) atTop := by
  have hp : 0 < 2 * κ - 1 := by linarith
  have h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∫ s in ε..1, s ^ (-2 * κ) = ((ε⁻¹) ^ (2 * κ - 1) - 1) / (2 * κ - 1) := by
    intro ε hε hε1
    have h0 : (0 : ℝ) ∉ Set.uIcc ε 1 := by
      rw [Set.uIcc_of_le hε1.le]; intro h0; linarith [h0.1]
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), one_rpow]
    have : -2 * κ + 1 = -(2 * κ - 1) := by ring
    rw [this, Real.rpow_neg hε.le, ← Real.inv_rpow hε.le, div_neg, ← neg_div, neg_sub]
  have hlim : Tendsto (fun ε : ℝ => ((ε⁻¹) ^ (2 * κ - 1) - 1) / (2 * κ - 1)) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (2 * κ - 1)) (𝓝[>] 0) atTop :=
      (tendsto_rpow_atTop hp).comp tendsto_inv_zero_atTop
    exact (tendsto_atTop_add_const_right _ (-1) h1).atTop_div_const hp
  refine hlim.congr' ?_
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0 := Ioo_mem_nhdsWithin_Ioi' one_pos
  filter_upwards [hmem] with ε hε
  rw [h ε hε.1 hε.2]

/-! ### α-VII.4 (Z28-d) 99/250 -/

private lemma ii (n : ℕ) (a b : ℝ) : IntervalIntegrable (fun x : ℝ => x ^ n) MeasureTheory.volume a b :=
  (continuous_pow n).intervalIntegrable a b

/-- Beta(2,3) の正規化:∫₀¹ x(1 − x)² dx = 1/12(= B(2,3)) -/
theorem beta23 : ∫ x in (0 : ℝ)..1, x * (1 - x) ^ 2 = 1 / 12 := by
  have e : (fun x : ℝ => x * (1 - x) ^ 2) = fun x => x ^ 1 - 2 * x ^ 2 + x ^ 3 := by
    funext x; ring
  rw [e, integral_add ((ii 1 0 1).sub ((ii 2 0 1).const_mul 2)) (ii 3 0 1),
    integral_sub (ii 1 0 1) ((ii 2 0 1).const_mul 2), integral_const_mul,
    integral_pow, integral_pow, integral_pow]
  norm_num

/-- E[X] = 12 ∫₀¹ x · x(1 − x)² dx = 2/5 -/
theorem beta23_m1 : 12 * ∫ x in (0 : ℝ)..1, x * (x * (1 - x) ^ 2) = 2 / 5 := by
  have e : (fun x : ℝ => x * (x * (1 - x) ^ 2)) = fun x => x ^ 2 - 2 * x ^ 3 + x ^ 4 := by
    funext x; ring
  rw [e, integral_add ((ii 2 0 1).sub ((ii 3 0 1).const_mul 2)) (ii 4 0 1),
    integral_sub (ii 2 0 1) ((ii 3 0 1).const_mul 2), integral_const_mul,
    integral_pow, integral_pow, integral_pow]
  norm_num

/-- E[X²] = 12 ∫₀¹ x² · x(1 − x)² dx = 1/5 -/
theorem beta23_m2 : 12 * ∫ x in (0 : ℝ)..1, x ^ 2 * (x * (1 - x) ^ 2) = 1 / 5 := by
  have e : (fun x : ℝ => x ^ 2 * (x * (1 - x) ^ 2)) = fun x => x ^ 3 - 2 * x ^ 4 + x ^ 5 := by
    funext x; ring
  rw [e, integral_add ((ii 3 0 1).sub ((ii 4 0 1).const_mul 2)) (ii 5 0 1),
    integral_sub (ii 3 0 1) ((ii 4 0 1).const_mul 2), integral_const_mul,
    integral_pow, integral_pow, integral_pow]
  norm_num

/-- A = Var X = 1/25、n = 9、k = 2、L_k = 20 の摂動公式で λ₂ = −207/500、係数 = 99/250 -/
theorem z28d_coefficient :
    let m1 : ℚ := 2 / 5
    let m2 : ℚ := 1 / 5
    let A := m2 - m1 ^ 2
    let n : ℚ := 9
    let k : ℚ := 2
    let Lk := k * (k + n - 1)
    let lam2 := -(n ^ 2 * (n - 1)) / (4 * Lk) * A - n / 4 * A
    let coef := n * (n - 1) / 4 * (1 - n / Lk) * A
    A = 1 / 25 ∧ Lk = 20 ∧ lam2 = -207 / 500 ∧ coef = 99 / 250 ∧ n ^ 2 / 4 * A + lam2 = coef := by
  norm_num

end CFT.AlphaIntegrals
