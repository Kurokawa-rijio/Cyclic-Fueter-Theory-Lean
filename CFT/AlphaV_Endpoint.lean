/-
  α-V.5(Z29)の残り:端点の漸近形の摂動評価(主要項 s^{∓κ} から実際の解へ)

  動径 Dirac 方程式(端点 s = 0 の近く、0 < s ≤ δ ≤ 1):
    F′ + (κ/s)F = p(s) G、 −G′ + (κ/s)G = q(s) F、|p|, |q| ≤ B
  (p = q = 0 が AlphaIntegrals の主要項:F = s^{−κ}、G = s^κ。p, q はエネルギー・質量・ゲージ場・
   曲率の正則な部分をまとめたもの)
  置き換え x = s^κ F、y = s^κ G で
    * xy_system:x′ = p y、y′ = (2κ/s) y − q x
    * norm_deriv:N = x² + y² は N′ = 2(p − q)xy + (4κ/s)y² ≥ −2B N
    * norm_bound:すべての解で x(s)² + y(s)² ≤ e^{2Bδ}(x(δ)² + y(δ)²)(0 < s ≤ δ)。
      したがって |F|, |G| ≤ C s^{−κ}:主要項より悪くならない
    * large_solution:x(δ) = 1、y(δ) = 0 の解は、Bδ ≤ 1/8 なら全区間で x ≥ 3/4、
      つまり F ≥ (3/4) s^{−κ}:主要項 s^{−κ} と同じ漸近形
    * large_not_L2:κ ≥ 1/2 なら、この解は ∫_ε^δ F² → ∞(ε → 0+):L² でない
  Weyl の交代定理(limit circle ⇔ 端点の近くですべての解が L²)により、L² でない解が一つあれば
  s = 0 は limit point(Dirac 作用素はこの端点で境界条件なしに本質的自己共役)。
  外部に残るもの:線形 ODE の解の存在(δ での初期値 (x, y) = (1, 0) に対して、連続係数の線形系の
  標準定理)と、Weyl の交代定理そのもの(定義と標準の定理)。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.MeanValue

open Real Set Filter Topology intervalIntegral

namespace CFT.Endpoint

variable (κ B δ : ℝ) (F G p q : ℝ → ℝ)

/-- x = s^κ F、y = s^κ G の満たす方程式 -/
theorem xy_system (s : ℝ) (hs : 0 < s) (F' G' : ℝ)
    (hF : HasDerivAt F F' s) (hG : HasDerivAt G G' s)
    (eF : F' = -(κ / s) * F s + p s * G s) (eG : G' = (κ / s) * G s - q s * F s) :
    HasDerivAt (fun s => s ^ κ * F s) (p s * (s ^ κ * G s)) s ∧
      HasDerivAt (fun s => s ^ κ * G s) ((2 * κ / s) * (s ^ κ * G s) - q s * (s ^ κ * F s)) s := by
  have hp := Real.hasDerivAt_rpow_const (p := κ) (Or.inl hs.ne')
  have e : s ^ (κ - 1) = s ^ κ / s := Real.rpow_sub_one hs.ne' κ
  constructor
  · convert hp.mul hF using 1; rw [eF, e]; field_simp; ring
  · convert hp.mul hG using 1; rw [eG, e]; field_simp; ring

/-- N′ ≥ −2B N の形の評価(各点の代数) -/
theorem norm_deriv_ge (x y pv qv s : ℝ) (hs : 0 < s) (hκ : 0 ≤ κ)
    (hpB : |pv| ≤ B) (hqB : |qv| ≤ B) :
    -(2 * B) * (x ^ 2 + y ^ 2) ≤ 2 * x * (pv * y) + 2 * y * ((2 * κ / s) * y - qv * x) := by
  have h1 : 0 ≤ (4 * κ / s) * y ^ 2 := by positivity
  have hpq : |pv - qv| ≤ 2 * B := by
    calc |pv - qv| ≤ |pv| + |qv| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hxy : |2 * (pv - qv) * (x * y)| ≤ 2 * B * (x ^ 2 + y ^ 2) := by
    rw [abs_mul, abs_mul, abs_two]
    have : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
    have hB : 0 ≤ B := le_trans (abs_nonneg _) hpB
    calc 2 * |pv - qv| * |x * y| ≤ 2 * (2 * B) * ((x ^ 2 + y ^ 2) / 2) := by
          apply mul_le_mul (by linarith) this (abs_nonneg _) (by linarith)
      _ = 2 * B * (x ^ 2 + y ^ 2) := by ring
  have e : 2 * x * (pv * y) + 2 * y * ((2 * κ / s) * y - qv * x)
      = 2 * (pv - qv) * (x * y) + (4 * κ / s) * y ^ 2 := by field_simp; ring
  rw [e]
  have := (abs_le.mp hxy).1
  linarith

section
variable (hκ : 1 / 2 ≤ κ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
  (hp : ∀ s ∈ Ioc 0 δ, |p s| ≤ B) (hq : ∀ s ∈ Ioc 0 δ, |q s| ≤ B)
  (F' G' : ℝ → ℝ)
  (hF : ∀ s ∈ Ioc 0 δ, HasDerivAt F (F' s) s) (hG : ∀ s ∈ Ioc 0 δ, HasDerivAt G (G' s) s)
  (eF : ∀ s ∈ Ioc 0 δ, F' s = -(κ / s) * F s + p s * G s)
  (eG : ∀ s ∈ Ioc 0 δ, G' s = (κ / s) * G s - q s * F s)

/-- x = s^κ F -/
noncomputable def xf (s : ℝ) : ℝ := s ^ κ * F s

include hκ hδ0 hp hq hF hG eF eG in
/-- すべての解で x² + y² ≤ e^{2B(δ − s)}(x(δ)² + y(δ)²) -/
theorem norm_bound (s : ℝ) (hs : s ∈ Ioc 0 δ) :
    xf κ F s ^ 2 + xf κ G s ^ 2 ≤ exp (2 * B * (δ - s)) * (xf κ F δ ^ 2 + xf κ G δ ^ 2) := by
  set N : ℝ → ℝ := fun s => exp (2 * B * s) * (xf κ F s ^ 2 + xf κ G s ^ 2) with hN
  have hder : ∀ s ∈ Ioc 0 δ, HasDerivAt N (exp (2 * B * s) * (2 * B * (xf κ F s ^ 2 + xf κ G s ^ 2)
      + (2 * xf κ F s * (p s * xf κ G s) + 2 * xf κ G s * ((2 * κ / s) * xf κ G s - q s * xf κ F s)))) s := by
    intro s hs
    obtain ⟨hx, hy⟩ := xy_system κ F G p q s hs.1 (F' s) (G' s) (hF s hs) (hG s hs) (eF s hs) (eG s hs)
    have he : HasDerivAt (fun s => exp (2 * B * s)) (exp (2 * B * s) * (2 * B)) s := by
      have := ((hasDerivAt_id s).const_mul (2 * B)).exp
      simpa [mul_comm] using this
    have := he.mul ((hx.pow 2).add (hy.pow 2))
    convert this using 1
    simp only [xf]; push_cast; ring
  have hmono : MonotoneOn N (Ioc 0 δ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 δ)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioc] at hs
      exact (hder s (Ioo_subset_Ioc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ioc] at hs
      have hs' := Ioo_subset_Ioc_self hs
      have := norm_deriv_ge κ B (xf κ F s) (xf κ G s) (p s) (q s) s hs.1 (by linarith) (hp s hs') (hq s hs')
      apply mul_nonneg (exp_pos _).le
      linarith
  have hδ : δ ∈ Ioc 0 δ := ⟨hδ0, le_rfl⟩
  have := hmono hs hδ hs.2
  simp only [hN] at this
  have e : exp (2 * B * (δ - s)) = exp (2 * B * δ) / exp (2 * B * s) := by
    rw [← exp_sub]; ring_nf
  rw [e, div_mul_eq_mul_div, le_div_iff₀ (exp_pos _)]
  linarith

include hκ hδ0 hp hq hF hG eF eG in
/-- 大きい解:x(δ) = 1、y(δ) = 0、Bδ ≤ 1/8 なら全区間で x ≥ 3/4 -/
theorem large_solution (hB : B * δ ≤ 1 / 8) (hx1 : xf κ F δ = 1) (hy0 : xf κ G δ = 0)
    (s : ℝ) (hs : s ∈ Ioc 0 δ) : 3 / 4 ≤ xf κ F s := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hp δ ⟨hδ0, le_rfl⟩)
  -- |y| ≤ 2 on (0, δ]
  have hy : ∀ t ∈ Ioc 0 δ, |xf κ G t| ≤ 2 := by
    intro t ht
    have h := norm_bound κ B δ F G p q hκ hδ0 hp hq F' G' hF hG eF eG t ht
    rw [hx1, hy0] at h
    have h2 : exp (2 * B * (δ - t)) ≤ exp (1 / 4) := by
      apply exp_le_exp.mpr; nlinarith [ht.1, ht.2]
    have h3 : exp (1 / 4 : ℝ) ≤ 2 := by
      have h4 := Real.add_one_le_exp (-(1 / 4 : ℝ))
      have h5 : exp (1 / 4 : ℝ) * exp (-(1 / 4 : ℝ)) = 1 := by rw [← exp_add]; norm_num
      nlinarith [exp_pos (1 / 4 : ℝ), exp_pos (-(1 / 4 : ℝ))]
    have : xf κ G t ^ 2 ≤ 4 := by nlinarith [sq_nonneg (xf κ F t)]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (xf κ G t + 2), sq_nonneg (xf κ G t - 2)]
  -- 平均値の評価:|x(δ) − x(s)| ≤ 2B(δ − s)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := xf κ F)
    (f' := fun t => p t * xf κ G t) (C := 2 * B) (a := s) (b := δ)
    (fun t ht => ((xy_system κ F G p q t (lt_of_lt_of_le hs.1 ht.1) (F' t) (G' t)
      (hF t ⟨lt_of_lt_of_le hs.1 ht.1, ht.2⟩) (hG t ⟨lt_of_lt_of_le hs.1 ht.1, ht.2⟩)
      (eF t ⟨lt_of_lt_of_le hs.1 ht.1, ht.2⟩) (eG t ⟨lt_of_lt_of_le hs.1 ht.1, ht.2⟩)).1).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Ioc 0 δ := ⟨lt_of_lt_of_le hs.1 ht.1, ht.2.le⟩
      rw [Real.norm_eq_abs, abs_mul]
      calc |p t| * |xf κ G t| ≤ B * 2 := mul_le_mul (hp t ht') (hy t ht') (abs_nonneg _) hB0
        _ = 2 * B := by ring)
    δ ⟨hs.2, le_rfl⟩
  rw [Real.norm_eq_abs, hx1] at hmvt
  have := (abs_le.mp hmvt).2
  have h8 : B * (δ - s) ≤ 1 / 8 := by nlinarith [mul_nonneg hB0 hs.1.le]
  linarith

include hκ hδ0 hδ1 hp hq hF hG eF eG in
/-- κ ≥ 1/2 なら、大きい解は L² でない:∫_ε^δ F² → ∞(ε → 0+) -/
theorem large_not_L2 (hB : B * δ ≤ 1 / 8) (hx1 : xf κ F δ = 1) (hy0 : xf κ G δ = 0) :
    Tendsto (fun ε => ∫ s in ε..δ, F s ^ 2) (𝓝[>] 0) atTop := by
  -- 下からの評価 F² ≥ (9/16)/s
  have hlow : ∀ s ∈ Ioc 0 δ, (9 / 16) * s⁻¹ ≤ F s ^ 2 := by
    intro s hs
    have hx := large_solution κ B δ F G p q hκ hδ0 hp hq F' G' hF hG eF eG hB hx1 hy0 s hs
    simp only [xf] at hx
    have hs0 := hs.1
    have hsk : 0 < s ^ κ := rpow_pos_of_pos hs0 κ
    -- s^{2κ} ≤ s (s ≤ 1、2κ ≥ 1)
    have hs1 : s ≤ 1 := le_trans hs.2 hδ1
    have h2k : s ^ κ * s ^ κ ≤ s := by
      rw [← rpow_add hs0]
      calc s ^ (κ + κ) ≤ s ^ (1 : ℝ) := rpow_le_rpow_of_exponent_ge hs0 hs1 (by linarith)
        _ = s := rpow_one s
    have hsq : (9 / 16) ≤ (s ^ κ * F s) ^ 2 := by nlinarith
    rw [mul_pow] at hsq
    rw [← div_eq_mul_inv, div_le_iff₀ hs0]
    have : (9 / 16) ≤ (s ^ κ) ^ 2 * F s ^ 2 := hsq
    nlinarith [sq_nonneg (F s), sq_nonneg (s ^ κ)]
  have hcont : ∀ ε ∈ Ioo 0 δ, ContinuousOn (fun s => F s ^ 2) (Icc ε δ) := by
    intro ε hε s hs
    exact ((hF s ⟨lt_of_lt_of_le hε.1 hs.1, hs.2⟩).continuousAt.pow 2).continuousWithinAt
  have hge : ∀ ε ∈ Ioo 0 δ, (9 / 16) * (log δ - log ε) ≤ ∫ s in ε..δ, F s ^ 2 := by
    intro ε hε
    have hint : ∫ s in ε..δ, (9 / 16) * s⁻¹ = (9 / 16) * (log δ - log ε) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hε.1 hδ0, log_div hδ0.ne' hε.1.ne']
    rw [← hint]
    apply intervalIntegral.integral_mono_on hε.2.le
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hε.2.le]
      exact continuousOn_const.mul (continuousOn_inv₀.mono (fun s hs => (lt_of_lt_of_le hε.1 hs.1).ne'))
    · apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hε.2.le]; exact hcont ε hε
    · intro s hs; exact hlow s ⟨lt_of_lt_of_le hε.1 hs.1, hs.2⟩
  have hlog : Tendsto (fun ε : ℝ => (9 / 16) * (log δ - log ε)) (𝓝[>] 0) atTop := by
    have h1 := tendsto_log_nhdsWithin_zero.mono_left (nhdsWithin_mono 0 (fun x (hx : 0 < x) => hx.ne'))
    have h2 : Tendsto (fun ε : ℝ => log δ - log ε) (𝓝[>] 0) atTop :=
      (tendsto_atTop_add_const_left (𝓝[>] 0) (log δ) (tendsto_neg_atBot_atTop.comp h1)).congr
        (fun ε => by simp [Function.comp, sub_eq_add_neg])
    exact h2.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlog
  have hmem : Ioo (0 : ℝ) δ ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hδ0
  filter_upwards [hmem] with ε hε
  exact hge ε hε

end

end CFT.Endpoint
