/-
  α-VII.4(Z28-d)の入力を定理に置き換える

  AlphaVII_Z28d の z28d_second は次を仮定に置いていた:
    (i)   D(fψ) = (n/2)fψ + df·ψ、D(df·ψ) = L fψ − ((n−2)/2) df·ψ
    (ii)  ⟨fψ, df·ψ⟩ = 0、固有空間で ⟨fψ, k⟩ = 0、⟨fψ, fψ⟩ = A
    (iii) X = |y_H|² が S⁹ 上で Beta(2, 3) に従う(A = Var X = 1/25)
    (iv)  ρ = 1 が楕円体族に沿った局所最小であること(係数 99/250 > 0 から)
  A. Clifford 代数(環 𝒜 の元 e_i、e_i e_j + e_j e_i = −2δ_ij):
    * clifford_sq_one、clifford_sq:e_i² = −1、Σ e_i e_i = −n
    * clifford_sandwich:Σ_i e_i v e_i = (n − 2) v(v = Σ v_j e_j)
    * clifford_hessian:H が対称なら Σ_ij H_ij e_i e_j = −(tr H)
    * dirac_killing:Killing スピノル ∇_iψ = c e_i ψ と Leibniz 則 D(Vψ) = Σ e_i(∇_iV)ψ + Σ e_i V ∇_iψ から
      Dψ = −nc ψ、D(df·ψ) = −(tr Hess f)ψ + c(n − 2) df·ψ
    * dirac_input:c = −½(Dψ = (n/2)ψ)、Δf = −tr Hess f = L f で D(df·ψ) = L fψ − ((n−2)/2) df·ψ。入力 (i) の後半
      (前半 D(fψ) = df·ψ + f Dψ は Dirac 作用素の Leibniz 則そのもの)
  B. 内積:
    * skew_cross:Clifford 積が歪対称なら ⟨ψ, Xψ⟩ = 0(交差項が消える、各点で)
    * killing_inner_const:同じ定数の Killing スピノルでは ∂⟨ψ, φ⟩ = 0(⟨ψ, φ⟩ は定数)。
      したがって ⟨fψ, φ⟩ = ⟨ψ, φ⟩∫f = 0、⟨fψ, fψ⟩ = |ψ|²∫f²
  C. S⁹ ⊂ R⁴ ⊕ R⁶ の上の分布 (iii):
    * join_metric:y = (cos θ ω, sin θ η)(ω ∈ S³、η ∈ S⁵)で |dy|² = dθ² + cos²θ|dω|² + sin²θ|dη|²
    * join_volume:体積要素 √(cos⁶θ sin¹⁰θ) = cos³θ sin⁵θ(0 ≤ θ ≤ π/2)
    * beta_substitution:∫₀^{π/2} g(cos²θ) cos³θ sin⁵θ dθ = ½∫₀¹ g(x) x(1 − x)² dx(連続な g すべて)。
      X = cos²θ = |y_H|² は Beta(2, 3)
    * sphere_moments:∫cos³ sin⁵ = 1/24、E[X] = 2/5、E[X²] = 1/5
    * mean_variance:f = X − 2/5 で E[f] = 0、E[f²] = 1/25 = A
  D. 局所最小 (iv):
    * local_min_of_quadratic:f(t) = f(0) + c t² + o(t²)、c > 0 なら 0 の近くで f(t) ≥ f(0)
    * z28d_local_min:係数 99/250 から ρ = 1(t = 0)は局所最小(大域的な主張はしない)
  外部に残るもの:S⁹ の Killing スピノルの存在と、固有値 n/2 の固有空間が Killing スピノルで張られること(Bär)、
  Dirac 作用素の Leibniz 則、球面の測度を極座標で書く公式(join_metric と join_volume は被積分関数を確かめる)、
  固有値の解析的な摂動(o(t²) の形の展開が存在すること)、楕円体族と共形族の二次係数の一致(台帳の論証)。
-/
import CFT.AlphaIntegrals
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals

open Real intervalIntegral Filter Topology Asymptotics

namespace CFT.Z28Input

section Clifford
variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℝ 𝒜] {n : ℕ} (e : Fin n → 𝒜)
  (hcl : ∀ i j, e i * e j + e j * e i = if i = j then -2 else 0)
include hcl

theorem clifford_sq_one (i : Fin n) : e i * e i = -1 := by
  have h := hcl i i
  simp only [if_true] at h
  have hx : e i * e i = (1 / 2 : ℝ) • (e i * e i + e i * e i) := by
    rw [← two_smul ℝ (e i * e i), smul_smul]; norm_num
  rw [hx, h, show (-2 : 𝒜) = (-2 : ℝ) • (1 : 𝒜) by rw [Algebra.smul_def, mul_one, map_neg, map_ofNat], smul_smul]
  norm_num

theorem clifford_sq : ∑ i, e i * e i = -(n : 𝒜) := by
  simp [clifford_sq_one e hcl]

theorem sandwich_basis (i j : Fin n) : e i * e j * e i = e j + (if i = j then -2 else 0) * e i := by
  have : e i * e j = (if i = j then -2 else 0) - e j * e i := by rw [← hcl i j]; abel
  rw [this, sub_mul, mul_assoc (e j), clifford_sq_one e hcl]
  noncomm_ring

theorem sandwich_sum (j : Fin n) : ∑ i, e i * e j * e i = ((n : ℝ) - 2) • e j := by
  simp only [sandwich_basis e hcl, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
  simp only [if_true]
  rw [sub_smul, Nat.cast_smul_eq_nsmul, two_smul, show (-2 : 𝒜) * e j = -(e j + e j) by noncomm_ring]
  abel

theorem clifford_sandwich (v : Fin n → ℝ) :
    ∑ i, e i * (∑ j, v j • e j) * e i = ((n : ℝ) - 2) • ∑ j, v j • e j := by
  have : ∀ i, e i * (∑ j, v j • e j) * e i = ∑ j, v j • (e i * e j * e i) := by
    intro i; rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul_comm, smul_mul_assoc]
  simp only [this]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.smul_sum, sandwich_sum e hcl, smul_comm]

theorem clifford_hessian (H : Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∑ i, ∑ j, H i j • (e i * e j) = -(∑ i, H i i) • (1 : 𝒜) := by
  have h2 : (2 : ℝ) • ∑ i, ∑ j, H i j • (e i * e j) = ∑ i, ∑ j, H i j • (e i * e j + e j * e i) := by
    rw [two_smul]
    conv_lhs => arg 2; rw [Finset.sum_comm]
    simp only [← Finset.sum_add_distrib, smul_add]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hH j i]
  simp only [hcl] at h2
  have h3 : ∑ i, ∑ j, H i j • (if i = j then (-2 : 𝒜) else 0) = (2 : ℝ) • (-(∑ i, H i i) • (1 : 𝒜)) := by
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hm2 : (-2 : 𝒜) = (-2 : ℝ) • (1 : 𝒜) := by rw [Algebra.smul_def, mul_one, map_neg, map_ofNat]
    simp only [hm2, smul_smul, ← Finset.sum_smul]
    congr 1; rw [← Finset.sum_mul]; ring
  rw [h3] at h2
  exact smul_right_injective 𝒜 two_ne_zero h2

/-- Killing スピノルと Leibniz 則からの Dirac 作用素の値(スピノルは 𝒜 の元、Clifford 積は左からの積) -/
theorem dirac_killing (c : ℝ) (ψ : 𝒜) (v : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i) :
    (∑ i, e i * (c • (e i * ψ)) = (-(n : ℝ) * c) • ψ) ∧
    (∑ i, e i * ((∑ j, H i j • e j) * ψ + (∑ j, v j • e j) * (c • (e i * ψ)))
      = (-(∑ i, H i i)) • ψ + (c * ((n : ℝ) - 2)) • ((∑ j, v j • e j) * ψ)) := by
  constructor
  · have : ∑ i, e i * (c • (e i * ψ)) = c • ((∑ i, e i * e i) * ψ) := by
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_smul_comm, mul_assoc]
    rw [this, clifford_sq e hcl]
    rw [show (-(n : 𝒜)) * ψ = (-(n : ℝ)) • ψ by
      rw [neg_smul, neg_mul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]]
    rw [smul_smul]; congr 1; ring
  · simp only [mul_add, Finset.sum_add_distrib]
    have h1 : ∑ i, e i * ((∑ j, H i j • e j) * ψ) = (∑ i, ∑ j, H i j • (e i * e j)) * ψ := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_smul_comm, smul_mul_assoc]
    have h2 : ∑ i, e i * ((∑ j, v j • e j) * (c • (e i * ψ)))
        = c • ((∑ i, e i * (∑ j, v j • e j) * e i) * ψ) := by
      rw [Finset.sum_mul, Finset.smul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc]
    rw [h1, h2, clifford_hessian e hcl H hH, clifford_sandwich e hcl, smul_mul_assoc, one_mul,
      smul_mul_assoc, smul_smul]

/-- c = −½(Dψ = (n/2)ψ)、Δf = −tr Hess f = L·f のとき:D(df·ψ) = L fψ − ((n−2)/2) df·ψ(入力 (i)) -/
theorem dirac_input (ψ : 𝒜) (v : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i)
    (L fv : ℝ) (hΔ : -(∑ i, H i i) = L * fv) :
    (∑ i, e i * ((-1 / 2 : ℝ) • (e i * ψ)) = ((n : ℝ) / 2) • ψ) ∧
    (∑ i, e i * ((∑ j, H i j • e j) * ψ + (∑ j, v j • e j) * ((-1 / 2 : ℝ) • (e i * ψ)))
      = L • (fv • ψ) - (((n : ℝ) - 2) / 2) • ((∑ j, v j • e j) * ψ)) := by
  obtain ⟨h1, h2⟩ := dirac_killing e hcl (-1 / 2) ψ v H hH
  refine ⟨by rw [h1]; congr 1; ring, ?_⟩
  rw [h2, hΔ, show (((n:ℝ) - 2) / 2) = -(-1 / 2 * ((n:ℝ) - 2)) by ring, neg_smul, sub_neg_eq_add, smul_smul]

end Clifford

/-! ### B. 内積 -/

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 歪対称な T では ⟨x, Tx⟩ = 0(交差項 ⟨fψ, df·ψ⟩ = 0 の各点の形) -/
theorem skew_cross (T : E → E) (hT : ∀ x y, @inner ℝ E _ (T x) y = -@inner ℝ E _ x (T y)) (x : E) :
    @inner ℝ E _ x (T x) = 0 := by
  have h := hT x x
  rw [real_inner_comm] at h
  linarith

/-- 同じ定数 c の Killing スピノル:∂⟨ψ, φ⟩ = ⟨c Xψ, φ⟩ + ⟨ψ, c Xφ⟩ = 0(⟨ψ, φ⟩ は定数) -/
theorem killing_inner_const (T : E → E) (hT : ∀ x y, @inner ℝ E _ (T x) y = -@inner ℝ E _ x (T y))
    (c : ℝ) (ψ φ : E) :
    @inner ℝ E _ (c • T ψ) φ + @inner ℝ E _ ψ (c • T φ) = 0 := by
  rw [real_inner_smul_left, real_inner_smul_right, hT]; ring

end Inner

/-! ### C. S⁹ の上の |y_H|² の分布 -/

section Join
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- y = (cos θ ω, sin θ η) の線素:|dy|² = dθ² + cos²θ|dω|² + sin²θ|dη|² -/
theorem join_metric (θ dθ : ℝ) (ω dω : E₁) (η dη : E₂) (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1)
    (hω' : @inner ℝ E₁ _ ω dω = 0) (hη' : @inner ℝ E₂ _ η dη = 0) :
    ‖(-sin θ * dθ) • ω + cos θ • dω‖ ^ 2 + ‖(cos θ * dθ) • η + sin θ • dη‖ ^ 2
      = dθ ^ 2 + cos θ ^ 2 * ‖dω‖ ^ 2 + sin θ ^ 2 * ‖dη‖ ^ 2 := by
  rw [norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    hω', hη', hω, hη]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  have := sin_sq_add_cos_sq θ
  nlinarith [this]

/-- 体積要素 √det = cos³θ sin⁵θ(0 ≤ θ ≤ π/2) -/
theorem join_volume (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    √(cos θ ^ 6 * sin θ ^ 10) = cos θ ^ 3 * sin θ ^ 5 := by
  have hc : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩
  have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])
  rw [show cos θ ^ 6 * sin θ ^ 10 = (cos θ ^ 3 * sin θ ^ 5) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

end Join

/-- X = cos²θ への変数変換:∫₀^{π/2} g(cos²θ) cos³θ sin⁵θ dθ = ½∫₀¹ g(x) x(1 − x)² dx -/
theorem beta_substitution (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ θ in (0 : ℝ)..(π / 2), g (cos θ ^ 2) * (cos θ ^ 3 * sin θ ^ 5)
      = (1 / 2) * ∫ x in (0 : ℝ)..1, g x * (x * (1 - x) ^ 2) := by
  set h : ℝ → ℝ := fun x => g x * (x * (1 - x) ^ 2) / 2 with hh
  have hcont : Continuous h := by simp only [hh]; fun_prop
  have hder : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      HasDerivAt (fun θ => cos θ ^ 2) (-(2 * cos θ * sin θ)) θ := by
    intro θ _
    have := (hasDerivAt_cos θ).pow 2
    convert this using 1; push_cast; ring
  have hsub := intervalIntegral.integral_comp_mul_deriv hder
    (by apply Continuous.continuousOn; fun_prop) hcont
  simp only [Function.comp, cos_zero, cos_pi_div_two] at hsub
  have e1 : ∀ θ, h (cos θ ^ 2) * (-(2 * cos θ * sin θ)) = -(g (cos θ ^ 2) * (cos θ ^ 3 * sin θ ^ 5)) := by
    intro θ; simp only [hh]
    have : 1 - cos θ ^ 2 = sin θ ^ 2 := by rw [← sin_sq_add_cos_sq θ]; ring
    rw [this]; ring
  simp only [e1, intervalIntegral.integral_neg] at hsub
  rw [show ((0:ℝ) ^ 2) = 0 by norm_num, one_pow, intervalIntegral.integral_symm 0 1] at hsub
  have : ∫ θ in (0 : ℝ)..(π / 2), g (cos θ ^ 2) * (cos θ ^ 3 * sin θ ^ 5) = ∫ x in (0 : ℝ)..1, h x := by
    linarith
  rw [this, hh, intervalIntegral.integral_div]; ring

/-- 正規化した S⁹ の上の期待値:E[g(X)] = 12 ∫₀¹ g(x) x(1 − x)² dx(全体の質量 ∫cos³ sin⁵ = 1/24) -/
theorem sphere_moments :
    (∫ θ in (0 : ℝ)..(π / 2), cos θ ^ 3 * sin θ ^ 5) = 1 / 24 ∧
    24 * (∫ θ in (0 : ℝ)..(π / 2), cos θ ^ 2 * (cos θ ^ 3 * sin θ ^ 5)) = 2 / 5 ∧
    24 * (∫ θ in (0 : ℝ)..(π / 2), (cos θ ^ 2) ^ 2 * (cos θ ^ 3 * sin θ ^ 5)) = 1 / 5 := by
  have h0 := beta_substitution (fun _ => 1) continuous_const
  have h1 := beta_substitution (fun x => x) continuous_id
  have h2 := beta_substitution (fun x => x ^ 2) (continuous_pow 2)
  simp only [one_mul] at h0
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, CFT.AlphaIntegrals.beta23]; norm_num
  · rw [h1]; have := CFT.AlphaIntegrals.beta23_m1; linarith
  · rw [h2]; have := CFT.AlphaIntegrals.beta23_m2; linarith

/-- f = X − 2/5 は平均 0、分散 1/25 = A(入力 ⟨fψ, k⟩ = 0 と ⟨fψ, fψ⟩ = A の出所) -/
theorem mean_variance (m0 m1 m2 : ℝ) (h0 : m0 = 1) (h1 : m1 = 2 / 5) (h2 : m2 = 1 / 5) :
    m1 - (2 / 5) * m0 = 0 ∧ m2 - 2 * (2 / 5) * m1 + (2 / 5) ^ 2 * m0 = 1 / 25 := by
  subst h0 h1 h2; norm_num

/-! ### D. 局所最小 -/

/-- f(t) = f(0) + c t² + o(t²)、c > 0 なら t = 0 の近くで f(t) ≥ f(0) -/
theorem local_min_of_quadratic (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : (fun t => f t - f 0 - c * t ^ 2) =o[𝓝 0] (fun t => t ^ 2)) :
    ∀ᶠ t in 𝓝 0, f 0 ≤ f t := by
  have := hf.def (half_pos hc)
  filter_upwards [this] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at ht
  have := (abs_le.mp ht).1
  nlinarith [sq_nonneg t]

/-- Z28-d:正規化した最低固有値の二次係数 99/250 > 0 なので、ρ = 1(t = 0)は楕円体族に沿った局所最小 -/
theorem z28d_local_min (Λ : ℝ → ℝ)
    (hΛ : (fun t => Λ t - Λ 0 - (99 / 250) * t ^ 2) =o[𝓝 0] (fun t => t ^ 2)) :
    ∀ᶠ t in 𝓝 0, Λ 0 ≤ Λ t :=
  local_min_of_quadratic Λ (99 / 250) (by norm_num) hΛ

/-! ### E. 楕円体族の一次の接方向 -/

/-- 楕円体 (ρ y_H, y₆)(ρ = 1 + t)の誘導計量の一次の変化は h = 2Σ_{a∈H} dy_a ⊗ dy_a。
  球面の座標関数は Hess y_a = −y_a g(入力、S⁹ ⊂ R¹⁰ の第二基本形式)、Leibniz 則
  Hess(y_a²/2) = dy_a ⊗ dy_a + y_a Hess y_a のもとで
    Σ dy_a ⊗ dy_a = Hess(X/2) + X g = ½ L_{∇X/2} g + (f + 2/5) g(X = |y_H|²、f = X − 2/5)。
  つまり一次では、楕円体族の接方向 = 微分同相(Lie 微分)+ 共形変形 f + 全体のスケール 2/5。
  二次係数が共形族と一致することは、規格化した固有値の汎関数が丸い S⁹ で臨界的で微分同相で
  不変であることから従う(台帳の論証、ここでは扱わない) -/
theorem ellipsoid_tangent {m : ℕ} (y : Fin 4 → ℝ) (dyy Hy Hsq : Fin 4 → Matrix (Fin m) (Fin m) ℝ)
    (g : Matrix (Fin m) (Fin m) ℝ)
    (hsphere : ∀ a, Hy a = -(y a) • g) (hleib : ∀ a, Hsq a = dyy a + y a • Hy a) :
    ∑ a, dyy a = ∑ a, Hsq a + (∑ a, y a ^ 2) • g := by
  have h : ∀ a, dyy a = Hsq a + (y a ^ 2) • g := by
    intro a; rw [hleib, hsphere, smul_smul, sq, mul_neg, neg_smul]; abel
  rw [Finset.sum_smul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => h a)

end CFT.Z28Input
