/-
  α-VII.1(Z24〜Z26):単極子の束と S³ 上の一様な Yang–Mills 場(座標表示での形式化)

  Z24(Dirac 量子化と Chern 数)。S² を北半球 U_N(θ < π)と南半球 U_S(θ > 0)で覆い、
    a_N = (N/2)(1 − cos θ) dφ、 a_S = −(N/2)(1 + cos θ) dφ
  とする。
    * 両者の差は a_N − a_S = N dφ(dirac_difference)。これは遷移関数 g = e^{iNφ} の −i g⁻¹dg
    * g が赤道で一価 ⇔ e^{2πiN} = 1 ⇔ N ∈ ℤ(dirac_quantization)
    * 曲率 f = da の dθ∧dφ 成分は両方の座標で (N/2) sin θ(curvature_N, curvature_S)
    * c₁ = (1/2π)∫_{S²} f = (1/2π)·2π·∫₀^π (N/2) sin θ dθ = N(chern_number)
    * 単極子の電荷を q = N/2 とすると c₁ = 2q(α-VII.7 の数え上げ 2|q| と同じ規約)
  Gauss–Bonnet(半径 r の球面):∫ K dA = ∫∫ r⁻²·r² sin θ dθdφ = 4π = 2πχ(S²)(gauss_bonnet_round)。

  Z25(S³ 上の一様な場 A = λ·(Maurer–Cartan))。左不変枠 [X_a, X_b] = −2ε_abc X_c、両側不変計量の
  Levi-Civita 接続 ∇_X Y = ½[X, Y] のもとで、左不変な 2 形式の発散は (∇^a F)_ab = Σ_a ε_abc F_ac。
  したがって YM 方程式 D^a F_ab = 0 は Σ_a([A_a, F_ab] + ε_abc F_ac) = 0。
    * 左辺 = 8iλ(1−λ)(2λ−1) s_b(ym_formula)
    * 解は λ = 0、1/2(メロン)、1 だけ(ym_roots)
  Z26(方向場 n とその作用)は、式が手元にないため未形式化。
-/
import CFT.AlphaV_A4
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Real

namespace CFT.Bundle

/-! ### Z24 Dirac 単極子 -/

/-- 北の座標での接続の dφ 成分 -/
noncomputable def aN (N θ : ℝ) : ℝ := N / 2 * (1 - cos θ)
/-- 南の座標での接続の dφ 成分 -/
noncomputable def aS (N θ : ℝ) : ℝ := -(N / 2) * (1 + cos θ)

theorem dirac_difference (N θ : ℝ) : aN N θ - aS N θ = N := by
  unfold aN aS; ring

/-- 遷移関数 e^{iNφ} が φ ↦ φ + 2π で一価 ⇔ N ∈ ℤ -/
theorem dirac_quantization (N : ℝ) :
    Complex.exp (Complex.I * N * (2 * π)) = 1 ↔ ∃ n : ℤ, N = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (N : ℂ) = n := by
      have h2 : (N : ℂ) * (2 * π * Complex.I) = n * (2 * π * Complex.I) := by
        rw [← hn]; ring
      exact mul_right_cancel₀ hpi h2
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

/-- 曲率 f = ∂_θ a_φ dθ∧dφ(北) -/
theorem curvature_N (N θ : ℝ) : HasDerivAt (aN N) (N / 2 * sin θ) θ := by
  have h := ((hasDerivAt_cos θ).const_sub 1).const_mul (N / 2)
  convert h using 1; ring

/-- 曲率(南)。両方の座標で同じ 2 形式 -/
theorem curvature_S (N θ : ℝ) : HasDerivAt (aS N) (N / 2 * sin θ) θ := by
  have h := ((hasDerivAt_cos θ).const_add 1).const_mul (-(N / 2))
  convert h using 1; ring

/-- c₁ = (1/2π) ∫₀^{2π} ∫₀^π (N/2) sin θ dθ dφ = N -/
theorem chern_number (N : ℝ) :
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, N / 2 * sin θ) = N := by
  rw [intervalIntegral.integral_const_mul, integral_sin, cos_zero, cos_pi]
  have h2 : (2 * π) ≠ 0 := by positivity
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]; ring

/-- 単極子の電荷 q = N/2 なら c₁ = 2q -/
theorem chern_eq_two_q (q : ℝ) :
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (2 * q) / 2 * sin θ) = 2 * q :=
  chern_number (2 * q)

/-- Gauss–Bonnet(半径 r の球面):∫∫ K dA = 4π = 2π χ(S²) -/
theorem gauss_bonnet_round (r : ℝ) (hr : r ≠ 0) :
    (2 * π) * ∫ θ in (0 : ℝ)..π, (1 / r ^ 2) * (r ^ 2 * sin θ) = 2 * π * 2 := by
  have e : ∀ θ : ℝ, (1 / r ^ 2) * (r ^ 2 * sin θ) = sin θ := by
    intro θ; field_simp
  simp only [e, integral_sin, cos_zero, cos_pi]
  ring

/-! ### Z25 S³ 上の一様な Yang–Mills 場 -/

open Matrix Complex CFT.A4

/-- YM 方程式の左辺 Σ_a([A_a, F_ab] + ε_abc F_ac) -/
noncomputable def YM (lam : ℝ) (b : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ a, (Ag lam a * F lam a b - F lam a b * Ag lam a + ∑ c, eps a b c • F lam a c)

set_option maxHeartbeats 0 in
theorem ym_formula (lam : ℝ) (b : Fin 3) :
    YM lam b = (8 * I * lam * (1 - lam) * (2 * lam - 1)) • s b := by
  simp only [YM, curvature_formula]
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Ag, s, σ, eps, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [I_sq, I_cubed]) <;> (try ring_nf) <;>
    (try simp [I_sq, I_cubed]) <;> (try ring)

/-- 一様な場の YM 方程式の解は λ = 0、1/2(メロン)、1 だけ -/
theorem ym_roots (lam : ℝ) : (∀ b, YM lam b = 0) ↔ lam = 0 ∨ lam = 1 / 2 ∨ lam = 1 := by
  have hs : s 0 0 1 = (1 / 2 : ℂ) := by simp [s, σ]
  constructor
  · intro h
    have h0 := congrFun (congrFun (h 0) 0) 1
    rw [ym_formula] at h0
    simp only [Matrix.smul_apply, smul_eq_mul, hs, Matrix.zero_apply] at h0
    have h1 : (lam : ℂ) * (1 - lam) * (2 * lam - 1) = 0 := by
      have hI : (8 * I * (1 / 2 : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero]
      have : (8 * I * (1 / 2 : ℂ)) * ((lam : ℂ) * (1 - lam) * (2 * lam - 1)) = 0 := by
        linear_combination h0
      exact (mul_eq_zero.mp this).resolve_left hI
    have h2 : lam * (1 - lam) * (2 * lam - 1) = 0 := by exact_mod_cast h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by linarith))
  · rintro (h | h | h) b <;> rw [ym_formula, h] <;> norm_num
end CFT.Bundle
