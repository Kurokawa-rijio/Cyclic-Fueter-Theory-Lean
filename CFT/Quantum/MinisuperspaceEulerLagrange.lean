import CFT.Quantum.MinisuperspaceVariation
import CFT.Spherical.CompletionNeckDynamics

/-!
  命題集 `LEAN_GAP_TREES.md` 1-2b/c/d（ゲージ Ṅ = 0、N は定数）：
  ミニスーパースペース Lagrangian `Lfun` の Euler–Lagrange 方程式を、
  ツリーで証明済みの偏微分（`L_ad`、`L_bd`、`L_a`、`L_b`）から組み立てる。
  さらに Hamilton 方程式との等価性（1-2d）：N·∂Hfun/∂q = −∂L/∂q（運動量に沿って）と
  Legendre 逆写像 N·∂Hfun/∂p_a = ȧ、N·∂Hfun/∂p_b = ḃ を代数恒等式として示し、
  EL = 0 ⟺ ṗ = −N ∂Hfun/∂q を得る。解いた形（b̈、ä の明示式）も系として含む。
  恒等式は sympy でも検証済み（`lean/demos/Gap12a_check.py`）。
-/

namespace CFT.Mini

/-- 共役運動量 p_a = ∂L/∂ȧ = −2cbḃ/N の軌道に沿った値。 -/
noncomputable def momA (a b : ℝ → ℝ) (N c : ℝ) (t : ℝ) : ℝ :=
  -2 * c * b t * deriv b t / N

/-- 共役運動量 p_b = ∂L/∂ḃ = −2c(aḃ + bȧ)/N の軌道に沿った値。 -/
noncomputable def momB (a b : ℝ → ℝ) (N c : ℝ) (t : ℝ) : ℝ :=
  -2 * c * (a t * deriv b t + b t * deriv a t) / N

theorem deriv_momA (a b : ℝ → ℝ) (N c : ℝ) (t : ℝ)
    (hb : Differentiable ℝ b) (hbb : Differentiable ℝ (deriv b)) :
    deriv (momA a b N c) t
      = -2 * c * (deriv b t * deriv b t + b t * deriv (deriv b) t) / N := by
  have hfun : momA a b N c = fun t => (-2 * c / N) * (b t * deriv b t) := by
    funext s; simp only [momA]; ring
  have hd : DifferentiableAt ℝ (fun t => b t * deriv b t) t := (hb t).mul (hbb t)
  rw [hfun, deriv_const_mul _ hd, deriv_mul (hb t) (hbb t)]
  ring

theorem deriv_momB (a b : ℝ → ℝ) (N c : ℝ) (t : ℝ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (haa : Differentiable ℝ (deriv a)) (hbb : Differentiable ℝ (deriv b)) :
    deriv (momB a b N c) t
      = -2 * c * (2 * (deriv a t * deriv b t) + a t * deriv (deriv b) t
          + b t * deriv (deriv a) t) / N := by
  have hfun : momB a b N c = fun t => (-2 * c / N) * (a t * deriv b t + b t * deriv a t) := by
    funext s; simp only [momB]; ring
  have hd1 : DifferentiableAt ℝ (fun t => a t * deriv b t) t := (ha t).mul (hbb t)
  have hd2 : DifferentiableAt ℝ (fun t => b t * deriv a t) t := (hb t).mul (haa t)
  rw [hfun, deriv_const_mul _ (hd1.add hd2), deriv_add hd1 hd2,
    deriv_mul (ha t) (hbb t), deriv_mul (hb t) (haa t)]
  ring

/-- 1-2b：EL_a の恒等式。左辺が d/dt p_a − ∂L/∂a（値は `L_a` のもの）。 -/
theorem eulerLagrange_a (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hb : Differentiable ℝ b) (hbb : Differentiable ℝ (deriv b))
    (hN : N ≠ 0) (hb0 : b t ≠ 0) :
    deriv (momA a b N c) t - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2))
      = c * (l ^ 2 * N / (b t) ^ 2 - N - 2 * b t * deriv (deriv b) t / N
          - deriv b t ^ 2 / N) := by
  rw [deriv_momA a b N c t hb hbb]
  field_simp
  ring

/-- 1-2c：EL_b の恒等式。左辺が d/dt p_b − ∂L/∂b（値は `L_b` のもの）。 -/
theorem eulerLagrange_b (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (haa : Differentiable ℝ (deriv a)) (hbb : Differentiable ℝ (deriv b))
    (hN : N ≠ 0) (hb0 : b t ≠ 0) :
    deriv (momB a b N c) t
        - (-2 * c * deriv a t * deriv b t / N + 2 * c * N * a t * l ^ 2 / (b t) ^ 3)
      = c * (-2 * l ^ 2 * N * a t / (b t) ^ 3 - 2 * a t * deriv (deriv b) t / N
          - 2 * b t * deriv (deriv a) t / N - 2 * deriv a t * deriv b t / N) := by
  rw [deriv_momB a b N c t ha hb haa hbb]
  field_simp
  ring

/-- 1-2d（代数部）：N·∂Hfun/∂a = −∂L/∂a（運動量に沿って。∂Hfun/∂a の値は `H_a` のもの）。 -/
theorem hamilton_a_value (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    N * (-c + c * l ^ 2 / (b t) ^ 2 + (momA a b N c t) ^ 2 / (4 * (b t) ^ 2 * c))
      = -(-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)) := by
  simp only [momA]
  field_simp
  ring

/-- 1-2d（代数部）：N·∂Hfun/∂b = −∂L/∂b（運動量に沿って。∂Hfun/∂b の値は `H_b` のもの）。 -/
theorem hamilton_b_value (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    N * ((-4 * a t * c ^ 2 * l ^ 2
        + (momA a b N c t) * (-(a t) * momA a b N c t + b t * momB a b N c t))
        / (2 * (b t) ^ 3 * c))
      = -(-2 * c * deriv a t * deriv b t / N
          + 2 * c * N * a t * l ^ 2 / (b t) ^ 3) := by
  simp only [momA, momB]
  field_simp
  ring

/-- 1-2d：EL_a = 0 ⟺ ṗ_a = −N·∂Hfun/∂a。 -/
theorem euler_iff_hamilton_a (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    deriv (momA a b N c) t - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)) = 0
      ↔ deriv (momA a b N c) t
        = -N * (-c + c * l ^ 2 / (b t) ^ 2
            + (momA a b N c t) ^ 2 / (4 * (b t) ^ 2 * c)) := by
  have hH := hamilton_a_value a b N c l t hN hc hb0
  constructor <;> intro h <;> linarith

/-- 1-2d：EL_b = 0 ⟺ ṗ_b = −N·∂Hfun/∂b。 -/
theorem euler_iff_hamilton_b (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    deriv (momB a b N c) t
        - (-2 * c * deriv a t * deriv b t / N + 2 * c * N * a t * l ^ 2 / (b t) ^ 3) = 0
      ↔ deriv (momB a b N c) t
        = -N * ((-4 * a t * c ^ 2 * l ^ 2
            + (momA a b N c t) * (-(a t) * momA a b N c t + b t * momB a b N c t))
            / (2 * (b t) ^ 3 * c)) := by
  have hH := hamilton_b_value a b N c l t hN hc hb0
  constructor <;> intro h <;> linarith

/-- 1-2d：Legendre 逆写像 N·∂Hfun/∂p_a = ȧ（∂Hfun/∂p_a の値は `H_pa` のもの）。 -/
theorem legendre_vel_a (a b : ℝ → ℝ) (N c : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    N * ((a t * momA a b N c t - b t * momB a b N c t) / (2 * (b t) ^ 2 * c))
      = deriv a t := by
  simp only [momA, momB]
  field_simp
  ring

/-- 1-2d：Legendre 逆写像 N·∂Hfun/∂p_b = ḃ（∂Hfun/∂p_b の値は `H_pb` のもの）。 -/
theorem legendre_vel_b (a b : ℝ → ℝ) (N c : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    N * (-(momA a b N c t) / (2 * b t * c)) = deriv b t := by
  simp only [momA]
  field_simp
  ring

/-- EL_a = 0 から解いた b̈ の明示式。 -/
theorem secondDeriv_b_of_euler_a (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hb : Differentiable ℝ b) (hbb : Differentiable ℝ (deriv b))
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0)
    (hEL : deriv (momA a b N c) t
      - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)) = 0) :
    deriv (deriv b) t
      = l ^ 2 * N ^ 2 / (2 * (b t) ^ 3) - N ^ 2 / (2 * b t)
        - deriv b t ^ 2 / (2 * b t) := by
  have hid : deriv (deriv b) t
        - (l ^ 2 * N ^ 2 / (2 * (b t) ^ 3) - N ^ 2 / (2 * b t)
          - deriv b t ^ 2 / (2 * b t))
      = -(N / (2 * b t * c)) * (deriv (momA a b N c) t
          - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2))) := by
    rw [eulerLagrange_a a b N c l t hb hbb hN hb0]
    field_simp
    ring
  rw [hEL] at hid
  simp at hid
  exact sub_eq_zero.mp hid

/-- EL_a = EL_b = 0 から解いた ä の明示式（b̈ の解を代入した形）。 -/
theorem secondDeriv_a_of_euler (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (haa : Differentiable ℝ (deriv a)) (hbb : Differentiable ℝ (deriv b))
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0)
    (hELa : deriv (momA a b N c) t
      - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)) = 0)
    (hELb : deriv (momB a b N c) t
      - (-2 * c * deriv a t * deriv b t / N
        + 2 * c * N * a t * l ^ 2 / (b t) ^ 3) = 0) :
    deriv (deriv a) t
      = -3 * l ^ 2 * N ^ 2 * a t / (2 * (b t) ^ 4) + N ^ 2 * a t / (2 * (b t) ^ 2)
        + a t * deriv b t ^ 2 / (2 * (b t) ^ 2) - deriv a t * deriv b t / (b t) := by
  have hid : deriv (deriv a) t
        - (-3 * l ^ 2 * N ^ 2 * a t / (2 * (b t) ^ 4) + N ^ 2 * a t / (2 * (b t) ^ 2)
          + a t * deriv b t ^ 2 / (2 * (b t) ^ 2) - deriv a t * deriv b t / (b t))
      = (N * a t / (2 * c * (b t) ^ 2)) * (deriv (momA a b N c) t
          - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)))
        + (-(N / (2 * b t * c))) * (deriv (momB a b N c) t
          - (-2 * c * deriv a t * deriv b t / N
            + 2 * c * N * a t * l ^ 2 / (b t) ^ 3)) := by
    rw [eulerLagrange_a a b N c l t hb hbb hN hb0,
      eulerLagrange_b a b N c l t ha hb haa hbb hN hb0]
    field_simp
    ring
  rw [hELa, hELb] at hid
  simp only [mul_zero, add_zero] at hid
  exact sub_eq_zero.mp hid

end CFT.Mini
