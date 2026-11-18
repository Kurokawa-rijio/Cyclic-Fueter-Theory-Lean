/-
  段階 4(特殊相対論)の有名な式(2026-11-18)

  * `mass_shell`:4 元速度 −u₀² + |u|² = −1、p = m u なら E² = |p|² + m²(E = p₀)。
  * `boost_interval`:γ²(1 − v²) = 1 の Lorentz ブーストは −t² + x² を保つ。
  * `velocity_addition`:ブーストの合成は速度 (v₁ + v₂)/(1 + v₁v₂)、γ = γ₁γ₂(1 + v₁v₂) のブースト
    (`velocity_addition_gamma`:その γ も γ²(1 − v²) = 1 をみたす)。
  * `em_invariant_dot`、`em_invariant_sq`:x 方向のブーストで電磁場は
      E′ = (E₁, γ(E₂ − vB₃), γ(E₃ + vB₂))、B′ = (B₁, γ(B₂ + vE₃), γ(B₃ − vE₂))
    と変わり、E·B と |E|² − |B|² は不変(電磁場テンソルの 2 つの不変量)。
-/
import Mathlib.Tactic

namespace CFT.SpecialRel

variable {S : Type*} [Field S]

theorem mass_shell (m u0 u1 u2 u3 : S) (hu : -u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2 = -1) :
    (m * u0) ^ 2 = (m * u1) ^ 2 + (m * u2) ^ 2 + (m * u3) ^ 2 + m ^ 2 := by
  linear_combination (-m ^ 2) * hu

theorem boost_interval (γ v t x : S) (hγ : γ ^ 2 * (1 - v ^ 2) = 1) :
    -(γ * t - γ * v * x) ^ 2 + (γ * x - γ * v * t) ^ 2 = -t ^ 2 + x ^ 2 := by
  linear_combination (x ^ 2 - t ^ 2) * hγ

theorem velocity_addition (γ1 v1 γ2 v2 t x : S) (h : 1 + v1 * v2 ≠ 0) :
    γ2 * ((γ1 * t - γ1 * v1 * x) - v2 * (γ1 * x - γ1 * v1 * t))
      = (γ1 * γ2 * (1 + v1 * v2)) * (t - ((v1 + v2) / (1 + v1 * v2)) * x) := by
  field_simp
  ring

theorem velocity_addition_gamma (γ1 v1 γ2 v2 : S) (h : 1 + v1 * v2 ≠ 0)
    (h1 : γ1 ^ 2 * (1 - v1 ^ 2) = 1) (h2 : γ2 ^ 2 * (1 - v2 ^ 2) = 1) :
    (γ1 * γ2 * (1 + v1 * v2)) ^ 2 * (1 - ((v1 + v2) / (1 + v1 * v2)) ^ 2) = 1 := by
  have e : (γ1 * γ2 * (1 + v1 * v2)) ^ 2 * (1 - ((v1 + v2) / (1 + v1 * v2)) ^ 2)
      = (γ1 ^ 2 * (1 - v1 ^ 2)) * (γ2 ^ 2 * (1 - v2 ^ 2)) := by
    field_simp
    ring
  rw [e, h1, h2, one_mul]

theorem em_invariant_dot (γ v E1 E2 E3 B1 B2 B3 : S) (hγ : γ ^ 2 * (1 - v ^ 2) = 1) :
    E1 * B1 + (γ * (E2 - v * B3)) * (γ * (B2 + v * E3)) + (γ * (E3 + v * B2)) * (γ * (B3 - v * E2))
      = E1 * B1 + E2 * B2 + E3 * B3 := by
  linear_combination (E2 * B2 + E3 * B3) * hγ

theorem em_invariant_sq (γ v E1 E2 E3 B1 B2 B3 : S) (hγ : γ ^ 2 * (1 - v ^ 2) = 1) :
    (E1 ^ 2 + (γ * (E2 - v * B3)) ^ 2 + (γ * (E3 + v * B2)) ^ 2)
      - (B1 ^ 2 + (γ * (B2 + v * E3)) ^ 2 + (γ * (B3 - v * E2)) ^ 2)
      = (E1 ^ 2 + E2 ^ 2 + E3 ^ 2) - (B1 ^ 2 + B2 ^ 2 + B3 ^ 2) := by
  linear_combination (E2 ^ 2 + E3 ^ 2 - B2 ^ 2 - B3 ^ 2) * hγ

end CFT.SpecialRel
