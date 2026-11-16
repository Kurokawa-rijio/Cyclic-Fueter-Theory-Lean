/-
  ゲージ共変性:A′ = gAg⁻¹ + g d(g⁻¹) なら F′ = gFg⁻¹

  任意の(非可換)環で、微分を積の微分則に従う記号として扱う。
  記号:
    g, gi(= g⁻¹)、Ai, Aj(接続の成分)
    dgi = ∂_i g、dgj = ∂_j g、ddg = ∂_i∂_j g = ∂_j∂_i g(混合微分の対称性)
    dAij = ∂_i A_j、dAji = ∂_j A_i
  ∂_k(g⁻¹) = −g⁻¹(∂_k g)g⁻¹(g g⁻¹ = 1 を微分して得る)。
  α-I.6 で前提にしていた事実を、この補題で置き換える。
-/
import Mathlib.Tactic.NoncommRing

namespace CFT.Gauge

variable {R : Type*} [Ring R]

/-- ゲージ変換した接続 A′_k = g A_k g⁻¹ + g ∂_k(g⁻¹) = g A_k g⁻¹ − (∂_k g) g⁻¹ -/
def Aprime (g gi Ak dgk : R) : R := g * Ak * gi - dgk * gi

/-- 積の微分則で得た ∂_i A′_j -/
def dAprime (g gi Aj dgi dgj ddg dAij : R) : R :=
  dgi * Aj * gi + g * dAij * gi + g * Aj * (-(gi * dgi * gi)) - (ddg * gi + dgj * (-(gi * dgi * gi)))

/-- ∂_k(g⁻¹) = −g⁻¹(∂_k g)g⁻¹ は g g⁻¹ = 1 の微分 (∂_k g)g⁻¹ + g ∂_k(g⁻¹) = 0 から従う -/
theorem d_inv (g gi dgk dgik : R) (h1 : g * gi = 1) (h2 : gi * g = 1)
    (hd : dgk * gi + g * dgik = 0) : dgik = -(gi * dgk * gi) := by
  have : gi * (dgk * gi + g * dgik) = 0 := by rw [hd, mul_zero]
  rw [mul_add, ← mul_assoc gi g, h2, one_mul] at this
  rw [← sub_eq_zero, sub_neg_eq_add, add_comm, mul_assoc]
  exact this

/-- 曲率の共変性 F′_ij = g F_ij g⁻¹ -/
theorem curvature_covariant (g gi Ai Aj dgi dgj ddg dAij dAji : R)
    (h1 : g * gi = 1) (h2 : gi * g = 1) :
    dAprime g gi Aj dgi dgj ddg dAij - dAprime g gi Ai dgj dgi ddg dAji
      + Aprime g gi Ai dgi * Aprime g gi Aj dgj - Aprime g gi Aj dgj * Aprime g gi Ai dgi
      = g * (dAij - dAji + Ai * Aj - Aj * Ai) * gi := by
  have key : ∀ X : R, X * gi * g = X := by
    intro X; rw [mul_assoc, h2, mul_one]
  simp only [Aprime, dAprime, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, ← mul_assoc,
    key]
  noncomm_ring

end CFT.Gauge
