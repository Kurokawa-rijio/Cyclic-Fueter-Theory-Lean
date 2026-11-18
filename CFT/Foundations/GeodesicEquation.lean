/-
  段階 6(一般相対論)その 2:測地線方程式(2026-11-18)

  世界線のパラメータ τ の導分 d の上で、点 x(τ) での計量の値 g_ab、その微分 ∂_c g_ab(dg c a b)、
  速度 v^μ = ẋ^μ、加速度 a^μ = v̇^μ を与える。連鎖律 d(g_ab) = Σ_c ∂_c g_ab v^c は入力。
  作用 L = ½ g_μν v^μ v^ν の Euler–Lagrange の式
    EL_λ = d(∂L/∂v^λ) − ∂L/∂x^λ = d(Σ_μ g_λμ v^μ) − ½ Σ_μν ∂_λ g_μν v^μ v^ν
  は、測地線方程式の左辺 Σ_μ g_λμ a^μ + Σ_μν Γ_λμν v^μ v^ν に等しい(`geodesic_EL`)。
  Γ_λμν = ½(∂_μ g_λν + ∂_ν g_λμ − ∂_λ g_μν) は第 1 種の Christoffel 記号(13-1 の `chr1` と同じ形)。
  定理の証明では計量の対称性は使わない(和の添字の付け替えだけで出る)。ただし `EL` の定義で
  ∂L/∂v^λ を Σ_μ g_λμ v^μ と書いた所に、すでに g_λμ = g_μλ が入っている(一般には ½Σ_μ (g_λμ + g_μλ) v^μ)。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace CFT.Geodesic

open Finset

variable {S : Type*} [Field S] [CharZero S] {n : ℕ}
variable (d : Derivation ℤ S S)

/-- 第 1 種の Christoffel 記号 Γ_λμν(dg c a b = ∂_c g_ab) -/
def chr1 (dg : Fin n → Fin n → Fin n → S) (lam μ ν : Fin n) : S :=
  (1/2 : S) * (dg μ lam ν + dg ν lam μ - dg lam μ ν)

/-- Euler–Lagrange の式の左辺 -/
def EL (g : Fin n → Fin n → S) (dg : Fin n → Fin n → Fin n → S) (v : Fin n → S) (lam : Fin n) : S :=
  d (∑ μ, g lam μ * v μ) - (1/2 : S) * ∑ μ, ∑ ν, dg lam μ ν * v μ * v ν

/-- 測地線方程式:EL_λ = Σ g_λμ a^μ + Σ Γ_λμν v^μ v^ν -/
theorem geodesic_EL (g : Fin n → Fin n → S) (dg : Fin n → Fin n → Fin n → S) (v acc : Fin n → S)
    (hg : ∀ a b, d (g a b) = ∑ c, dg c a b * v c) (hv : ∀ μ, d (v μ) = acc μ) (lam : Fin n) :
    EL d g dg v lam = ∑ μ, g lam μ * acc μ + ∑ μ, ∑ ν, chr1 dg lam μ ν * v μ * v ν := by
  have e1 : d (∑ μ, g lam μ * v μ)
      = ∑ μ, g lam μ * acc μ + ∑ μ, ∑ c, dg c lam μ * v c * v μ := by
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hv, hg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun c _ => by ring)
  have e2 : ∑ μ, ∑ ν, dg μ lam ν * v μ * v ν = ∑ μ, ∑ c, dg c lam μ * v c * v μ :=
    Finset.sum_comm
  have e3 : ∑ μ, ∑ ν, dg ν lam μ * v μ * v ν = ∑ μ, ∑ c, dg c lam μ * v c * v μ :=
    Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => by ring))
  have e4 : ∑ μ, ∑ ν, chr1 dg lam μ ν * v μ * v ν
      = (1/2 : S) * (∑ μ, ∑ ν, dg μ lam ν * v μ * v ν)
        + (1/2 : S) * (∑ μ, ∑ ν, dg ν lam μ * v μ * v ν)
        - (1/2 : S) * (∑ μ, ∑ ν, dg lam μ ν * v μ * v ν) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
    unfold chr1
    ring
  unfold EL
  rw [e1, e4, e2, e3]
  ring

end CFT.Geodesic
