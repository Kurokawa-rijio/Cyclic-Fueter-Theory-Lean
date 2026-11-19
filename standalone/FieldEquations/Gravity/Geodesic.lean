import Mathlib.Tactic

/-
# The geodesic equation as an Euler–Lagrange equation

For L = ½ g_{μν}(x) v^μ v^ν the Euler–Lagrange expression is
g_{λμ}(a^μ + Γ^μ_{νρ} v^ν v^ρ) with Γ of the first kind (`geodesic_EL`).
The derivative ∂L/∂v^λ is entered as Σ_μ g_{λμ} v^μ, which assumes g symmetric.
-/

namespace FieldEquations.Geodesic

open Finset

variable {S : Type*} [Field S] [CharZero S] {n : ℕ}
variable (d : Derivation ℤ S S)

def chr1 (dg : Fin n → Fin n → Fin n → S) (lam μ ν : Fin n) : S :=
  (1/2 : S) * (dg μ lam ν + dg ν lam μ - dg lam μ ν)

def EL (g : Fin n → Fin n → S) (dg : Fin n → Fin n → Fin n → S) (v : Fin n → S) (lam : Fin n) : S :=
  d (∑ μ, g lam μ * v μ) - (1/2 : S) * ∑ μ, ∑ ν, dg lam μ ν * v μ * v ν

/-- The Euler–Lagrange expression of ½ g v v is the geodesic equation. -/
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

end FieldEquations.Geodesic
