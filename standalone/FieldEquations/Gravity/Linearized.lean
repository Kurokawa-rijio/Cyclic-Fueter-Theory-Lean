import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-
# Linearized gravity

Metric g = η + h with η = diag(−1,1,1,1), partial derivatives given by commuting derivations.
Linearized Ricci tensor and Einstein tensor; gauge invariance under h ↦ h + ∂ξ + ∂ξ
(`ric_gauge`), the linearized Bianchi identity ∂^μ G_{μν} = 0 (`lin_bianchi`) and hence
conservation of the source (`matter_conservation`); in Lorenz gauge G = −½ □ h̄
(`G_lorenz_gauge`) and vacuum waves (`gw_vacuum`). Newtonian limit: for h = −2Φ dt² − 2Φ dx²
with static Φ, G₀₀ = 2ΔΦ (`newton_G00`), so G₀₀ = 8πρ gives ΔΦ = 4πρ (`newton_poisson`), and
Γ^i₀₀ = ∂_iΦ (`newton_christoffel`).
-/

namespace FieldEquations.LinearizedGravity

set_option maxHeartbeats 0

open Finset

variable {S : Type*} [Field S] [CharZero S]
variable (D : Fin 4 → Derivation ℤ S S)

def eta (μ : Fin 4) : S := if μ = 0 then -1 else 1

def etaM (μ ν : Fin 4) : S := if μ = ν then eta μ else 0

theorem d_half (d : Derivation ℤ S S) : d (1/2 : S) = 0 := by
  have h := map_nsmul d 2 (1/2 : S)
  rw [nsmul_eq_mul, nsmul_eq_mul, show ((2:ℕ):S) * (1/2) = 1 by norm_num,
    Derivation.map_one_eq_zero] at h
  have h2 : ((2:ℕ):S) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h.symm).resolve_left h2

variable (h : Fin 4 → Fin 4 → S)

def tr : S := ∑ μ, eta μ * h μ μ

def box (f : S) : S := ∑ ρ, eta ρ * D ρ (D ρ f)

def dv (ν : Fin 4) : S := ∑ ρ, eta ρ * D ρ (h ρ ν)

def Ric (μ ν : Fin 4) : S :=
  (1/2 : S) * (D μ (dv D h ν) + D ν (dv D h μ) - box D (h μ ν) - D μ (D ν (tr h)))

def Rs : S := ∑ μ, eta μ * Ric D h μ μ

def Gt (μ ν : Fin 4) : S := Ric D h μ ν - (1/2 : S) * etaM μ ν * Rs D h

def hbar (μ ν : Fin 4) : S := h μ ν - (1/2 : S) * etaM μ ν * tr h

theorem ric_gauge (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (ξ : Fin 4 → S) (μ ν : Fin 4) :
    Ric D (fun a b => D a (ξ b) + D b (ξ a)) μ ν = 0 := by
  fin_cases μ <;> fin_cases ν <;>
  simp (config := { decide := true }) only [Ric, dv, box, tr, eta, map_add, map_sub, map_sum,
    map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, Fin.sum_univ_four,
    Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, mul_zero, add_zero,
    neg_zero, hc 1 0, hc 2 0, hc 3 0, hc 2 1, hc 3 1, hc 3 2] <;>
  ring

/-- Linearized Bianchi identity. -/
theorem lin_bianchi (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (hs : ∀ μ ν, h μ ν = h ν μ)
    (ν : Fin 4) : ∑ μ, eta μ * D μ (Gt D h μ ν) = 0 := by
  have h12 : ∀ μ, D μ (1/2 : S) = 0 := fun μ => d_half (D μ)
  fin_cases ν <;>
  simp (config := { decide := true }) only [Gt, Rs, Ric, dv, box, tr, etaM, eta, map_add, map_sub,
    map_sum, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero,
    Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, h12, hc 1 0, hc 2 0, hc 3 0,
    hc 2 1, hc 3 1, hc 3 2, hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2] <;>
  ring

theorem matter_conservation (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (hs : ∀ μ ν, h μ ν = h ν μ) (T : Fin 4 → Fin 4 → S) (κ : S) (hκ : κ ≠ 0)
    (hκc : ∀ μ, D μ κ = 0) (hE : ∀ μ ν, Gt D h μ ν = κ * T μ ν) (ν : Fin 4) :
    ∑ μ, eta μ * D μ (T μ ν) = 0 := by
  have hb := lin_bianchi D h hc hs ν
  simp only [hE, Derivation.leibniz, smul_eq_mul, hκc, mul_zero, add_zero] at hb
  have hk : κ * ∑ μ, eta μ * D μ (T μ ν) = 0 := by
    calc κ * ∑ μ, eta μ * D μ (T μ ν) = ∑ μ, eta μ * (κ * D μ (T μ ν)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun μ _ => by ring)
      _ = 0 := hb
  exact (mul_eq_zero.mp hk).resolve_left hκ

def Lg (ν : Fin 4) : S := ∑ ρ, eta ρ * D ρ (hbar h ρ ν)

theorem G_harmonic (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (μ ν : Fin 4) :
    Gt D h μ ν = (1/2 : S) * (D μ (Lg D h ν) + D ν (Lg D h μ))
      - (1/2 : S) * etaM μ ν * (∑ ρ, eta ρ * D ρ (Lg D h ρ)) - (1/2 : S) * box D (hbar h μ ν) := by
  have h12 : ∀ μ, D μ (1/2 : S) = 0 := fun μ => d_half (D μ)
  fin_cases μ <;> fin_cases ν <;>
  simp (config := { decide := true }) only [Gt, Rs, Ric, dv, box, tr, Lg, hbar, etaM, eta,
    map_add, map_sub, map_sum, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero,
    Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, h12, hc 1 0, hc 2 0, hc 3 0,
    hc 2 1, hc 3 1, hc 3 2] <;>
  ring

theorem G_lorenz_gauge (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (hL : ∀ ν, Lg D h ν = 0) (μ ν : Fin 4) :
    Gt D h μ ν = -((1/2 : S) * box D (hbar h μ ν)) := by
  rw [G_harmonic D h hc μ ν]
  simp only [hL, map_zero, add_zero, mul_zero, Finset.sum_const_zero, sub_zero, zero_sub]

theorem gw_vacuum (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (hL : ∀ ν, Lg D h ν = 0) (hbox : ∀ μ ν, box D (hbar h μ ν) = 0) (μ ν : Fin 4) :
    Gt D h μ ν = 0 := by
  rw [G_lorenz_gauge D h hc hL μ ν, hbox, mul_zero, neg_zero]

def hN (Φ : S) : Fin 4 → Fin 4 → S := fun μ ν => if μ = ν then -(Φ + Φ) else 0

def lap (Φ : S) : S := D 1 (D 1 Φ) + D 2 (D 2 Φ) + D 3 (D 3 Φ)

/-- Newtonian limit: G₀₀ = 2ΔΦ. -/
theorem newton_G00 (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (Φ : S) (hst : D 0 Φ = 0) :
    Gt D (hN Φ) 0 0 = 2 * lap D Φ := by
  have h12 : ∀ μ, D μ (1/2 : S) = 0 := fun μ => d_half (D μ)
  have hst' : ∀ i, D 0 (D i Φ) = 0 := fun i => by rw [hc 0 i, hst, map_zero]
  simp (config := { decide := true }) only [Gt, Rs, Ric, dv, box, tr, hN, lap, etaM, eta,
    map_add, map_sub, map_sum, map_neg, map_zero, hst, hst' 1, hst' 2, hst' 3, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero,
    Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, h12, hc 1 0, hc 2 0, hc 3 0,
    hc 2 1, hc 3 1, hc 3 2]
  ring

/-- Newtonian limit: the 00 Einstein equation is Poisson's equation. -/
theorem newton_poisson (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (Φ ρ k : S)
    (hst : D 0 Φ = 0) (hE : Gt D (hN Φ) 0 0 = 8 * k * ρ) : lap D Φ = 4 * k * ρ := by
  rw [newton_G00 D hc Φ hst] at hE
  linear_combination (1/2 : S) * hE

def Γlin (lam μ ν : Fin 4) : S :=
  (1/2 : S) * eta lam * (D μ (h lam ν) + D ν (h lam μ) - D lam (h μ ν))

theorem newton_christoffel (Φ : S) (i : Fin 4) (hi : i ≠ 0) :
    Γlin D (hN Φ) i 0 0 = D i Φ := by
  fin_cases i
  · exact absurd rfl hi
  all_goals
    simp (config := { decide := true }) only [Γlin, hN, eta, map_add, map_neg, map_zero,
      Fin.isValue, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk]
    ring

end FieldEquations.LinearizedGravity
