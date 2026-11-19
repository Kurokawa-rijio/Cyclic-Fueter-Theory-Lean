import Mathlib.Tactic

/-
# Continuum field laws (support file)

Navier–Stokes in conservation form, Bernoulli, Navier–Cauchy, the acoustic wave equation and
Coulomb's law (q/r is harmonic for r ≠ 0, and E = −∇(q/r) = q x/r³), with partial derivatives
given by commuting derivations; spatial indices are j ≠ 0.
-/

namespace FieldEquations.Continuum

variable {S : Type*} [Field S] [CharZero S]
variable (D : Fin 4 → Derivation ℤ S S)

def ssum (f : Fin 4 → S) : S := f 1 + f 2 + f 3

theorem d_half' (d : Derivation ℤ S S) : d (1/2 : S) = 0 := by
  have h := map_nsmul d 2 (1/2 : S)
  rw [nsmul_eq_mul, nsmul_eq_mul, show ((2:ℕ):S) * (1/2) = 1 by norm_num,
    Derivation.map_one_eq_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

theorem navier_stokes (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (ρ p μ : S) (u : Fin 4 → S)
    (hμ : ∀ j, D j μ = 0)
    (hcont : D 0 ρ + ssum (fun j => D j (ρ * u j)) = 0)
    (hdiv : ssum (fun j => D j (u j)) = 0) (i : Fin 4)
    (hmom : D 0 (ρ * u i) + ssum (fun j => D j (ρ * u i * u j - μ * (D j (u i) + D i (u j))))
      + D i p = 0) :
    ρ * (D 0 (u i) + ssum (fun j => u j * D j (u i)))
      = -(D i p) + μ * ssum (fun j => D j (D j (u i))) := by
  have hdiv' := congrArg (D i) hdiv
  unfold ssum at hcont hdiv' hmom ⊢
  simp only [map_add, map_sub, map_zero, Derivation.leibniz, smul_eq_mul, hμ, mul_zero,
    add_zero] at hcont hdiv' hmom ⊢
  rw [hc 1 i, hc 2 i, hc 3 i] at hmom
  linear_combination hmom - u i * hcont + μ * hdiv'

theorem bernoulli (ρ p Φ : S) (u : Fin 4 → S) (i : Fin 4) (hρ : ρ ≠ 0) (hρc : D i ρ = 0)
    (hirr1 : D i (u 1) = D 1 (u i)) (hirr2 : D i (u 2) = D 2 (u i))
    (hirr3 : D i (u 3) = D 3 (u i))
    (heuler : ρ * ssum (fun j => u j * D j (u i)) = -(D i p) - ρ * D i Φ) :
    D i ((1/2 : S) * ssum (fun j => u j * u j) + p * ρ⁻¹ + Φ) = 0 := by
  have hinv : D i ρ⁻¹ = 0 := by
    have e := congrArg (D i) (mul_inv_cancel₀ hρ)
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul, hρc,
      mul_zero, add_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hρ
  have hρi : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ
  unfold ssum at heuler ⊢
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hinv, d_half' (D i), mul_zero, add_zero]
  rw [hirr1, hirr2, hirr3]
  linear_combination ρ⁻¹ * heuler
    - (u 1 * D 1 (u i) + u 2 * D 2 (u i) + u 3 * D 3 (u i) + D i Φ) * hρi

theorem navier_cauchy (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (lam mu : S) (u : Fin 4 → S)
    (hl : ∀ j, D j lam = 0) (hm : ∀ j, D j mu = 0) (i : Fin 4) :
    D i (lam * ssum (fun k => D k (u k))) + ssum (fun j => D j (mu * (D i (u j) + D j (u i))))
      = (lam + mu) * D i (ssum (fun k => D k (u k))) + mu * ssum (fun j => D j (D j (u i))) := by
  unfold ssum
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hl, hm, mul_zero, add_zero]
  rw [hc 1 i, hc 2 i, hc 3 i]
  ring

theorem sound_wave (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (ρ1 ρ0 c2 : S) (u : Fin 4 → S)
    (h0 : ∀ j, D j ρ0 = 0) (h2 : ∀ j, D j c2 = 0)
    (hcont : D 0 ρ1 + ρ0 * ssum (fun j => D j (u j)) = 0)
    (hmom : ∀ i, ρ0 * D 0 (u i) = -(c2 * D i ρ1)) :
    D 0 (D 0 ρ1) = c2 * ssum (fun j => D j (D j ρ1)) := by
  have e0 := congrArg (D 0) hcont
  have e1 := congrArg (D 1) (hmom 1)
  have e2 := congrArg (D 2) (hmom 2)
  have e3 := congrArg (D 3) (hmom 3)
  unfold ssum at e0 ⊢
  simp only [map_add, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, h0, h2, mul_zero,
    add_zero] at e0 e1 e2 e3
  rw [hc 0 1, hc 0 2, hc 0 3] at e0
  linear_combination e0 - e1 - e2 - e3

/-- q/r is harmonic (spatial indices j = 1, 2, 3). -/
theorem coulomb_harmonic (q ri : S) (x : Fin 4 → S) (hq : ∀ j, D j q = 0)
    (hx : ∀ j, j ≠ 0 → D j (x j) = 1) (hri : ∀ j, j ≠ 0 → D j ri = -(x j * (ri * ri * ri)))
    (hnorm : (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * ri ^ 2 = 1) :
    ssum (fun j => D j (D j (q * ri))) = 0 := by
  have hx1 := hx 1 (by decide)
  have hx2 := hx 2 (by decide)
  have hx3 := hx 3 (by decide)
  have hr1 := hri 1 (by decide)
  have hr2 := hri 2 (by decide)
  have hr3 := hri 3 (by decide)
  unfold ssum
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hq, hx1, hx2, hx3, hr1, hr2, hr3,
    mul_zero, add_zero]
  linear_combination (3 * q * ri ^ 3) * hnorm

theorem coulomb_field (q ri : S) (x : Fin 4 → S) (hq : ∀ j, D j q = 0)
    (hri : ∀ j, j ≠ 0 → D j ri = -(x j * (ri * ri * ri))) (j : Fin 4) (hj : j ≠ 0) :
    -(D j (q * ri)) = q * x j * (ri * ri * ri) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hq, hri j hj]
  ring

end FieldEquations.Continuum
