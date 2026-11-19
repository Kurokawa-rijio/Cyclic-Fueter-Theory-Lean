import FieldEquations.Quaternionic.Operators
import FieldEquations.Quaternionic.ContinuumLaws
import FieldEquations.Gravity.Linearized
import FieldEquations.Gravity.BianchiSecond

/-
# Field equations in Fueter form

Vec = i∂₁ + j∂₂ + k∂₃ with Vec² = −Δ₃ (`vec_vec`).
* `maxwell_single_equation`: Maxwell's equations (c = 1) imply the single biquaternionic
  equation D F = −(Iρ + j) for F = E + I B (one direction; the converse is not formalized).
* `em_square`: F² = −(|E|² − |B|² + 2I E·B) for F = E + I B; `em_square_invariant`: if F² is a
  scalar s, then (qFq⁻¹)² = s (that this conjugation realizes a Lorentz transformation is not
  formalized).
* `mass_shell_biquaternion`: P P̄ = p₀² − |p|².
* Bernoulli, viscous Navier–Stokes and Coulomb written with Vec; `box_bridge`, the Lorenz
  gauge, and the gauge Bianchi identity for quaternion-valued connections.
-/

open Quaternion FieldEquations.QuaternionOperators

namespace FieldEquations.FueterForms

set_option maxHeartbeats 2000000

section Ring

variable {R : Type*} [CommRing R] (d : Fin 4 → Derivation ℤ R R)

def vecQ (u : Fin 4 → R) : ℍ[R] := ⟨0, u 1, u 2, u 3⟩

theorem vec_vector (u : Fin 4 → R) :
    Vec d (vecQ u) = ⟨-(d 1 (u 1) + d 2 (u 2) + d 3 (u 3)), d 2 (u 3) - d 3 (u 2),
      d 3 (u 1) - d 1 (u 3), d 1 (u 2) - d 2 (u 1)⟩ := by
  ext <;> simp [Vec, vecQ, dq, e] <;> ring

theorem fueter_regular_iff (u : Fin 4 → R) :
    Vec d (vecQ u) = 0 ↔ (d 1 (u 1) + d 2 (u 2) + d 3 (u 3) = 0 ∧ d 2 (u 3) = d 3 (u 2)
      ∧ d 3 (u 1) = d 1 (u 3) ∧ d 1 (u 2) = d 2 (u 1)) := by
  rw [vec_vector]
  constructor
  · intro h
    have h0 : -(d 1 (u 1) + d 2 (u 2) + d 3 (u 3)) = 0 := congrArg (fun q : ℍ[R] => q.re) h
    have h1 : d 2 (u 3) - d 3 (u 2) = 0 := congrArg (fun q : ℍ[R] => q.imI) h
    have h2 : d 3 (u 1) - d 1 (u 3) = 0 := congrArg (fun q : ℍ[R] => q.imJ) h
    have h3 : d 1 (u 2) - d 2 (u 1) = 0 := congrArg (fun q : ℍ[R] => q.imK) h
    exact ⟨neg_eq_zero.mp h0, sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext <;> simp [h0, h1, h2, h3]

theorem vec_vec (hc : ∀ a b x, d a (d b x) = d b (d a x)) (f : ℍ[R]) :
    Vec d (Vec d f) = -(dq (d 1) (dq (d 1) f) + dq (d 2) (dq (d 2) f) + dq (d 3) (dq (d 3) f)) := by
  have c21 := hc 2 1
  have c31 := hc 3 1
  have c32 := hc 3 2
  ext <;> simp [Vec, dq, e, map_add, map_sub, map_neg, c21, c31, c32] <;> ring

theorem maxwell_biquaternion (I : R) (hI : I * I = -1) (hdI : ∀ a, d a I = 0) (E B : Fin 4 → R) :
    DB d I (vecQ (fun a => E a + I * B a))
      = ⟨(d 1 (B 1) + d 2 (B 2) + d 3 (B 3)) - I * (d 1 (E 1) + d 2 (E 2) + d 3 (E 3)),
          (d 0 (E 1) - (d 2 (B 3) - d 3 (B 2))) + I * (d 0 (B 1) + (d 2 (E 3) - d 3 (E 2))),
          (d 0 (E 2) - (d 3 (B 1) - d 1 (B 3))) + I * (d 0 (B 2) + (d 3 (E 1) - d 1 (E 3))),
          (d 0 (E 3) - (d 1 (B 2) - d 2 (B 1))) + I * (d 0 (B 3) + (d 1 (E 2) - d 2 (E 1)))⟩ := by
  have hd : ∀ a x, d a (I * x) = I * d a x := by
    intro a x; rw [Derivation.leibniz, hdI a]; simp [smul_eq_mul]
  ext
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (-(d 1 (B 1) + d 2 (B 2) + d 3 (B 3))) * hI
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (d 2 (B 3) - d 3 (B 2)) * hI
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (d 3 (B 1) - d 1 (B 3)) * hI
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (d 1 (B 2) - d 2 (B 1)) * hI

/-- Maxwell's equations imply D F = −(Iρ + j). -/
theorem maxwell_single_equation (I : R) (hI : I * I = -1) (hdI : ∀ a, d a I = 0)
    (E B j : Fin 4 → R) (ρ : R)
    (gaussE : d 1 (E 1) + d 2 (E 2) + d 3 (E 3) = ρ) (gaussB : d 1 (B 1) + d 2 (B 2) + d 3 (B 3) = 0)
    (ampere1 : d 2 (B 3) - d 3 (B 2) - d 0 (E 1) = j 1)
    (ampere2 : d 3 (B 1) - d 1 (B 3) - d 0 (E 2) = j 2)
    (ampere3 : d 1 (B 2) - d 2 (B 1) - d 0 (E 3) = j 3)
    (faraday1 : d 2 (E 3) - d 3 (E 2) + d 0 (B 1) = 0)
    (faraday2 : d 3 (E 1) - d 1 (E 3) + d 0 (B 2) = 0)
    (faraday3 : d 1 (E 2) - d 2 (E 1) + d 0 (B 3) = 0) :
    DB d I (vecQ (fun a => E a + I * B a)) = ⟨-(I * ρ), -(j 1), -(j 2), -(j 3)⟩ := by
  rw [maxwell_biquaternion d I hI hdI E B]
  ext
  · simp only; rw [gaussB, gaussE]; ring
  · simp only; linear_combination -ampere1 + I * faraday1
  · simp only; linear_combination -ampere2 + I * faraday2
  · simp only; linear_combination -ampere3 + I * faraday3

theorem em_square (I : R) (hI : I * I = -1) (E B : Fin 4 → R) :
    vecQ (fun a => E a + I * B a) * vecQ (fun a => E a + I * B a)
      = ⟨-((E 1 ^ 2 + E 2 ^ 2 + E 3 ^ 2) - (B 1 ^ 2 + B 2 ^ 2 + B 3 ^ 2))
          - 2 * I * (E 1 * B 1 + E 2 * B 2 + E 3 * B 3), 0, 0, 0⟩ := by
  ext
  · simp [vecQ]
    linear_combination (-(B 1 ^ 2 + B 2 ^ 2 + B 3 ^ 2)) * hI
  · simp [vecQ]; ring
  · simp [vecQ]; ring
  · simp [vecQ]; ring

/-- Invariance of the scalar part of F² under conjugation. -/
theorem em_square_invariant (F q q' : ℍ[R]) (s : R) (hFF : F * F = (s : ℍ[R]))
    (hq : q' * q = 1) (hq' : q * q' = 1) :
    (q * F * q') * (q * F * q') = (s : ℍ[R]) := by
  have e1 : (q * F * q') * (q * F * q') = q * (F * (q' * q) * F) * q' := by noncomm_ring
  rw [e1, hq, mul_one, hFF, ← Quaternion.coe_commutes s q, mul_assoc, hq', mul_one]

theorem mass_shell_biquaternion (I : R) (hI : I * I = -1) (p0 p1 p2 p3 : R) :
    (⟨p0, I * p1, I * p2, I * p3⟩ : ℍ[R]) * star (⟨p0, I * p1, I * p2, I * p3⟩ : ℍ[R])
      = ⟨p0 ^ 2 - (p1 ^ 2 + p2 ^ 2 + p3 ^ 2), 0, 0, 0⟩ := by
  ext
  · simp
    linear_combination (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) * hI
  · simp; ring
  · simp; ring
  · simp; ring

end Ring

section Field

variable {S : Type*} [Field S] [CharZero S] (D : Fin 4 → Derivation ℤ S S)

theorem bernoulli_fueter (ρ p Φ : S) (u : Fin 4 → S) (hreg : Vec D (vecQ u) = 0) (i : Fin 4)
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (hρ : ρ ≠ 0) (hρc : D i ρ = 0)
    (heuler : ρ * FieldEquations.Continuum.ssum (fun j => u j * D j (u i)) = -(D i p) - ρ * D i Φ) :
    D i ((1/2 : S) * FieldEquations.Continuum.ssum (fun j => u j * u j) + p * ρ⁻¹ + Φ) = 0 := by
  obtain ⟨_, h1, h2, h3⟩ := (fueter_regular_iff D u).mp hreg
  rcases hi with rfl | rfl | rfl
  · exact FieldEquations.Continuum.bernoulli D ρ p Φ u 1 hρ hρc rfl h3 h2.symm heuler
  · exact FieldEquations.Continuum.bernoulli D ρ p Φ u 2 hρ hρc h3.symm rfl h1 heuler
  · exact FieldEquations.Continuum.bernoulli D ρ p Φ u 3 hρ hρc h2 h1.symm rfl heuler

theorem ns_viscous_fueter (hc : ∀ a b x, D a (D b x) = D b (D a x)) (u : Fin 4 → S) :
    Vec D (Vec D (vecQ u)) = -(⟨0, FieldEquations.Continuum.ssum (fun j => D j (D j (u 1))),
      FieldEquations.Continuum.ssum (fun j => D j (D j (u 2))),
      FieldEquations.Continuum.ssum (fun j => D j (D j (u 3)))⟩ : ℍ[S]) := by
  rw [vec_vec D hc]
  ext <;> simp [dq, vecQ, FieldEquations.Continuum.ssum]

theorem coulomb_fueter (hc : ∀ a b x, D a (D b x) = D b (D a x)) (q ri : S) (x : Fin 4 → S)
    (hq : ∀ j, D j q = 0) (hx : ∀ j, j ≠ 0 → D j (x j) = 1)
    (hri : ∀ j, j ≠ 0 → D j ri = -(x j * (ri * ri * ri)))
    (hnorm : (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * ri ^ 2 = 1) :
    Vec D (Vec D (⟨q * ri, 0, 0, 0⟩ : ℍ[S])) = 0 := by
  have h := FieldEquations.Continuum.coulomb_harmonic D q ri x hq hx hri hnorm
  unfold FieldEquations.Continuum.ssum at h
  rw [vec_vec D hc]
  ext
  · simp only [dq, Quaternion.neg_re, Quaternion.add_re, Quaternion.zero_re]
    rw [h, neg_zero]
  all_goals simp [dq]

theorem box_bridge (s : S) :
    FieldEquations.LinearizedGravity.box D s = -(Box D (⟨s, 0, 0, 0⟩ : ℍ[S])).re := by
  simp (config := { decide := true }) [FieldEquations.LinearizedGravity.box, FieldEquations.LinearizedGravity.eta, Box, dq,
    Fin.sum_univ_four] <;> ring

theorem lorenz_gauge_fueter (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (h : Fin 4 → Fin 4 → S) (hL : ∀ ν, FieldEquations.LinearizedGravity.Lg D h ν = 0) (μ ν : Fin 4) :
    FieldEquations.LinearizedGravity.Gt D h μ ν
      = (1/2 : S) * (Box D (⟨FieldEquations.LinearizedGravity.hbar h μ ν, 0, 0, 0⟩ : ℍ[S])).re := by
  rw [FieldEquations.LinearizedGravity.G_lorenz_gauge D h hc hL μ ν, box_bridge]
  ring

end Field

theorem quaternion_gauge_bianchi {ι S : Type*} [CommRing S] (A : ι → ℍ[S])
    (dA : ι → ι → ℍ[S]) (ddA : ι → ι → ι → ℍ[S]) (hsym : ∀ i j k, ddA i j k = ddA j i k)
    (e c d : ι) :
    FieldEquations.Curvature.Dcurv A dA ddA e c d + FieldEquations.Curvature.Dcurv A dA ddA c d e
      + FieldEquations.Curvature.Dcurv A dA ddA d e c = 0 :=
  FieldEquations.Curvature.gauge_bianchi A dA ddA hsym e c d

end FieldEquations.FueterForms
