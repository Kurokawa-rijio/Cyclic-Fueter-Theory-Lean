import FieldEquations.Quaternionic.Operators
import Mathlib.Tactic

/-
# Quaternionic mechanics

* Kustaanheimo–Stiefel map x = q i q̄: x is pure (`ks_pure`), |x| = |q|² (`ks_norm`), the speed
  identity (`ks_velocity`, `ks_speed`), and the Kepler energy relation rewritten in the form
  2|q′|² − E|q|² = k (`ks_oscillator`; an algebraic rewriting with the kinematic relations as
  hypotheses, not a derivation of the equation of motion).
* Rigid body: Lω − ωL = 2(Iω × ω) (`euler_commutator`); |q|² is conserved for 2q̇ = qω with ω
  pure (`attitude_unit`).
* Frame geodesics V̇ = −(PV − VQ) with P, Q pure conserve |V|² (`frame_geodesic_speed`).
-/

open Quaternion FieldEquations.QuaternionOperators

namespace FieldEquations.QuaternionMechanics

set_option maxHeartbeats 2000000

section Algebra

variable {R : Type*} [CommRing R]

def qi : ℍ[R] := ⟨0, 1, 0, 0⟩

theorem ks_pure (q : ℍ[R]) : (q * qi * star q).re = 0 := by
  simp [qi] <;> ring

/-- |q i q̄| = |q|². -/
theorem ks_norm (q : ℍ[R]) :
    (q * qi * star q).imI ^ 2 + (q * qi * star q).imJ ^ 2 + (q * qi * star q).imK ^ 2
      = (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) ^ 2 := by
  simp [qi] <;> ring

theorem ks_velocity (q qd : ℍ[R]) :
    (qd * qi * star q + q * qi * star qd).re ^ 2
      + (qd * qi * star q + q * qi * star qd).imI ^ 2
      + (qd * qi * star q + q * qi * star qd).imJ ^ 2
      + (qd * qi * star q + q * qi * star qd).imK ^ 2
      = 4 * (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)
          * (qd.re ^ 2 + qd.imI ^ 2 + qd.imJ ^ 2 + qd.imK ^ 2)
        - 4 * ((qd * qi * star q).re) ^ 2 := by
  simp [qi] <;> ring

theorem ks_speed (q qd : ℍ[R]) (hKS : (qd * qi * star q).re = 0) :
    (qd * qi * star q + q * qi * star qd).re ^ 2
      + (qd * qi * star q + q * qi * star qd).imI ^ 2
      + (qd * qi * star q + q * qi * star qd).imJ ^ 2
      + (qd * qi * star q + q * qi * star qd).imK ^ 2
      = 4 * (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)
          * (qd.re ^ 2 + qd.imI ^ 2 + qd.imJ ^ 2 + qd.imK ^ 2) := by
  rw [ks_velocity, hKS]; ring

/-- Euler's rigid-body equation as a quaternion commutator. -/
theorem euler_commutator (I1 I2 I3 w1 w2 w3 : R) :
    (⟨0, I1 * w1, I2 * w2, I3 * w3⟩ : ℍ[R]) * ⟨0, w1, w2, w3⟩
      - (⟨0, w1, w2, w3⟩ : ℍ[R]) * ⟨0, I1 * w1, I2 * w2, I3 * w3⟩
      = ⟨0, 2 * ((I2 - I3) * w2 * w3), 2 * ((I3 - I1) * w3 * w1), 2 * ((I1 - I2) * w1 * w2)⟩ := by
  ext <;> simp <;> ring

end Algebra

theorem ks_oscillator {S : Type*} [Field S] [CharZero S] (r E k X Y Y' : S) (hr : r ≠ 0)
    (hE : E = X / 2 - k / r) (hX : X = 4 * r * Y) (hY' : Y' = r ^ 2 * Y) :
    2 * Y' - E * r = k := by
  subst hE hX hY'
  field_simp
  ring

section Deriv

variable {R : Type*} [CommRing R] (d : Derivation ℤ R R)

theorem dq_mul (a b : ℍ[R]) : dq d (a * b) = dq d a * b + a * dq d b := by
  ext <;> simp [dq, Derivation.leibniz] <;> ring

theorem dq_star (a : ℍ[R]) : dq d (star a) = star (dq d a) := by
  ext <;> simp [dq]

theorem dq_add (a b : ℍ[R]) : dq d (a + b) = dq d a + dq d b := by
  ext <;> simp [dq]

theorem frame_geodesic_speed (V P Q : ℍ[R]) (hP : star P = -P) (hQ : star Q = -Q)
    (hV : dq d V = -(P * V - V * Q)) : dq d (V * star V) = 0 := by
  rw [dq_mul, dq_star, hV, star_neg, star_sub, star_mul, star_mul, hP, hQ]
  have e : -(P * V - V * Q) * star V + V * -(star V * -P - -Q * star V)
      = -(P * (V * star V)) + (V * star V) * P := by noncomm_ring
  rw [e, Quaternion.self_mul_star, ← Quaternion.coe_commutes]
  abel

end Deriv

theorem attitude_unit {S : Type*} [Field S] [CharZero S] (d : Derivation ℤ S S)
    (q ω : ℍ[S]) (hω : star ω = -ω) (hq : dq d q + dq d q = q * ω) :
    dq d (q * star q) = 0 := by
  have h1 : dq d (q * star q) + dq d (q * star q)
      = (dq d q + dq d q) * star q + q * star (dq d q + dq d q) := by
    rw [dq_mul, dq_star, star_add]; noncomm_ring
  rw [hq, star_mul, hω] at h1
  have h2 : dq d (q * star q) + dq d (q * star q) = 0 := by
    rw [h1]; noncomm_ring
  ext
  · exact add_self_eq_zero.mp (congrArg (fun x : ℍ[S] => x.re) h2)
  · exact add_self_eq_zero.mp (congrArg (fun x : ℍ[S] => x.imI) h2)
  · exact add_self_eq_zero.mp (congrArg (fun x : ℍ[S] => x.imJ) h2)
  · exact add_self_eq_zero.mp (congrArg (fun x : ℍ[S] => x.imK) h2)

end FieldEquations.QuaternionMechanics
