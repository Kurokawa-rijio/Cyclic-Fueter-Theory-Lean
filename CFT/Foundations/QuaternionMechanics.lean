/-
  「外」に残っていた力学・測地線を四元数で書き直す(2026-11-18)

  * Kepler 問題(Kustaanheimo–Stiefel 変換):四元数 q から x = q i q̄ を作る。
    - `ks_pure`:x は純虚(3 次元のベクトル)。`ks_norm`:|x|² = |q|⁴(|x| = |q|²)。
    - `ks_velocity`:ẋ = q̇ i q̄ + q i \bar{q̇} について |ẋ|² = 4|q|²|q̇|² − 4 (Re(q̇ i q̄))²。
      KS の条件 Re(q̇ i q̄) = 0 のもとで |ẋ|² = 4|q|²|q̇|²(`ks_speed`)。
    - `ks_oscillator`:仮想時間 ds = dt/r(q′ = r q̇)に移ると、Kepler のエネルギーの式
      E = ½|ẋ|² − k/r は 2|q′|² − E|q|² = k に書き換わる(4 次元の調和振動子のエネルギーの形)。
      示しているのはこの代数的な書き換えだけで、|ẋ|² = 4r|q̇|²、|q′|² = r²|q̇|² は仮定 hX、hY′ として与える。
      運動方程式が 4 次元の調和振動子 q″ = (E/2) q になることは示していない。
  * 剛体:
    - `dq_mul`、`dq_star`:成分ごとの微分は四元数の積と共役を通る(Leibniz)。
    - `attitude_unit`:姿勢の式 2q̇ = qω(ω は純虚の角速度)なら |q|² は一定(単位四元数のまま)。
    - `euler_commutator`:L = Iω(体の角運動量)について Lω − ωL = 2(Iω × ω)。
      Euler の方程式 I ω̇ = (Iω) × ω は I ω̇ = ½[L, ω](四元数の交換子)。
  * 測地線(四元数の枠):4 次元の正規直交枠では接続は so(4) ≅ su(2) ⊕ su(2) に値をとり、
    ℍ ≅ ℝ⁴ に V ↦ PV − VQ(P, Q は純虚、左と右からの掛け算。`SelfDualTwoForms` の Λ²₊ ⊕ Λ²₋)で作用する。
    - `frame_geodesic_speed`:枠での測地線の式 V̇ = −(PV − VQ) なら |V|² は一定(速さが保たれる)。
-/
import CFT.Foundations.FueterOperatorSquares
import Mathlib.Tactic

open Quaternion CFT.Operators

namespace CFT.QuatMech

set_option maxHeartbeats 2000000

section Algebra

variable {R : Type*} [CommRing R]

/-- 単位 i -/
def qi : ℍ[R] := ⟨0, 1, 0, 0⟩

theorem ks_pure (q : ℍ[R]) : (q * qi * star q).re = 0 := by
  simp [qi] <;> ring

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

/-- 剛体:Lω − ωL = 2(Iω × ω) -/
theorem euler_commutator (I1 I2 I3 w1 w2 w3 : R) :
    (⟨0, I1 * w1, I2 * w2, I3 * w3⟩ : ℍ[R]) * ⟨0, w1, w2, w3⟩
      - (⟨0, w1, w2, w3⟩ : ℍ[R]) * ⟨0, I1 * w1, I2 * w2, I3 * w3⟩
      = ⟨0, 2 * ((I2 - I3) * w2 * w3), 2 * ((I3 - I1) * w3 * w1), 2 * ((I1 - I2) * w1 * w2)⟩ := by
  ext <;> simp <;> ring

end Algebra

/-- Kepler ↔ 4 次元の調和振動子(仮想時間 ds = dt/r) -/
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

/-- 枠での測地線:V̇ = −(PV − VQ)(P、Q は純虚)なら |V|² は一定 -/
theorem frame_geodesic_speed (V P Q : ℍ[R]) (hP : star P = -P) (hQ : star Q = -Q)
    (hV : dq d V = -(P * V - V * Q)) : dq d (V * star V) = 0 := by
  rw [dq_mul, dq_star, hV, star_neg, star_sub, star_mul, star_mul, hP, hQ]
  have e : -(P * V - V * Q) * star V + V * -(star V * -P - -Q * star V)
      = -(P * (V * star V)) + (V * star V) * P := by noncomm_ring
  rw [e, Quaternion.self_mul_star, ← Quaternion.coe_commutes]
  abel

end Deriv

/-- 剛体の姿勢:2q̇ = qω(ω は純虚)なら |q|² は一定 -/
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

end CFT.QuatMech
