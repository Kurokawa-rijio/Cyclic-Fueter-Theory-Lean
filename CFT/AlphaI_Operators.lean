/-
  α-I.1(Y1):Fueter 作用素の規約と二乗の公式(台帳 Y1 の中心の式)

  関数の環 R(可換環)と、互いに可換な四つの導分 ∂₀, …, ∂₃(座標の偏微分の代数的な抽象)。
  四元数に値をとる関数 f ∈ ℍ[R] には成分ごとに作用させる(dq)。係数は左から掛ける。
  実四元数の規約:
    D_R = ∂₀ + i∂₁ + j∂₂ + k∂₃、 D̄_R = ∂₀ − i∂₁ − j∂₂ − k∂₃、 Δ₄ = Σ ∂_a²、 □ = ∂₀² − ∂₁² − ∂₂² − ∂₃²
  定理:
    * conj_product:D̄_R D_R = Δ₄、 product_conj:D_R D̄_R = Δ₄(Euclid の Laplacian、すべて +)
    * square:D_R² = □ + 2∂₀(i∂₁ + j∂₂ + k∂₃)(スカラー部分は □ だが、ベクトル部分が残る)
    * square_sum:D_R² + D̄_R² = 2□(ベクトル部分は打ち消す)
  双四元数の規約(R の元 I、I² = −1、∂I = 0、四元数の単位と可換):
    D = ∂₀ + I(i∂₁ + j∂₂ + k∂₃)、 D̄ = ∂₀ − I(i∂₁ + j∂₂ + k∂₃)
    * biquaternion_box:D̄D = DD̄ = □(Lorentz の d'Alembertian)
  これで「□ は実四元数では共役積ではなく二乗の和から、双四元数では共役積から出る」という
  規約の区別(results-and-corrections の正準の表)が定理になる。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open Quaternion

namespace CFT.Operators

set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R]

/-- 成分ごとの導分 -/
def dq (d : Derivation ℤ R R) (f : ℍ[R]) : ℍ[R] := ⟨d f.re, d f.imI, d f.imJ, d f.imK⟩

/-- 単位 1, i, j, k -/
def e : Fin 4 → ℍ[R] := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

variable (d : Fin 4 → Derivation ℤ R R)

/-- D_R = Σ e_a ∂_a(係数は左から) -/
def DR (f : ℍ[R]) : ℍ[R] := ∑ a, e a * dq (d a) f
/-- D̄_R = Σ ē_a ∂_a -/
def DRbar (f : ℍ[R]) : ℍ[R] := ∑ a, star (e a) * dq (d a) f
/-- Δ₄ = Σ ∂_a² -/
def Lap (f : ℍ[R]) : ℍ[R] := ∑ a, dq (d a) (dq (d a) f)
/-- □ = ∂₀² − ∂₁² − ∂₂² − ∂₃² -/
def Box (f : ℍ[R]) : ℍ[R] :=
  dq (d 0) (dq (d 0) f) - dq (d 1) (dq (d 1) f) - dq (d 2) (dq (d 2) f) - dq (d 3) (dq (d 3) f)
/-- ベクトル部分 i∂₁ + j∂₂ + k∂₃ -/
def Vec (f : ℍ[R]) : ℍ[R] := e 1 * dq (d 1) f + e 2 * dq (d 2) f + e 3 * dq (d 3) f

section
variable (hc : ∀ a b x, d a (d b x) = d b (d a x))
include hc

/-- 可換性を正規形に:添字の大きい方を外に出さない -/
private theorem c10 (x : R) : d 1 (d 0 x) = d 0 (d 1 x) := hc 1 0 x
private theorem c20 (x : R) : d 2 (d 0 x) = d 0 (d 2 x) := hc 2 0 x
private theorem c30 (x : R) : d 3 (d 0 x) = d 0 (d 3 x) := hc 3 0 x
private theorem c21 (x : R) : d 2 (d 1 x) = d 1 (d 2 x) := hc 2 1 x
private theorem c31 (x : R) : d 3 (d 1 x) = d 1 (d 3 x) := hc 3 1 x
private theorem c32 (x : R) : d 3 (d 2 x) = d 2 (d 3 x) := hc 3 2 x

theorem conj_product (f : ℍ[R]) : DRbar d (DR d f) = Lap d f := by
  ext <;>
  simp [DR, DRbar, Lap, dq, e, Fin.sum_univ_four, Quaternion.ext_iff, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

theorem product_conj (f : ℍ[R]) : DR d (DRbar d f) = Lap d f := by
  ext <;>
  simp [DR, DRbar, Lap, dq, e, Fin.sum_univ_four, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

theorem square (f : ℍ[R]) :
    DR d (DR d f) = Box d f + (2 : R) • dq (d 0) (Vec d f) := by
  ext <;>
  simp [DR, Box, Vec, dq, e, Fin.sum_univ_four, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

theorem square_sum (f : ℍ[R]) : DR d (DR d f) + DRbar d (DRbar d f) = (2 : R) • Box d f := by
  ext <;>
  simp [DR, DRbar, Box, dq, e, Fin.sum_univ_four, map_add, map_sub, map_neg,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;> ring

/-! ### 双四元数 -/

variable (I : R) (hI : I * I = -1) (hdI : ∀ a, d a I = 0)

/-- D = ∂₀ + I(i∂₁ + j∂₂ + k∂₃) -/
def DB (f : ℍ[R]) : ℍ[R] := dq (d 0) f + I • Vec d f
/-- D̄ = ∂₀ − I(i∂₁ + j∂₂ + k∂₃) -/
def DBbar (f : ℍ[R]) : ℍ[R] := dq (d 0) f - I • Vec d f

include hI hdI

theorem biquaternion_box (f : ℍ[R]) :
    DBbar d I (DB d I f) = Box d f ∧ DB d I (DBbar d I f) = Box d f := by
  have hd : ∀ a x, d a (I * x) = I * d a x := by
    intro a x; rw [Derivation.leibniz, hdI a]; simp [smul_eq_mul]
  constructor <;>
  ext <;>
  simp [DB, DBbar, Box, Vec, dq, e, map_add, map_sub, map_neg, hd,
    c10 d hc, c20 d hc, c30 d hc, c21 d hc, c31 d hc, c32 d hc] <;>
  (ring_nf; simp only [show I ^ 2 = -1 by rw [sq, hI]]; ring)

end

end CFT.Operators
