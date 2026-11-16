/-
  命題集 `LEAN_GAP_TREES.md` 4-5（エネルギー恒等式）。
  `CFT/Spherical/WedgeEYMSystem.lean` の W 方程式
    W_uv = Ω W (1 - W²) / (2 r²)
  だけから、ゲージ場のエネルギー・フラックス恒等式を導く（解の存在は仮定、
  r・Ω の発展方程式は使わない — 4-2 と同じく導分代数の流儀）。
  ポテンシャル V(W) = W²/2 - W⁴/4（V' = W(1-W²)）、A = Ω/(2r²) と置くと
    ∂_v (W_u²/2) - ∂_u (A V) = -V ∂_u A,
    ∂_u (W_v²/2) - ∂_v (A V) = -V ∂_v A,
  したがってフラックス F^u = W_v²/2 - A V, F^v = W_u²/2 - A V に対し
    ∂_u F^u + ∂_v F^v = -V (∂_u A + ∂_v A)。
  V(W) = W²(2-W²)/4 ≥ 0 ⟺ |W| ≤ √2（データは |W| ≤ 1）。
  sympy による jet 空間での厳密チェック：`cft/wedge45_check.py`（再実行クリーン、
  W_uv の係数を摂動させると恒等式は壊れる）。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.WedgeEnergy

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]

/-- 導分の逆元の公式（`WedgeConstraintPropagation.lean` と同じもの）。 -/
theorem deriv_inv (d : Derivation ℤ S S) (a : S) (ha : a ≠ 0) : d a⁻¹ = -(a⁻¹ ^ 2 * d a) := by
  have h : d (a * a⁻¹) = 0 := by rw [mul_inv_cancel₀ ha]; exact d.map_one_eq_zero
  rw [Derivation.leibniz] at h
  simp only [smul_eq_mul] at h
  have e : d a⁻¹ = a⁻¹ * (a * d a⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [e, show a * d a⁻¹ = -(a⁻¹ * d a) by linear_combination h]
  ring

omit [CharZero S] in
theorem deriv_ofNat (d : Derivation ℤ S S) (n : ℕ) [n.AtLeastTwo] : d (OfNat.ofNat n : S) = 0 := by
  have : (OfNat.ofNat n : S) = ((n : ℕ) : S) := (Nat.cast_ofNat).symm
  rw [this]; exact d.map_natCast n

/-- (4 : S) ≠ 0 in characteristic zero (`four_ne_zero` needs a `NeZero 4` instance). -/
theorem four_ne_zero_S : (4 : S) ≠ 0 := by
  rw [show (4 : S) = ((4 : ℕ) : S) by norm_cast]
  exact Nat.cast_ne_zero.mpr (by norm_num)

variable (du dv : Derivation ℤ S S) (r Om W : S)

/-- ポテンシャル V(W) = W²/2 - W⁴/4。V' = W - W³ = W(1-W²)。 -/
noncomputable def wedgePot (W : S) : S := W ^ 2 / 2 - W ^ 4 / 4

/-- 係数 A = Ω/(2r²)。 -/
noncomputable def wedgeA (Om r : S) : S := 2⁻¹ * Om * (r⁻¹) ^ 2

/-- W_uv の右辺（`WedgeEYMSystem.rhsW` と同じもの）。 -/
noncomputable def wedgeWuv (Om W r : S) : S :=
  2⁻¹ * Om * W * (1 - W ^ 2) * (r⁻¹) ^ 2

/-- フラックスの u 成分 F^u = W_v²/2 - A V。 -/
noncomputable def wedgeFu (dv : Derivation ℤ S S) (Om W r : S) : S :=
  (dv W) ^ 2 / 2 - wedgeA Om r * wedgePot W

/-- フラックスの v 成分 F^v = W_u²/2 - A V。 -/
noncomputable def wedgeFv (du : Derivation ℤ S S) (Om W r : S) : S :=
  (du W) ^ 2 / 2 - wedgeA Om r * wedgePot W

/-- 4-5 の代数核：恒等式は W 方程式に W_u を掛けたものに他ならない。 -/
theorem wedge_energy_algebraic (W Wu Wuv A Au : S)
    (eW : Wuv = A * (W - W ^ 3)) :
    Wu * Wuv - (Au * wedgePot W + A * (W - W ^ 3) * Wu)
      = - wedgePot W * Au := by
  rw [eW]
  simp only [wedgePot]
  ring

/-- A の u 微分の明示形。 -/
theorem wedgeA_du (hr : r ≠ 0) :
    du (wedgeA Om r) = 2⁻¹ * du Om * (r⁻¹) ^ 2 - Om * (r⁻¹) ^ 3 * du r := by
  have h2 : du (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat du 2]; ring
  simp only [wedgeA, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hr,
    deriv_ofNat, Derivation.map_one_eq_zero, h2,
    deriv_ofNat du 2, deriv_ofNat du 4, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- A の v 微分の明示形。 -/
theorem wedgeA_dv (hr : r ≠ 0) :
    dv (wedgeA Om r) = 2⁻¹ * dv Om * (r⁻¹) ^ 2 - Om * (r⁻¹) ^ 3 * dv r := by
  have h2 : dv (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dv 2]; ring
  simp only [wedgeA, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hr,
    deriv_ofNat, Derivation.map_one_eq_zero, h2,
    deriv_ofNat dv 2, deriv_ofNat dv 4, nsmul_eq_mul, Nat.cast_ofNat]
  ring

section
variable (hr : r ≠ 0)
  (hc : ∀ f, du (dv f) = dv (du f))
  (eW : du (dv W) = wedgeWuv Om W r)
include hr hc eW

/-- 4-5（v 方向のエネルギー恒等式）：∂_v (W_u²/2) - ∂_u (A V) = -V ∂_u A。 -/
theorem wedge_energy_v :
    dv ((du W) ^ 2 / 2) - du (wedgeA Om r * wedgePot W)
      = - wedgePot W * du (wedgeA Om r) := by
  have hW : dv (du W) = wedgeWuv Om W r := by rw [← hc W, eW]
  have h2u : du (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat du 2]; ring
  have h4u : du (4⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ four_ne_zero_S, deriv_ofNat du 4]; ring
  have h2v : dv (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dv 2]; ring
  have h4v : dv (4⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ four_ne_zero_S, deriv_ofNat dv 4]; ring
  have key : dv ((du W) ^ 2 / 2) - du (wedgeA Om r * wedgePot W)
      = du W * (wedgeA Om r * (W - W ^ 3))
        - (du (wedgeA Om r) * wedgePot W + wedgeA Om r * (W - W ^ 3) * du W) := by
    simp only [wedgePot, wedgeA, wedgeWuv, div_eq_mul_inv, map_add, map_sub, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      deriv_inv _ _ hr, deriv_ofNat, Derivation.map_one_eq_zero, hW,
      h2u, h4u, h2v, h4v,
      deriv_ofNat du 2, deriv_ofNat du 4, deriv_ofNat dv 2, deriv_ofNat dv 4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [key]
  ring

omit hc in
/-- 4-5（u 方向のエネルギー恒等式）：∂_u (W_v²/2) - ∂_v (A V) = -V ∂_v A。
    こちらは可換性 hc を使わない（eW を直接使う）。 -/
theorem wedge_energy_u :
    du ((dv W) ^ 2 / 2) - dv (wedgeA Om r * wedgePot W)
      = - wedgePot W * dv (wedgeA Om r) := by
  have h2u : du (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat du 2]; ring
  have h4u : du (4⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ four_ne_zero_S, deriv_ofNat du 4]; ring
  have h2v : dv (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dv 2]; ring
  have h4v : dv (4⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ four_ne_zero_S, deriv_ofNat dv 4]; ring
  have key : du ((dv W) ^ 2 / 2) - dv (wedgeA Om r * wedgePot W)
      = dv W * (wedgeA Om r * (W - W ^ 3))
        - (dv (wedgeA Om r) * wedgePot W + wedgeA Om r * (W - W ^ 3) * dv W) := by
    simp only [wedgePot, wedgeA, wedgeWuv, div_eq_mul_inv, map_add, map_sub, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
      deriv_inv _ _ hr, deriv_ofNat, Derivation.map_one_eq_zero, eW,
      h2u, h4u, h2v, h4v,
      deriv_ofNat du 2, deriv_ofNat du 4, deriv_ofNat dv 2, deriv_ofNat dv 4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [key]
  ring

/-- 4-5（フラックス形）：∂_u F^u + ∂_v F^v = -V (∂_u A + ∂_v A)。 -/
theorem wedge_energy_flux :
    du (wedgeFu dv Om W r) + dv (wedgeFv du Om W r)
      = - wedgePot W * (du (wedgeA Om r) + dv (wedgeA Om r)) := by
  have hv := wedge_energy_v du dv r Om W hr hc eW
  have hu := wedge_energy_u du dv r Om W hr eW
  simp only [wedgeFu, wedgeFv, map_add, map_sub]
  linear_combination hu + hv

end

end CFT.WedgeEnergy
