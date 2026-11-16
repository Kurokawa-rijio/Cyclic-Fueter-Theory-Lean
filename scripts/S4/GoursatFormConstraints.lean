/-! ### B. Goursat の形と拘束の伝播 -/

section Goursat
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- uu の拘束(Raychaudhuri):C_u = r_uu − (Ω_u/Ω) r_u + 2ℓ² W_u²/r -/
def Cu (Om r W l : S) : S := d 0 (d 0 r) - d 0 Om * Om⁻¹ * d 0 r + 2 * l ^ 2 * (d 0 W) ^ 2 * r⁻¹
/-- vv の拘束 -/
def Cv (Om r W l : S) : S := d 1 (d 1 r) - d 1 Om * Om⁻¹ * d 1 r + 2 * l ^ 2 * (d 1 W) ^ 2 * r⁻¹

theorem constraint_uu (W Om r s c l : S) (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 0 - 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 0
      = -(2 * r⁻¹) * Cu d Om r W l := by
  rw [einN_00 d Om r s c H, tymN_00 d W s H.hO H.hr H.hs, Cu]; ring

theorem constraint_vv (W Om r s c l : S) (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 1 1 - 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 1 1
      = -(2 * r⁻¹) * Cv d Om r W l := by
  rw [einN_11 d Om r s c H, tymN_11 d W s H.hO H.hr H.hs, Cv]; ring

/-- Goursat の形(r):uv 成分の Einstein 方程式から r_uv を 1 階微分で書く -/
theorem goursat_r (W Om r s c l : S) (H : SphN d Om r s c)
    (hE : Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 1 = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 1) :
    d 0 (d 1 r) = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹ := by
  have hm := (CFT.S4J.mixed_eq d W Om r s c l H).mp hE
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ H.hr
  generalize r⁻¹ = ir at hir hm ⊢
  linear_combination ir * hm + ((-1 : S) * (d 0 (d 1 r))) * hir

/-- Goursat の形(Ω):θθ 成分の Einstein 方程式から Ω_uv -/
theorem goursat_Om (W Om r s c l : S) (H : SphN d Om r s c)
    (hE : Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 2 2 = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 2 2) :
    d 0 (d 1 Om) = d 0 Om * d 1 Om * Om⁻¹ - 2 * Om * d 0 (d 1 r) * r⁻¹ - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4 := by
  rw [einN_22 d Om r s c H, tymN_22 d W s H.hO H.hr H.hs] at hE
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ H.hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ H.hr
  generalize Om⁻¹ = iOm at hiOm hE ⊢
  generalize r⁻¹ = ir at hir hE ⊢
  linear_combination ((-1 : S) * Om ^ 2 * ir ^ 2) * hE + ((1 : S) * Om * (d 0 Om) * (d 1 Om) * iOm ^ 2 * ir ^ 2 * r ^ 2 + (-1 : S) * Om * (d 0 (d 1 Om)) * iOm * ir ^ 2 * r ^ 2 + (-2 : S) * Om * ir ^ 2 * r * (d 0 (d 1 r)) + (1 : S) * (d 0 Om) * (d 1 Om) * iOm * ir ^ 2 * r ^ 2 + (-1 : S) * (d 0 (d 1 Om)) * ir ^ 2 * r ^ 2) * hiOm + ((-2 : S) * Om * ir * (d 0 (d 1 r)) + (1 : S) * (d 0 Om) * (d 1 Om) * iOm * ir * r + (1 : S) * (d 0 Om) * (d 1 Om) * iOm + (-1 : S) * (d 0 (d 1 Om)) * ir * r + (-1 : S) * (d 0 (d 1 Om))) * hir

/-- Goursat の形(W):YM 方程式から W_uv = ½ Ω W(1 − W²)/r²(Z8 の式) -/
theorem goursat_W (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0)
    (hY : YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = 0) :
    d 0 (d 1 W) = 2⁻¹ * Om * W * (1 - W ^ 2) * r⁻¹ ^ 2 := by
  rw [ymN_02 d W Om r s c H W2 W3] at hY
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ H.hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ H.hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ H.hs
  generalize Om⁻¹ = iOm at hiOm hY ⊢
  generalize r⁻¹ = ir at hir hY ⊢
  generalize s⁻¹ = is at his hY ⊢
  linear_combination (-(2⁻¹ : S) * is) * hY + ((-1/2 : S) * Om * W ^ 3 * ir ^ 2 + (1/2 : S) * Om * W * ir ^ 2 + (-1 : S) * (d 0 (d 1 W))) * his

/-- 拘束の伝播(u の拘束を v の方向に):Goursat の三つの式のもとで ∂_v C_u = −(r_v/r) C_u -/
theorem constraint_prop_u (W Om r s c l : S) (H : SphN d Om r s c) (dl : ∀ i, d i l = 0)
    (hr : d 0 (d 1 r) = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹)
    (hO : d 0 (d 1 Om) = d 0 Om * d 1 Om * Om⁻¹ - 2 * Om * d 0 (d 1 r) * r⁻¹ - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4)
    (hW : d 0 (d 1 W) = 2⁻¹ * Om * W * (1 - W ^ 2) * r⁻¹ ^ 2) :
    d 1 (Cu d Om r W l) = -(d 1 r * r⁻¹) * Cu d Om r W l := by
  obtain ⟨hO, hr', hs, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr'
  have d2 : ∀ i, d i (2 : S) = 0 := fun i => deriv_ofNat (d i) 2
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, d2 i]; ring
  have kr := comm 1 0 r
  have kO := comm 1 0 Om
  have kW := comm 1 0 W
  have k1 : d 1 (d 0 (d 0 r)) = d 0 (d 0 (d 1 r)) := by rw [comm 1 0 (d 0 r), kr]
  have hr1 : d 0 (d 0 (d 1 r)) = d 0 (2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹) := by
    rw [hr]
  simp only [Cu, k1, map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, iO, ir, dl, d2, d2i,
    kr, kO, kW, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul] at hr1 ⊢
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr'
  generalize Om⁻¹ = iOm at hiOm hr hO hW hr1 ⊢
  generalize r⁻¹ = ir at hir hr hO hW hr1 ⊢
  linear_combination ((1 : S)) * hr1 + ((-1 : S) * iOm * (d 0 r)) * hO + ((4 : S) * (d 0 W) * ir * l ^ 2) * hW + ((2 : S) * Om * iOm * ir * (d 0 r) + (-1 : S) * (d 0 Om) * iOm + (-1 : S) * ir * (d 0 r)) * hr + ((2 : S) * Om * W ^ 4 * ir ^ 4 * l ^ 2 * (d 0 r) + (-4 : S) * Om * W ^ 2 * ir ^ 4 * l ^ 2 * (d 0 r) + (2 : S) * Om * ir ^ 4 * l ^ 2 * (d 0 r) + (-1 : S) * Om * ir ^ 2 * (d 0 r) + (-1/2 : S) * (d 0 Om) * W ^ 4 * ir ^ 3 * l ^ 2 + (1 : S) * (d 0 Om) * W ^ 2 * ir ^ 3 * l ^ 2 + (-1/2 : S) * (d 0 Om) * ir ^ 3 * l ^ 2 + (1/2 : S) * (d 0 Om) * ir + (-2 : S) * ir ^ 2 * (d 0 r) ^ 2 * (d 1 r)) * hiOm

/-- 拘束の伝播(v の拘束を u の方向に):∂_u C_v = −(r_u/r) C_v -/
theorem constraint_prop_v (W Om r s c l : S) (H : SphN d Om r s c) (dl : ∀ i, d i l = 0)
    (hr : d 0 (d 1 r) = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹)
    (hO : d 0 (d 1 Om) = d 0 Om * d 1 Om * Om⁻¹ - 2 * Om * d 0 (d 1 r) * r⁻¹ - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4)
    (hW : d 0 (d 1 W) = 2⁻¹ * Om * W * (1 - W ^ 2) * r⁻¹ ^ 2) :
    d 0 (Cv d Om r W l) = -(d 0 r * r⁻¹) * Cv d Om r W l := by
  obtain ⟨hO, hr', hs, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr'
  have d2 : ∀ i, d i (2 : S) = 0 := fun i => deriv_ofNat (d i) 2
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, d2 i]; ring
  have kr := comm 1 0 r
  have kO := comm 1 0 Om
  have kW := comm 1 0 W
  have k1 : d 0 (d 1 (d 1 r)) = d 1 (d 0 (d 1 r)) := by rw [comm 0 1 (d 1 r)]
  have hr1 : d 1 (d 0 (d 1 r)) = d 1 (2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹) := by
    rw [hr]
  simp only [Cv, k1, map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, iO, ir, dl, d2, d2i,
    kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul] at hr1 ⊢
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr'
  generalize Om⁻¹ = iOm at hiOm hr hO hW hr1 ⊢
  generalize r⁻¹ = ir at hir hr hO hW hr1 ⊢
  linear_combination ((1 : S)) * hr1 + ((-1 : S) * iOm * (d 1 r)) * hO + ((4 : S) * (d 1 W) * ir * l ^ 2) * hW + ((2 : S) * Om * iOm * ir * (d 1 r) + (-1 : S) * (d 1 Om) * iOm + (-1 : S) * ir * (d 1 r)) * hr + ((2 : S) * Om * W ^ 4 * ir ^ 4 * l ^ 2 * (d 1 r) + (-4 : S) * Om * W ^ 2 * ir ^ 4 * l ^ 2 * (d 1 r) + (2 : S) * Om * ir ^ 4 * l ^ 2 * (d 1 r) + (-1 : S) * Om * ir ^ 2 * (d 1 r) + (-1/2 : S) * (d 1 Om) * W ^ 4 * ir ^ 3 * l ^ 2 + (1 : S) * (d 1 Om) * W ^ 2 * ir ^ 3 * l ^ 2 + (-1/2 : S) * (d 1 Om) * ir ^ 3 * l ^ 2 + (1/2 : S) * (d 1 Om) * ir + (-2 : S) * ir ^ 2 * (d 0 r) * (d 1 r) ^ 2) * hiOm

end Goursat
