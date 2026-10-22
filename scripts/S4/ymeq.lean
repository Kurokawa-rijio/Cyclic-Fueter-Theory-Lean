/-! ### A. 二重ヌル座標の YM 方程式(Z8 の W_uv の式を F = dA + A∧A から導く) -/

section YMEq
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

theorem eps3_table : (eps3 : Fin 3 → Fin 3 → Fin 3 → S) =
    ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
      ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] := by
  funext a b e
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp [eps3]

/-- 上付きの F^{aμν} = g^{μα} g^{νβ} F^a_αβ -/
def Fup (gi : Fin 4 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S) (a : Fin 3) (m n : Fin 4) : S :=
  ∑ al, ∑ be, gi m al * gi n be * F a al be

/-- YM 方程式 √−g D_μ F^{aμν} = ∂_μ(√−g F^{aμν}) + √−g ε_abc A^b_μ F^{cμν} -/
def YMeq (gi : Fin 4 → Fin 4 → S) (sg : S) (Aa : Fin 3 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S)
    (a : Fin 3) (n : Fin 4) : S :=
  ∑ m, d m (sg * Fup gi F a m n) + sg * ∑ m, ∑ b, ∑ e, eps3 a b e * Aa b m * Fup gi F e m n

set_option maxHeartbeats 0 in
theorem ymN_00 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 0 0 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1 : S) * (d 1 W) * c * ir ^ 2 * is ^ 2 * r ^ 2 * s ^ 2 + (1 : S) * (d 1 W) * c * ir ^ 2 * r ^ 2) * hiOm + ((-1 : S) * (d 1 W) * c * ir * is ^ 2 * r * s ^ 2 + (1 : S) * (d 1 W) * c * ir * r + (-1 : S) * (d 1 W) * c * is ^ 2 * s ^ 2 + (1 : S) * (d 1 W) * c) * hir + ((-1 : S) * (d 1 W) * c * is * s + (-1 : S) * (d 1 W) * c) * his

set_option maxHeartbeats 0 in
theorem ymN_01 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 0 1 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1 : S) * (d 0 W) * c * ir ^ 2 * is ^ 2 * r ^ 2 * s ^ 2 + (1 : S) * (d 0 W) * c * ir ^ 2 * r ^ 2) * hiOm + ((-1 : S) * (d 0 W) * c * ir * is ^ 2 * r * s ^ 2 + (1 : S) * (d 0 W) * c * ir * r + (-1 : S) * (d 0 W) * c * is ^ 2 * s ^ 2 + (1 : S) * (d 0 W) * c) * hir + ((-1 : S) * (d 0 W) * c * is * s + (-1 : S) * (d 0 W) * c) * his

set_option maxHeartbeats 0 in
theorem ymN_02 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = (-1 : S) * Om * W ^ 3 * r⁻¹ ^ 2 * s + (1 : S) * Om * W * r⁻¹ ^ 2 * s + (-2 : S) * (d 0 (d 1 W)) * s := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * (d 0 Om) * (d 1 W) * iOm * ir ^ 2 * r ^ 2 * s + (1 : S) * (d 1 Om) * (d 0 W) * iOm * ir ^ 2 * r ^ 2 * s + (2 : S) * (d 0 W) * ir ^ 3 * r ^ 2 * (d 1 r) * s + (-2 : S) * (d 0 W) * ir ^ 2 * r * (d 1 r) * s + (-2 : S) * (d 0 (d 1 W)) * ir ^ 2 * r ^ 2 * s + (2 : S) * (d 1 W) * ir ^ 3 * r ^ 2 * (d 0 r) * s + (-2 : S) * (d 1 W) * ir ^ 2 * r * (d 0 r) * s) * hiOm + ((-1 : S) * Om * W ^ 3 * ir ^ 3 * is ^ 2 * r * s ^ 3 + (-1 : S) * Om * W ^ 3 * ir ^ 2 * is ^ 2 * s ^ 3 + (1 : S) * Om * W * ir ^ 3 * is ^ 2 * r * s ^ 3 + (1 : S) * Om * W * ir ^ 2 * is ^ 2 * s ^ 3 + (2 : S) * (d 0 W) * ir ^ 2 * r * (d 1 r) * s + (-2 : S) * (d 0 (d 1 W)) * ir * r * s + (-2 : S) * (d 0 (d 1 W)) * s + (2 : S) * (d 1 W) * ir ^ 2 * r * (d 0 r) * s) * hir + ((-1 : S) * Om * W ^ 3 * ir ^ 2 * is * s ^ 2 + (-1 : S) * Om * W ^ 3 * ir ^ 2 * s + (1 : S) * Om * W * ir ^ 2 * is * s ^ 2 + (1 : S) * Om * W * ir ^ 2 * s) * his

set_option maxHeartbeats 0 in
theorem ymN_03 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 0 3 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_10 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 1 0 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_11 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 1 1 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_12 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 1 2 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_13 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 1 3 = (-1 : S) * Om * W ^ 3 * r⁻¹ ^ 2 + (1 : S) * Om * W * r⁻¹ ^ 2 + (-2 : S) * (d 0 (d 1 W)) := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * (d 0 Om) * (d 1 W) * iOm * ir ^ 2 * is ^ 2 * r ^ 2 * s ^ 2 + (1 : S) * (d 1 Om) * (d 0 W) * iOm * ir ^ 2 * is ^ 2 * r ^ 2 * s ^ 2 + (2 : S) * (d 0 W) * ir ^ 3 * is ^ 2 * r ^ 2 * (d 1 r) * s ^ 2 + (-2 : S) * (d 0 W) * ir ^ 2 * is ^ 2 * r * (d 1 r) * s ^ 2 + (-2 : S) * (d 0 (d 1 W)) * ir ^ 2 * is ^ 2 * r ^ 2 * s ^ 2 + (2 : S) * (d 1 W) * ir ^ 3 * is ^ 2 * r ^ 2 * (d 0 r) * s ^ 2 + (-2 : S) * (d 1 W) * ir ^ 2 * is ^ 2 * r * (d 0 r) * s ^ 2) * hiOm + ((-1 : S) * Om * W ^ 3 * ir ^ 3 * is ^ 2 * r * s ^ 2 + (-1 : S) * Om * W ^ 3 * ir ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * Om * W * ir ^ 3 * is ^ 2 * r * s ^ 2 + (1 : S) * Om * W * ir ^ 2 * is ^ 2 * s ^ 2 + (2 : S) * (d 0 W) * ir ^ 2 * is ^ 2 * r * (d 1 r) * s ^ 2 + (-2 : S) * (d 0 (d 1 W)) * ir * is ^ 2 * r * s ^ 2 + (-2 : S) * (d 0 (d 1 W)) * is ^ 2 * s ^ 2 + (2 : S) * (d 1 W) * ir ^ 2 * is ^ 2 * r * (d 0 r) * s ^ 2) * hir + ((-1 : S) * Om * W ^ 3 * ir ^ 2 * is * s + (-1 : S) * Om * W ^ 3 * ir ^ 2 + (1 : S) * Om * W * ir ^ 2 * is * s + (1 : S) * Om * W * ir ^ 2 + (-2 : S) * (d 0 (d 1 W)) * is * s + (-2 : S) * (d 0 (d 1 W))) * his

set_option maxHeartbeats 0 in
theorem ymN_20 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 2 0 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_21 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 2 1 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_22 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 2 2 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ymN_23 (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 2 3 = 0 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-2 : S) * Om * W ^ 2 * c * ir ^ 3 * is ^ 3 * r * s ^ 2 + (2 : S) * Om * W ^ 2 * c * ir ^ 3 * is ^ 2 * r * s + (-2 : S) * Om * W ^ 2 * c * ir ^ 2 * is ^ 3 * s ^ 2 + (2 : S) * Om * W ^ 2 * c * ir ^ 2 * is ^ 2 * s + (2 : S) * Om * c * ir ^ 3 * is ^ 3 * r * s ^ 2 + (-2 : S) * Om * c * ir ^ 3 * is ^ 2 * r * s + (2 : S) * Om * c * ir ^ 2 * is ^ 3 * s ^ 2 + (-2 : S) * Om * c * ir ^ 2 * is ^ 2 * s) * hir + ((-2 : S) * Om * W ^ 2 * c * ir ^ 2 * is ^ 2 * s + (2 : S) * Om * c * ir ^ 2 * is ^ 2 * s) * his

end YMEq
