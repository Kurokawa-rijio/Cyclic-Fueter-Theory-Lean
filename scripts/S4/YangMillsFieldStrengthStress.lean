/-! ### Yang–Mills の場の強さと応力(球対称な磁気的な仮定 A = W τ₁ dθ + (W s τ₂ + c τ₃) dφ) -/

section YM
variable (W s c : S)

/-- Levi-Civita 記号 ε_abc(su(2) の構造定数) -/
def eps3 (a b e : Fin 3) : S :=
  if (a, b, e) = (0, 1, 2) ∨ (a, b, e) = (1, 2, 0) ∨ (a, b, e) = (2, 0, 1) then 1
  else if (a, b, e) = (0, 2, 1) ∨ (a, b, e) = (2, 1, 0) ∨ (a, b, e) = (1, 0, 2) then -1 else 0

/-- 接続 A^a_μ(座標 0, 1 は (t, x) または (u, v)、2 = θ、3 = φ) -/
def Aym : Fin 3 → Fin 4 → S := ![![0, 0, W, 0], ![0, 0, 0, W * s], ![0, 0, 0, c]]

/-- 場の強さ F^a_μν = ∂_μ A^a_ν − ∂_ν A^a_μ + ε_abc A^b_μ A^c_ν -/
def Fym (Aa : Fin 3 → Fin 4 → S) (a : Fin 3) (m n : Fin 4) : S :=
  d m (Aa a n) - d n (Aa a m) + ∑ b, ∑ e, eps3 a b e * Aa b m * Aa e n

/-- F の表 -/
def FT : Fin 3 → Fin 4 → Fin 4 → S :=
  ![![![0, 0, (1 : S) * (d 0 W), 0], ![0, 0, (1 : S) * (d 1 W), 0], ![(-1 : S) * (d 0 W), (-1 : S) * (d 1 W), 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, (1 : S) * (d 0 W) * s], ![0, 0, 0, (1 : S) * (d 1 W) * s], ![0, 0, 0, 0], ![(-1 : S) * (d 0 W) * s, (-1 : S) * (d 1 W) * s, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, (1 : S) * W ^ 2 * s + (-1 : S) * s], ![0, 0, (-1 : S) * W ^ 2 * s + (1 : S) * s, 0]]]

/-- YM の応力 T̂_μν = F^a_μλ F^a_ν^λ − ¼ g_μν F^a_αβ F^{aαβ}(T = T̂/g²、8πG T = 2ℓ² T̂) -/
def Tym (g gi : Fin 4 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S) (m n : Fin 4) : S :=
  ∑ a, ∑ l, ∑ k, F a m l * gi l k * F a n k
    - 4⁻¹ * g m n * ∑ a, ∑ al, ∑ be, ∑ ga, ∑ de, F a al be * gi al ga * gi be de * F a ga de

set_option maxHeartbeats 0 in
theorem fym_eq (W2 : d 2 W = 0) (W3 : d 3 W = 0) (s0 : d 0 s = 0) (s1 : d 1 s = 0) (s2 : d 2 s = c)
    (s3 : d 3 s = 0) (c0 : d 0 c = 0) (c1 : d 1 c = 0) (c2 : d 2 c = -s) (c3 : d 3 c = 0) :
    Fym d (Aym W s c) = FT d W s c := by
  funext a m n
  fin_cases a <;> fin_cases m <;> fin_cases n <;>
    simp [Fym, Aym, FT, eps3, Fin.sum_univ_three, Derivation.leibniz, smul_eq_mul, W2, W3, s0, s1, s2, s3,
      c0, c1, c2, c3] <;> ring

set_option maxHeartbeats 0 in
theorem tymD_00 (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s c) 0 0 =
    (1/2 : S) * N ^ 2 * W ^ 4 * R⁻¹ ^ 4 + (-1 : S) * N ^ 2 * W ^ 2 * R⁻¹ ^ 4 + (1 : S) * N ^ 2 * (d 1 W) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + (1/2 : S) * N ^ 2 * R⁻¹ ^ 4 + (1 : S) * (d 0 W) ^ 2 * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1/2 : S) * N * (d 0 W) ^ 2 * iN * iR ^ 2 * is ^ 2 * s ^ 2 + (-1/2 : S) * N * (d 0 W) ^ 2 * iN * iR ^ 2 + (-1/2 : S) * (d 0 W) ^ 2 * iR ^ 2 * is ^ 2 * s ^ 2 + (-1/2 : S) * (d 0 W) ^ 2 * iR ^ 2) * hiN + ((1/2 : S) * N ^ 2 * W ^ 4 * iR ^ 4 * is * s + (1/2 : S) * N ^ 2 * W ^ 4 * iR ^ 4 + (-1 : S) * N ^ 2 * W ^ 2 * iR ^ 4 * is * s + (-1 : S) * N ^ 2 * W ^ 2 * iR ^ 4 + (1/2 : S) * N ^ 2 * (d 1 W) ^ 2 * iA ^ 2 * iR ^ 2 * is * s + (1/2 : S) * N ^ 2 * (d 1 W) ^ 2 * iA ^ 2 * iR ^ 2 + (1/2 : S) * N ^ 2 * iR ^ 4 * is * s + (1/2 : S) * N ^ 2 * iR ^ 4 + (1/2 : S) * (d 0 W) ^ 2 * iR ^ 2 * is * s + (1/2 : S) * (d 0 W) ^ 2 * iR ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymD_11 (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s c) 1 1 =
    (-1/2 : S) * A ^ 2 * W ^ 4 * R⁻¹ ^ 4 + (1 : S) * A ^ 2 * W ^ 2 * R⁻¹ ^ 4 + (1 : S) * A ^ 2 * (d 0 W) ^ 2 * N⁻¹ ^ 2 * R⁻¹ ^ 2 + (-1/2 : S) * A ^ 2 * R⁻¹ ^ 4 + (1 : S) * (d 1 W) ^ 2 * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1/2 : S) * A * (d 1 W) ^ 2 * iA * iR ^ 2 * is ^ 2 * s ^ 2 + (-1/2 : S) * A * (d 1 W) ^ 2 * iA * iR ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iR ^ 2 * is ^ 2 * s ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iR ^ 2) * hiA + ((-1/2 : S) * A ^ 2 * W ^ 4 * iR ^ 4 * is * s + (-1/2 : S) * A ^ 2 * W ^ 4 * iR ^ 4 + (1 : S) * A ^ 2 * W ^ 2 * iR ^ 4 * is * s + (1 : S) * A ^ 2 * W ^ 2 * iR ^ 4 + (1/2 : S) * A ^ 2 * (d 0 W) ^ 2 * iN ^ 2 * iR ^ 2 * is * s + (1/2 : S) * A ^ 2 * (d 0 W) ^ 2 * iN ^ 2 * iR ^ 2 + (-1/2 : S) * A ^ 2 * iR ^ 4 * is * s + (-1/2 : S) * A ^ 2 * iR ^ 4 + (1/2 : S) * (d 1 W) ^ 2 * iR ^ 2 * is * s + (1/2 : S) * (d 1 W) ^ 2 * iR ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymD_01 (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s c) 0 1 =
    (2 : S) * (d 0 W) * (d 1 W) * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * (d 0 W) * (d 1 W) * iR ^ 2 * is * s + (1 : S) * (d 0 W) * (d 1 W) * iR ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymD_22 (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s c) 2 2 =
    (1/2 : S) * W ^ 4 * R⁻¹ ^ 2 + (-1 : S) * W ^ 2 * R⁻¹ ^ 2 + (1/2 : S) * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1/2 : S) * R * W ^ 4 * iR ^ 3 * is ^ 2 * s ^ 2 + (1 : S) * R * W ^ 2 * iR ^ 3 * is ^ 2 * s ^ 2 + (1/2 : S) * R * (d 0 W) ^ 2 * iN ^ 2 * iR * is ^ 2 * s ^ 2 + (1/2 : S) * R * (d 0 W) ^ 2 * iN ^ 2 * iR + (-1/2 : S) * R * (d 1 W) ^ 2 * iA ^ 2 * iR * is ^ 2 * s ^ 2 + (-1/2 : S) * R * (d 1 W) ^ 2 * iA ^ 2 * iR + (-1/2 : S) * R * iR ^ 3 * is ^ 2 * s ^ 2 + (-1/2 : S) * W ^ 4 * iR ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * W ^ 2 * iR ^ 2 * is ^ 2 * s ^ 2 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 * is ^ 2 * s ^ 2 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 * is ^ 2 * s ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 + (-1/2 : S) * iR ^ 2 * is ^ 2 * s ^ 2) * hiR + ((1/2 : S) * W ^ 4 * iR ^ 2 * is * s + (1/2 : S) * W ^ 4 * iR ^ 2 + (-1 : S) * W ^ 2 * iR ^ 2 * is * s + (-1 : S) * W ^ 2 * iR ^ 2 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 * is * s + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 * is * s + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 + (1/2 : S) * iR ^ 2 * is * s + (1/2 : S) * iR ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymN_00 (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s c) 0 0 =
    (2 : S) * (d 0 W) ^ 2 * r⁻¹ ^ 2 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * (d 0 W) ^ 2 * ir ^ 2 * is * s + (1 : S) * (d 0 W) ^ 2 * ir ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymN_11 (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s c) 1 1 =
    (2 : S) * (d 1 W) ^ 2 * r⁻¹ ^ 2 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * (d 1 W) ^ 2 * ir ^ 2 * is * s + (1 : S) * (d 1 W) ^ 2 * ir ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymN_01 (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s c) 0 1 =
    (1/2 : S) * Om * W ^ 4 * r⁻¹ ^ 4 + (-1 : S) * Om * W ^ 2 * r⁻¹ ^ 4 + (1/2 : S) * Om * r⁻¹ ^ 4 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1 : S) * (d 0 W) * (d 1 W) * ir ^ 2 * is ^ 2 * s ^ 2 + (-1 : S) * (d 0 W) * (d 1 W) * ir ^ 2) * hiOm + ((1/2 : S) * Om * W ^ 4 * ir ^ 4 * is * s + (1/2 : S) * Om * W ^ 4 * ir ^ 4 + (-1 : S) * Om * W ^ 2 * ir ^ 4 * is * s + (-1 : S) * Om * W ^ 2 * ir ^ 4 + (1/2 : S) * Om * ir ^ 4 * is * s + (1/2 : S) * Om * ir ^ 4) * his

set_option maxHeartbeats 0 in
theorem tymN_22 (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s c) 2 2 =
    (1/2 : S) * W ^ 4 * r⁻¹ ^ 2 + (-1 : S) * W ^ 2 * r⁻¹ ^ 2 + (1/2 : S) * r⁻¹ ^ 2 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1/2 : S) * W ^ 4 * ir ^ 3 * is ^ 2 * r * s ^ 2 + (-1/2 : S) * W ^ 4 * ir ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * W ^ 2 * ir ^ 3 * is ^ 2 * r * s ^ 2 + (1 : S) * W ^ 2 * ir ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * (d 0 W) * (d 1 W) * iOm * ir * is ^ 2 * r * s ^ 2 + (1 : S) * (d 0 W) * (d 1 W) * iOm * ir * r + (1 : S) * (d 0 W) * (d 1 W) * iOm * is ^ 2 * s ^ 2 + (1 : S) * (d 0 W) * (d 1 W) * iOm + (-1/2 : S) * ir ^ 3 * is ^ 2 * r * s ^ 2 + (-1/2 : S) * ir ^ 2 * is ^ 2 * s ^ 2) * hir + ((1/2 : S) * W ^ 4 * ir ^ 2 * is * s + (1/2 : S) * W ^ 4 * ir ^ 2 + (-1 : S) * W ^ 2 * ir ^ 2 * is * s + (-1 : S) * W ^ 2 * ir ^ 2 + (1 : S) * (d 0 W) * (d 1 W) * iOm * is * s + (1 : S) * (d 0 W) * (d 1 W) * iOm + (1/2 : S) * ir ^ 2 * is * s + (1/2 : S) * ir ^ 2) * his

set_option maxHeartbeats 0 in
theorem tymN_12 (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s c) 1 2 =
    0 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymN_13 (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s c) 1 3 =
    0 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

end YM
