set_option maxHeartbeats 0 in
/-- 対角の計量での YM 方程式の (1, θ) 成分 -/
theorem ymD_02 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = (-1 : S) * A * N * W ^ 3 * R⁻¹ ^ 2 * s + (1 : S) * A * N * W * R⁻¹ ^ 2 * s + (1 : S) * A * (d 0 N) * (d 0 W) * N⁻¹ ^ 2 * s + (-1 : S) * A * (d 0 (d 0 W)) * N⁻¹ * s + (-1 : S) * (d 0 A) * (d 0 W) * N⁻¹ * s + (-1 : S) * (d 1 A) * N * (d 1 W) * A⁻¹ ^ 2 * s + (1 : S) * N * (d 1 (d 1 W)) * A⁻¹ * s + (1 : S) * (d 1 N) * (d 1 W) * A⁻¹ * s := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  simp only [eps3_table, YMeq, Fup, giD, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((2 : S) * A * (d 0 N) * R ^ 2 * (d 0 W) * iN ^ 2 * iR ^ 2 * s + (2 : S) * A * R ^ 2 * (d 0 R) * (d 0 W) * iN * iR ^ 3 * s + (-1 : S) * A * R ^ 2 * (d 0 (d 0 W)) * iN * iR ^ 2 * s + (-2 : S) * A * R * (d 0 R) * (d 0 W) * iN * iR ^ 2 * s + (-1 : S) * (d 0 A) * R ^ 2 * (d 0 W) * iN * iR ^ 2 * s) * hiN + ((-2 : S) * (d 1 A) * N * R ^ 2 * (d 1 W) * iA ^ 2 * iR ^ 2 * s + (-2 : S) * N * R ^ 2 * (d 1 R) * (d 1 W) * iA * iR ^ 3 * s + (1 : S) * N * R ^ 2 * (d 1 (d 1 W)) * iA * iR ^ 2 * s + (2 : S) * N * R * (d 1 R) * (d 1 W) * iA * iR ^ 2 * s + (1 : S) * (d 1 N) * R ^ 2 * (d 1 W) * iA * iR ^ 2 * s) * hiA + ((-1 : S) * A * N * R * W ^ 3 * iR ^ 3 * is ^ 2 * s ^ 3 + (1 : S) * A * N * R * W * iR ^ 3 * is ^ 2 * s ^ 3 + (-1 : S) * A * N * W ^ 3 * iR ^ 2 * is ^ 2 * s ^ 3 + (1 : S) * A * N * W * iR ^ 2 * is ^ 2 * s ^ 3 + (1 : S) * A * (d 0 N) * R * (d 0 W) * iN ^ 2 * iR * s + (1 : S) * A * (d 0 N) * (d 0 W) * iN ^ 2 * s + (2 : S) * A * R * (d 0 R) * (d 0 W) * iN * iR ^ 2 * s + (-1 : S) * A * R * (d 0 (d 0 W)) * iN * iR * s + (-1 : S) * A * (d 0 (d 0 W)) * iN * s + (-1 : S) * (d 0 A) * R * (d 0 W) * iN * iR * s + (-1 : S) * (d 0 A) * (d 0 W) * iN * s + (-1 : S) * (d 1 A) * N * R * (d 1 W) * iA ^ 2 * iR * s + (-1 : S) * (d 1 A) * N * (d 1 W) * iA ^ 2 * s + (-2 : S) * N * R * (d 1 R) * (d 1 W) * iA * iR ^ 2 * s + (1 : S) * N * R * (d 1 (d 1 W)) * iA * iR * s + (1 : S) * N * (d 1 (d 1 W)) * iA * s + (1 : S) * (d 1 N) * R * (d 1 W) * iA * iR * s + (1 : S) * (d 1 N) * (d 1 W) * iA * s) * hiR + ((-1 : S) * A * N * W ^ 3 * iR ^ 2 * is * s ^ 2 + (-1 : S) * A * N * W ^ 3 * iR ^ 2 * s + (1 : S) * A * N * W * iR ^ 2 * is * s ^ 2 + (1 : S) * A * N * W * iR ^ 2 * s) * his

set_option maxHeartbeats 0 in
/-- 流束の形:YM 方程式 = ∂_x(N s W_x/A) + ∂_t(−A s W_t/N) + A N s W(1 − W²)/R²。
  x の 2 階微分は流束 √−g F^{1xθ} = N s W_x/A(ym_flux_tube)の ∂_x にだけ入る -/
theorem ymD_split (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2
      = d 1 (N * s * (d 1 W * A⁻¹)) + d 0 (-(A * s * (d 0 W * N⁻¹)))
        + A * N * s * W * (1 - W ^ 2) * R⁻¹ ^ 2 := by
  rw [ymD_02 d W N A R s c H W2 W3]
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have kW := comm 1 0 W
  simp only [map_add, map_sub, map_neg, map_mul, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, iN, iA, s0, s1, kW]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0
