set_option maxHeartbeats 0 in
theorem ricA_00 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 0 =
    (1 : S) * (d 0 A) * (d 0 N) * A⁻¹ * N⁻¹ + (-1 : S) * (d 0 (d 0 A)) * A⁻¹ + (-1 : S) * (d 1 A) * N * (d 1 N) * A⁻¹ ^ 3 + (2 : S) * N * (d 1 N) * (d 1 R) * A⁻¹ ^ 2 * R⁻¹ + (1 : S) * N * (d 1 (d 1 N)) * A⁻¹ ^ 2 + (2 : S) * (d 0 N) * (d 0 R) * N⁻¹ * R⁻¹ + (-2 : S) * (d 0 (d 0 R)) * R⁻¹ := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-1 : S) * (d 1 N) ^ 2 * iA ^ 2) * hiN

set_option maxHeartbeats 0 in
theorem ricA_01 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 1 =
    (2 : S) * (d 0 A) * (d 1 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 N) * (d 0 R) * N⁻¹ * R⁻¹ + (-2 : S) * (d 0 (d 1 R)) * R⁻¹ := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-1 : S) * A * (d 0 A) * (d 1 N) * iA ^ 2 * iN) * hiN + ((-1 : S) * (d 0 A) * (d 1 N) * iA * iN) * hiA

set_option maxHeartbeats 0 in
theorem ricA_02 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 2 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_03 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 3 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_10 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 1 0 =
    (2 : S) * (d 0 A) * (d 1 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 N) * (d 0 R) * N⁻¹ * R⁻¹ + (-2 : S) * (d 0 (d 1 R)) * R⁻¹ := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-1 : S) * A * (d 0 A) * (d 1 N) * iA ^ 2 * iN) * hiN + ((-1 : S) * (d 0 A) * (d 1 N) * iA * iN) * hiA

set_option maxHeartbeats 0 in
theorem ricA_11 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 1 1 =
    (-1 : S) * A * (d 0 A) * (d 0 N) * N⁻¹ ^ 3 + (2 : S) * A * (d 0 A) * (d 0 R) * N⁻¹ ^ 2 * R⁻¹ + (1 : S) * A * (d 0 (d 0 A)) * N⁻¹ ^ 2 + (1 : S) * (d 1 A) * (d 1 N) * A⁻¹ * N⁻¹ + (2 : S) * (d 1 A) * (d 1 R) * A⁻¹ * R⁻¹ + (-1 : S) * (d 1 (d 1 N)) * N⁻¹ + (-2 : S) * (d 1 (d 1 R)) * R⁻¹ := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-1 : S) * (d 0 A) ^ 2 * iN ^ 2) * hiA

set_option maxHeartbeats 0 in
theorem ricA_12 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 1 2 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_13 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 1 3 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_20 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 2 0 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_21 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 2 1 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_22 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 2 2 =
    (1 : S) * (d 0 A) * R * (d 0 R) * A⁻¹ * N⁻¹ ^ 2 + (1 : S) * (d 1 A) * R * (d 1 R) * A⁻¹ ^ 3 + (-1 : S) * (d 0 N) * R * (d 0 R) * N⁻¹ ^ 3 + (-1 : S) * (d 1 N) * R * (d 1 R) * A⁻¹ ^ 2 * N⁻¹ + (1 : S) * R * (d 0 (d 0 R)) * N⁻¹ ^ 2 + (-1 : S) * R * (d 1 (d 1 R)) * A⁻¹ ^ 2 + (1 : S) * (d 0 R) ^ 2 * N⁻¹ ^ 2 + (-1 : S) * (d 1 R) ^ 2 * A⁻¹ ^ 2 + (1 : S) := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((1 : S)) * his

set_option maxHeartbeats 0 in
theorem ricA_23 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 2 3 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_30 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 3 0 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_31 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 3 1 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_32 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 3 2 =
    0 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem ricA_33 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 3 3 =
    (1 : S) * (d 0 A) * R * (d 0 R) * A⁻¹ * N⁻¹ ^ 2 * s ^ 2 + (1 : S) * (d 1 A) * R * (d 1 R) * A⁻¹ ^ 3 * s ^ 2 + (-1 : S) * (d 0 N) * R * (d 0 R) * N⁻¹ ^ 3 * s ^ 2 + (-1 : S) * (d 1 N) * R * (d 1 R) * A⁻¹ ^ 2 * N⁻¹ * s ^ 2 + (1 : S) * R * (d 0 (d 0 R)) * N⁻¹ ^ 2 * s ^ 2 + (-1 : S) * R * (d 1 (d 1 R)) * A⁻¹ ^ 2 * s ^ 2 + (1 : S) * (d 0 R) ^ 2 * N⁻¹ ^ 2 * s ^ 2 + (-1 : S) * (d 1 R) ^ 2 * A⁻¹ ^ 2 * s ^ 2 + (1 : S) * s ^ 2 := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((1 : S) * c ^ 2) * his

set_option maxHeartbeats 0 in
theorem einA_00 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0 =
    (2 : S) * (d 0 A) * (d 0 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 A) * N ^ 2 * (d 1 R) * A⁻¹ ^ 3 * R⁻¹ + (-1 : S) * N ^ 2 * (d 1 R) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + (-2 : S) * N ^ 2 * (d 1 (d 1 R)) * A⁻¹ ^ 2 * R⁻¹ + (1 : S) * N ^ 2 * R⁻¹ ^ 2 + (1 : S) * (d 0 R) ^ 2 * R⁻¹ ^ 2 := by
  have hR' := ricA_00 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-1 : S) * (d 0 A) * N * (d 0 N) * iA * iN ^ 2 + (2 : S) * (d 0 A) * N * (d 0 R) * iA * iN * iR + (-1 : S) * (d 0 A) * (d 0 N) * iA * iN + (2 : S) * (d 0 A) * (d 0 R) * iA * iR + (1 : S) * (d 0 (d 0 A)) * N * iA * iN + (1 : S) * (d 0 (d 0 A)) * iA + (1 : S) * (d 1 A) * N * (d 1 N) * iA ^ 3 + (-2 : S) * N * (d 0 N) * (d 0 R) * iN ^ 2 * iR + (-2 : S) * N * (d 1 N) * (d 1 R) * iA ^ 2 * iR + (-1 : S) * N * (d 1 (d 1 N)) * iA ^ 2 + (1 : S) * N * (d 0 R) ^ 2 * iN * iR ^ 2 + (2 : S) * N * (d 0 (d 0 R)) * iN * iR + (-2 : S) * (d 0 N) * (d 0 R) * iN * iR + (1 : S) * (d 0 R) ^ 2 * iR ^ 2 + (2 : S) * (d 0 (d 0 R)) * iR) * hiN

set_option maxHeartbeats 0 in
theorem einA_01 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 1 =
    (2 : S) * (d 0 A) * (d 1 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 N) * (d 0 R) * N⁻¹ * R⁻¹ + (-2 : S) * (d 0 (d 1 R)) * R⁻¹ := by
  have hR' := ricA_01 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_02 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 2 =
    0 := by
  have hR' := ricA_02 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_03 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 3 =
    0 := by
  have hR' := ricA_03 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_10 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 0 =
    (2 : S) * (d 0 A) * (d 1 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 N) * (d 0 R) * N⁻¹ * R⁻¹ + (-2 : S) * (d 0 (d 1 R)) * R⁻¹ := by
  have hR' := ricA_10 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_11 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 1 =
    (2 : S) * A ^ 2 * (d 0 N) * (d 0 R) * N⁻¹ ^ 3 * R⁻¹ + (-1 : S) * A ^ 2 * (d 0 R) ^ 2 * N⁻¹ ^ 2 * R⁻¹ ^ 2 + (-2 : S) * A ^ 2 * (d 0 (d 0 R)) * N⁻¹ ^ 2 * R⁻¹ + (-1 : S) * A ^ 2 * R⁻¹ ^ 2 + (2 : S) * (d 1 N) * (d 1 R) * N⁻¹ * R⁻¹ + (1 : S) * (d 1 R) ^ 2 * R⁻¹ ^ 2 := by
  have hR' := ricA_11 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((1 : S) * A * (d 0 A) * (d 0 N) * iN ^ 3 + (-2 : S) * A * (d 0 A) * (d 0 R) * iN ^ 2 * iR + (-1 : S) * A * (d 0 (d 0 A)) * iN ^ 2 + (-1 : S) * A * (d 1 A) * (d 1 N) * iA ^ 2 * iN + (-2 : S) * A * (d 1 A) * (d 1 R) * iA ^ 2 * iR + (2 : S) * A * (d 1 N) * (d 1 R) * iA * iN * iR + (1 : S) * A * (d 1 (d 1 N)) * iA * iN + (1 : S) * A * (d 1 R) ^ 2 * iA * iR ^ 2 + (2 : S) * A * (d 1 (d 1 R)) * iA * iR + (-1 : S) * (d 1 A) * (d 1 N) * iA * iN + (-2 : S) * (d 1 A) * (d 1 R) * iA * iR + (2 : S) * (d 1 N) * (d 1 R) * iN * iR + (1 : S) * (d 1 (d 1 N)) * iN + (1 : S) * (d 1 R) ^ 2 * iR ^ 2 + (2 : S) * (d 1 (d 1 R)) * iR) * hiA

set_option maxHeartbeats 0 in
theorem einA_12 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 2 =
    0 := by
  have hR' := ricA_12 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_13 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 3 =
    0 := by
  have hR' := ricA_13 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_20 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 0 =
    0 := by
  have hR' := ricA_20 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_21 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 1 =
    0 := by
  have hR' := ricA_21 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_22 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 2 =
    (1 : S) * (d 0 A) * (d 0 N) * R ^ 2 * A⁻¹ * N⁻¹ ^ 3 + (-1 : S) * (d 0 A) * R * (d 0 R) * A⁻¹ * N⁻¹ ^ 2 + (-1 : S) * (d 0 (d 0 A)) * R ^ 2 * A⁻¹ * N⁻¹ ^ 2 + (-1 : S) * (d 1 A) * (d 1 N) * R ^ 2 * A⁻¹ ^ 3 * N⁻¹ + (-1 : S) * (d 1 A) * R * (d 1 R) * A⁻¹ ^ 3 + (1 : S) * (d 0 N) * R * (d 0 R) * N⁻¹ ^ 3 + (1 : S) * (d 1 N) * R * (d 1 R) * A⁻¹ ^ 2 * N⁻¹ + (1 : S) * (d 1 (d 1 N)) * R ^ 2 * A⁻¹ ^ 2 * N⁻¹ + (-1 : S) * R * (d 0 (d 0 R)) * N⁻¹ ^ 2 + (1 : S) * R * (d 1 (d 1 R)) * A⁻¹ ^ 2 := by
  have hR' := ricA_22 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-2 : S) * (d 0 A) * R * (d 0 R) * iA * iN ^ 2 + (-2 : S) * (d 1 A) * R * (d 1 R) * iA ^ 3 + (2 : S) * (d 0 N) * R * (d 0 R) * iN ^ 3 + (2 : S) * (d 1 N) * R * (d 1 R) * iA ^ 2 * iN + (-1 : S) * R * (d 0 R) ^ 2 * iN ^ 2 * iR + (-2 : S) * R * (d 0 (d 0 R)) * iN ^ 2 + (1 : S) * R * (d 1 R) ^ 2 * iA ^ 2 * iR + (2 : S) * R * (d 1 (d 1 R)) * iA ^ 2 + (-1 : S) * R * iR + (-1 : S) * (d 0 R) ^ 2 * iN ^ 2 + (1 : S) * (d 1 R) ^ 2 * iA ^ 2 + (-1 : S)) * hiR

set_option maxHeartbeats 0 in
theorem einA_23 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 3 =
    0 := by
  have hR' := ricA_23 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_30 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 3 0 =
    0 := by
  have hR' := ricA_30 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_31 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 3 1 =
    0 := by
  have hR' := ricA_31 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_32 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 3 2 =
    0 := by
  have hR' := ricA_32 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0

set_option maxHeartbeats 0 in
theorem einA_33 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 3 3 =
    (1 : S) * (d 0 A) * (d 0 N) * R ^ 2 * A⁻¹ * N⁻¹ ^ 3 * s ^ 2 + (-1 : S) * (d 0 A) * R * (d 0 R) * A⁻¹ * N⁻¹ ^ 2 * s ^ 2 + (-1 : S) * (d 0 (d 0 A)) * R ^ 2 * A⁻¹ * N⁻¹ ^ 2 * s ^ 2 + (-1 : S) * (d 1 A) * (d 1 N) * R ^ 2 * A⁻¹ ^ 3 * N⁻¹ * s ^ 2 + (-1 : S) * (d 1 A) * R * (d 1 R) * A⁻¹ ^ 3 * s ^ 2 + (1 : S) * (d 0 N) * R * (d 0 R) * N⁻¹ ^ 3 * s ^ 2 + (1 : S) * (d 1 N) * R * (d 1 R) * A⁻¹ ^ 2 * N⁻¹ * s ^ 2 + (1 : S) * (d 1 (d 1 N)) * R ^ 2 * A⁻¹ ^ 2 * N⁻¹ * s ^ 2 + (-1 : S) * R * (d 0 (d 0 R)) * N⁻¹ ^ 2 * s ^ 2 + (1 : S) * R * (d 1 (d 1 R)) * A⁻¹ ^ 2 * s ^ 2 := by
  have hR' := ricA_33 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-2 : S) * (d 0 A) * R * (d 0 R) * iA * iN ^ 2 * s ^ 2 + (-2 : S) * (d 1 A) * R * (d 1 R) * iA ^ 3 * s ^ 2 + (2 : S) * (d 0 N) * R * (d 0 R) * iN ^ 3 * s ^ 2 + (2 : S) * (d 1 N) * R * (d 1 R) * iA ^ 2 * iN * s ^ 2 + (-1 : S) * R * (d 0 R) ^ 2 * iN ^ 2 * iR * s ^ 2 + (-2 : S) * R * (d 0 (d 0 R)) * iN ^ 2 * s ^ 2 + (1 : S) * R * (d 1 R) ^ 2 * iA ^ 2 * iR * s ^ 2 + (2 : S) * R * (d 1 (d 1 R)) * iA ^ 2 * s ^ 2 + (-1 : S) * R * iR * s ^ 2 + (-1 : S) * (d 0 R) ^ 2 * iN ^ 2 * s ^ 2 + (1 : S) * (d 1 R) ^ 2 * iA ^ 2 * s ^ 2 + (-1 : S) * s ^ 2) * hiR

set_option maxHeartbeats 0 in
theorem tymA_00 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0 =
    (1/2 : S) * N ^ 2 * W ^ 4 * R⁻¹ ^ 4 + (-1 : S) * N ^ 2 * W ^ 2 * R⁻¹ ^ 4 + (1 : S) * N ^ 2 * (d 1 W) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + (1/2 : S) * N ^ 2 * R⁻¹ ^ 4 + (1 : S) * (d 0 W) ^ 2 * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
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
theorem tymA_01 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 1 =
    (2 : S) * (d 0 W) * (d 1 W) * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
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
theorem tymA_02 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 2 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_03 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 3 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_10 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 1 0 =
    (2 : S) * (d 0 W) * (d 1 W) * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
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
theorem tymA_11 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 1 1 =
    (-1/2 : S) * A ^ 2 * W ^ 4 * R⁻¹ ^ 4 + (1 : S) * A ^ 2 * W ^ 2 * R⁻¹ ^ 4 + (1 : S) * A ^ 2 * (d 0 W) ^ 2 * N⁻¹ ^ 2 * R⁻¹ ^ 2 + (-1/2 : S) * A ^ 2 * R⁻¹ ^ 4 + (1 : S) * (d 1 W) ^ 2 * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
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
theorem tymA_12 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 1 2 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_13 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 1 3 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_20 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 2 0 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_21 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 2 1 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_22 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 2 2 =
    (1/2 : S) * W ^ 4 * R⁻¹ ^ 2 + (-1 : S) * W ^ 2 * R⁻¹ ^ 2 + (1/2 : S) * R⁻¹ ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
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
theorem tymA_23 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 2 3 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_30 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 3 0 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_31 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 3 1 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_32 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 3 2 =
    0 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem tymA_33 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 3 3 =
    (1/2 : S) * W ^ 4 * R⁻¹ ^ 2 * s ^ 2 + (-1 : S) * W ^ 2 * R⁻¹ ^ 2 * s ^ 2 + (1/2 : S) * R⁻¹ ^ 2 * s ^ 2 := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
  all_goals
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1/2 : S) * R * W ^ 4 * iR ^ 3 * is ^ 2 * s ^ 4 + (1 : S) * R * W ^ 2 * iR ^ 3 * is ^ 2 * s ^ 4 + (1/2 : S) * R * (d 0 W) ^ 2 * iN ^ 2 * iR * is ^ 2 * s ^ 4 + (1/2 : S) * R * (d 0 W) ^ 2 * iN ^ 2 * iR * s ^ 2 + (-1/2 : S) * R * (d 1 W) ^ 2 * iA ^ 2 * iR * is ^ 2 * s ^ 4 + (-1/2 : S) * R * (d 1 W) ^ 2 * iA ^ 2 * iR * s ^ 2 + (-1/2 : S) * R * iR ^ 3 * is ^ 2 * s ^ 4 + (-1/2 : S) * W ^ 4 * iR ^ 2 * is ^ 2 * s ^ 4 + (1 : S) * W ^ 2 * iR ^ 2 * is ^ 2 * s ^ 4 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 * is ^ 2 * s ^ 4 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 * s ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 * is ^ 2 * s ^ 4 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 * s ^ 2 + (-1/2 : S) * iR ^ 2 * is ^ 2 * s ^ 4) * hiR + ((-1/2 : S) * W ^ 4 * iR ^ 2 * is * s ^ 3 + (-1/2 : S) * W ^ 4 * iR ^ 2 * s ^ 2 + (1 : S) * W ^ 2 * iR ^ 2 * is * s ^ 3 + (1 : S) * W ^ 2 * iR ^ 2 * s ^ 2 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 * is * s ^ 3 + (1/2 : S) * (d 0 W) ^ 2 * iN ^ 2 * s ^ 2 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 * is * s ^ 3 + (-1/2 : S) * (d 1 W) ^ 2 * iA ^ 2 * s ^ 2 + (-1/2 : S) * iR ^ 2 * is * s ^ 3 + (-1/2 : S) * iR ^ 2 * s ^ 2) * his
