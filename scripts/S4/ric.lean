set_option maxHeartbeats 0 in
theorem ricD_00 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 0 = -(d 0 (d 0 A))/A - 2*(d 0 (d 0 R))/R + (d 0 A)*(d 0 N)/(A*N) + 2*(d 0 N)*(d 0 R)/(N*R) + (d 1 (d 1 N))*N/A^2 - (d 1 A)*(d 1 N)*N/A^3 + 2*(d 1 N)*(d 1 R)*N/(A^2*R) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricD_11 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 1 1 = (d 0 (d 0 A))*A/N^2 - (d 0 A)*(d 0 N)*A/N^3 + 2*(d 0 A)*(d 0 R)*A/(N^2*R) - (d 1 (d 1 N))/N - 2*(d 1 (d 1 R))/R + (d 1 A)*(d 1 N)/(A*N) + 2*(d 1 A)*(d 1 R)/(A*R) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricD_22 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 2 2 = (d 0 (d 0 R))*R/N^2 + (d 0 A)*(d 0 R)*R/(A*N^2) - (d 0 N)*(d 0 R)*R/N^3 + (d 0 R)^2/N^2 - (d 1 (d 1 R))*R/A^2 + (d 1 A)*(d 1 R)*R/A^3 - (d 1 N)*(d 1 R)*R/(A^2*N) - (d 1 R)^2/A^2 + 1 := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricD_33 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 3 3 = (d 0 (d 0 R))*R*s^2/N^2 + (d 0 A)*(d 0 R)*R*s^2/(A*N^2) - (d 0 N)*(d 0 R)*R*s^2/N^3 + (d 0 R)^2*s^2/N^2 - (d 1 (d 1 R))*R*s^2/A^2 + (d 1 A)*(d 1 R)*R*s^2/A^3 - (d 1 N)*(d 1 R)*R*s^2/(A^2*N) - (d 1 R)^2*s^2/A^2 + s^2 := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricD_01 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 1 = -2*(d 0 (d 1 R))/R + 2*(d 0 A)*(d 1 R)/(A*R) + 2*(d 0 R)*(d 1 N)/(N*R) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

theorem rscD (H : SphD d N A R s c) :
    Rsc d (giD N A R s) (GD d N A R s c) = 2*(d 0 (d 0 A))/(A*N^2) + 4*(d 0 (d 0 R))/(N^2*R) - 2*(d 0 A)*(d 0 N)/(A*N^3) + 4*(d 0 A)*(d 0 R)/(A*N^2*R) - 4*(d 0 N)*(d 0 R)/(N^3*R) + 2*(d 0 R)^2/(N^2*R^2) - 2*(d 1 (d 1 N))/(A^2*N) - 4*(d 1 (d 1 R))/(A^2*R) + 2*(d 1 A)*(d 1 N)/(A^3*N) + 4*(d 1 A)*(d 1 R)/(A^3*R) - 4*(d 1 N)*(d 1 R)/(A^2*N*R) - 2*(d 1 R)^2/(A^2*R^2) + 2/R^2 := by
  have h00 := ricD_00 d N A R s c H
  have h11 := ricD_11 d N A R s c H
  have h22 := ricD_22 d N A R s c H
  have h33 := ricD_33 d N A R s c H
  have h01 := ricD_01 d N A R s c H
  have H0 := H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  simp only [Rsc, giD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, zero_mul, add_zero, zero_add]
  rw [h00, h11, h22, h33]
  field_simp
  ring

theorem einD_00 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0 = 2*(d 0 A)*(d 0 R)/(A*R) + (d 0 R)^2/R^2 - 2*(d 1 (d 1 R))*N^2/(A^2*R) + 2*(d 1 A)*(d 1 R)*N^2/(A^3*R) - (d 1 R)^2*N^2/(A^2*R^2) + N^2/R^2 := by
  have hR := ricD_00 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR0, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem einD_11 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 1 = -2*(d 0 (d 0 R))*A^2/(N^2*R) + 2*(d 0 N)*(d 0 R)*A^2/(N^3*R) - (d 0 R)^2*A^2/(N^2*R^2) + 2*(d 1 N)*(d 1 R)/(N*R) + (d 1 R)^2/R^2 - A^2/R^2 := by
  have hR := ricD_11 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR0, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem einD_22 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 2 = -(d 0 (d 0 A))*R^2/(A*N^2) - (d 0 (d 0 R))*R/N^2 + (d 0 A)*(d 0 N)*R^2/(A*N^3) - (d 0 A)*(d 0 R)*R/(A*N^2) + (d 0 N)*(d 0 R)*R/N^3 + (d 1 (d 1 N))*R^2/(A^2*N) + (d 1 (d 1 R))*R/A^2 - (d 1 A)*(d 1 N)*R^2/(A^3*N) - (d 1 A)*(d 1 R)*R/A^3 + (d 1 N)*(d 1 R)*R/(A^2*N) := by
  have hR := ricD_22 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR0, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem einD_01 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 1 = -2*(d 0 (d 1 R))/R + 2*(d 0 A)*(d 1 R)/(A*R) + 2*(d 0 R)*(d 1 N)/(N*R) := by
  have hR := ricD_01 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR0, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricN_00 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 0 0 = -2*(d 0 (d 0 r))/r + 2*(d 0 Om)*(d 0 r)/(Om*r) := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricN_11 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 1 1 = -2*(d 1 (d 1 r))/r + 2*(d 1 Om)*(d 1 r)/(Om*r) := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricN_22 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 2 2 = 2*(d 0 (d 1 r))*r/Om + 2*(d 0 r)*(d 1 r)/Om + 1 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricN_33 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 3 3 = 2*(d 0 (d 1 r))*r*s^2/Om + 2*(d 0 r)*(d 1 r)*s^2/Om + s^2 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricN_01 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 0 1 = -(d 0 (d 1 Om))/Om - 2*(d 0 (d 1 r))/r + (d 0 Om)*(d 1 Om)/Om^2 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

set_option maxHeartbeats 0 in
theorem ricN_10 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 1 0 = -(d 0 (d 1 Om))/Om - 2*(d 0 (d 1 r))/r + (d 0 Om)*(d 1 Om)/Om^2 := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring

theorem rscN (H : SphN d Om r s c) :
    Rsc d (giN Om r s) (GN d Om r s c) = 2*(d 0 (d 1 Om))/Om^2 + 8*(d 0 (d 1 r))/(Om*r) - 2*(d 0 Om)*(d 1 Om)/Om^3 + 4*(d 0 r)*(d 1 r)/(Om*r^2) + 2/r^2 := by
  have h00 := ricN_00 d Om r s c H
  have h11 := ricN_11 d Om r s c H
  have h22 := ricN_22 d Om r s c H
  have h33 := ricN_33 d Om r s c H
  have h01 := ricN_01 d Om r s c H
  have H0 := H
  obtain ⟨hO, hr, hs, -⟩ := H
  simp only [Rsc, giN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, zero_mul, add_zero, zero_add]
  rw [h01, ricN_10 d Om r s c H0, h22, h33]
  field_simp
  ring

theorem einN_00 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 0 = -2*(d 0 (d 0 r))/r + 2*(d 0 Om)*(d 0 r)/(Om*r) := by
  have hR := ricN_00 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem einN_11 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 1 1 = -2*(d 1 (d 1 r))/r + 2*(d 1 Om)*(d 1 r)/(Om*r) := by
  have hR := ricN_11 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem einN_22 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 2 2 = -(d 0 (d 1 Om))*r^2/Om^2 - 2*(d 0 (d 1 r))*r/Om + (d 0 Om)*(d 1 Om)*r^2/Om^3 := by
  have hR := ricN_22 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem einN_01 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 1 = 2*(d 0 (d 1 r))/r + 2*(d 0 r)*(d 1 r)/r^2 + Om/r^2 := by
  have hR := ricN_01 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR, hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring
