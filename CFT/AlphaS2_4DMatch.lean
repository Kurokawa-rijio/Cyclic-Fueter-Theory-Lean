/-
  段階 2 の補い:縮約した方程式と 4 次元の EYM 方程式の全成分の直接の照合(Palais の対称臨界性を使わない)

  同期ゲージ N = 1、シフト 0、計量 −dt² + A²dx² + R²dΩ²、YM の接続 A = Wτ₁dθ + (Wsτ₂ + cτ₃)dφ。
  E_μν := G_μν − 2ℓ²T̂_μν(4 次元の Einstein テンソルは Levi-Civita の公式から、T̂ は F = dA + A∧A から)。
  縮約の残差 H = Hα、M = Mα、X = eKxα、T = eKTα、eP = ePα(AlphaS2_Match)について
    E₀₀ = H/2、E₀₁ = E₁₀ = −A M、E₁₁ = A²(2T + H/2)、E₂₂ = R²(X + T + H/2)、E₃₃ = s² E₂₂、他の 10 成分は 0
    YM の (1,θ) 成分 = −s eP、(2,φ) 成分 = −eP、他の 10 成分は 0
  (sync_ij、ym_all)。したがって
  * full_4d_iff_alpha:4 次元の EYM 方程式の全成分(Einstein 16、YM 12)⇔ α の五つの方程式
  * palais_free:4 次元の EYM 方程式の全成分 ⇔ 縮約した作用の五つの Euler–Lagrange 方程式(el_iff_alpha と合成)
  この ansatz について、縮約してから変分してよいこと(Palais)を外部定理として使わずに済む。
  補題 ricA_ij、einA_ij(全 16 成分の Ricci と Einstein)、tymA_ij(全 16 成分の YM の応力)、ymA_an(YM 方程式の全 12 成分)。
-/
import CFT.AlphaS4_Distrib
import CFT.AlphaS2_Match

namespace CFT.S2M

open CFT.S4 CFT.S5 CFT.S2
open CFT.Propagation (deriv_inv deriv_ofNat)

section Curv
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S) (N A R s c : S)

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


end Curv

section Stress
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S) (W s : S)

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

end Stress

section YMall
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)
set_option maxHeartbeats 0 in
theorem ymA_00 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 0 = 0 := by
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
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-1 : S) * A * R ^ 2 * (d 0 W) * c * iN * iR ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * A * R ^ 2 * (d 0 W) * c * iN * iR ^ 2) * hiN + ((-1 : S) * A * R * (d 0 W) * c * iN * iR * is ^ 2 * s ^ 2 + (1 : S) * A * R * (d 0 W) * c * iN * iR + (-1 : S) * A * (d 0 W) * c * iN * is ^ 2 * s ^ 2 + (1 : S) * A * (d 0 W) * c * iN) * hiR + ((-1 : S) * A * (d 0 W) * c * iN * is * s + (-1 : S) * A * (d 0 W) * c * iN) * his
set_option maxHeartbeats 0 in
theorem ymA_01 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 1 = 0 := by
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
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((1 : S) * N * R ^ 2 * (d 1 W) * c * iA * iR ^ 2 * is ^ 2 * s ^ 2 + (-1 : S) * N * R ^ 2 * (d 1 W) * c * iA * iR ^ 2) * hiA + ((1 : S) * N * R * (d 1 W) * c * iA * iR * is ^ 2 * s ^ 2 + (-1 : S) * N * R * (d 1 W) * c * iA * iR + (1 : S) * N * (d 1 W) * c * iA * is ^ 2 * s ^ 2 + (-1 : S) * N * (d 1 W) * c * iA) * hiR + ((1 : S) * N * (d 1 W) * c * iA * is * s + (1 : S) * N * (d 1 W) * c * iA) * his
set_option maxHeartbeats 0 in
theorem ymA_02 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
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
  all_goals
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
theorem ymA_03 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 3 = 0 := by
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
theorem ymA_10 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 1 0 = 0 := by
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
theorem ymA_11 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 1 1 = 0 := by
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
theorem ymA_12 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 1 2 = 0 := by
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
theorem ymA_13 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 1 3 = (-1 : S) * A * N * W ^ 3 * R⁻¹ ^ 2 + (1 : S) * A * N * W * R⁻¹ ^ 2 + (1 : S) * A * (d 0 N) * (d 0 W) * N⁻¹ ^ 2 + (-1 : S) * A * (d 0 (d 0 W)) * N⁻¹ + (-1 : S) * (d 0 A) * (d 0 W) * N⁻¹ + (-1 : S) * (d 1 A) * N * (d 1 W) * A⁻¹ ^ 2 + (1 : S) * N * (d 1 (d 1 W)) * A⁻¹ + (1 : S) * (d 1 N) * (d 1 W) * A⁻¹ := by
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
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((2 : S) * A * (d 0 N) * R ^ 2 * (d 0 W) * iN ^ 2 * iR ^ 2 * is ^ 2 * s ^ 2 + (2 : S) * A * R ^ 2 * (d 0 R) * (d 0 W) * iN * iR ^ 3 * is ^ 2 * s ^ 2 + (-1 : S) * A * R ^ 2 * (d 0 (d 0 W)) * iN * iR ^ 2 * is ^ 2 * s ^ 2 + (-2 : S) * A * R * (d 0 R) * (d 0 W) * iN * iR ^ 2 * is ^ 2 * s ^ 2 + (-1 : S) * (d 0 A) * R ^ 2 * (d 0 W) * iN * iR ^ 2 * is ^ 2 * s ^ 2) * hiN + ((-2 : S) * (d 1 A) * N * R ^ 2 * (d 1 W) * iA ^ 2 * iR ^ 2 * is ^ 2 * s ^ 2 + (-2 : S) * N * R ^ 2 * (d 1 R) * (d 1 W) * iA * iR ^ 3 * is ^ 2 * s ^ 2 + (1 : S) * N * R ^ 2 * (d 1 (d 1 W)) * iA * iR ^ 2 * is ^ 2 * s ^ 2 + (2 : S) * N * R * (d 1 R) * (d 1 W) * iA * iR ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * (d 1 N) * R ^ 2 * (d 1 W) * iA * iR ^ 2 * is ^ 2 * s ^ 2) * hiA + ((-1 : S) * A * N * R * W ^ 3 * iR ^ 3 * is ^ 2 * s ^ 2 + (1 : S) * A * N * R * W * iR ^ 3 * is ^ 2 * s ^ 2 + (-1 : S) * A * N * W ^ 3 * iR ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * A * N * W * iR ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * A * (d 0 N) * R * (d 0 W) * iN ^ 2 * iR * is ^ 2 * s ^ 2 + (1 : S) * A * (d 0 N) * (d 0 W) * iN ^ 2 * is ^ 2 * s ^ 2 + (2 : S) * A * R * (d 0 R) * (d 0 W) * iN * iR ^ 2 * is ^ 2 * s ^ 2 + (-1 : S) * A * R * (d 0 (d 0 W)) * iN * iR * is ^ 2 * s ^ 2 + (-1 : S) * A * (d 0 (d 0 W)) * iN * is ^ 2 * s ^ 2 + (-1 : S) * (d 0 A) * R * (d 0 W) * iN * iR * is ^ 2 * s ^ 2 + (-1 : S) * (d 0 A) * (d 0 W) * iN * is ^ 2 * s ^ 2 + (-1 : S) * (d 1 A) * N * R * (d 1 W) * iA ^ 2 * iR * is ^ 2 * s ^ 2 + (-1 : S) * (d 1 A) * N * (d 1 W) * iA ^ 2 * is ^ 2 * s ^ 2 + (-2 : S) * N * R * (d 1 R) * (d 1 W) * iA * iR ^ 2 * is ^ 2 * s ^ 2 + (1 : S) * N * R * (d 1 (d 1 W)) * iA * iR * is ^ 2 * s ^ 2 + (1 : S) * N * (d 1 (d 1 W)) * iA * is ^ 2 * s ^ 2 + (1 : S) * (d 1 N) * R * (d 1 W) * iA * iR * is ^ 2 * s ^ 2 + (1 : S) * (d 1 N) * (d 1 W) * iA * is ^ 2 * s ^ 2) * hiR + ((-1 : S) * A * N * W ^ 3 * iR ^ 2 * is * s + (-1 : S) * A * N * W ^ 3 * iR ^ 2 + (1 : S) * A * N * W * iR ^ 2 * is * s + (1 : S) * A * N * W * iR ^ 2 + (1 : S) * A * (d 0 N) * (d 0 W) * iN ^ 2 * is * s + (1 : S) * A * (d 0 N) * (d 0 W) * iN ^ 2 + (-1 : S) * A * (d 0 (d 0 W)) * iN * is * s + (-1 : S) * A * (d 0 (d 0 W)) * iN + (-1 : S) * (d 0 A) * (d 0 W) * iN * is * s + (-1 : S) * (d 0 A) * (d 0 W) * iN + (-1 : S) * (d 1 A) * N * (d 1 W) * iA ^ 2 * is * s + (-1 : S) * (d 1 A) * N * (d 1 W) * iA ^ 2 + (1 : S) * N * (d 1 (d 1 W)) * iA * is * s + (1 : S) * N * (d 1 (d 1 W)) * iA + (1 : S) * (d 1 N) * (d 1 W) * iA * is * s + (1 : S) * (d 1 N) * (d 1 W) * iA) * his
set_option maxHeartbeats 0 in
theorem ymA_20 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 2 0 = 0 := by
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
theorem ymA_21 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 2 1 = 0 := by
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
theorem ymA_22 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 2 2 = 0 := by
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
theorem ymA_23 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 2 3 = 0 := by
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
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-2 : S) * A * N * R * W ^ 2 * c * iR ^ 3 * is ^ 3 * s ^ 2 + (2 : S) * A * N * R * W ^ 2 * c * iR ^ 3 * is ^ 2 * s + (2 : S) * A * N * R * c * iR ^ 3 * is ^ 3 * s ^ 2 + (-2 : S) * A * N * R * c * iR ^ 3 * is ^ 2 * s + (-2 : S) * A * N * W ^ 2 * c * iR ^ 2 * is ^ 3 * s ^ 2 + (2 : S) * A * N * W ^ 2 * c * iR ^ 2 * is ^ 2 * s + (2 : S) * A * N * c * iR ^ 2 * is ^ 3 * s ^ 2 + (-2 : S) * A * N * c * iR ^ 2 * is ^ 2 * s) * hiR + ((-2 : S) * A * N * W ^ 2 * c * iR ^ 2 * is ^ 2 * s + (2 : S) * A * N * c * iR ^ 2 * is ^ 2 * s) * his
end YMall

section Sync
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)
set_option maxHeartbeats 0 in
theorem sync_00 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 0 0
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 0 0 = 2⁻¹ * Hα (d 0) (d 1) A R W l := by
  have hE := einA_00 d 1 A R s c H
  have hT := tymA_00 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((2 : S) * A * (d 0 W) ^ 2 * iA * iR ^ 2 * l ^ 2 + (2 : S) * (d 0 W) ^ 2 * iR ^ 2 * l ^ 2) * hiA + ((-1 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR + (1 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR) * hiR
set_option maxHeartbeats 0 in
theorem sync_01 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 0 1
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 0 1 = -(A * Mα (d 0) (d 1) A R W l) := by
  have hE := einA_01 d 1 A R s c H
  have hT := tymA_01 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((4 : S) * A * (d 0 W) * (d 1 W) * iA * iR ^ 2 * l ^ 2 + (-2 : S) * (d 0 A) * (d 1 R) * iA * iR + (2 : S) * (d 0 (d 1 R)) * iR + (4 : S) * (d 0 W) * (d 1 W) * iR ^ 2 * l ^ 2) * hiA
set_option maxHeartbeats 0 in
theorem sync_02 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 0 2
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 0 2 = 0 := by
  have hE := einA_02 d 1 A R s c H
  have hT := tymA_02 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_03 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 0 3
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 0 3 = 0 := by
  have hE := einA_03 d 1 A R s c H
  have hT := tymA_03 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_10 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 1 0
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 1 0 = -(A * Mα (d 0) (d 1) A R W l) := by
  have hE := einA_10 d 1 A R s c H
  have hT := tymA_10 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((4 : S) * A * (d 0 W) * (d 1 W) * iA * iR ^ 2 * l ^ 2 + (-2 : S) * (d 0 A) * (d 1 R) * iA * iR + (2 : S) * (d 0 (d 1 R)) * iR + (4 : S) * (d 0 W) * (d 1 W) * iR ^ 2 * l ^ 2) * hiA
set_option maxHeartbeats 0 in
theorem sync_11 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 1 1
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 1 1 = A ^ 2 * (2 * eKTα (d 0) (d 1) A R W l + 2⁻¹ * Hα (d 0) (d 1) A R W l) := by
  have hE := einA_11 d 1 A R s c H
  have hT := tymA_11 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((2 : S) * A ^ 3 * (d 0 W) ^ 2 * iA * iR ^ 2 * l ^ 2 + (2 : S) * A ^ 2 * (d 0 W) ^ 2 * iR ^ 2 * l ^ 2 + (1 : S) * A * (d 1 A) * R * (d 1 R) * iA ^ 2 * iR ^ 2 + (-1 : S) * A * (d 1 A) * (d 1 R) * iA ^ 2 * iR + (-1 : S) * A * R * (d 1 (d 1 R)) * iA * iR ^ 2 + (-1 : S) * A * (d 1 R) ^ 2 * iA * iR ^ 2 + (1 : S) * A * (d 1 (d 1 R)) * iA * iR + (2 : S) * A * (d 1 W) ^ 2 * iA * iR ^ 2 * l ^ 2 + (1 : S) * (d 1 A) * R * (d 1 R) * iA * iR ^ 2 + (-1 : S) * (d 1 A) * (d 1 R) * iA * iR + (-1 : S) * R * (d 1 (d 1 R)) * iR ^ 2 + (-1 : S) * (d 1 R) ^ 2 * iR ^ 2 + (1 : S) * (d 1 (d 1 R)) * iR + (2 : S) * (d 1 W) ^ 2 * iR ^ 2 * l ^ 2) * hiA + ((1 : S) * (d 1 A) * (d 1 R) * iA * iR + (-1 : S) * (d 1 (d 1 R)) * iR) * hiR
set_option maxHeartbeats 0 in
theorem sync_12 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 1 2
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 1 2 = 0 := by
  have hE := einA_12 d 1 A R s c H
  have hT := tymA_12 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_13 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 1 3
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 1 3 = 0 := by
  have hE := einA_13 d 1 A R s c H
  have hT := tymA_13 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_20 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 2 0
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 2 0 = 0 := by
  have hE := einA_20 d 1 A R s c H
  have hT := tymA_20 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_21 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 2 1
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 2 1 = 0 := by
  have hE := einA_21 d 1 A R s c H
  have hT := tymA_21 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_22 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 2 2
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 2 2 = R ^ 2 * (eKxα (d 0) (d 1) A R W l + eKTα (d 0) (d 1) A R W l + 2⁻¹ * Hα (d 0) (d 1) A R W l) := by
  have hE := einA_22 d 1 A R s c H
  have hT := tymA_22 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((1 : S) * (d 0 A) * R * (d 0 R) * iA + (1 : S) * (d 1 A) * R * (d 1 R) * iA ^ 3 + (1 : S) * R * (d 0 (d 0 R)) + (-1 : S) * R * (d 1 (d 1 R)) * iA ^ 2 + (1 : S) * R * W ^ 4 * iR ^ 3 * l ^ 2 + (-2 : S) * R * W ^ 2 * iR ^ 3 * l ^ 2 + (1 : S) * R * iR ^ 3 * l ^ 2 + (1 : S) * W ^ 4 * iR ^ 2 * l ^ 2 + (-2 : S) * W ^ 2 * iR ^ 2 * l ^ 2 + (1 : S) * iR ^ 2 * l ^ 2) * hiR
set_option maxHeartbeats 0 in
theorem sync_23 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 2 3
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 2 3 = 0 := by
  have hE := einA_23 d 1 A R s c H
  have hT := tymA_23 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_30 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 3 0
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 3 0 = 0 := by
  have hE := einA_30 d 1 A R s c H
  have hT := tymA_30 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_31 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 3 1
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 3 1 = 0 := by
  have hE := einA_31 d 1 A R s c H
  have hT := tymA_31 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_32 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 3 2
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 3 2 = 0 := by
  have hE := einA_32 d 1 A R s c H
  have hT := tymA_32 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination 0
set_option maxHeartbeats 0 in
theorem sync_33 (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) 3 3
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) 3 3 = s ^ 2 * (R ^ 2 * (eKxα (d 0) (d 1) A R W l + eKTα (d 0) (d 1) A R W l + 2⁻¹ * Hα (d 0) (d 1) A R W l)) := by
  have hE := einA_33 d 1 A R s c H
  have hT := tymA_33 d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((1 : S) * (d 0 A) * R * (d 0 R) * iA * s ^ 2 + (1 : S) * (d 1 A) * R * (d 1 R) * iA ^ 3 * s ^ 2 + (1 : S) * R * (d 0 (d 0 R)) * s ^ 2 + (-1 : S) * R * (d 1 (d 1 R)) * iA ^ 2 * s ^ 2 + (1 : S) * R * W ^ 4 * iR ^ 3 * l ^ 2 * s ^ 2 + (-2 : S) * R * W ^ 2 * iR ^ 3 * l ^ 2 * s ^ 2 + (1 : S) * R * iR ^ 3 * l ^ 2 * s ^ 2 + (1 : S) * W ^ 4 * iR ^ 2 * l ^ 2 * s ^ 2 + (-2 : S) * W ^ 2 * iR ^ 2 * l ^ 2 * s ^ 2 + (1 : S) * iR ^ 2 * l ^ 2 * s ^ 2) * hiR
end Sync

section Equiv
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- YM の (1,θ) 成分 = −s eP(N = 1、ymD_split から) -/
theorem ym_sync_02 (W A R s c : S) (H : SphD d 1 A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = -(s * ePα (d 0) (d 1) A R W 0) := by
  rw [CFT.S4D.ymD_split d W 1 A R s c H W2 W3]
  simp only [ePα, map_add, map_sub, map_neg, map_mul, Derivation.leibniz, smul_eq_mul, H.s0, H.s1, inv_one,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- YM の (2,φ) 成分 × s = (1,θ) 成分 -/
theorem ym_sync_13 (W A R s c : S) (H : SphD d 1 A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    s * YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (FT d W s) 1 3
      = YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2 := by
  rw [ymA_13 d W 1 A R s c H W2 W3, ymA_02 d W 1 A R s c H W2 W3]; ring

theorem fin4_cases (μ : Fin 4) : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 := by
  fin_cases μ <;> simp

theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a <;> simp

/-- 4 次元の EYM 方程式の全成分(Einstein 16、YM 12、F = dA + A∧A)⇔ α の五つの方程式 -/
theorem full_4d_iff_alpha (W A R s c l : S) (H : SphD d 1 A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0)
    (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    ((∀ μ ν, Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) μ ν
        = 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (Fym d (Aym W s c)) μ ν) ∧
      (∀ a n, YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (Fym d (Aym W s c)) a n = 0))
    ↔ (Hα (d 0) (d 1) A R W l = 0 ∧ Mα (d 0) (d 1) A R W l = 0 ∧ ePα (d 0) (d 1) A R W l = 0 ∧
        eKxα (d 0) (d 1) A R W l = 0 ∧ eKTα (d 0) (d 1) A R W l = 0) := by
  rw [fym_eq d W s c W2 W3 H.s0 H.s1 H.s2 H.s3 H.c0 H.c1 H.c2 H.c3]
  have hA := H.hA
  have hR := H.hR
  have hs := H.hs
  have eP0 : ePα (d 0) (d 1) A R W 0 = ePα (d 0) (d 1) A R W l := by simp only [ePα]
  have E : ∀ μ ν, (Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) μ ν
      = 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) μ ν) ↔
      Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) μ ν
        - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) μ ν = 0 := fun μ ν => sub_eq_zero.symm
  constructor
  · rintro ⟨hE, hY⟩
    have e00 := (E 0 0).mp (hE 0 0); rw [sync_00 d W A R s c l H hl0 hl1] at e00
    have e01 := (E 0 1).mp (hE 0 1); rw [sync_01 d W A R s c l H hl0 hl1] at e01
    have e11 := (E 1 1).mp (hE 1 1); rw [sync_11 d W A R s c l H hl0 hl1] at e11
    have e22 := (E 2 2).mp (hE 2 2); rw [sync_22 d W A R s c l H hl0 hl1] at e22
    have y02 := hY 0 2; rw [ym_sync_02 d W A R s c H W2 W3, eP0] at y02
    have hH : Hα (d 0) (d 1) A R W l = 0 := by
      have := e00; simp only [mul_eq_zero, inv_eq_zero, two_ne_zero, false_or] at this; exact this
    have hM : Mα (d 0) (d 1) A R W l = 0 := by
      have := neg_eq_zero.mp e01; exact (mul_eq_zero.mp this).resolve_left hA
    have hT : eKTα (d 0) (d 1) A R W l = 0 := by
      rw [hH] at e11
      have := (mul_eq_zero.mp e11).resolve_left (pow_ne_zero 2 hA)
      linear_combination this / 2
    have hX : eKxα (d 0) (d 1) A R W l = 0 := by
      rw [hH, hT] at e22
      have := (mul_eq_zero.mp e22).resolve_left (pow_ne_zero 2 hR)
      linear_combination this
    have hP : ePα (d 0) (d 1) A R W l = 0 := by
      have := neg_eq_zero.mp y02; exact (mul_eq_zero.mp this).resolve_left hs
    exact ⟨hH, hM, hP, hX, hT⟩
  · rintro ⟨hH, hM, hP, hX, hT⟩
    constructor
    · intro μ ν
      rw [E]
      rcases fin4_cases μ with rfl | rfl | rfl | rfl <;> rcases fin4_cases ν with rfl | rfl | rfl | rfl
      all_goals first
        | rw [sync_00 d W A R s c l H hl0 hl1, hH]; ring
        | rw [sync_01 d W A R s c l H hl0 hl1, hM]; ring
        | rw [sync_02 d W A R s c l H hl0 hl1]
        | rw [sync_03 d W A R s c l H hl0 hl1]
        | rw [sync_10 d W A R s c l H hl0 hl1, hM]; ring
        | rw [sync_11 d W A R s c l H hl0 hl1, hH, hT]; ring
        | rw [sync_12 d W A R s c l H hl0 hl1]
        | rw [sync_13 d W A R s c l H hl0 hl1]
        | rw [sync_20 d W A R s c l H hl0 hl1]
        | rw [sync_21 d W A R s c l H hl0 hl1]
        | rw [sync_22 d W A R s c l H hl0 hl1, hH, hX, hT]; ring
        | rw [sync_23 d W A R s c l H hl0 hl1]
        | rw [sync_30 d W A R s c l H hl0 hl1]
        | rw [sync_31 d W A R s c l H hl0 hl1]
        | rw [sync_32 d W A R s c l H hl0 hl1]
        | rw [sync_33 d W A R s c l H hl0 hl1, hH, hX, hT]; ring
    · intro a n
      have y02 : YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = 0 := by
        rw [ym_sync_02 d W A R s c H W2 W3, eP0, hP]; ring
      have y13 : YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (FT d W s) 1 3 = 0 := by
        have h13 := ym_sync_13 d W A R s c H W2 W3; rw [y02] at h13
        exact (mul_eq_zero.mp h13).resolve_left hs
      rcases fin3_cases a with rfl | rfl | rfl <;> rcases fin4_cases n with rfl | rfl | rfl | rfl
      · exact ymA_00 d W 1 A R s c H W2 W3
      · exact ymA_01 d W 1 A R s c H W2 W3
      · exact y02
      · exact ymA_03 d W 1 A R s c H W2 W3
      · exact ymA_10 d W 1 A R s c H W2 W3
      · exact ymA_11 d W 1 A R s c H W2 W3
      · exact ymA_12 d W 1 A R s c H W2 W3
      · exact y13
      · exact ymA_20 d W 1 A R s c H W2 W3
      · exact ymA_21 d W 1 A R s c H W2 W3
      · exact ymA_22 d W 1 A R s c H W2 W3
      · exact ymA_23 d W 1 A R s c H W2 W3

/-- Palais なしの照合:4 次元の EYM 方程式の全成分 ⇔ 縮約した作用の五つの Euler–Lagrange 方程式
  (同期ゲージ N = 1、β = 0、full_4d_iff_alpha と el_iff_alpha を合成) -/
theorem palais_free (W A R s c l : S) (H : SphD d 1 A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0)
    (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) (hl : l ≠ 0) :
    ((∀ μ ν, Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) μ ν
        = 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (Fym d (Aym W s c)) μ ν) ∧
      (∀ a n, YMeq d (giD 1 A R s) (1 * A * R ^ 2 * s) (Aym W s c) (Fym d (Aym W s c)) a n = 0))
    ↔ (EN (d 0) (d 1) 1 A R 0 W l = 0 ∧ Eb (d 0) (d 1) 1 A R 0 W l = 0 ∧ EW (d 0) (d 1) 1 A R 0 W l = 0 ∧
        EA (d 0) (d 1) 1 A R 0 W l = 0 ∧ ER (d 0) (d 1) 1 A R 0 W l = 0) := by
  rw [full_4d_iff_alpha d W A R s c l H W2 W3 hl0 hl1,
    el_iff_alpha (d 0) (d 1) A R W l H.hA H.hR hl (fun f => H.comm 0 1 f) hl0 hl1]

end Equiv

end CFT.S2M
