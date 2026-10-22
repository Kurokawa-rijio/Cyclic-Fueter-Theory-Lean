/-
  段階 4 の幾何の入力:球対称な計量の Einstein テンソルを Levi-Civita の公式から計算する

  関数は微分体 S の元、∂_0..∂_3 は可換な導分(滑らかな関数の芽の代数的な抽象、AlphaIV_Propagation と同じ)。
  Christoffel 記号 Γ^a_bc = ½ g^{ae}(∂_b g_ec + ∂_c g_eb − ∂_e g_bc)、
  Ricci R_bc = ∂_a Γ^a_bc − ∂_c Γ^a_ba + Γ^a_ae Γ^e_bc − Γ^a_ce Γ^e_ba、スカラー R = g^{bc} R_bc、
  Einstein G_bc = R_bc − ½ g_bc R。角度は s = sin θ、c = cos θ(∂_θ s = c、∂_θ c = −s)。
  * 対角の計量 −N²dt² + A²dx² + R²dΩ²(座標 t, x, θ, φ):gamD(Γ の表)、einD_00、einD_11、einD_22、einD_01
  * 二重ヌルの計量 −2Ω du dv + r²dΩ²(座標 u, v, θ, φ):gamN、einN_00(G_uu)、einN_11(G_vv)、
    einN_01(G_uv)、einN_22(G_θθ)
  これで、これまで外部(教科書の公式)に置いていた G_uu = −(2/r)(r_uu − (Ω_u/Ω) r_u)(Ω = e^{2σ} で
  r_uu − 2σ_u r_u)と、空間的な切り口の ³R の公式(時間対称で G_tt/N² = ½ ³R)が、Levi-Civita の公式から出る。
-/
import CFT.AlphaIV_Propagation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace CFT.S4

open CFT.Propagation (deriv_inv deriv_ofNat)

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- Christoffel 記号 Γ^a_bc -/
def Gam (g gi : Fin 4 → Fin 4 → S) (a b c : Fin 4) : S :=
  2⁻¹ * ∑ e, gi a e * (d b (g e c) + d c (g e b) - d e (g b c))

/-- Ricci テンソル R_bc(Γ を与えて) -/
def Ric (Γ : Fin 4 → Fin 4 → Fin 4 → S) (b c : Fin 4) : S :=
  ∑ a, (d a (Γ a b c) - d c (Γ a b a)) + ∑ a, ∑ e, (Γ a a e * Γ e b c - Γ a c e * Γ e b a)

/-- スカラー曲率 -/
def Rsc (gi : Fin 4 → Fin 4 → S) (Γ : Fin 4 → Fin 4 → Fin 4 → S) : S :=
  ∑ b, ∑ c, gi b c * Ric d Γ b c

/-- Einstein テンソル G_bc -/
def Ein (g gi : Fin 4 → Fin 4 → S) (Γ : Fin 4 → Fin 4 → Fin 4 → S) (b c : Fin 4) : S :=
  Ric d Γ b c - 2⁻¹ * g b c * Rsc d gi Γ

/-! ### 対角の計量 −N²dt² + A²dx² + R²(dθ² + s²dφ²) -/

section Diag
variable (N A R s c : S)

def gD : Fin 4 → Fin 4 → S := ![![-N^2, 0, 0, 0], ![0, A^2, 0, 0], ![0, 0, R^2, 0], ![0, 0, 0, R^2*s^2]]
def giD : Fin 4 → Fin 4 → S :=
  ![![-(N⁻¹^2), 0, 0, 0], ![0, A⁻¹^2, 0, 0], ![0, 0, R⁻¹^2, 0], ![0, 0, 0, R⁻¹^2 * s⁻¹^2]]

/-- Γ の表(gamD で Gam と一致することを示す) -/
def GD : Fin 4 → Fin 4 → Fin 4 → S :=
  ![![![d 0 N * N⁻¹, d 1 N * N⁻¹, 0, 0], ![d 1 N * N⁻¹, d 0 A * A * N⁻¹^2, 0, 0],
      ![0, 0, d 0 R * R * N⁻¹^2, 0], ![0, 0, 0, d 0 R * R * s^2 * N⁻¹^2]],
    ![![d 1 N * N * A⁻¹^2, d 0 A * A⁻¹, 0, 0], ![d 0 A * A⁻¹, d 1 A * A⁻¹, 0, 0],
      ![0, 0, -(d 1 R * R * A⁻¹^2), 0], ![0, 0, 0, -(d 1 R * R * s^2 * A⁻¹^2)]],
    ![![0, 0, d 0 R * R⁻¹, 0], ![0, 0, d 1 R * R⁻¹, 0], ![d 0 R * R⁻¹, d 1 R * R⁻¹, 0, 0],
      ![0, 0, 0, -(s * c)]],
    ![![0, 0, 0, d 0 R * R⁻¹], ![0, 0, 0, d 1 R * R⁻¹], ![0, 0, 0, c * s⁻¹],
      ![d 0 R * R⁻¹, d 1 R * R⁻¹, c * s⁻¹, 0]]]

/-- 球対称の座標の仮定 -/
structure SphD : Prop where
  hN : N ≠ 0
  hA : A ≠ 0
  hR : R ≠ 0
  hs : s ≠ 0
  N2 : d 2 N = 0
  N3 : d 3 N = 0
  A2 : d 2 A = 0
  A3 : d 3 A = 0
  R2 : d 2 R = 0
  R3 : d 3 R = 0
  s0 : d 0 s = 0
  s1 : d 1 s = 0
  s2 : d 2 s = c
  s3 : d 3 s = 0
  c0 : d 0 c = 0
  c1 : d 1 c = 0
  c2 : d 2 c = -s
  c3 : d 3 c = 0
  comm : ∀ i j f, d i (d j f) = d j (d i f)

theorem giD_inv (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    ∀ i k, ∑ j, gD N A R s i j * giD N A R s j k = if i = k then 1 else 0 := by
  intro i k
  fin_cases i <;> fin_cases k <;> simp [gD, giD, Fin.sum_univ_four] <;> field_simp <;> ring

set_option maxHeartbeats 0 in
theorem gamD (H : SphD d N A R s c) : Gam d (gD N A R s) (giD N A R s) = GD d N A R s c := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, -⟩ := H
  funext a b e
  fin_cases a <;> fin_cases b <;> fin_cases e <;>
    simp [Gam, gD, giD, GD, Fin.sum_univ_four, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3] <;> field_simp <;> ring

set_option maxHeartbeats 0 in
theorem ricD_00 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 0 =
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
theorem ricD_11 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 1 1 =
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
theorem ricD_22 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 2 2 =
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
theorem ricD_33 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 3 3 =
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
theorem ricD_01 (H : SphD d N A R s c) : Ric d (GD d N A R s c) 0 1 =
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
theorem rscD (H : SphD d N A R s c) : Rsc d (giD N A R s) (GD d N A R s c) =
    (-2 : S) * (d 0 A) * (d 0 N) * A⁻¹ * N⁻¹ ^ 3 + (4 : S) * (d 0 A) * (d 0 R) * A⁻¹ * N⁻¹ ^ 2 * R⁻¹ + (2 : S) * (d 0 (d 0 A)) * A⁻¹ * N⁻¹ ^ 2 + (2 : S) * (d 1 A) * (d 1 N) * A⁻¹ ^ 3 * N⁻¹ + (4 : S) * (d 1 A) * (d 1 R) * A⁻¹ ^ 3 * R⁻¹ + (-4 : S) * (d 0 N) * (d 0 R) * N⁻¹ ^ 3 * R⁻¹ + (-4 : S) * (d 1 N) * (d 1 R) * A⁻¹ ^ 2 * N⁻¹ * R⁻¹ + (-2 : S) * (d 1 (d 1 N)) * A⁻¹ ^ 2 * N⁻¹ + (2 : S) * (d 0 R) ^ 2 * N⁻¹ ^ 2 * R⁻¹ ^ 2 + (4 : S) * (d 0 (d 0 R)) * N⁻¹ ^ 2 * R⁻¹ + (-2 : S) * (d 1 R) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + (-4 : S) * (d 1 (d 1 R)) * A⁻¹ ^ 2 * R⁻¹ + (2 : S) * R⁻¹ ^ 2 := by
  have h00 := ricD_00 d N A R s c H
  have h11 := ricD_11 d N A R s c H
  have h22 := ricD_22 d N A R s c H
  have h33 := ricD_33 d N A R s c H
  have h01 := ricD_01 d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  simp only [Rsc, giD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, zero_mul, add_zero, zero_add]
  rw [h00, h11, h22, h33]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * (d 1 A) * (d 1 N) * iA ^ 3 * iN + (-2 : S) * (d 1 N) * (d 1 R) * iA ^ 2 * iN * iR + (-1 : S) * (d 1 (d 1 N)) * iA ^ 2 * iN) * hiN + ((-1 : S) * (d 0 A) * (d 0 N) * iA * iN ^ 3 + (2 : S) * (d 0 A) * (d 0 R) * iA * iN ^ 2 * iR + (1 : S) * (d 0 (d 0 A)) * iA * iN ^ 2) * hiA + ((1 : S) * (d 0 A) * (d 0 R) * iA * iN ^ 2 * iR * is ^ 2 * s ^ 2 + (1 : S) * (d 0 A) * (d 0 R) * iA * iN ^ 2 * iR + (1 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR * is ^ 2 * s ^ 2 + (1 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR + (-1 : S) * (d 0 N) * (d 0 R) * iN ^ 3 * iR * is ^ 2 * s ^ 2 + (-1 : S) * (d 0 N) * (d 0 R) * iN ^ 3 * iR + (-1 : S) * (d 1 N) * (d 1 R) * iA ^ 2 * iN * iR * is ^ 2 * s ^ 2 + (-1 : S) * (d 1 N) * (d 1 R) * iA ^ 2 * iN * iR + (1 : S) * (d 0 (d 0 R)) * iN ^ 2 * iR * is ^ 2 * s ^ 2 + (1 : S) * (d 0 (d 0 R)) * iN ^ 2 * iR + (-1 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR * is ^ 2 * s ^ 2 + (-1 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR) * hiR + ((1 : S) * (d 0 A) * (d 0 R) * iA * iN ^ 2 * iR * is * s + (1 : S) * (d 0 A) * (d 0 R) * iA * iN ^ 2 * iR + (1 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR * is * s + (1 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR + (-1 : S) * (d 0 N) * (d 0 R) * iN ^ 3 * iR * is * s + (-1 : S) * (d 0 N) * (d 0 R) * iN ^ 3 * iR + (-1 : S) * (d 1 N) * (d 1 R) * iA ^ 2 * iN * iR * is * s + (-1 : S) * (d 1 N) * (d 1 R) * iA ^ 2 * iN * iR + (1 : S) * (d 0 R) ^ 2 * iN ^ 2 * iR ^ 2 * is * s + (1 : S) * (d 0 R) ^ 2 * iN ^ 2 * iR ^ 2 + (1 : S) * (d 0 (d 0 R)) * iN ^ 2 * iR * is * s + (1 : S) * (d 0 (d 0 R)) * iN ^ 2 * iR + (-1 : S) * (d 1 R) ^ 2 * iA ^ 2 * iR ^ 2 * is * s + (-1 : S) * (d 1 R) ^ 2 * iA ^ 2 * iR ^ 2 + (-1 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR * is * s + (-1 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR + (1 : S) * iR ^ 2 * is * s + (1 : S) * iR ^ 2) * his

set_option maxHeartbeats 0 in
theorem einD_00 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0 =
    (2 : S) * (d 0 A) * (d 0 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 A) * N ^ 2 * (d 1 R) * A⁻¹ ^ 3 * R⁻¹ + (-1 : S) * N ^ 2 * (d 1 R) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + (-2 : S) * N ^ 2 * (d 1 (d 1 R)) * A⁻¹ ^ 2 * R⁻¹ + (1 : S) * N ^ 2 * R⁻¹ ^ 2 + (1 : S) * (d 0 R) ^ 2 * R⁻¹ ^ 2 := by
  have hR' := ricD_00 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
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
theorem einD_11 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 1 =
    (2 : S) * A ^ 2 * (d 0 N) * (d 0 R) * N⁻¹ ^ 3 * R⁻¹ + (-1 : S) * A ^ 2 * (d 0 R) ^ 2 * N⁻¹ ^ 2 * R⁻¹ ^ 2 + (-2 : S) * A ^ 2 * (d 0 (d 0 R)) * N⁻¹ ^ 2 * R⁻¹ + (-1 : S) * A ^ 2 * R⁻¹ ^ 2 + (2 : S) * (d 1 N) * (d 1 R) * N⁻¹ * R⁻¹ + (1 : S) * (d 1 R) ^ 2 * R⁻¹ ^ 2 := by
  have hR' := ricD_11 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
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
theorem einD_22 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 2 =
    (1 : S) * (d 0 A) * (d 0 N) * R ^ 2 * A⁻¹ * N⁻¹ ^ 3 + (-1 : S) * (d 0 A) * R * (d 0 R) * A⁻¹ * N⁻¹ ^ 2 + (-1 : S) * (d 0 (d 0 A)) * R ^ 2 * A⁻¹ * N⁻¹ ^ 2 + (-1 : S) * (d 1 A) * (d 1 N) * R ^ 2 * A⁻¹ ^ 3 * N⁻¹ + (-1 : S) * (d 1 A) * R * (d 1 R) * A⁻¹ ^ 3 + (1 : S) * (d 0 N) * R * (d 0 R) * N⁻¹ ^ 3 + (1 : S) * (d 1 N) * R * (d 1 R) * A⁻¹ ^ 2 * N⁻¹ + (1 : S) * (d 1 (d 1 N)) * R ^ 2 * A⁻¹ ^ 2 * N⁻¹ + (-1 : S) * R * (d 0 (d 0 R)) * N⁻¹ ^ 2 + (1 : S) * R * (d 1 (d 1 R)) * A⁻¹ ^ 2 := by
  have hR' := ricD_22 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
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
theorem einD_01 (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 1 =
    (2 : S) * (d 0 A) * (d 1 R) * A⁻¹ * R⁻¹ + (2 : S) * (d 1 N) * (d 0 R) * N⁻¹ * R⁻¹ + (-2 : S) * (d 0 (d 1 R)) * R⁻¹ := by
  have hR' := ricD_01 d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

end Diag

/-! ### 二重ヌルの計量 −2Ω du dv + r²(dθ² + s²dφ²)(座標 u, v, θ, φ;Ω = e^{2σ}) -/

section Null
variable (Om r s c : S)

def gN : Fin 4 → Fin 4 → S := ![![0, -Om, 0, 0], ![-Om, 0, 0, 0], ![0, 0, r^2, 0], ![0, 0, 0, r^2*s^2]]
def giN : Fin 4 → Fin 4 → S :=
  ![![0, -Om⁻¹, 0, 0], ![-Om⁻¹, 0, 0, 0], ![0, 0, r⁻¹^2, 0], ![0, 0, 0, r⁻¹^2 * s⁻¹^2]]

/-- Γ の表(gamN) -/
def GN : Fin 4 → Fin 4 → Fin 4 → S :=
  ![![![d 0 Om * Om⁻¹, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, d 1 r * r * Om⁻¹, 0], ![0, 0, 0, d 1 r * r * s^2 * Om⁻¹]],
    ![![0, 0, 0, 0], ![0, d 1 Om * Om⁻¹, 0, 0], ![0, 0, d 0 r * r * Om⁻¹, 0], ![0, 0, 0, d 0 r * r * s^2 * Om⁻¹]],
    ![![0, 0, d 0 r * r⁻¹, 0], ![0, 0, d 1 r * r⁻¹, 0], ![d 0 r * r⁻¹, d 1 r * r⁻¹, 0, 0],
      ![0, 0, 0, -(s * c)]],
    ![![0, 0, 0, d 0 r * r⁻¹], ![0, 0, 0, d 1 r * r⁻¹], ![0, 0, 0, c * s⁻¹],
      ![d 0 r * r⁻¹, d 1 r * r⁻¹, c * s⁻¹, 0]]]

structure SphN : Prop where
  hO : Om ≠ 0
  hr : r ≠ 0
  hs : s ≠ 0
  O2 : d 2 Om = 0
  O3 : d 3 Om = 0
  r2 : d 2 r = 0
  r3 : d 3 r = 0
  s0 : d 0 s = 0
  s1 : d 1 s = 0
  s2 : d 2 s = c
  s3 : d 3 s = 0
  c0 : d 0 c = 0
  c1 : d 1 c = 0
  c2 : d 2 c = -s
  c3 : d 3 c = 0
  comm : ∀ i j f, d i (d j f) = d j (d i f)

theorem giN_inv (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    ∀ i k, ∑ j, gN Om r s i j * giN Om r s j k = if i = k then 1 else 0 := by
  intro i k
  fin_cases i <;> fin_cases k <;> simp [gN, giN, Fin.sum_univ_four] <;> field_simp <;> ring

set_option maxHeartbeats 0 in
theorem gamN (H : SphN d Om r s c) : Gam d (gN Om r s) (giN Om r s) = GN d Om r s c := by
  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, -⟩ := H
  funext a b e
  fin_cases a <;> fin_cases b <;> fin_cases e <;>
    simp [Gam, gN, giN, GN, Fin.sum_univ_four, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, O2, O3, r2, r3, s0, s1, s2, s3] <;> field_simp <;> ring

set_option maxHeartbeats 0 in
theorem ricN_00 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 0 0 =
    (2 : S) * (d 0 Om) * Om⁻¹ * r⁻¹ * (d 0 r) + (-2 : S) * r⁻¹ * (d 0 (d 0 r)) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ricN_11 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 1 1 =
    (2 : S) * (d 1 Om) * Om⁻¹ * r⁻¹ * (d 1 r) + (-2 : S) * r⁻¹ * (d 1 (d 1 r)) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ricN_22 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 2 2 =
    (2 : S) * Om⁻¹ * r * (d 0 (d 1 r)) + (2 : S) * Om⁻¹ * (d 0 r) * (d 1 r) + (1 : S) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S)) * his

set_option maxHeartbeats 0 in
theorem ricN_33 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 3 3 =
    (2 : S) * Om⁻¹ * r * (d 0 (d 1 r)) * s ^ 2 + (2 : S) * Om⁻¹ * (d 0 r) * (d 1 r) * s ^ 2 + (1 : S) * s ^ 2 := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((1 : S) * c ^ 2) * his

set_option maxHeartbeats 0 in
theorem ricN_01 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 0 1 =
    (1 : S) * (d 0 Om) * (d 1 Om) * Om⁻¹ ^ 2 + (-1 : S) * (d 0 (d 1 Om)) * Om⁻¹ + (-2 : S) * r⁻¹ * (d 0 (d 1 r)) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem ricN_10 (H : SphN d Om r s c) : Ric d (GN d Om r s c) 1 0 =
    (1 : S) * (d 0 Om) * (d 1 Om) * Om⁻¹ ^ 2 + (-1 : S) * (d 0 (d 1 Om)) * Om⁻¹ + (-2 : S) * r⁻¹ * (d 0 (d 1 r)) := by
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
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem rscN (H : SphN d Om r s c) : Rsc d (giN Om r s) (GN d Om r s c) =
    (-2 : S) * (d 0 Om) * (d 1 Om) * Om⁻¹ ^ 3 + (2 : S) * (d 0 (d 1 Om)) * Om⁻¹ ^ 2 + (4 : S) * Om⁻¹ * r⁻¹ ^ 2 * (d 0 r) * (d 1 r) + (8 : S) * Om⁻¹ * r⁻¹ * (d 0 (d 1 r)) + (2 : S) * r⁻¹ ^ 2 := by
  have h00 := ricN_00 d Om r s c H
  have h11 := ricN_11 d Om r s c H
  have h22 := ricN_22 d Om r s c H
  have h33 := ricN_33 d Om r s c H
  have h01 := ricN_01 d Om r s c H
  have h10 := ricN_10 d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  simp only [Rsc, giN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, zero_mul, add_zero, zero_add]
  rw [h01, h10, h22, h33]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((2 : S) * iOm * ir * is ^ 2 * (d 0 (d 1 r)) * s ^ 2 + (2 : S) * iOm * ir * (d 0 (d 1 r))) * hir + ((2 : S) * iOm * ir ^ 2 * is * (d 0 r) * (d 1 r) * s + (2 : S) * iOm * ir ^ 2 * (d 0 r) * (d 1 r) + (2 : S) * iOm * ir * is * (d 0 (d 1 r)) * s + (2 : S) * iOm * ir * (d 0 (d 1 r)) + (1 : S) * ir ^ 2 * is * s + (1 : S) * ir ^ 2) * his

set_option maxHeartbeats 0 in
theorem einN_00 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 0 =
    (2 : S) * (d 0 Om) * Om⁻¹ * r⁻¹ * (d 0 r) + (-2 : S) * r⁻¹ * (d 0 (d 0 r)) := by
  have hR' := ricN_00 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem einN_11 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 1 1 =
    (2 : S) * (d 1 Om) * Om⁻¹ * r⁻¹ * (d 1 r) + (-2 : S) * r⁻¹ * (d 1 (d 1 r)) := by
  have hR' := ricN_11 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

set_option maxHeartbeats 0 in
theorem einN_22 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 2 2 =
    (1 : S) * (d 0 Om) * (d 1 Om) * Om⁻¹ ^ 3 * r ^ 2 + (-1 : S) * (d 0 (d 1 Om)) * Om⁻¹ ^ 2 * r ^ 2 + (-2 : S) * Om⁻¹ * r * (d 0 (d 1 r)) := by
  have hR' := ricN_22 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-2 : S) * iOm * ir * r * (d 0 r) * (d 1 r) + (-4 : S) * iOm * r * (d 0 (d 1 r)) + (-2 : S) * iOm * (d 0 r) * (d 1 r) + (-1 : S) * ir * r + (-1 : S)) * hir

set_option maxHeartbeats 0 in
theorem einN_01 (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 1 =
    (1 : S) * Om * r⁻¹ ^ 2 + (2 : S) * r⁻¹ ^ 2 * (d 0 r) * (d 1 r) + (2 : S) * r⁻¹ * (d 0 (d 1 r)) := by
  have hR' := ricN_01 d Om r s c H
  have hS := rscN d Om r s c H
  obtain ⟨hO, hr, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gN, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((-1 : S) * (d 0 Om) * (d 1 Om) * iOm ^ 2 + (1 : S) * (d 0 (d 1 Om)) * iOm + (2 : S) * ir ^ 2 * (d 0 r) * (d 1 r) + (4 : S) * ir * (d 0 (d 1 r))) * hiO

end Null

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
    Fym d (Aym W s c) = FT d W s := by
  funext a m n
  fin_cases a <;> fin_cases m <;> fin_cases n <;>
    simp [Fym, Aym, FT, eps3, Fin.sum_univ_three, Derivation.leibniz, smul_eq_mul, W2, W3, s0, s1, s2, s3,
      c0, c1, c2, c3] <;> ring

set_option maxHeartbeats 0 in
theorem tymD_00 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0 =
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
theorem tymD_11 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 1 1 =
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
theorem tymD_01 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 1 =
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
theorem tymD_22 {N A R : S} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 2 2 =
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
theorem tymN_00 {Om r : S} (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 0 0 =
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
theorem tymN_11 {Om r : S} (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 1 1 =
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
theorem tymN_01 {Om r : S} (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 0 1 =
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
theorem tymN_22 {Om r : S} (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 2 2 =
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
theorem tymN_12 {Om r : S} (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 1 2 =
    0 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]

set_option maxHeartbeats 0 in
theorem tymN_13 {Om r : S} (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 1 3 =
    0 := by
  simp only [Tym, gN, giN, FT, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]

end YM

end CFT.S4
