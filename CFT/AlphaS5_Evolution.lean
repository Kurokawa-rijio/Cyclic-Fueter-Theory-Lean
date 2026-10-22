/-
  段階 5:時間発展(α-IV.1、IV.2、IV.4、IV.5、IV.7、IV.8、IV.9)を、作用から出た方程式で閉じる
  (2026-10-21 の外部監査を確認し、監査に頼らず最初から計算し直した)

  A. 二重ヌル座標の YM 方程式(ymN_ab):接続 A から F = dA + A∧A を計算し、√−g D_μF^{aμν} の 12 成分を
     求めた。0 でないのは (1, θ) と (2, φ) だけで、どちらも 2r²W_uv − ΩW(1 − W²) に比例する(仮定の整合性)。
     goursat_W:W_uv = ½ΩW(1 − W²)/r²(Z8 の W_uv = F の式、Ω = e^{2σ} で AlphaIV の FW、fw_eq)
  B. Goursat の形と拘束の伝播(α-IV.1):
     * goursat_r、goursat_Om、goursat_W:uv・θθ の Einstein 方程式と YM 方程式は (r, Ω, W)_uv = F(値, 1 階微分)
       の形(1+1 次元の半線形双曲系、特性初期値問題 = Goursat 問題の形)
     * constraint_uu、constraint_vv:uu、vv 成分の方程式 ⇔ C_u = 0、C_v = 0(特性線に沿う拘束)
     * constraint_prop_u、constraint_prop_v:Goursat の式のもとで ∂_v C_u = −(r_v/r) C_u、∂_u C_v = −(r_u/r) C_v
     * constraint_transport:初期の特性線で C = 0 なら至る所で C = 0
  C. 外側の厳密解(作用の式から検算):
     * cap_00、cap_11、cap_22、cap_01:帽子(N = A = a(η)、R = a sin χ、W = cos χ)の EYM ⇔
       a′² + a² = ℓ² かつ 2aa″ − a′² + a² + ℓ² = 0(閉じた放射 FRW、共形時間)
     * neck_00〜neck_01:首 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²(AdS₂ × S² の同期座標、W = 0)は EYM の厳密解
  D. 実解析:
     * IV.7(Z10):front_gd_inv、gd_front_inv(z_ℓ と ℓ gd(·/ℓ) は主値の帯で互いに逆)、cos_gd、mercator、
       neck_mercator(同じ Gudermann 写像が球面と首の 2 次元の計量を共形平坦にする)、null_curve_unique
       (原点を通るヌル曲線は t = ℓ gd(z/ℓ) に限る = Mercator の 45° の航程線の像)。座標の対応であって
       力学的な同値ではない(曲率の符号が逆)
     * IV.8:fronts_meet_iff(波面の出会いは t = ℓ gd(L/2ℓ) に限る、等式)。帽子:cap_accel(a″ = −a)、
       cap_unique(a = ℓ cos η だけ)、cap_proper_time(中心の固有時 ℓ sin η → ℓ)
     * IV.5(Z9):cap_density(ρ̂ = 3/(2a⁴))、cap_crunch(η → π/2 で ρ̂ → ∞)、t_sing_lt(t_sing = ℓ < πℓ/2)、
       center_before_front(中心は崩壊まで厳密な FRW の領域にある)。比較定理 z9_collapse の正しい読み:
       z9_maximal(最大の存在区間)、z9_reaches_zero_vacuous(旧 z9_reaches_zero は κ > 0 で仮定が両立しない)
     * IV.9:flat_clock、flat_front、flat_metric(ℓ → ∞ の極限そのもの)
  外部に残るもの:1+1 次元の半線形双曲系の特性初期値問題(Goursat 問題)の局所的な存在と一意性(古典的な定理)、
  なめらかなデータの EYM の解の依存領域での一意性(Choquet-Bruhat)。
-/
import CFT.AlphaS4_Junction
import CFT.AlphaIV_Z9
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Real.Pi.Bounds

namespace CFT.S5

open CFT.S4
open CFT.Propagation (deriv_inv deriv_ofNat)

/-! ### A. 二重ヌル座標の YM 方程式(Z8 の W_uv の式を F = dA + A∧A から導く) -/

section YMEq
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

theorem eps3_table : (eps3 : Fin 3 → Fin 3 → Fin 3 → S) =
    ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
      ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] := by
  funext a b e
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp (config := {decide := true}) [eps3]

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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
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
  simp only [eps3_table, YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
    have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
    have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize Om⁻¹ = iOm at hiOm ⊢
    generalize r⁻¹ = ir at hir ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination ((-2 : S) * Om * W ^ 2 * c * ir ^ 3 * is ^ 3 * r * s ^ 2 + (2 : S) * Om * W ^ 2 * c * ir ^ 3 * is ^ 2 * r * s + (-2 : S) * Om * W ^ 2 * c * ir ^ 2 * is ^ 3 * s ^ 2 + (2 : S) * Om * W ^ 2 * c * ir ^ 2 * is ^ 2 * s + (2 : S) * Om * c * ir ^ 3 * is ^ 3 * r * s ^ 2 + (-2 : S) * Om * c * ir ^ 3 * is ^ 2 * r * s + (2 : S) * Om * c * ir ^ 2 * is ^ 3 * s ^ 2 + (-2 : S) * Om * c * ir ^ 2 * is ^ 2 * s) * hir + ((-2 : S) * Om * W ^ 2 * c * ir ^ 2 * is ^ 2 * s + (2 : S) * Om * c * ir ^ 2 * is ^ 2 * s) * his

end YMEq

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
  obtain ⟨hO0, hr', hs, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO0
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
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO0
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
  obtain ⟨hO0, hr', hs, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO0
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
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO0
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr'
  generalize Om⁻¹ = iOm at hiOm hr hO hW hr1 ⊢
  generalize r⁻¹ = ir at hir hr hO hW hr1 ⊢
  linear_combination ((1 : S)) * hr1 + ((-1 : S) * iOm * (d 1 r)) * hO + ((4 : S) * (d 1 W) * ir * l ^ 2) * hW + ((2 : S) * Om * iOm * ir * (d 1 r) + (-1 : S) * (d 1 Om) * iOm + (-1 : S) * ir * (d 1 r)) * hr + ((2 : S) * Om * W ^ 4 * ir ^ 4 * l ^ 2 * (d 1 r) + (-4 : S) * Om * W ^ 2 * ir ^ 4 * l ^ 2 * (d 1 r) + (2 : S) * Om * ir ^ 4 * l ^ 2 * (d 1 r) + (-1 : S) * Om * ir ^ 2 * (d 1 r) + (-1/2 : S) * (d 1 Om) * W ^ 4 * ir ^ 3 * l ^ 2 + (1 : S) * (d 1 Om) * W ^ 2 * ir ^ 3 * l ^ 2 + (-1/2 : S) * (d 1 Om) * ir ^ 3 * l ^ 2 + (1/2 : S) * (d 1 Om) * ir + (-2 : S) * ir ^ 2 * (d 0 r) * (d 1 r) ^ 2) * hiOm

end Goursat

/-! ### C. 外側の厳密解:帽子(閉じた放射 FRW)と首(AdS₂ × S²)を EYM の式から -/

section Exact
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- 帽子:共形時間 η(座標 0)と χ(座標 1)、N = A = a(η)、R = a(η) X(X = sin χ、Y = cos χ)、W = Y -/
structure CapData (a X Y s c : S) : Prop where
  ha : a ≠ 0
  hX : X ≠ 0
  hs : s ≠ 0
  a1 : d 1 a = 0
  a2 : d 2 a = 0
  a3 : d 3 a = 0
  X0 : d 0 X = 0
  X1 : d 1 X = Y
  X2 : d 2 X = 0
  X3 : d 3 X = 0
  Y0 : d 0 Y = 0
  Y1 : d 1 Y = -X
  hXY : X ^ 2 + Y ^ 2 = 1
  s0 : d 0 s = 0
  s1 : d 1 s = 0
  s2 : d 2 s = c
  s3 : d 3 s = 0
  c0 : d 0 c = 0
  c1 : d 1 c = 0
  c2 : d 2 c = -s
  c3 : d 3 c = 0
  comm : ∀ i j f, d i (d j f) = d j (d i f)

theorem capSph (a X Y s c : S) (H : CapData d a X Y s c) : SphD d a a (a * X) s c := by
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  refine ⟨ha, ha, mul_ne_zero ha hX, hs, a2, a3, a2, a3, ?_, ?_, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ <;>
    simp [Derivation.leibniz, a2, a3, X2, X3]

set_option maxHeartbeats 0 in
/-- 帽子の tt 成分 ⇔ Friedmann の式 a′² + a² = ℓ²(閉じた放射 FRW、共形時間) -/
theorem cap_00 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 0 0
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 0 0 ↔ (d 0 a) ^ 2 + a ^ 2 = l ^ 2 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_00 d a a (a * X) s c HS, tymD_00 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  constructor
  · intro h
    linear_combination ((1/3 : S) * a ^ 2) * h + ((-1/3 : S) * X ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1/3 : S) * Y ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1/3 : S) * a ^ 6 * iX ^ 2 * ia ^ 4 + (-1/3 : S) * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2) * hXY + ((1/3 : S) * X ^ 3 * a ^ 4 * iX ^ 3 * ia ^ 4 * l ^ 2 + (1/3 : S) * X ^ 2 * a ^ 4 * iX ^ 2 * ia ^ 4 * l ^ 2 + (-1/3 : S) * X * a ^ 6 * iX * ia ^ 4 + (1 : S) * X * a ^ 4 * iX * ia ^ 4 * l ^ 2 + (-1/3 : S) * X * a ^ 2 * (d 0 a) ^ 2 * iX * ia ^ 2 + (-1/3 : S) * a ^ 6 * ia ^ 4 + (-2/3 : S) * a ^ 5 * ia ^ 3 + (1 : S) * a ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 2) * hiX + ((1/3 : S) * a ^ 5 * iX ^ 2 * ia ^ 3 + (-1/3 : S) * a ^ 5 * ia ^ 3 + (1/3 : S) * a ^ 4 * iX ^ 2 * ia ^ 2 + (-1 : S) * a ^ 4 * ia ^ 2 + (1 : S) * a ^ 3 * ia ^ 3 * l ^ 2 + (-1 : S) * a ^ 3 * ia + (1 : S) * a ^ 2 * ia ^ 2 * l ^ 2 + (-1 : S) * a ^ 2 + (-1 : S) * a * (d 0 a) ^ 2 * ia + (1 : S) * a * ia * l ^ 2 + (-1 : S) * (d 0 a) ^ 2 + (1 : S) * l ^ 2) * hia
  · intro h
    linear_combination ((3 : S) * ia ^ 2) * h + ((1 : S) * X ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * Y ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 4 * iX ^ 2 * ia ^ 4 + (1 : S) * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2) * hXY + ((-1 : S) * X ^ 3 * a ^ 2 * iX ^ 3 * ia ^ 4 * l ^ 2 + (-1 : S) * X ^ 2 * a ^ 2 * iX ^ 2 * ia ^ 4 * l ^ 2 + (1 : S) * X * a ^ 4 * iX * ia ^ 4 + (-3 : S) * X * a ^ 2 * iX * ia ^ 4 * l ^ 2 + (1 : S) * X * (d 0 a) ^ 2 * iX * ia ^ 2 + (1 : S) * a ^ 4 * ia ^ 4 + (2 : S) * a ^ 3 * ia ^ 3 + (-3 : S) * a ^ 2 * ia ^ 4 * l ^ 2 + (3 : S) * (d 0 a) ^ 2 * ia ^ 2) * hiX + ((-1 : S) * a ^ 3 * iX ^ 2 * ia ^ 3 + (1 : S) * a ^ 3 * ia ^ 3 + (-1 : S) * a ^ 2 * iX ^ 2 * ia ^ 2 + (3 : S) * a ^ 2 * ia ^ 2 + (-3 : S) * a * ia ^ 3 * l ^ 2 + (-3 : S) * ia ^ 2 * l ^ 2) * hia

set_option maxHeartbeats 0 in
/-- 帽子の χχ 成分 ⇔ 2aa″ − a′² + a² + ℓ² = 0 -/
theorem cap_11 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 1 1
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 1 1 ↔ 2 * a * d 0 (d 0 a) - (d 0 a) ^ 2 + a ^ 2 + l ^ 2 = 0 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_11 d a a (a * X) s c HS, tymD_11 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  constructor
  · intro h
    linear_combination ((-1 : S) * a ^ 2) * h + ((-1 : S) * X ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * Y ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * a ^ 4 * iX ^ 2 * ia ^ 2) * hXY + ((1 : S) * X ^ 3 * a ^ 4 * iX ^ 3 * ia ^ 4 * l ^ 2 + (1 : S) * X ^ 2 * a ^ 4 * iX ^ 2 * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 4 * (d 0 a) ^ 2 * iX * ia ^ 4 + (1 : S) * X * a ^ 4 * iX * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 4 * iX * ia ^ 2 + (-2 : S) * X * a ^ 2 * iX * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 4 * (d 0 a) ^ 2 * ia ^ 4 + (-2 : S) * a ^ 4 * (d 0 (d 0 a)) * ia ^ 3 + (1 : S) * a ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 4 * ia ^ 2 + (-2 : S) * a ^ 2 * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * a ^ 3 * (d 0 a) ^ 2 * ia ^ 3 + (-2 : S) * a ^ 3 * (d 0 (d 0 a)) * ia ^ 2 + (1 : S) * a ^ 3 * ia ^ 3 * l ^ 2 + (-1 : S) * a ^ 3 * ia + (1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 2 + (-2 : S) * a ^ 2 * (d 0 (d 0 a)) * ia + (1 : S) * a ^ 2 * ia ^ 2 * l ^ 2 + (-1 : S) * a ^ 2 + (1 : S) * a * (d 0 a) ^ 2 * ia + (-2 : S) * a * (d 0 (d 0 a)) + (-1 : S) * a * ia * l ^ 2 + (1 : S) * (d 0 a) ^ 2 + (-1 : S) * l ^ 2) * hia
  · intro h
    linear_combination ((-1 : S) * ia ^ 2) * h + ((-1 : S) * X ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * Y ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * a ^ 2 * iX ^ 2 * ia ^ 2) * hXY + ((1 : S) * X ^ 3 * a ^ 2 * iX ^ 3 * ia ^ 4 * l ^ 2 + (1 : S) * X ^ 2 * a ^ 2 * iX ^ 2 * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 2 * (d 0 a) ^ 2 * iX * ia ^ 4 + (1 : S) * X * a ^ 2 * iX * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 2 * iX * ia ^ 2 + (-2 : S) * X * iX * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 4 + (-2 : S) * a ^ 2 * (d 0 (d 0 a)) * ia ^ 3 + (1 : S) * a ^ 2 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 2 * ia ^ 2 + (-2 : S) * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * a * (d 0 a) ^ 2 * ia ^ 3 + (-2 : S) * a * (d 0 (d 0 a)) * ia ^ 2 + (1 : S) * a * ia ^ 3 * l ^ 2 + (1 : S) * (d 0 a) ^ 2 * ia ^ 2 + (1 : S) * ia ^ 2 * l ^ 2) * hia

set_option maxHeartbeats 0 in
/-- 帽子の θθ 成分 ⇔ 2aa″ − a′² + a² + ℓ² = 0(等方) -/
theorem cap_22 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 2 2
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 2 2 ↔ 2 * a * d 0 (d 0 a) - (d 0 a) ^ 2 + a ^ 2 + l ^ 2 = 0 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_22 d a a (a * X) s c HS, tymD_22 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  constructor
  · intro h
    linear_combination ((-1 : S) * a ^ 2 * iX ^ 2) * h + ((1 : S) * X ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 2 * l ^ 2 + (-1 : S) * Y ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 2 * iX ^ 4 * ia ^ 2 * l ^ 2) * hXY + ((-1 : S) * X ^ 3 * a ^ 2 * iX ^ 3 * ia ^ 2 * l ^ 2 + (-1 : S) * X ^ 2 * a ^ 2 * iX ^ 2 * ia ^ 2 * l ^ 2 + (1 : S) * X * a ^ 4 * (d 0 a) ^ 2 * iX * ia ^ 4 + (-1 : S) * X * a ^ 4 * (d 0 (d 0 a)) * iX * ia ^ 3 + (-1 : S) * X * a ^ 4 * iX * ia ^ 2 + (-1 : S) * X * a ^ 3 * (d 0 (d 0 a)) * iX * ia ^ 2 + (-1 : S) * X * a ^ 2 * iX * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 4 * (d 0 a) ^ 2 * ia ^ 4 + (-1 : S) * a ^ 4 * (d 0 (d 0 a)) * ia ^ 3 + (-1 : S) * a ^ 4 * ia ^ 2 + (-1 : S) * a ^ 3 * (d 0 (d 0 a)) * ia ^ 2 + (-1 : S) * a ^ 2 * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * a ^ 3 * (d 0 a) ^ 2 * ia ^ 3 + (-1 : S) * a ^ 3 * (d 0 (d 0 a)) * ia ^ 2 + (-1 : S) * a ^ 3 * ia + (1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 2 + (-2 : S) * a ^ 2 * (d 0 (d 0 a)) * ia + (-1 : S) * a ^ 2 + (1 : S) * a * (d 0 a) ^ 2 * ia + (-2 : S) * a * (d 0 (d 0 a)) + (-1 : S) * a * ia * l ^ 2 + (1 : S) * (d 0 a) ^ 2 + (-1 : S) * l ^ 2) * hia
  · intro h
    linear_combination ((-1 : S) * X ^ 2 * ia ^ 2) * h + ((1 : S) * X ^ 2 * iX ^ 2 * ia ^ 2 * l ^ 2 + (-1 : S) * Y ^ 2 * iX ^ 2 * ia ^ 2 * l ^ 2 + (1 : S) * iX ^ 2 * ia ^ 2 * l ^ 2) * hXY + ((-1 : S) * X ^ 3 * iX * ia ^ 2 * l ^ 2 + (-1 : S) * X ^ 2 * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * X ^ 2 * a * (d 0 a) ^ 2 * ia ^ 3 + (-1 : S) * X ^ 2 * a * (d 0 (d 0 a)) * ia ^ 2 + (1 : S) * X ^ 2 * (d 0 a) ^ 2 * ia ^ 2) * hia

set_option maxHeartbeats 0 in
/-- 帽子の tχ 成分は恒等的に成り立つ(W_η = 0) -/
theorem cap_01 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 0 1
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 0 1 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_01 d a a (a * X) s c HS, tymD_01 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  linear_combination ((2 : S) * Y * (d 0 a) * iX * ia) * hia

/-- 首:時間 t(座標 0)と z(座標 1)、N = 1、A = C(C = cos(t/ℓ)、S = sin(t/ℓ))、R = ℓ、W = 0 -/
structure NeckData (C Sn l s c : S) : Prop where
  hC : C ≠ 0
  hl : l ≠ 0
  hs : s ≠ 0
  dl : ∀ i, d i l = 0
  C0 : d 0 C = -(Sn * l⁻¹)
  C1 : d 1 C = 0
  C2 : d 2 C = 0
  C3 : d 3 C = 0
  S0 : d 0 Sn = C * l⁻¹
  S1 : d 1 Sn = 0
  s0 : d 0 s = 0
  s1 : d 1 s = 0
  s2 : d 2 s = c
  s3 : d 3 s = 0
  c0 : d 0 c = 0
  c1 : d 1 c = 0
  c2 : d 2 c = -s
  c3 : d 3 c = 0
  comm : ∀ i j f, d i (d j f) = d j (d i f)

theorem neckSph (C Sn l s c : S) (H : NeckData d C Sn l s c) : SphD d 1 C l s c := by
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  exact ⟨one_ne_zero, hC, hl, hs, Derivation.map_one_eq_zero _, Derivation.map_one_eq_zero _, C2, C3,
    dl 2, dl 3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (0,0) 成分を満たす -/
theorem neck_00 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 0 0
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 0 0 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_00 d 1 C l s c HS, tymD_00 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination ((-1 : S) * il ^ 3 * l + (-1 : S) * il ^ 2) * hil

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (1,1) 成分を満たす -/
theorem neck_11 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 1 1
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 1 1 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_11 d 1 C l s c HS, tymD_11 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination ((1 : S) * C ^ 2 * il ^ 3 * l + (1 : S) * C ^ 2 * il ^ 2) * hil

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (2,2) 成分を満たす -/
theorem neck_22 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 2 2
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 2 2 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_22 d 1 C l s c HS, tymD_22 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination ((1 : S) * il ^ 2 * l ^ 2) * hiC

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (0,1) 成分を満たす -/
theorem neck_01 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 0 1
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 0 1 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_01 d 1 C l s c HS, tymD_01 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
    have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
    generalize C⁻¹ = iC at hiC ⊢
    generalize l⁻¹ = il at hil ⊢
    linear_combination 0

end Exact

/-! ### D. 実解析:拘束の輸送、Gudermann と Mercator、波面の出会い、帽子の崩壊、平坦極限、Z9 の整理 -/

section Analysis
open Real Filter Topology Set CFT.AlphaIV

/-- 拘束の輸送:∂_v C = −(r_v/r) C(constraint_prop_u)、初期の特性線で C = 0、r > 0 なら C ≡ 0 -/
theorem constraint_transport {v0 v1 : ℝ} {r rv C C' : ℝ → ℝ}
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hC : ∀ v ∈ Icc v0 v1, HasDerivWithinAt C (C' v) (Icc v0 v1) v)
    (heq : ∀ v ∈ Icc v0 v1, C' v = -(rv v * (r v)⁻¹) * C v) (h0 : C v0 = 0)
    (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0) : ∀ v ∈ Icc v0 v1, C v = 0 :=
  CFT.S4J.jump_transport hr hC (fun v hv => by rw [heq v hv]; field_simp [hpos v hv]; ring) h0 hpos

/-- W_uv の右辺(AlphaIV の FW)は Ω = e^{2σ} で goursat_W の右辺と同じ -/
theorem fw_eq (r σ W : ℝ) : FW r σ W = 2⁻¹ * exp (2 * σ) * W * (1 - W ^ 2) * r⁻¹ ^ 2 := by
  simp only [FW]; ring

/-- 首の波面 z_ℓ(t) = ℓ arsinh(tan(t/ℓ)) -/
noncomputable def zfront (l t : ℝ) : ℝ := l * arsinh (tan (t / l))

/-- z_ℓ(ℓ gd(z/ℓ)) = z(すべての z) -/
theorem front_gd_inv (l z : ℝ) (hl : l ≠ 0) : zfront l (l * gd (z / l)) = z := by
  simp only [zfront]
  rw [show l * gd (z / l) / l = gd (z / l) by field_simp, tan_gd, arsinh_sinh]
  field_simp

/-- 主値の帯 |t| < πℓ/2 で ℓ gd(z_ℓ(t)/ℓ) = t:z_ℓ と t ↦ ℓ gd(·/ℓ) は互いに逆 -/
theorem gd_front_inv (l t : ℝ) (hl : 0 < l) (ht : |t| < π * l / 2) : l * gd (zfront l t / l) = t := by
  have h1 : -(π / 2) < t / l := by
    rw [lt_div_iff₀ hl]; have := neg_abs_le t; nlinarith
  have h2 : t / l < π / 2 := by
    rw [div_lt_iff₀ hl]; have := le_abs_self t; nlinarith
  simp only [zfront, gd]
  rw [show l * arsinh (tan (t / l)) / l = arsinh (tan (t / l)) by field_simp, sinh_arsinh, arctan_tan h1 h2]
  field_simp

/-- cos(gd y) = sech y -/
theorem cos_gd (y : ℝ) : cos (gd y) = 1 / cosh y := by
  rw [gd, cos_arctan, ← cosh_sq', sqrt_sq (cosh_pos y).le]

/-- Mercator:gd′ = cos ∘ gd。したがって緯度 φ = gd(y) で球面の dφ² + cos²φ dλ² = sech²y (dy² + dλ²) -/
theorem mercator (y : ℝ) : HasDerivAt gd (cos (gd y)) y := by
  rw [cos_gd]; exact gd_deriv y

/-- 首の Mercator 座標:t(y) = ℓ gd(y/ℓ) は dt/dy = cos(t/ℓ)。したがって
  −dt² + cos²(t/ℓ)dz² = cos²(t/ℓ)(−dy² + dz²)(同じ Gudermann 写像が首の 2 次元の計量を共形平坦にする) -/
theorem neck_mercator (l y : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun y => l * gd (y / l)) (cos (l * gd (y / l) / l)) y := by
  have h := ((gd_deriv (y / l)).comp y ((hasDerivAt_id y).div_const l)).const_mul l
  rw [show l * gd (y / l) / l = gd (y / l) by field_simp, cos_gd]
  convert h using 1
  field_simp

/-- 原点を通る未来向き・右向きのヌル曲線(dt/dz = cos(t/ℓ)、主値の帯の中)は t = ℓ gd(z/ℓ) に限る。
  台帳 Z10 の t/ℓ* = gd(z/ℓ*)。これは Mercator 座標での 45° の航程線 y = z の像:座標の対応であって、
  球面(K = +1)と首の 2 次元部分(K = −1/ℓ²、AdS₂)の力学的な同値ではない -/
theorem null_curve_unique (l : ℝ) (hl : 0 < l) (T T' : ℝ → ℝ) (hT : ∀ z, HasDerivAt T (T' z) z)
    (hnull : ∀ z, T' z = cos (T z / l)) (hstrip : ∀ z, |T z| < π * l / 2) (h0 : T 0 = 0) :
    ∀ z, T z = l * gd (z / l) := by
  have hcos : ∀ z, 0 < cos (T z / l) := by
    intro z
    apply cos_pos_of_mem_Ioo
    constructor
    · rw [lt_div_iff₀ hl]; have := neg_abs_le (T z); have := hstrip z; nlinarith
    · rw [div_lt_iff₀ hl]; have := le_abs_self (T z); have := hstrip z; nlinarith
  have hd : ∀ z, HasDerivAt (fun z => zfront l (T z) - z) 0 z := by
    intro z
    have h := ((front_deriv l (T z) hl (hcos z)).comp z (hT z)).sub (hasDerivAt_id z)
    convert h using 1
    rw [hnull z]; field_simp [(hcos z).ne']
  have hconst : ∀ z, zfront l (T z) - z = zfront l (T 0) - 0 := fun z =>
    is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) z 0
  intro z
  have e := hconst z
  rw [h0, show zfront l 0 = 0 by simp [zfront]] at e
  have hz : zfront l (T z) = z := by linarith
  rw [← gd_front_inv l (T z) hl (hstrip z), hz]

/-- 長さ L の首の両端からの波面 z_L = −L/2 + z_ℓ(t)、z_R = L/2 − z_ℓ(t) が出会うのは t = ℓ gd(L/(2ℓ)) のときに限る
  (上界でなく等式。t* < πℓ/2 は fronts_meet_before) -/
theorem fronts_meet_iff (l L t : ℝ) (hl : 0 < l) (ht : |t| < π * l / 2) :
    -(L / 2) + zfront l t = L / 2 - zfront l t ↔ t = l * gd (L / (2 * l)) := by
  constructor
  · intro h
    have hz : zfront l t = L / 2 := by linarith
    rw [← gd_front_inv l t hl ht, hz]; congr 2; field_simp
  · intro h
    have : zfront l t = L / 2 := by
      rw [h, show L / (2 * l) = (L / 2) / l by field_simp]; exact front_gd_inv l (L / 2) hl.ne'
    linarith

/-- 帽子の加速度:tt 成分 a′² + a² = ℓ² と θθ 成分 2aa″ − a′² + a² + ℓ² = 0 から a″ = −a -/
theorem cap_accel (a a1 a2 l : ℝ) (ha : a ≠ 0) (h00 : a1 ^ 2 + a ^ 2 = l ^ 2)
    (h22 : 2 * a * a2 - a1 ^ 2 + a ^ 2 + l ^ 2 = 0) : a2 = -a := by
  have : 2 * a * (a2 + a) = 0 := by linear_combination h22 + h00
  have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero ha)
  linarith

/-- 時間対称な初期値 a(0) = ℓ、a′(0) = 0 で a″ = −a の解は a = ℓ cos η だけ -/
theorem cap_unique (l : ℝ) (A A' : ℝ → ℝ) (h1 : ∀ η, HasDerivAt A (A' η) η)
    (h2 : ∀ η, HasDerivAt A' (-A η) η) (h0 : A 0 = l) (h0' : A' 0 = 0) : ∀ η, A η = l * cos η := by
  let E : ℝ → ℝ := fun η => (A η - l * cos η) ^ 2 + (A' η + l * sin η) ^ 2
  have hE : ∀ η, HasDerivAt E 0 η := by
    intro η
    have h := (((h1 η).sub ((hasDerivAt_cos η).const_mul l)).pow 2).add
      (((h2 η).add ((hasDerivAt_sin η).const_mul l)).pow 2)
    convert h using 1
    push_cast; ring
  have hc : ∀ η, E η = E 0 := fun η =>
    is_const_of_deriv_eq_zero (fun z => (hE z).differentiableAt) (fun z => (hE z).deriv) η 0
  intro η
  have e := hc η
  simp only [E, h0, h0', cos_zero, sin_zero, mul_one, mul_zero, sub_self, add_zero] at e
  have h3 : (A η - l * cos η) ^ 2 = 0 := by
    have := sq_nonneg (A' η + l * sin η); nlinarith [sq_nonneg (A η - l * cos η)]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  linarith

/-- 中心の固有時 t(η) = ∫₀^η a = ℓ sin η(dt = a dη)、崩壊 η = π/2 で t = ℓ -/
theorem cap_proper_time (l η : ℝ) :
    HasDerivAt (fun η => l * sin η) (l * cos η) η ∧ l * sin (π / 2) = l :=
  ⟨by simpa using (hasDerivAt_sin η).const_mul l, by simp⟩

/-- 帽子の YM のエネルギー密度(rho_tube の Rho、W = cos χ、W_χ/A = −sin χ/a)は ρ̂ = 3/(2a⁴) -/
theorem cap_density (a X Y : ℝ) (ha : a ≠ 0) (hX : X ≠ 0) (hXY : X ^ 2 + Y ^ 2 = 1) :
    CFT.S4J.Rho (a * X) Y 0 (-X / a) = 3 / (2 * a ^ 4) := by
  simp only [CFT.S4J.Rho]
  have hY : 1 - Y ^ 2 = X ^ 2 := by linarith
  rw [hY]; field_simp; ring

/-- 崩壊:a = ℓ cos η → 0(η → π/2⁻)で ρ̂ = 3/(2a⁴) → ∞(中心の測地線に沿って曲率の不変量が発散) -/
theorem cap_crunch (l : ℝ) (hl : 0 < l) :
    Tendsto (fun η => 3 / (2 * (l * cos η) ^ 4)) (𝓝[<] (π / 2)) atTop := by
  have h1 : Tendsto (fun η => l * cos η) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    have hc := tendsto_cos_pi_div_two
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (tendsto_nhdsWithin_iff.mp hc).1
      simpa using this.const_mul l
    · filter_upwards [(tendsto_nhdsWithin_iff.mp hc).2] with η hη
      exact Set.mem_Ioi.mpr (mul_pos hl (Set.mem_Ioi.mp hη))
  have h2 : Tendsto (fun η => 2 * (l * cos η) ^ 4) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((tendsto_nhdsWithin_iff.mp h1).1.pow 4).const_mul 2
      simpa using this
    · filter_upwards [(tendsto_nhdsWithin_iff.mp h1).2] with η hη
      have : 0 < (l * cos η) ^ 4 := pow_pos (Set.mem_Ioi.mp hη) 4
      exact Set.mem_Ioi.mpr (by linarith)
  have h3 := (tendsto_inv_nhdsGT_zero.comp h2).const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  refine h3.congr' ?_
  filter_upwards with η
  simp [div_eq_mul_inv]

/-- t_sing = ℓ < πℓ/2(Z9 の目標) -/
theorem t_sing_lt (l : ℝ) (hl : 0 < l) : l < π * l / 2 := by
  have := Real.pi_gt_three; nlinarith

/-- 接合から帽子へ向かう波面は共形座標で χ = π/2 − η(dχ = −dη)。η < π/2 なら中心 χ = 0 はまだ波面の外
  (厳密な FRW の領域)にある。波面が中心に着く η = π/2 は崩壊の瞬間に一致する -/
theorem center_before_front (η : ℝ) (h : η < π / 2) : (0 : ℝ) < π / 2 - η := by linarith

/-- 平坦極限:到着時計 ℓ gd(z/ℓ) → z(ℓ → ∞) -/
theorem flat_clock (z : ℝ) : Tendsto (fun l : ℝ => l * gd (z / l)) atTop (𝓝 z) := by
  by_cases hz : z = 0
  · subst hz; simp [gd_zero]
  have hslope := gd_deriv_zero.tendsto_slope_zero
  simp only [zero_add, gd_zero, sub_zero, smul_eq_mul] at hslope
  have hu : Tendsto (fun l : ℝ => z / l) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.div_atTop tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with l hl
      exact div_ne_zero hz hl.ne'
  have := (hslope.comp hu).const_mul z
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  simp only [Function.comp]
  field_simp

/-- arsinh ∘ tan の 0 での微分は 1 -/
theorem front_deriv_zero : HasDerivAt (fun x => arsinh (tan x)) 1 0 := by
  have ht := hasDerivAt_tan (by simp : cos (0 : ℝ) ≠ 0)
  have h := (hasDerivAt_arsinh (tan 0)).comp (0 : ℝ) ht
  simpa using h

/-- 平坦極限:波面 ℓ arsinh(tan(t/ℓ)) → t -/
theorem flat_front (t : ℝ) : Tendsto (fun l : ℝ => zfront l t) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · subst ht; simp [zfront]
  have hslope := front_deriv_zero.tendsto_slope_zero
  simp only [zero_add, tan_zero, arsinh_zero, sub_zero, smul_eq_mul] at hslope
  have hu : Tendsto (fun l : ℝ => t / l) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.div_atTop tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with l hl
      exact div_ne_zero ht hl.ne'
  have := (hslope.comp hu).const_mul t
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  simp only [Function.comp, zfront]
  field_simp

/-- 平坦極限:計量の係数 cos²(t/ℓ) → 1、時計の速さ sech(z/ℓ) → 1 -/
theorem flat_metric (t z : ℝ) :
    Tendsto (fun l : ℝ => cos (t / l) ^ 2) atTop (𝓝 1) ∧
    Tendsto (fun l : ℝ => 1 / cosh (z / l)) atTop (𝓝 1) := by
  have h : ∀ x : ℝ, Tendsto (fun l : ℝ => x / l) atTop (𝓝 0) := fun x =>
    tendsto_const_nhds.div_atTop tendsto_id
  constructor
  · simpa using ((continuous_cos.tendsto 0).comp (h t)).pow 2
  · have := (continuous_cosh.tendsto 0).comp (h z)
    simpa using this.inv₀ (by simp)

/-- Z9 の正しい形:正の解が [τ₁, T) で類の条件を満たすなら T − τ₁ ≤ πr₁/2(最大の存在区間の長さ) -/
theorem z9_maximal (r rp W : ℝ → ℝ) (l κ τ1 T r1 : ℝ) (hT : τ1 < T)
    (hpos : ∀ τ ∈ Ico τ1 T, 0 < r τ)
    (h1 : ∀ τ ∈ Ico τ1 T, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Ico τ1 T, HasDerivAt rp (CFT.Z9.acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Ico τ1 T, κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) : T - τ1 ≤ π * r1 / 2 := by
  have hr1p : 0 < r1 := by rw [← hr1]; exact hpos τ1 ⟨le_refl _, hT⟩
  by_contra hlt
  push_neg at hlt
  have hp : 0 < π * r1 / 2 := by have := pi_pos; positivity
  have hsub : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), τ ∈ Ico τ1 T := fun τ hτ =>
    ⟨hτ.1, lt_of_le_of_lt hτ.2 (by linarith)⟩
  have := CFT.Z9.z9_collapse r rp W l κ τ1 (τ1 + π * r1 / 2) r1 (by linarith) (fun τ hτ => hpos τ (hsub τ hτ))
    (fun τ hτ => h1 τ (hsub τ hτ)) (fun τ hτ => h2 τ (hsub τ hτ)) hk (fun τ hτ => hW τ (hsub τ hτ)) h0 hr1
  linarith

/-- 旧 z9_reaches_zero の仮定は κ > 0 では両立しない(r = 0 の点で κ ≤ W²r² = 0 が破れる)。
  したがってその結論は空虚で、正しい形は z9_collapse、z9_maximal -/
theorem z9_reaches_zero_vacuous (r rp W : ℝ → ℝ) (l κ τ1 r1 : ℝ) (hr1p : 0 < r1) (hκ : 0 < κ)
    (h1 : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), HasDerivAt rp (CFT.Z9.acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) : False := by
  obtain ⟨T, hT, hrT⟩ := CFT.Z9.z9_reaches_zero r rp W l κ τ1 r1 hr1p h1 h2 hk hW h0 hr1
  have := hW T hT
  rw [hrT] at this
  simp at this
  linarith

end Analysis

end CFT.S5
