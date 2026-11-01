/-
  α-V.7 (Z31):閉じた FRW の上の量子場の応力と半古典的な反作用(曲率から計算する版)

  外部の入力(確立した結果。適用条件をここに明記する)
  (E1) 共形平坦な時空で、質量ゼロの共形不変な自由場(スカラー、Weyl スピノル、Maxwell/YM の 1 ループ)の
       共形真空での繰り込まれた応力は
         ⟨T^μ_ν⟩_ren = ⟨T^μ_ν⟩_state + α ⁽¹⁾H^μ_ν + β ⁽³⁾H^μ_ν
       (Birrell–Davies 第 6〜7 章、Brown–Cassidy 1977、Bunch–Davies 1977)。
       ⟨T⟩_state は共形な状態の寄与で、閉じた FRW では ESU の値の共形変換 ħκ₁/a⁴(輻射と同じ形、跡ゼロ)。
       β はトレースアノマリーの Euler 密度の係数で場の種類だけで決まる(繰り込みの方式によらない)。
       α は R² の有限な対抗項で任意に動かせる(Brown–Ottewill 1986 の曖昧さ)。
  (E2) 繰り込みの条件として α = 0 を選ぶ(高階微分を入れない方式。状態は共形真空、場の内容は固定)。
  (E3) 共形平坦では Weyl テンソルが 0 なので、Euler 密度は E = −2(R_μν R^μν − R²/3)。
  ここで Lean で示すこと(すべて曲率の道具 `ricD_*`、`rscD` から計算):
  * 閉じた FRW(N = 1、A = a(t)、R = a(t) sin χ)の混合 Ricci:R^0_0 = 3ä/a、R^i_i = ä/a + 2X
    (X = (ȧ² + 1)/a²)、非対角 R_01 = 0、R = 6ä/a + 6X(`frw_r0`〜`frw_r3`、`frw_ric01`、`frw_rsc`)。
  * Einstein テンソル:G^0_0 = −3X(`frw_G00`)。
  * ⁽³⁾H^μ_ν = R^μ_ρR^ρ_ν − ⅔ R R^μ_ν − ½ R_ρσR^ρσ δ + ¼ R² δ(混合成分、計量の符号の規約によらない)は
    ⁽³⁾H^0_0 = 3X²、⁽³⁾H^i_i = 4uX − X²(u = ä/a)、跡 12uX(`h3_frw`)。
    R_μνR^μν − R²/3 = −(跡)(`ricci_sq_identity`)なので、(E3) から E = 2·(跡) = 24uX。
  * 保存則:ρ = −3βX²、p = β(4uX − X²) は ρ̇ + 3(ȧ/a)(ρ + p) = 0 をみたす(`h3_conserved`、実関数)。
    (⟨T⟩_state の κ₁/a⁴ は輻射と同じ形で AlphaV_Backreaction の `continuity_radiation`。)
  * 半古典的な Friedmann 方程式 3X = 8πG(ρ_cl + ħκ₁/a⁴ + ħκ₂X²)は、L = (8πG/3)(K_cl + ħκ₁)、
    γ = (8πG/3)ħκ₂ で X = L/a⁴ + γX²。x = a²X について γx² − a²x + L = 0(`friedmann_quadratic`)。
    γ = 0(主要な次数)では帽子 a = √(L − t²) が解(`cap_semiclassical`)。γ ≠ 0 のときの実数解の条件
    a⁴ ≥ 4γL と小さい枝は AlphaV_Backreaction の `quad_solvable`、`small_branch`。
  * ESU(ȧ = ä = 0):⁽³⁾H の跡は 0、R は定数なので □R = 0、Weyl = 0。したがってアノマリーは消え、
    ⟨T⟩_ren は跡ゼロ(`esu_trace_zero`)。これが AlphaV_Backreaction の `esu_backreaction` の仮定の根拠。
  κ₂ の符号:β は Euler 密度の係数で、自由場では一つの符号にそろう(Duff 1977。Starobinsky 1980 の
  de Sitter 解の存在と同じ符号)。Lean の定理は κ₂ の符号を仮定しない。
-/
import CFT.AlphaS4_Curv
import CFT.AlphaV_Backreaction

namespace CFT.FRW

open CFT.S4

section Curv

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- 閉じた FRW の置き換え:R = a σ(σ = sin χ、κ = cos χ) -/
theorem frw_subs (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) :
    d 0 (a * σ) = d 0 a * σ ∧ d 0 (d 0 a * σ) = d 0 (d 0 a) * σ ∧ d 1 (a * σ) = a * κ ∧
    d 1 (a * κ) = -(a * σ) ∧ d 0 (a * κ) = d 0 a * κ ∧ d 0 (1 : S) = 0 ∧ d 1 (1 : S) = 0 := by
  have hκ0 : d 0 κ = 0 := by rw [← hσ1, H.comm 0 1 σ, hσ0, map_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, (d 0).map_one_eq_zero, (d 1).map_one_eq_zero⟩ <;>
    simp only [Derivation.leibniz, smul_eq_mul, hσ0, hσ1, hκ1, ha1, hκ0] <;> ring

set_option maxHeartbeats 4000000 in
/-- 【α-V.7】R^0_0 = 3ä/a -/
theorem frw_r0 (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    giD 1 a (a * σ) s 0 0 * Ric d (GD d 1 a (a * σ) s c) 0 0 = 3 * d 0 (d 0 a) * a⁻¹ := by
  obtain ⟨e0R, e00R, e1R, e1k, e0k, e01, e11⟩ := frw_subs d a σ κ s c H ha1 hσ0 hσ1 hκ1
  have hA : a ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  have hs : s ≠ 0 := H.hs
  rw [ricD_00 d 1 a (a * σ) s c H]
  simp only [giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, e0R, e00R, e1R, e1k, e0k, e01, e11, ha1, map_zero,
    inv_one, one_pow, mul_inv, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hiS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize a⁻¹ = ia at hia ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  generalize s⁻¹ = iS at hiS ⊢
  linear_combination ((2 : S) * (d 0 (d 0 a)) * ia) * hiσ

set_option maxHeartbeats 4000000 in
/-- 【α-V.7】R^1_1 = ä/a + 2X -/
theorem frw_r1 (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    giD 1 a (a * σ) s 1 1 * Ric d (GD d 1 a (a * σ) s c) 1 1 = d 0 (d 0 a) * a⁻¹ + 2 * ((d 0 a ^ 2 + 1) * a⁻¹ ^ 2) := by
  obtain ⟨e0R, e00R, e1R, e1k, e0k, e01, e11⟩ := frw_subs d a σ κ s c H ha1 hσ0 hσ1 hκ1
  have hA : a ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  have hs : s ≠ 0 := H.hs
  rw [ricD_11 d 1 a (a * σ) s c H]
  simp only [giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, e0R, e00R, e1R, e1k, e0k, e01, e11, ha1, map_zero,
    inv_one, one_pow, mul_inv, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hiS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize a⁻¹ = ia at hia ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  generalize s⁻¹ = iS at hiS ⊢
  linear_combination ((2 : S) * (d 0 a) ^ 2 * ia ^ 2 * iσ * σ + (1 : S) * (d 0 (d 0 a)) * ia + (2 : S) * ia ^ 2 * iσ * σ) * hia + ((2 : S) * (d 0 a) ^ 2 * ia ^ 2 + (2 : S) * ia ^ 2) * hiσ

set_option maxHeartbeats 4000000 in
/-- 【α-V.7】R^2_2 = ä/a + 2X -/
theorem frw_r2 (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    giD 1 a (a * σ) s 2 2 * Ric d (GD d 1 a (a * σ) s c) 2 2 = d 0 (d 0 a) * a⁻¹ + 2 * ((d 0 a ^ 2 + 1) * a⁻¹ ^ 2) := by
  obtain ⟨e0R, e00R, e1R, e1k, e0k, e01, e11⟩ := frw_subs d a σ κ s c H ha1 hσ0 hσ1 hκ1
  have hA : a ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  have hs : s ≠ 0 := H.hs
  rw [ricD_22 d 1 a (a * σ) s c H]
  simp only [giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, e0R, e00R, e1R, e1k, e0k, e01, e11, ha1, map_zero,
    inv_one, one_pow, mul_inv, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hiS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize a⁻¹ = ia at hia ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  generalize s⁻¹ = iS at hiS ⊢
  linear_combination ((-1 : S) * a * ia ^ 3 * iσ ^ 2 * κ ^ 2 + (1 : S) * a * ia ^ 3 * iσ ^ 2 * σ ^ 2 + (1 : S) * (d 0 a) ^ 2 * ia ^ 2 * iσ ^ 2 * σ ^ 2 + (1 : S) * (d 0 (d 0 a)) * ia * iσ ^ 2 * σ ^ 2 + (-1 : S) * ia ^ 2 * iσ ^ 2 * κ ^ 2 + (1 : S) * ia ^ 2 * iσ ^ 2 * σ ^ 2) * hia + ((2 : S) * (d 0 a) ^ 2 * ia ^ 2 + (2 : S) * (d 0 a) ^ 2 * ia ^ 2 * iσ * σ + (1 : S) * (d 0 (d 0 a)) * ia + (1 : S) * (d 0 (d 0 a)) * ia * iσ * σ + (2 : S) * ia ^ 2 + (2 : S) * ia ^ 2 * iσ * σ) * hiσ + ((-1 : S) * ia ^ 2 * iσ ^ 2) * pyth

set_option maxHeartbeats 4000000 in
/-- 【α-V.7】R^3_3 = ä/a + 2X -/
theorem frw_r3 (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    giD 1 a (a * σ) s 3 3 * Ric d (GD d 1 a (a * σ) s c) 3 3 = d 0 (d 0 a) * a⁻¹ + 2 * ((d 0 a ^ 2 + 1) * a⁻¹ ^ 2) := by
  obtain ⟨e0R, e00R, e1R, e1k, e0k, e01, e11⟩ := frw_subs d a σ κ s c H ha1 hσ0 hσ1 hκ1
  have hA : a ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  have hs : s ≠ 0 := H.hs
  rw [ricD_33 d 1 a (a * σ) s c H]
  simp only [giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, e0R, e00R, e1R, e1k, e0k, e01, e11, ha1, map_zero,
    inv_one, one_pow, mul_inv, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hiS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize a⁻¹ = ia at hia ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  generalize s⁻¹ = iS at hiS ⊢
  linear_combination ((-1 : S) * a * ia ^ 3 * iS ^ 2 * iσ ^ 2 * κ ^ 2 * s ^ 2 + (1 : S) * a * ia ^ 3 * iS ^ 2 * iσ ^ 2 * s ^ 2 * σ ^ 2 + (1 : S) * (d 0 a) ^ 2 * ia ^ 2 * iS ^ 2 * iσ ^ 2 * s ^ 2 * σ ^ 2 + (1 : S) * (d 0 (d 0 a)) * ia * iS ^ 2 * iσ ^ 2 * s ^ 2 * σ ^ 2 + (-1 : S) * ia ^ 2 * iS ^ 2 * iσ ^ 2 * κ ^ 2 * s ^ 2 + (1 : S) * ia ^ 2 * iS ^ 2 * iσ ^ 2 * s ^ 2 * σ ^ 2) * hia + ((2 : S) * (d 0 a) ^ 2 * ia ^ 2 * iS ^ 2 * iσ * s ^ 2 * σ + (2 : S) * (d 0 a) ^ 2 * ia ^ 2 * iS ^ 2 * s ^ 2 + (1 : S) * (d 0 (d 0 a)) * ia * iS ^ 2 * iσ * s ^ 2 * σ + (1 : S) * (d 0 (d 0 a)) * ia * iS ^ 2 * s ^ 2 + (1 : S) * ia ^ 2 + (1 : S) * ia ^ 2 * iS ^ 2 * iσ * s ^ 2 * σ + (1 : S) * ia ^ 2 * iS ^ 2 * s ^ 2 + (1 : S) * ia ^ 2 * iσ * σ) * hiσ + ((2 : S) * (d 0 a) ^ 2 * ia ^ 2 + (2 : S) * (d 0 a) ^ 2 * ia ^ 2 * iS * s + (1 : S) * (d 0 (d 0 a)) * ia + (1 : S) * (d 0 (d 0 a)) * ia * iS * s + (1 : S) * ia ^ 2 + (-1 : S) * ia ^ 2 * iS * iσ ^ 2 * κ ^ 2 * s + (1 : S) * ia ^ 2 * iS * iσ ^ 2 * s + (1 : S) * ia ^ 2 * iS * s + (1 : S) * ia ^ 2 * iσ ^ 2 + (-1 : S) * ia ^ 2 * iσ ^ 2 * κ ^ 2) * hiS + ((-1 : S) * ia ^ 2 * iσ ^ 2) * pyth

set_option maxHeartbeats 4000000 in
/-- 非対角 R_01 = 0 -/
theorem frw_ric01 (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    Ric d (GD d 1 a (a * σ) s c) 0 1 = 0 := by
  obtain ⟨e0R, e00R, e1R, e1k, e0k, e01, e11⟩ := frw_subs d a σ κ s c H ha1 hσ0 hσ1 hκ1
  have hA : a ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  have hs : s ≠ 0 := H.hs
  rw [ricD_01 d 1 a (a * σ) s c H]
  simp only [giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, e0R, e00R, e1R, e1k, e0k, e01, e11, ha1, map_zero,
    inv_one, one_pow, mul_inv, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hiS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize a⁻¹ = ia at hia ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  generalize s⁻¹ = iS at hiS ⊢
  linear_combination ((2 : S) * (d 0 a) * ia * iσ * κ) * hia

set_option maxHeartbeats 4000000 in
/-- 【α-V.7】R = 6ä/a + 6X -/
theorem frw_rsc (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    Rsc d (giD 1 a (a * σ) s) (GD d 1 a (a * σ) s c) = 6 * d 0 (d 0 a) * a⁻¹ + 6 * ((d 0 a ^ 2 + 1) * a⁻¹ ^ 2) := by
  obtain ⟨e0R, e00R, e1R, e1k, e0k, e01, e11⟩ := frw_subs d a σ κ s c H ha1 hσ0 hσ1 hκ1
  have hA : a ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  have hs : s ≠ 0 := H.hs
  rw [rscD d 1 a (a * σ) s c H]
  simp only [giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, e0R, e00R, e1R, e1k, e0k, e01, e11, ha1, map_zero,
    inv_one, one_pow, mul_inv, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hiS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize a⁻¹ = ia at hia ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  generalize s⁻¹ = iS at hiS ⊢
  linear_combination ((-2 : S) * a * ia ^ 3 * iσ ^ 2 * κ ^ 2 + (4 : S) * ia ^ 2 * iσ * σ + (-2 : S) * ia ^ 2 * iσ ^ 2 * κ ^ 2) * hia + ((6 : S) * (d 0 a) ^ 2 * ia ^ 2 + (2 : S) * (d 0 a) ^ 2 * ia ^ 2 * iσ * σ + (4 : S) * (d 0 (d 0 a)) * ia + (6 : S) * ia ^ 2 + (2 : S) * ia ^ 2 * iσ * σ) * hiσ + ((-2 : S) * ia ^ 2 * iσ ^ 2) * pyth

/-- 【α-V.7】Einstein テンソル:G^0_0 = R^0_0 − R/2 = −3X -/
theorem frw_G00 (a σ κ s c : S) (H : SphD d 1 a (a * σ) s c) (ha1 : d 1 a = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) :
    giD 1 a (a * σ) s 0 0 * Ein d (gD 1 a (a * σ) s) (giD 1 a (a * σ) s) (GD d 1 a (a * σ) s c) 0 0
      = -3 * ((d 0 a ^ 2 + 1) * a⁻¹ ^ 2) := by
  have h0 := frw_r0 d a σ κ s c H ha1 hσ0 hσ1 hκ1 pyth
  have hR := frw_rsc d a σ κ s c H ha1 hσ0 hσ1 hκ1 pyth
  simp only [Ein, mul_sub]
  rw [h0, hR]
  simp only [giD, gD, Matrix.cons_val_zero, Matrix.head_cons, inv_one, one_pow]
  ring

end Curv

/-! ### ⁽³⁾H の代数(混合成分、対角な Ricci) -/

section H3

variable {S : Type*} [Field S] [CharZero S]

/-- ⁽³⁾H^μ_μ(混合成分、対角な Ricci の固有値 r_ν について) -/
def H3mix (r : Fin 4 → S) (m : Fin 4) : S :=
  r m ^ 2 - 2 / 3 * (∑ i, r i) * r m - 1 / 2 * (∑ i, r i ^ 2) + 1 / 4 * (∑ i, r i) ^ 2

/-- 【α-V.7】閉じた FRW(r = (3u, u + 2X, u + 2X, u + 2X))で ⁽³⁾H^0_0 = 3X²、⁽³⁾H^i_i = 4uX − X²、跡 12uX -/
theorem h3_frw (u X : S) :
    H3mix ![3 * u, u + 2 * X, u + 2 * X, u + 2 * X] 0 = 3 * X ^ 2 ∧
    H3mix ![3 * u, u + 2 * X, u + 2 * X, u + 2 * X] 1 = 4 * u * X - X ^ 2 ∧
    H3mix ![3 * u, u + 2 * X, u + 2 * X, u + 2 * X] 2 = 4 * u * X - X ^ 2 ∧
    H3mix ![3 * u, u + 2 * X, u + 2 * X, u + 2 * X] 3 = 4 * u * X - X ^ 2 ∧
    ∑ m, H3mix ![3 * u, u + 2 * X, u + 2 * X, u + 2 * X] m = 12 * u * X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [H3mix, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons] <;> ring

/-- 跡と Ricci の二乗:R_μνR^μν − R²/3 = −Σ ⁽³⁾H^μ_μ(任意の対角な Ricci) -/
theorem ricci_sq_identity (r : Fin 4 → S) :
    (∑ i, r i ^ 2) - (∑ i, r i) ^ 2 / 3 = -∑ m, H3mix r m := by
  simp only [H3mix, Fin.sum_univ_four]
  ring

/-- 【α-V.7】ESU(u = 0):⁽³⁾H の跡は 0(Euler 密度 E = 2·跡 = 0) -/
theorem esu_trace_zero (X : S) :
    ∑ m, H3mix ![3 * 0, 0 + 2 * X, 0 + 2 * X, 0 + 2 * X] m = 0 := by
  rw [(h3_frw (0 : S) X).2.2.2.2]
  ring

end H3

/-! ### 保存則と半古典的な Friedmann 方程式(実関数) -/

section Real

/-- X = (ȧ² + 1)/a² -/
noncomputable def Xf (a ad : ℝ → ℝ) (τ : ℝ) : ℝ := (ad τ * ad τ + 1) / (a τ * a τ)

/-- 【α-V.7】⁽³⁾H の項は保存する:ρ = −3X²、p = 4uX − X²(β を除いた形)で
ρ̇ = −3(ȧ/a)(ρ + p)(u = ä/a) -/
theorem h3_conserved (a ad : ℝ → ℝ) (add t : ℝ) (ha : HasDerivAt a (ad t) t)
    (had : HasDerivAt ad add t) (ha0 : a t ≠ 0) :
    HasDerivAt (fun τ => -3 * (Xf a ad τ * Xf a ad τ))
      (-3 * (ad t / a t) * (-3 * (Xf a ad t * Xf a ad t)
        + (4 * (add / a t) * Xf a ad t - Xf a ad t * Xf a ad t))) t := by
  have haa : a t * a t ≠ 0 := mul_ne_zero ha0 ha0
  have hX : HasDerivAt (Xf a ad)
      (((add * ad t + ad t * add) * (a t * a t) - (ad t * ad t + 1) * (ad t * a t + a t * ad t))
        / (a t * a t) ^ 2) t :=
    ((had.mul had).add_const 1).div (ha.mul ha) haa
  have h := (hX.mul hX).const_mul (-3)
  refine h.congr_deriv ?_
  simp only [Xf]
  field_simp <;> ring

/-- 【α-V.7】半古典的な Friedmann 方程式 X = L/a⁴ + γX² ⇔ x = a²X について γx² − a²x + L = 0 -/
theorem friedmann_quadratic (X a L γ : ℝ) (ha : a ≠ 0) (h : X = L / a ^ 4 + γ * X ^ 2) :
    γ * (a ^ 2 * X) ^ 2 - a ^ 2 * (a ^ 2 * X) + L = 0 := by
  have h1 : X - γ * X ^ 2 = L / a ^ 4 := by linarith
  have h2 : (X - γ * X ^ 2) * a ^ 4 = L := by
    rw [h1]; exact div_mul_cancel₀ L (pow_ne_zero 4 ha)
  linear_combination (-1 : ℝ) * h2

/-- 【α-V.7】主要な次数(γ = 0):帽子 a = √(L − t²) は X = L/a⁴(3X = 8πGρ、ρ ∝ 1/a⁴)をみたす -/
theorem cap_semiclassical (L t : ℝ) (ht : t ^ 2 < L) :
    ((-t / Real.sqrt (L - t ^ 2)) ^ 2 + 1) / (Real.sqrt (L - t ^ 2)) ^ 2
      = L / (Real.sqrt (L - t ^ 2)) ^ 4 := by
  have hpos : 0 < L - t ^ 2 := by linarith
  have hne : Real.sqrt (L - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [(CFT.Backreaction.cap_friedmann L t ht).2, div_div, ← pow_add] <;> norm_num

end Real

end CFT.FRW
