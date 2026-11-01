/-
  α-VI.3:S³ 相は宇宙定数なしでは静的でない(曲率から導く版)

  超静的な計量 g = −dt² + ℓ²(dχ² + sin²χ dθ² + sin²χ sin²θ dφ²) について:
  * スカラー曲率 R = 6/ℓ²(Levi-Civita の公式から計算。`rscD` に N = 1、A = ℓ、R = ℓ sin χ を代入)
  * 対角の計量では Σ_a g^{aa} G_aa = −R(Einstein テンソルの跡)
  * 物質の応力が跡ゼロ(YM 場、輻射)なら、Einstein 方程式 G = κT の跡から R = 0
  したがって ℓ ≠ 0 なら矛盾:超静的な S³ は跡ゼロの物質では Einstein 方程式を満たさない。
  宇宙定数 Λ があれば跡は −R + 4Λ = 0 となり、Λ = 3/(2ℓ²) … のように静的解が可能になる(ここでは扱わない)。

  関数は微分体 S の元(AlphaS4_Curv と同じ設定)。σ = sin χ、κ = cos χ は座標 1(χ)の関数で
  ∂_χ σ = κ、∂_χ κ = −σ、σ² + κ² = 1。
-/
import CFT.AlphaS4_Curv

namespace CFT.VIStatic

open CFT.S4

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- 対角の計量では Einstein テンソルの跡は −R:Σ_a g^{aa} G_aa = −R -/
theorem trace_einD (N A R s : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0)
    (Γ : Fin 4 → Fin 4 → Fin 4 → S) :
    giD N A R s 0 0 * Ein d (gD N A R s) (giD N A R s) Γ 0 0
      + giD N A R s 1 1 * Ein d (gD N A R s) (giD N A R s) Γ 1 1
      + giD N A R s 2 2 * Ein d (gD N A R s) (giD N A R s) Γ 2 2
      + giD N A R s 3 3 * Ein d (gD N A R s) (giD N A R s) Γ 3 3
      = -Rsc d (giD N A R s) Γ := by
  have hRs : Rsc d (giD N A R s) Γ = -(N⁻¹ ^ 2) * Ric d Γ 0 0 + A⁻¹ ^ 2 * Ric d Γ 1 1
      + R⁻¹ ^ 2 * Ric d Γ 2 2 + R⁻¹ ^ 2 * s⁻¹ ^ 2 * Ric d Γ 3 3 := by
    simp only [Rsc, giD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      zero_mul, add_zero, zero_add]
    try ring
  simp only [Ein]
  generalize Rsc d (giD N A R s) Γ = X at hRs ⊢
  simp only [gD, giD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN hRs ⊢
  generalize A⁻¹ = iA at hiA hRs ⊢
  generalize R⁻¹ = iR at hiR hRs ⊢
  generalize s⁻¹ = is at his hRs ⊢
  linear_combination (-1 : S) * hRs + (-(1 / 2 : S) * X * (N * iN + 1)) * hiN
    + (-(1 / 2 : S) * X * (A * iA + 1)) * hiA + (-X * (R * iR + 1)) * hiR
    + (-(1 / 2 : S) * X * (R * iR) ^ 2 * (s * is + 1)) * his

/-- 超静的な S³ のスカラー曲率は 6/ℓ² -/
theorem rsc_static_S3 (l σ κ s c : S) (H : SphD d 1 l (l * σ) s c) (hl : ∀ i, d i l = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ)
    (pyth : σ ^ 2 + κ ^ 2 = 1) :
    Rsc d (giD 1 l (l * σ) s) (GD d 1 l (l * σ) s c) = 6 * l⁻¹ ^ 2 := by
  have hA : l ≠ 0 := H.hA
  have hσ : σ ≠ 0 := right_ne_zero_of_mul H.hR
  rw [rscD d 1 l (l * σ) s c H]
  have e0R : d 0 (l * σ) = 0 := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hσ0, hl 0]; ring
  have e1R : d 1 (l * σ) = l * κ := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hσ1, hl 1]; ring
  have e1k : d 1 (l * κ) = -(l * σ) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hκ1, hl 1]; ring
  have e1 : d 0 (1 : S) = 0 := (d 0).map_one_eq_zero
  have e1' : d 1 (1 : S) = 0 := (d 1).map_one_eq_zero
  simp only [e0R, e1R, e1k, e1, e1', hl 0, hl 1, map_zero, mul_inv, inv_one, one_pow,
    zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul]
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  generalize l⁻¹ = il at hil ⊢
  generalize σ⁻¹ = iσ at hiσ ⊢
  linear_combination (-2 * κ ^ 2 * il ^ 2 * iσ ^ 2 * (l * il + 1) + 4 * il ^ 2) * hil
    + (4 * il ^ 2 * (l * il) + 2 * il ^ 2 * (σ * iσ + 1)) * hiσ
    + (-2 * il ^ 2 * iσ ^ 2) * pyth

/-- 【α-VI.3】超静的な S³(半径 ℓ)は、跡ゼロの物質(YM 場・輻射)と Einstein 方程式
G_aa = κ_G T_aa を同時にはみたせない。
計算:跡をとると −R = κ_G Σ g^{aa}T_aa = 0、一方 R = 6/ℓ² ≠ 0。 -/
theorem static_S3_impossible (l σ κ s c κG : S) (H : SphD d 1 l (l * σ) s c)
    (hl : ∀ i, d i l = 0) (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ)
    (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) (T : Fin 4 → Fin 4 → S)
    (E : ∀ a, Ein d (gD 1 l (l * σ) s) (giD 1 l (l * σ) s) (GD d 1 l (l * σ) s c) a a
      = κG * T a a)
    (traceless : giD 1 l (l * σ) s 0 0 * T 0 0 + giD 1 l (l * σ) s 1 1 * T 1 1
      + giD 1 l (l * σ) s 2 2 * T 2 2 + giD 1 l (l * σ) s 3 3 * T 3 3 = 0) : False := by
  have htr := trace_einD d 1 l (l * σ) s one_ne_zero H.hA H.hR H.hs (GD d 1 l (l * σ) s c)
  rw [E 0, E 1, E 2, E 3, rsc_static_S3 d l σ κ s c H hl hσ0 hσ1 hκ1 pyth] at htr
  have h0 : (6 : S) * l⁻¹ ^ 2 = 0 := by linear_combination htr - κG * traceless
  have hl0 : l ≠ 0 := H.hA
  have : (6 : S) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h0 with h | h
  · exact this h
  · exact hl0 (inv_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h))

set_option maxHeartbeats 0 in
/-- 【α-VI.3 の物質側】4 次元の YM の応力は跡ゼロ:対角の計量で Σ_m g^{mm} T̂_mm = 0。
F は任意の成分の表(ゲージ場の具体形によらない)。g^{mm} g_mm = 1 と 4 次元(¼ · 4 = 1)だけを使う。 -/
theorem tym_traceless (N A R s : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0)
    (F : Fin 3 → Fin 4 → Fin 4 → S) :
    giD N A R s 0 0 * Tym (gD N A R s) (giD N A R s) F 0 0
      + giD N A R s 1 1 * Tym (gD N A R s) (giD N A R s) F 1 1
      + giD N A R s 2 2 * Tym (gD N A R s) (giD N A R s) F 2 2
      + giD N A R s 3 3 * Tym (gD N A R s) (giD N A R s) F 3 3 = 0 := by
  simp only [Tym, gD, giD, Fin.sum_univ_four, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, zero_mul, mul_zero, add_zero, zero_add]
  field_simp
  ring

/-- 【α-VI.3】Einstein–Yang–Mills:超静的な S³ に YM の応力 T̂(任意の F)を置いた Einstein 方程式
G_aa = κ_G T̂_aa は解をもたない(跡ゼロの YM 応力を `static_S3_impossible` に代入)。 -/
theorem static_S3_YM_impossible (l σ κ s c κG : S) (H : SphD d 1 l (l * σ) s c)
    (hl : ∀ i, d i l = 0) (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ)
    (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1) (F : Fin 3 → Fin 4 → Fin 4 → S)
    (E : ∀ a, Ein d (gD 1 l (l * σ) s) (giD 1 l (l * σ) s) (GD d 1 l (l * σ) s c) a a
      = κG * Tym (gD 1 l (l * σ) s) (giD 1 l (l * σ) s) F a a) : False :=
  static_S3_impossible d l σ κ s c κG H hl hσ0 hσ1 hκ1 pyth
    (fun a b => Tym (gD 1 l (l * σ) s) (giD 1 l (l * σ) s) F a b) E
    (tym_traceless 1 l (l * σ) s one_ne_zero H.hA H.hR H.hs F)

end CFT.VIStatic
