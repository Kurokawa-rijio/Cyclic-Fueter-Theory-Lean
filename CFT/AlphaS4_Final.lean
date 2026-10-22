/-
  段階 4 の最終定理を、補題を実際に呼び出す形で閉じる(2026-10-21 の評価基準 D:依存関係)

  AlphaS4_Distrib の合成定理(timelike_dumbbell、null_front_weak)は δ の係数の関係式を入力にしていた。
  ここでは最終定理が、場の方程式(微分体 S の上の恒等式)と分布としての方程式(弱い形)だけを入力にとり、
  δ の係数を delta_coeff_weighted で、両側の値を nn_eq_eval で、YM の流束を ymD_split で出す。

  橋渡し:RealLine(横断線の実現)。微分体 S の元 f を線の上の実数値関数 x ↦ ev_x(f) に送る環準同型の族で、
  導分 d が x 微分に対応する(HasDerivWithinAt (fun y => ev y f) (ev x (d f)))。
  * shell_coeff:両側の実現と、各側の古典的な方程式 κ·∂g = src(S の上)と、κ の連続性、分布としての方程式から
    δ の係数 m = κ(x₀)[g](delta_coeff_weighted を呼ぶ)
  * tt_side、ang_side:Einstein 方程式(tt、θθ 成分)と tube_tt_form、tube_ang_form から、κ_tt ∂_x(R_x) = src_tt、
    κ_ang ∂_x(N_x) = src_ang(src は 2ℓ²T̂ − (x の 2 階微分を含まない項))
  * ym_side:YM 方程式 = 0 と ymD_split から ∂_x(N s W_x/A) = src_YM
  * timelike_final(α-III.1):帽子と首の両側の EYM 解、接合点での連続性と時間対称、帽子 w = −1/ℓ、首 w = 0、
    tt・角度成分の分布としての Einstein 方程式から、表面応力は 0 になれない(shell_coeff ×2、tube_israel、
    nn_eq_eval ×2、timelike_no_go を呼ぶ)
  * color_final(α-III.1):YM の分布としての方程式から、表面の色の流れは 0 になれない(shell_coeff、ym_side)
  * slice_final(α-III.9):時間対称な切り口のハミルトン拘束の分布としての式から σ = −[R_x]/(4πG R₀)
  * null_final(α-III.2):両側の EYM 解(二重ヌル)、波面に沿う実現、各 v での分布としての uu 方程式、
    角での [r_u] = 0 から、波面全体で面密度 μ = 0(shell_coeff、mixed_eq、trace_deriv_eq、null_front_from_mixed を呼ぶ)
  入力として残るもの:両側の解が面まで C²(実現の微分可能性)、分布としての方程式(弱解の定義そのもの)。
-/
import CFT.AlphaS4_Distrib

open Real Set intervalIntegral

namespace CFT.S4F

open CFT.S4 CFT.S5

/-- 横断線の実現:S の元を線の上の関数に送り、導分 dd を微分に対応させる -/
structure RealLine {S : Type*} [Field S] (dd : Derivation ℤ S S) (ev : ℝ → S →+* ℝ) (I : Set ℝ) : Prop where
  deriv : ∀ f x, x ∈ I → HasDerivWithinAt (fun y => ev y f) (ev x (dd f)) I x

theorem RealLine.cont {S : Type*} [Field S] {dd : Derivation ℤ S S} {ev : ℝ → S →+* ℝ} {I : Set ℝ}
    (L : RealLine dd ev I) (f : S) : ContinuousOn (fun y => ev y f) I :=
  fun x hx => (L.deriv f x hx).continuousWithinAt

/-- 両側の実現と古典的な方程式から、分布としての方程式の δ の係数 m = κ(x₀)[g] -/
theorem shell_coeff {S₁ S₂ : Type*} [Field S₁] [Field S₂] {d₁ : Derivation ℤ S₁ S₁} {d₂ : Derivation ℤ S₂ S₂}
    {ev₁ : ℝ → S₁ →+* ℝ} {ev₂ : ℝ → S₂ →+* ℝ} {a x0 b m : ℝ} (hax : a < x0) (hxb : x0 < b)
    (L₁ : RealLine d₁ ev₁ (Icc a x0)) (L₂ : RealLine d₂ ev₂ (Icc x0 b))
    (κ₁ g₁ src₁ : S₁) (κ₂ g₂ src₂ : S₂) (e₁ : κ₁ * d₁ g₁ = src₁) (e₂ : κ₂ * d₂ g₂ = src₂)
    (hκ : ev₁ x0 κ₁ = ev₂ x0 κ₂)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, ev₁ x g₁ * (ev₁ x (d₁ κ₁) * φ x + ev₁ x κ₁ * φ' x))
        + ∫ x in x0..b, ev₂ x g₂ * (ev₂ x (d₂ κ₂) * φ x + ev₂ x κ₂ * φ' x))
        = (∫ x in a..x0, ev₁ x src₁ * φ x) + (∫ x in x0..b, ev₂ x src₂ * φ x) + m * φ x0) :
    m = ev₁ x0 κ₁ * (ev₂ x0 g₂ - ev₁ x0 g₁) := by
  let κ : ℝ → ℝ := fun x => if x ≤ x0 then ev₁ x κ₁ else ev₂ x κ₂
  have kL : ∀ x ∈ Icc a x0, κ x = ev₁ x κ₁ := fun x hx => if_pos hx.2
  have kR : ∀ x ∈ Icc x0 b, κ x = ev₂ x κ₂ := by
    intro x hx
    by_cases h : x ≤ x0
    · have : x = x0 := le_antisymm h hx.1
      simp only [κ, if_pos h]; rw [this, hκ]
    · simp only [κ, if_neg h]
  have uL : uIcc a x0 = Icc a x0 := uIcc_of_le hax.le
  have uR : uIcc x0 b = Icc x0 b := uIcc_of_le hxb.le
  have hres := CFT.S4D.delta_coeff_weighted hax hxb (pm := fun x => ev₁ x g₁) (pp := fun x => ev₂ x g₂)
    (qm := fun x => ev₁ x (d₁ g₁)) (qp := fun x => ev₂ x (d₂ g₂)) (Sm := fun x => ev₁ x src₁)
    (Sp := fun x => ev₂ x src₂) (κ := κ) (km := fun x => ev₁ x (d₁ κ₁)) (kp := fun x => ev₂ x (d₂ κ₂)) (m := m)
    (fun x hx => L₁.deriv g₁ x hx) (fun x hx => L₂.deriv g₂ x hx)
    (fun x hx => (L₁.deriv κ₁ x hx).congr (fun y hy => kL y hy) (kL x hx))
    (fun x hx => (L₂.deriv κ₂ x hx).congr (fun y hy => kR y hy) (kR x hx))
    (L₁.cont _) (L₂.cont _) (L₁.cont _) (L₂.cont _)
    (fun x hx => by simp only; rw [kL x hx, ← map_mul, e₁])
    (fun x hx => by simp only; rw [kR x hx, ← map_mul, e₂])
    (fun φ φ' hφ hc ha hb => by
      have h := weak φ φ' hφ hc ha hb
      have i1 : ∫ x in a..x0, ev₁ x g₁ * (ev₁ x (d₁ κ₁) * φ x + κ x * φ' x)
          = ∫ x in a..x0, ev₁ x g₁ * (ev₁ x (d₁ κ₁) * φ x + ev₁ x κ₁ * φ' x) := by
        apply integral_congr; intro x hx; rw [uL] at hx; simp only; rw [kL x hx]
      have i2 : ∫ x in x0..b, ev₂ x g₂ * (ev₂ x (d₂ κ₂) * φ x + κ x * φ' x)
          = ∫ x in x0..b, ev₂ x g₂ * (ev₂ x (d₂ κ₂) * φ x + ev₂ x κ₂ * φ' x) := by
        apply integral_congr; intro x hx; rw [uR] at hx; simp only; rw [kR x hx]
      rw [i1, i2]; exact h)
  rw [hres, kL x0 ⟨hax.le, le_refl _⟩]

section Sides
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- tt 成分の x の 2 階微分を含まない部分 -/
def P00 (N A R : S) : S :=
  2 * d 0 A * d 0 R * A⁻¹ * R⁻¹ + 2 * d 1 A * N ^ 2 * d 1 R * A⁻¹ ^ 3 * R⁻¹
    - N ^ 2 * (d 1 R) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + N ^ 2 * R⁻¹ ^ 2 + (d 0 R) ^ 2 * R⁻¹ ^ 2

/-- 角度の組み合わせの x の 2 階微分を含まない部分 -/
def P22 (N A R : S) : S :=
  -(d 0 (d 0 A)) * R ^ 2 * A⁻¹ * N⁻¹ ^ 2 - R * d 0 (d 0 R) * N⁻¹ ^ 2
    + d 0 A * d 0 N * R ^ 2 * A⁻¹ * N⁻¹ ^ 3 + d 0 N * R * d 0 R * N⁻¹ ^ 3
    - d 1 A * d 1 N * R ^ 2 * A⁻¹ ^ 3 * N⁻¹ + d 1 N * R * d 1 R * A⁻¹ ^ 2 * N⁻¹
    - (d 1 R) ^ 2 * A⁻¹ ^ 2 / 2 + 1 / 2 + (d 0 R) ^ 2 * N⁻¹ ^ 2 / 2

/-- tt 成分の Einstein 方程式 ⇒ κ_tt ∂_x(R_x) = 2ℓ²T̂_tt − P00 -/
theorem tt_side (W N A R s c l : S) (H : SphD d N A R s c)
    (E00 : Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0
      = 2 * l ^ 2 * Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0) :
    -(2 * N ^ 2 * A⁻¹ ^ 2 * R⁻¹) * d 1 (d 1 R)
      = 2 * l ^ 2 * Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0 - P00 d N A R := by
  have h := CFT.S4J.tube_tt_form d N A R s c H
  rw [E00] at h; rw [P00]; linear_combination -h

/-- θθ と tt 成分の Einstein 方程式 ⇒ κ_ang ∂_x(N_x) = 2ℓ²(T̂_θθ + (R²/2N²)T̂_tt) − P22 -/
theorem ang_side (W N A R s c l : S) (H : SphD d N A R s c)
    (E00 : Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0
      = 2 * l ^ 2 * Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0)
    (E22 : Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 2
      = 2 * l ^ 2 * Tym (gD N A R s) (giD N A R s) (FT d W s) 2 2) :
    R ^ 2 * A⁻¹ ^ 2 * N⁻¹ * d 1 (d 1 N)
      = 2 * l ^ 2 * (Tym (gD N A R s) (giD N A R s) (FT d W s) 2 2
          + R ^ 2 * N⁻¹ ^ 2 / 2 * Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0) - P22 d N A R := by
  have h := CFT.S4J.tube_ang_form d N A R s c H
  rw [E00, E22] at h; rw [P22]; linear_combination -h

/-- YM 方程式 = 0 ⇒ ∂_x(N s W_x/A) = −∂_t(−A s W_t/N) − A N s W(1 − W²)/R² -/
theorem ym_side (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0)
    (hY : YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = 0) :
    1 * d 1 (N * s * (d 1 W * A⁻¹))
      = -(d 0 (-(A * s * (d 0 W * N⁻¹))) + A * N * s * W * (1 - W ^ 2) * R⁻¹ ^ 2) := by
  have h := CFT.S4D.ymD_split d W N A R s c H W2 W3
  rw [hY] at h; linear_combination -h

/-- uu 成分の Einstein 方程式 ⇒ κ_uu ∂_u(r_u) = 2ℓ²T̂_uu − (2Ω_u/(Ωr)) r_u(κ_uu = −2/r) -/
theorem uu_side (Om r s c W l : S) (H : SphN d Om r s c)
    (E : Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 0 = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 0) :
    -(2 * r⁻¹) * d 0 (d 0 r)
      = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 0 - 2 * d 0 Om * Om⁻¹ * r⁻¹ * d 0 r := by
  have h := CFT.S4J.uu_form d Om r s c H
  rw [E] at h; linear_combination -h

/-- F = dA + A∧A は表 FT に等しい(fym_eq を球対称の仮定から) -/
theorem fymD (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    Fym d (Aym W s c) = FT d W s :=
  fym_eq d W s c W2 W3 H.s0 H.s1 H.s2 H.s3 H.c0 H.c1 H.c2 H.c3

theorem fymN (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    Fym d (Aym W s c) = FT d W s :=
  fym_eq d W s c W2 W3 H.s0 H.s1 H.s2 H.s3 H.c0 H.c1 H.c2 H.c3

end Sides

/-- α-III.1(重力):帽子(左、S₁)と首(右、S₂)の EYM 解。接合点 x₀ で計量の成分と W が連続、
  時間対称(W_t = 0)、帽子 w = W_x/A = −1/ℓ、首 w = 0。tt と角度成分の分布としての Einstein 方程式の
  δ の係数を 8πG S_tt、8πG S_ang とすると、S_tt = S_ang = 0(殻なし)は起こらない -/
theorem timelike_final {S₁ S₂ : Type*} [Field S₁] [CharZero S₁] [Field S₂] [CharZero S₂]
    (d₁ : Fin 4 → Derivation ℤ S₁ S₁) (d₂ : Fin 4 → Derivation ℤ S₂ S₂)
    (N₁ A₁ R₁ s₁ c₁ W₁ l₁ : S₁) (N₂ A₂ R₂ s₂ c₂ W₂ l₂ : S₂)
    (H₁ : SphD d₁ N₁ A₁ R₁ s₁ c₁) (H₂ : SphD d₂ N₂ A₂ R₂ s₂ c₂)
    (W2₁ : d₁ 2 W₁ = 0) (W3₁ : d₁ 3 W₁ = 0) (W2₂ : d₂ 2 W₂ = 0) (W3₂ : d₂ 3 W₂ = 0)
    (E00₁ : Ein d₁ (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (GD d₁ N₁ A₁ R₁ s₁ c₁) 0 0
      = 2 * l₁ ^ 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0)
    (E11₁ : Ein d₁ (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (GD d₁ N₁ A₁ R₁ s₁ c₁) 1 1
      = 2 * l₁ ^ 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 1 1)
    (E22₁ : Ein d₁ (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (GD d₁ N₁ A₁ R₁ s₁ c₁) 2 2
      = 2 * l₁ ^ 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 2 2)
    (E00₂ : Ein d₂ (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (GD d₂ N₂ A₂ R₂ s₂ c₂) 0 0
      = 2 * l₂ ^ 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0)
    (E11₂ : Ein d₂ (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (GD d₂ N₂ A₂ R₂ s₂ c₂) 1 1
      = 2 * l₂ ^ 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 1 1)
    (E22₂ : Ein d₂ (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (GD d₂ N₂ A₂ R₂ s₂ c₂) 2 2
      = 2 * l₂ ^ 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 2 2)
    {ev₁ : ℝ → S₁ →+* ℝ} {ev₂ : ℝ → S₂ →+* ℝ} {a x0 b G l Stt Sang : ℝ} (hax : a < x0) (hxb : x0 < b)
    (L₁ : RealLine (d₁ 1) ev₁ (Icc a x0)) (L₂ : RealLine (d₂ 1) ev₂ (Icc x0 b))
    (hG : G ≠ 0) (hl : l ≠ 0) (hl₁ : ev₁ x0 l₁ = l) (hl₂ : ev₂ x0 l₂ = l)
    (cN : ev₁ x0 N₁ = ev₂ x0 N₂) (cA : ev₁ x0 A₁ = ev₂ x0 A₂) (cR : ev₁ x0 R₁ = ev₂ x0 R₂)
    (cNt : ev₁ x0 (d₁ 0 N₁) = ev₂ x0 (d₂ 0 N₂)) (cRt : ev₁ x0 (d₁ 0 R₁) = ev₂ x0 (d₂ 0 R₂))
    (cRtt : ev₁ x0 (d₁ 0 (d₁ 0 R₁)) = ev₂ x0 (d₂ 0 (d₂ 0 R₂))) (cW : ev₁ x0 W₁ = ev₂ x0 W₂)
    (ts₁ : ev₁ x0 (d₁ 0 W₁) = 0) (ts₂ : ev₂ x0 (d₂ 0 W₂) = 0)
    (cap : ev₁ x0 (d₁ 1 W₁) * (ev₁ x0 A₁)⁻¹ = -1 / l) (neck : ev₂ x0 (d₂ 1 W₂) * (ev₂ x0 A₂)⁻¹ = 0)
    (weak_tt : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, ev₁ x (d₁ 1 R₁) * (ev₁ x (d₁ 1 (-(2 * N₁ ^ 2 * A₁⁻¹ ^ 2 * R₁⁻¹))) * φ x
            + ev₁ x (-(2 * N₁ ^ 2 * A₁⁻¹ ^ 2 * R₁⁻¹)) * φ' x))
        + ∫ x in x0..b, ev₂ x (d₂ 1 R₂) * (ev₂ x (d₂ 1 (-(2 * N₂ ^ 2 * A₂⁻¹ ^ 2 * R₂⁻¹))) * φ x
            + ev₂ x (-(2 * N₂ ^ 2 * A₂⁻¹ ^ 2 * R₂⁻¹)) * φ' x))
        = (∫ x in a..x0, ev₁ x (2 * l₁ ^ 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0
              - P00 d₁ N₁ A₁ R₁) * φ x)
          + (∫ x in x0..b, ev₂ x (2 * l₂ ^ 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0
              - P00 d₂ N₂ A₂ R₂) * φ x)
          + 8 * π * G * Stt * φ x0)
    (weak_ang : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, ev₁ x (d₁ 1 N₁) * (ev₁ x (d₁ 1 (R₁ ^ 2 * A₁⁻¹ ^ 2 * N₁⁻¹)) * φ x
            + ev₁ x (R₁ ^ 2 * A₁⁻¹ ^ 2 * N₁⁻¹) * φ' x))
        + ∫ x in x0..b, ev₂ x (d₂ 1 N₂) * (ev₂ x (d₂ 1 (R₂ ^ 2 * A₂⁻¹ ^ 2 * N₂⁻¹)) * φ x
            + ev₂ x (R₂ ^ 2 * A₂⁻¹ ^ 2 * N₂⁻¹) * φ' x))
        = (∫ x in a..x0, ev₁ x (2 * l₁ ^ 2 * (Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 2 2
              + R₁ ^ 2 * N₁⁻¹ ^ 2 / 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0)
              - P22 d₁ N₁ A₁ R₁) * φ x)
          + (∫ x in x0..b, ev₂ x (2 * l₂ ^ 2 * (Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 2 2
              + R₂ ^ 2 * N₂⁻¹ ^ 2 / 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0)
              - P22 d₂ N₂ A₂ R₂) * φ x)
          + 8 * π * G * Sang * φ x0) :
    ¬ (Stt = 0 ∧ Sang = 0) := by
  rw [fymD d₁ W₁ N₁ A₁ R₁ s₁ c₁ H₁ W2₁ W3₁] at E00₁ E11₁ E22₁ weak_tt weak_ang
  rw [fymD d₂ W₂ N₂ A₂ R₂ s₂ c₂ H₂ W2₂ W3₂] at E00₂ E11₂ E22₂ weak_tt weak_ang
  -- δ の係数(delta_coeff_weighted を shell_coeff 経由で)
  have htt := shell_coeff hax hxb L₁ L₂ _ _ _ _ _ _ (tt_side d₁ W₁ N₁ A₁ R₁ s₁ c₁ l₁ H₁ E00₁)
    (tt_side d₂ W₂ N₂ A₂ R₂ s₂ c₂ l₂ H₂ E00₂)
    (by simp only [map_neg, map_mul, map_pow, map_inv₀, map_ofNat]; rw [cN, cA, cR]) weak_tt
  have hang := shell_coeff hax hxb L₁ L₂ _ _ _ _ _ _ (ang_side d₁ W₁ N₁ A₁ R₁ s₁ c₁ l₁ H₁ E00₁ E22₁)
    (ang_side d₂ W₂ N₂ A₂ R₂ s₂ c₂ l₂ H₂ E00₂ E22₂)
    (by simp only [map_mul, map_pow, map_inv₀]; rw [cN, cA, cR]) weak_ang
  simp only [map_neg, map_mul, map_pow, map_inv₀, map_ofNat] at htt hang
  have hN : ev₁ x0 N₁ ≠ 0 := (map_ne_zero _).mpr H₁.hN
  have hA : ev₁ x0 A₁ ≠ 0 := (map_ne_zero _).mpr H₁.hA
  have hR : ev₁ x0 R₁ ≠ 0 := (map_ne_zero _).mpr H₁.hR
  intro hS
  obtain ⟨j1, j2⟩ := (CFT.S4J.tube_israel G (ev₁ x0 N₁) (ev₁ x0 A₁) (ev₁ x0 R₁) _ _ Stt Sang hG hN hA hR
    htt.symm hang.symm).mp hS
  -- 両側の nn 方程式の値(nn_eq_eval)
  have g1 := CFT.S4D.nn_eq_eval d₁ W₁ N₁ A₁ R₁ s₁ c₁ l₁ H₁ (ev₁ x0) E11₁
  have g2 := CFT.S4D.nn_eq_eval d₂ W₂ N₂ A₂ R₂ s₂ c₂ l₂ H₂ (ev₂ x0) E11₂
  have eRx : ev₂ x0 (d₂ 1 R₂) = ev₁ x0 (d₁ 1 R₁) := by linarith
  have eNx : ev₂ x0 (d₂ 1 N₂) = ev₁ x0 (d₁ 1 N₁) := by linarith
  rw [ts₁, zero_mul, cap, hl₁] at g1
  rw [ts₂, zero_mul, neck, hl₂] at g2
  simp only [← cN, ← cA, ← cR, ← cNt, ← cRt, ← cRtt, ← cW, eRx, eNx] at g2
  have := CFT.S4J.timelike_no_go l _ _ _ _ _ _ _ _ (-1 / l) 0 hl hR g1 g2
  exact (CFT.S4J.dumbbell_timelike l hl).1 this.symm

/-- α-III.1(ゲージ場):YM 方程式 = 0(各側)と分布としての YM 方程式(流束 N s W_x/A の δ の係数 j)から、
  ダンベルの接合球では表面の色の流れ j は 0 になれない(ymD_split、shell_coeff を呼ぶ) -/
theorem color_final {S₁ S₂ : Type*} [Field S₁] [CharZero S₁] [Field S₂] [CharZero S₂]
    (d₁ : Fin 4 → Derivation ℤ S₁ S₁) (d₂ : Fin 4 → Derivation ℤ S₂ S₂)
    (N₁ A₁ R₁ s₁ c₁ W₁ : S₁) (N₂ A₂ R₂ s₂ c₂ W₂ : S₂)
    (H₁ : SphD d₁ N₁ A₁ R₁ s₁ c₁) (H₂ : SphD d₂ N₂ A₂ R₂ s₂ c₂)
    (W2₁ : d₁ 2 W₁ = 0) (W3₁ : d₁ 3 W₁ = 0) (W2₂ : d₂ 2 W₂ = 0) (W3₂ : d₂ 3 W₂ = 0)
    (Y₁ : YMeq d₁ (giD N₁ A₁ R₁ s₁) (N₁ * A₁ * R₁ ^ 2 * s₁) (Aym W₁ s₁ c₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 2 = 0)
    (Y₂ : YMeq d₂ (giD N₂ A₂ R₂ s₂) (N₂ * A₂ * R₂ ^ 2 * s₂) (Aym W₂ s₂ c₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 2 = 0)
    {ev₁ : ℝ → S₁ →+* ℝ} {ev₂ : ℝ → S₂ →+* ℝ} {a x0 b l j : ℝ} (hax : a < x0) (hxb : x0 < b)
    (L₁ : RealLine (d₁ 1) ev₁ (Icc a x0)) (L₂ : RealLine (d₂ 1) ev₂ (Icc x0 b)) (hl : l ≠ 0)
    (cN : ev₁ x0 N₁ = ev₂ x0 N₂) (cs : ev₁ x0 s₁ = ev₂ x0 s₂)
    (cap : ev₁ x0 (d₁ 1 W₁) * (ev₁ x0 A₁)⁻¹ = -1 / l) (neck : ev₂ x0 (d₂ 1 W₂) * (ev₂ x0 A₂)⁻¹ = 0)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, ev₁ x (N₁ * s₁ * (d₁ 1 W₁ * A₁⁻¹)) * (ev₁ x (d₁ 1 1) * φ x + ev₁ x 1 * φ' x))
        + ∫ x in x0..b, ev₂ x (N₂ * s₂ * (d₂ 1 W₂ * A₂⁻¹)) * (ev₂ x (d₂ 1 1) * φ x + ev₂ x 1 * φ' x))
        = (∫ x in a..x0, ev₁ x (-(d₁ 0 (-(A₁ * s₁ * (d₁ 0 W₁ * N₁⁻¹)))
              + A₁ * N₁ * s₁ * W₁ * (1 - W₁ ^ 2) * R₁⁻¹ ^ 2)) * φ x)
          + (∫ x in x0..b, ev₂ x (-(d₂ 0 (-(A₂ * s₂ * (d₂ 0 W₂ * N₂⁻¹)))
              + A₂ * N₂ * s₂ * W₂ * (1 - W₂ ^ 2) * R₂⁻¹ ^ 2)) * φ x)
          + j * φ x0) :
    j ≠ 0 := by
  rw [fymD d₁ W₁ N₁ A₁ R₁ s₁ c₁ H₁ W2₁ W3₁] at Y₁
  rw [fymD d₂ W₂ N₂ A₂ R₂ s₂ c₂ H₂ W2₂ W3₂] at Y₂
  have hj := shell_coeff hax hxb L₁ L₂ (1 : S₁) _ _ (1 : S₂) _ _
    (ym_side d₁ W₁ N₁ A₁ R₁ s₁ c₁ H₁ W2₁ W3₁ Y₁) (ym_side d₂ W₂ N₂ A₂ R₂ s₂ c₂ H₂ W2₂ W3₂ Y₂)
    (by simp) weak
  simp only [map_one, one_mul, map_mul, map_inv₀] at hj
  rw [show ev₂ x0 N₂ * ev₂ x0 s₂ * (ev₂ x0 (d₂ 1 W₂) * (ev₂ x0 A₂)⁻¹)
      - ev₁ x0 N₁ * ev₁ x0 s₁ * (ev₁ x0 (d₁ 1 W₁) * (ev₁ x0 A₁)⁻¹)
      = ev₁ x0 N₁ * ev₁ x0 s₁ * (0 - -1 / l) by rw [neck, cap, ← cN, ← cs]; ring] at hj
  rw [hj]
  exact CFT.S4D.dumbbell_color_needed _ _ l ((map_ne_zero _).mpr H₁.hN) ((map_ne_zero _).mpr H₁.hs) hl

/-- α-III.9:時間対称な切り口の球面 x₀(A = 1:x は固有の半径)。ハミルトン拘束(tt 成分)の分布としての式の
  δ の係数を 8πG N₀² σ(T_tt = N²ρ、ρ ⊃ σ δ)とすると σ = −[R_x]/(4πG R₀)(tt_side、shell_coeff を呼ぶ) -/
theorem slice_final {S₁ S₂ : Type*} [Field S₁] [CharZero S₁] [Field S₂] [CharZero S₂]
    (d₁ : Fin 4 → Derivation ℤ S₁ S₁) (d₂ : Fin 4 → Derivation ℤ S₂ S₂)
    (N₁ A₁ R₁ s₁ c₁ W₁ l₁ : S₁) (N₂ A₂ R₂ s₂ c₂ W₂ l₂ : S₂)
    (H₁ : SphD d₁ N₁ A₁ R₁ s₁ c₁) (H₂ : SphD d₂ N₂ A₂ R₂ s₂ c₂)
    (W2₁ : d₁ 2 W₁ = 0) (W3₁ : d₁ 3 W₁ = 0) (W2₂ : d₂ 2 W₂ = 0) (W3₂ : d₂ 3 W₂ = 0)
    (E00₁ : Ein d₁ (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (GD d₁ N₁ A₁ R₁ s₁ c₁) 0 0
      = 2 * l₁ ^ 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0)
    (E00₂ : Ein d₂ (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (GD d₂ N₂ A₂ R₂ s₂ c₂) 0 0
      = 2 * l₂ ^ 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0)
    {ev₁ : ℝ → S₁ →+* ℝ} {ev₂ : ℝ → S₂ →+* ℝ} {a x0 b G σ : ℝ} (hax : a < x0) (hxb : x0 < b)
    (L₁ : RealLine (d₁ 1) ev₁ (Icc a x0)) (L₂ : RealLine (d₂ 1) ev₂ (Icc x0 b)) (hG : G ≠ 0)
    (cN : ev₁ x0 N₁ = ev₂ x0 N₂) (cA : ev₁ x0 A₁ = ev₂ x0 A₂) (cR : ev₁ x0 R₁ = ev₂ x0 R₂)
    (hA1 : ev₁ x0 A₁ = 1)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, ev₁ x (d₁ 1 R₁) * (ev₁ x (d₁ 1 (-(2 * N₁ ^ 2 * A₁⁻¹ ^ 2 * R₁⁻¹))) * φ x
            + ev₁ x (-(2 * N₁ ^ 2 * A₁⁻¹ ^ 2 * R₁⁻¹)) * φ' x))
        + ∫ x in x0..b, ev₂ x (d₂ 1 R₂) * (ev₂ x (d₂ 1 (-(2 * N₂ ^ 2 * A₂⁻¹ ^ 2 * R₂⁻¹))) * φ x
            + ev₂ x (-(2 * N₂ ^ 2 * A₂⁻¹ ^ 2 * R₂⁻¹)) * φ' x))
        = (∫ x in a..x0, ev₁ x (2 * l₁ ^ 2 * Tym (gD N₁ A₁ R₁ s₁) (giD N₁ A₁ R₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0
              - P00 d₁ N₁ A₁ R₁) * φ x)
          + (∫ x in x0..b, ev₂ x (2 * l₂ ^ 2 * Tym (gD N₂ A₂ R₂ s₂) (giD N₂ A₂ R₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0
              - P00 d₂ N₂ A₂ R₂) * φ x)
          + 8 * π * G * (ev₁ x0 N₁) ^ 2 * σ * φ x0) :
    σ = -(ev₂ x0 (d₂ 1 R₂) - ev₁ x0 (d₁ 1 R₁)) / (4 * π * G * ev₁ x0 R₁) := by
  rw [fymD d₁ W₁ N₁ A₁ R₁ s₁ c₁ H₁ W2₁ W3₁] at E00₁ weak
  rw [fymD d₂ W₂ N₂ A₂ R₂ s₂ c₂ H₂ W2₂ W3₂] at E00₂ weak
  have h := shell_coeff hax hxb L₁ L₂ _ _ _ _ _ _ (tt_side d₁ W₁ N₁ A₁ R₁ s₁ c₁ l₁ H₁ E00₁)
    (tt_side d₂ W₂ N₂ A₂ R₂ s₂ c₂ l₂ H₂ E00₂)
    (by simp only [map_neg, map_mul, map_pow, map_inv₀, map_ofNat]; rw [cN, cA, cR]) weak
  simp only [map_neg, map_mul, map_pow, map_inv₀, map_ofNat, hA1, inv_one, one_pow, mul_one] at h
  have hN : ev₁ x0 N₁ ≠ 0 := (map_ne_zero _).mpr H₁.hN
  have hR : ev₁ x0 R₁ ≠ 0 := (map_ne_zero _).mpr H₁.hR
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  have h2 : (ev₁ x0 N₁) ^ 2 * (8 * π * G * σ * ev₁ x0 R₁ + 2 * (ev₂ x0 (d₂ 1 R₂) - ev₁ x0 (d₁ 1 R₁))) = 0 := by
    field_simp at h; linear_combination h
  have := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hN)
  linear_combination this / 2

/-- α-III.2:二重ヌルの両側の EYM 解(S₁、S₂)、波面 u = u₀ に沿う実現 fvᵢ、各 v での横断線の実現 euᵢ v、
  波面の上で r, Ω, W, ℓ が連続、角 v₀ で [r_u] = 0。各 v での分布としての uu 方程式の δ の係数を 8πG μ(v) と
  すると、波面全体で μ = 0。さらに YM の表面流 [−s W_v] も 0(uu_form、mixed_eq、shell_coeff、
  trace_deriv_eq、null_front_from_mixed を呼ぶ) -/
theorem null_final {S₁ S₂ : Type*} [Field S₁] [CharZero S₁] [Field S₂] [CharZero S₂]
    (d₁ : Fin 4 → Derivation ℤ S₁ S₁) (d₂ : Fin 4 → Derivation ℤ S₂ S₂)
    (Om₁ r₁ s₁ c₁ W₁ l₁ : S₁) (Om₂ r₂ s₂ c₂ W₂ l₂ : S₂)
    (H₁ : SphN d₁ Om₁ r₁ s₁ c₁) (H₂ : SphN d₂ Om₂ r₂ s₂ c₂)
    (W2₁ : d₁ 2 W₁ = 0) (W3₁ : d₁ 3 W₁ = 0) (W2₂ : d₂ 2 W₂ = 0) (W3₂ : d₂ 3 W₂ = 0)
    (E00₁ : Ein d₁ (gN Om₁ r₁ s₁) (giN Om₁ r₁ s₁) (GN d₁ Om₁ r₁ s₁ c₁) 0 0
      = 2 * l₁ ^ 2 * Tym (gN Om₁ r₁ s₁) (giN Om₁ r₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0)
    (E01₁ : Ein d₁ (gN Om₁ r₁ s₁) (giN Om₁ r₁ s₁) (GN d₁ Om₁ r₁ s₁ c₁) 0 1
      = 2 * l₁ ^ 2 * Tym (gN Om₁ r₁ s₁) (giN Om₁ r₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 1)
    (E00₂ : Ein d₂ (gN Om₂ r₂ s₂) (giN Om₂ r₂ s₂) (GN d₂ Om₂ r₂ s₂ c₂) 0 0
      = 2 * l₂ ^ 2 * Tym (gN Om₂ r₂ s₂) (giN Om₂ r₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0)
    (E01₂ : Ein d₂ (gN Om₂ r₂ s₂) (giN Om₂ r₂ s₂) (GN d₂ Om₂ r₂ s₂ c₂) 0 1
      = 2 * l₂ ^ 2 * Tym (gN Om₂ r₂ s₂) (giN Om₂ r₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 1)
    {v0 v1 a u0 b G : ℝ} (hv : v0 < v1) (hau : a < u0) (hub : u0 < b) (hG : G ≠ 0)
    {fv₁ : ℝ → S₁ →+* ℝ} {fv₂ : ℝ → S₂ →+* ℝ}
    (F₁ : RealLine (d₁ 1) fv₁ (Icc v0 v1)) (F₂ : RealLine (d₂ 1) fv₂ (Icc v0 v1))
    {eu₁ : ℝ → ℝ → S₁ →+* ℝ} {eu₂ : ℝ → ℝ → S₂ →+* ℝ}
    (U₁ : ∀ v, RealLine (d₁ 0) (eu₁ v) (Icc a u0)) (U₂ : ∀ v, RealLine (d₂ 0) (eu₂ v) (Icc u0 b))
    (hpt₁ : ∀ v, eu₁ v u0 = fv₁ v) (hpt₂ : ∀ v, eu₂ v u0 = fv₂ v)
    (cr : ∀ v ∈ Icc v0 v1, fv₁ v r₁ = fv₂ v r₂) (cO : ∀ v ∈ Icc v0 v1, fv₁ v Om₁ = fv₂ v Om₂)
    (cW : ∀ v ∈ Icc v0 v1, fv₁ v W₁ = fv₂ v W₂) (cs : ∀ v ∈ Icc v0 v1, fv₁ v s₁ = fv₂ v s₂)
    (cl : ∀ v ∈ Icc v0 v1, fv₁ v l₁ = fv₂ v l₂)
    (h0 : fv₂ v0 (d₂ 0 r₂) = fv₁ v0 (d₁ 0 r₁)) {μ : ℝ → ℝ}
    (weak : ∀ v ∈ Icc v0 v1, ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..u0, eu₁ v x (d₁ 0 r₁) * (eu₁ v x (d₁ 0 (-(2 * r₁⁻¹))) * φ x + eu₁ v x (-(2 * r₁⁻¹)) * φ' x))
        + ∫ x in u0..b, eu₂ v x (d₂ 0 r₂) * (eu₂ v x (d₂ 0 (-(2 * r₂⁻¹))) * φ x + eu₂ v x (-(2 * r₂⁻¹)) * φ' x))
        = (∫ x in a..u0, eu₁ v x (2 * l₁ ^ 2 * Tym (gN Om₁ r₁ s₁) (giN Om₁ r₁ s₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 0
              - 2 * d₁ 0 Om₁ * Om₁⁻¹ * r₁⁻¹ * d₁ 0 r₁) * φ x)
          + (∫ x in u0..b, eu₂ v x (2 * l₂ ^ 2 * Tym (gN Om₂ r₂ s₂) (giN Om₂ r₂ s₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 0
              - 2 * d₂ 0 Om₂ * Om₂⁻¹ * r₂⁻¹ * d₂ 0 r₂) * φ x)
          + 8 * π * G * μ v * φ u0) :
    (∀ v ∈ Icc v0 v1, μ v = 0) ∧
    (∀ v ∈ Icc v0 v1,
      -(fv₂ v s₂ * fv₂ v (d₂ 1 W₂)) - (-(fv₁ v s₁ * fv₁ v (d₁ 1 W₁))) = 0) := by
  rw [fymN d₁ W₁ Om₁ r₁ s₁ c₁ H₁ W2₁ W3₁] at E00₁ E01₁ weak
  rw [fymN d₂ W₂ Om₂ r₂ s₂ c₂ H₂ W2₂ W3₂] at E00₂ E01₂ weak
  -- 各側の uu 方程式:κ ∂_u(r_u) = 2ℓ²T̂_uu − (2Ω_u/(Ωr)) r_u
  have hδ : ∀ v ∈ Icc v0 v1, 8 * π * G * μ v
      = -2 / fv₁ v r₁ * (fv₂ v (d₂ 0 r₂) - fv₁ v (d₁ 0 r₁)) := by
    intro v hv'
    have h := shell_coeff hau hub (U₁ v) (U₂ v) _ _ _ _ _ _ (uu_side d₁ Om₁ r₁ s₁ c₁ W₁ l₁ H₁ E00₁)
      (uu_side d₂ Om₂ r₂ s₂ c₂ W₂ l₂ H₂ E00₂)
      (by rw [hpt₁, hpt₂]; simp only [map_neg, map_mul, map_inv₀, map_ofNat]; rw [cr v hv']) (weak v hv')
    rw [hpt₁, hpt₂] at h
    simp only [map_neg, map_mul, map_inv₀, map_ofNat] at h
    rw [h]; ring
  -- 波面に沿う接線微分の連続性
  have crv : ∀ v ∈ Icc v0 v1, fv₂ v (d₂ 1 r₂) = fv₁ v (d₁ 1 r₁) :=
    CFT.S4D.trace_deriv_eq hv (fun v hv' => (cr v hv').symm) (fun v hv' => F₂.deriv r₂ v hv')
      (fun v hv' => F₁.deriv r₁ v hv')
  have cWv : ∀ v ∈ Icc v0 v1, fv₂ v (d₂ 1 W₂) = fv₁ v (d₁ 1 W₁) :=
    CFT.S4D.trace_deriv_eq hv (fun v hv' => (cW v hv').symm) (fun v hv' => F₂.deriv W₂ v hv')
      (fun v hv' => F₁.deriv W₁ v hv')
  refine ⟨?_, fun v hv' => by rw [cs v hv', cWv v hv']; ring⟩
  -- 混合成分の式(mixed_eq)を波面の上へ
  have m₁ := (CFT.S4J.mixed_eq d₁ W₁ Om₁ r₁ s₁ c₁ l₁ H₁).mp E01₁
  have m₂ := (CFT.S4J.mixed_eq d₂ W₂ Om₂ r₂ s₂ c₂ l₂ H₂).mp E01₂
  rw [← H₁.comm 1 0 r₁] at m₁
  rw [← H₂.comm 1 0 r₂] at m₂
  refine CFT.S4D.null_front_weak hG (r := fun v => fv₁ v r₁) (rv := fun v => fv₁ v (d₁ 1 r₁))
    (rup := fun v => fv₂ v (d₂ 0 r₂)) (rum := fun v => fv₁ v (d₁ 0 r₁))
    (ruvp := fun v => fv₂ v (d₂ 1 (d₂ 0 r₂))) (ruvm := fun v => fv₁ v (d₁ 1 (d₁ 0 r₁)))
    (F := fun v => fv₁ v (Om₁ / 2 * (l₁ ^ 2 * (1 - W₁ ^ 2) ^ 2 * r₁⁻¹ ^ 2 - 1)))
    (fun v hv' => F₁.deriv r₁ v hv') (fun v hv' => F₂.deriv _ v hv') (fun v hv' => F₁.deriv _ v hv')
    (fun v hv' => ?_) (fun v hv' => ?_) h0 (fun v _ => (map_ne_zero _).mpr H₁.hr) hδ
  · have e := congrArg (fv₂ v) m₂
    simp only [map_add, map_mul, map_sub, map_pow, map_inv₀, map_div₀, map_ofNat, map_one] at e ⊢
    rw [cr v hv', ← crv v hv', cO v hv', cW v hv', cl v hv']
    exact e
  · have e := congrArg (fv₁ v) m₁
    simp only [map_add, map_mul, map_sub, map_pow, map_inv₀, map_div₀, map_ofNat, map_one] at e ⊢
    exact e

end CFT.S4F
