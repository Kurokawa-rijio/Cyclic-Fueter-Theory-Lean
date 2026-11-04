/-
  α-IX.16〜IX.20:流体と磁気流体(作用原理・保存則からの帰結)

  関数は微分体 S の元、∂_μ は可換な導分(AlphaS4_Curv と同じ抽象)。平坦な計量 η = diag(−1, 1, 1, 1)。
  * IX.16 完全流体 T^{μν} = (ρ + p)u^μu^ν + pη^{μν}:∂_μT^{μν} = 0 と u·u = −1 から
      連続の式(エネルギー)Σ_μ ∂_μ((ρ + p)u^μ) = u^μ∂_μ p(`fluid_energy`)、
      相対論的 Euler 方程式 (ρ + p)u^μ∂_μ u^ν = −η^{νν}∂_ν p − u^ν u^μ∂_μ p(`fluid_euler`)。
      非相対論の極限(u ≈ (1, v)、p ≪ ρ)で通常の Euler 方程式になること:標準(外部)。
  * IX.17 帽子は輻射の宇宙:YM の応力は跡ゼロ(AlphaII_EYM `ym_stress`)、帽子で p_r = p_T = ρ/3、
      a = √(L − t²) は閉じた輻射 FRW の Friedmann 方程式の解(`cap_radiation`)。
  * IX.18 Kelvin の循環定理の局所形:ω = dw(w = hu)、L_u ω = d(i_u ω) + i_u dω で dω = 0
      (`cyclic_zero`)、したがって L_u ω_{μν} = ∂_μ(i_uω)_ν − ∂_ν(i_uω)_μ(`lie_two_form`)。
      i_u ω = 0(Carter–Lichnerowicz 形の Euler 方程式、外部)なら L_u ω = 0(`kelvin`)。循環の保存は Stokes(外部)。
      3 次元の渦度方程式の外積は純虚四元数の交換子の半分(`cross_is_commutator`)。
  * IX.19 磁束凍結:F = dA、理想 MHD i_u F = 0 なら L_u F = 0(`flux_freezing`、IX.18 と同じ恒等式)。
  * IX.20 ヘリシティ:∂_t(A·B) + ∇·(φB + E×A) + 2E·B = 0(`helicity_balance`)。理想 MHD(E·B = 0)で
      磁気ヘリシティは保存。Hopf 不変量・Chern–Simons としての解釈は外部。
-/
import CFT.AlphaS4_Curv
import CFT.AlphaII_EYM
import CFT.AlphaV_Backreaction
import Mathlib.Algebra.Quaternion

namespace CFT.Fluid

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-! ### IX.16 完全流体 -/

/-- η = diag(−1, 1, 1, 1) -/
def eta (μ ν : Fin 4) : S := if μ = ν then (if μ = 0 then -1 else 1) else 0

theorem d_eta (i μ ν : Fin 4) : d i (eta μ ν : S) = 0 := by
  unfold eta; split_ifs <;> simp

/-- ∂_μ T^{μν} -/
def divT (ρ p : S) (u : Fin 4 → S) (ν : Fin 4) : S :=
  ∑ μ, d μ ((ρ + p) * u μ * u ν + p * eta μ ν)

/-- 展開:∂_μT^{μν} = D u^ν + (ρ + p) u^μ∂_μu^ν + η^{νν}∂_ν p、D = Σ_μ ∂_μ((ρ + p)u^μ) -/
theorem divT_expand (ρ p : S) (u : Fin 4 → S) (ν : Fin 4) :
    divT d ρ p u ν = (∑ μ, d μ ((ρ + p) * u μ)) * u ν + (ρ + p) * (∑ μ, u μ * d μ (u ν))
      + eta ν ν * d ν p := by
  unfold divT
  have h : ∀ μ, d μ ((ρ + p) * u μ * u ν + p * eta μ ν)
      = d μ ((ρ + p) * u μ) * u ν + (ρ + p) * (u μ * d μ (u ν)) + eta μ ν * d μ p := by
    intro μ
    rw [map_add, Derivation.leibniz, Derivation.leibniz (d μ) p, d_eta]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single ν]
  · intro b _ hb; simp [eta, hb]
  · intro h; exact absurd (Finset.mem_univ ν) h

/-- 規格化の微分:u·u = −1 なら u_ν∂_μu^ν = 0 -/
theorem norm_deriv (u : Fin 4 → S) (hn : -(u 0) ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = -1) (μ : Fin 4) :
    -(u 0) * d μ (u 0) + u 1 * d μ (u 1) + u 2 * d μ (u 2) + u 3 * d μ (u 3) = 0 := by
  have h := congrArg (d μ) hn
  simp only [map_add, map_neg, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Derivation.map_one_eq_zero,
    neg_zero, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  have h2 : (2 : S) * (-(u 0) * d μ (u 0) + u 1 * d μ (u 1) + u 2 * d μ (u 2) + u 3 * d μ (u 3)) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- 【α-IX.16】連続の式:Σ_μ ∂_μ((ρ + p)u^μ) = u^μ∂_μ p -/
theorem fluid_energy (ρ p : S) (u : Fin 4 → S) (h : ∀ ν, divT d ρ p u ν = 0)
    (hn : -(u 0) ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = -1) :
    ∑ μ, d μ ((ρ + p) * u μ) = ∑ μ, u μ * d μ p := by
  have e : ∀ ν, (∑ μ, d μ ((ρ + p) * u μ)) * u ν + (ρ + p) * (∑ μ, u μ * d μ (u ν))
      + eta ν ν * d ν p = 0 := fun ν => (divT_expand d ρ p u ν).symm.trans (h ν)
  have n0 := norm_deriv d u hn 0
  have n1 := norm_deriv d u hn 1
  have n2 := norm_deriv d u hn 2
  have n3 := norm_deriv d u hn 3
  have h00 : (eta 0 0 : S) = -1 := by simp [eta]
  have h11 : (eta 1 1 : S) = 1 := by simp [eta]
  have h22 : (eta 2 2 : S) = 1 := by simp [eta]
  have h33 : (eta 3 3 : S) = 1 := by simp [eta]
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3
  rw [h00] at e0; rw [h11] at e1; rw [h22] at e2; rw [h33] at e3
  simp only [Fin.sum_univ_four] at e0 e1 e2 e3 ⊢
  linear_combination -(-(u 0) * e0 + u 1 * e1 + u 2 * e2 + u 3 * e3)
    + (d 0 ((ρ + p) * u 0) + d 1 ((ρ + p) * u 1) + d 2 ((ρ + p) * u 2) + d 3 ((ρ + p) * u 3)) * hn
    + (ρ + p) * (u 0 * n0 + u 1 * n1 + u 2 * n2 + u 3 * n3)

/-- 【α-IX.16】相対論的 Euler 方程式 (ρ + p)u^μ∂_μu^ν = −η^{νν}∂_ν p − u^ν u^μ∂_μ p -/
theorem fluid_euler (ρ p : S) (u : Fin 4 → S) (h : ∀ ν, divT d ρ p u ν = 0)
    (hn : -(u 0) ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = -1) (ν : Fin 4) :
    (ρ + p) * (∑ μ, u μ * d μ (u ν)) = -(eta ν ν * d ν p) - u ν * (∑ μ, u μ * d μ p) := by
  have e := (divT_expand d ρ p u ν).symm.trans (h ν)
  have en := fluid_energy d ρ p u h hn
  linear_combination e - u ν * en

/-! ### IX.17 帽子は輻射の宇宙 -/

open Real in
/-- 【α-IX.17】YM の応力は跡ゼロ、帽子で p_r = p_T = ρ/3、a = √(L − t²) は Friedmann 方程式 ȧ² + 1 = L/a² の解 -/
theorem cap_radiation (g l x L t : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) (hx : sin x ≠ 0) (ht : t ^ 2 < L) :
    (-CFT.EYM.rho g (cos x) (-(sin x) / l) (l * sin x) + CFT.EYM.pr g (cos x) (-(sin x) / l) (l * sin x)
      + 2 * CFT.EYM.pT g (cos x) (-(sin x) / l) (l * sin x) = 0) ∧
    CFT.EYM.pr g (cos x) (-(sin x) / l) (l * sin x) = CFT.EYM.rho g (cos x) (-(sin x) / l) (l * sin x) / 3 ∧
    CFT.EYM.pT g (cos x) (-(sin x) / l) (l * sin x) = CFT.EYM.rho g (cos x) (-(sin x) / l) (l * sin x) / 3 ∧
    (-t / Real.sqrt (L - t ^ 2)) ^ 2 + 1 = L / (Real.sqrt (L - t ^ 2)) ^ 2 := by
  have hr : l * sin x ≠ 0 := mul_ne_zero hl hx
  obtain ⟨c1, c2, c3⟩ := CFT.EYM.cap_stress g l x hg hl hx
  refine ⟨(CFT.EYM.ym_stress g _ _ _ hg hr).2.2.2, ?_, ?_, (CFT.Backreaction.cap_friedmann L t ht).2⟩
  · rw [c1, c2]; field_simp <;> ring
  · rw [c1, c3]; field_simp <;> ring

/-! ### IX.18、IX.19 Kelvin と磁束凍結(2 形式の Lie 微分) -/

section Lie

variable {n : ℕ} (D : Fin n → Derivation ℤ S S) (hcomm : ∀ i j f, D i (D j f) = D j (D i f))

/-- ω = dw:ω_{μν} = ∂_μ w_ν − ∂_ν w_μ -/
def om (w : Fin n → S) (μ ν : Fin n) : S := D μ (w ν) - D ν (w μ)

include hcomm in
/-- dω = 0 の成分:∂_λ ω_{μν} − ∂_μ ω_{λν} + ∂_ν ω_{λμ} = 0 -/
theorem cyclic_zero (w : Fin n → S) (l μ ν : Fin n) :
    D l (om D w μ ν) - D μ (om D w l ν) + D ν (om D w l μ) = 0 := by
  simp only [om, map_sub]
  rw [hcomm l μ (w ν), hcomm l ν (w μ), hcomm μ ν (w l)]
  ring

/-- L_u ω_{μν} = Σ_λ (u^λ∂_λω_{μν} + ω_{λν}∂_μu^λ + ω_{μλ}∂_νu^λ) -/
def lieOm (w u : Fin n → S) (μ ν : Fin n) : S :=
  ∑ l, (u l * D l (om D w μ ν) + om D w l ν * D μ (u l) + om D w μ l * D ν (u l))

/-- (i_u ω)_ν = Σ_λ u^λ ω_{λν} -/
def iuOm (w u : Fin n → S) (ν : Fin n) : S := ∑ l, u l * om D w l ν

include hcomm in
/-- 【α-IX.18】Cartan の公式(dω = 0 のとき):L_u ω_{μν} = ∂_μ(i_uω)_ν − ∂_ν(i_uω)_μ -/
theorem lie_two_form (w u : Fin n → S) (μ ν : Fin n) :
    lieOm D w u μ ν = D μ (iuOm D w u ν) - D ν (iuOm D w u μ) := by
  simp only [lieOm, iuOm, map_sum, Derivation.leibniz, smul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hc := cyclic_zero D hcomm w l μ ν
  have ha : om D w μ l = -(om D w l μ) := by simp only [om]; ring
  rw [ha]
  linear_combination (u l) * hc

include hcomm in
/-- 【α-IX.18】Kelvin:i_u ω = 0 なら L_u ω = 0 -/
theorem kelvin (w u : Fin n → S) (h : ∀ ν, iuOm D w u ν = 0) (μ ν : Fin n) : lieOm D w u μ ν = 0 := by
  rw [lie_two_form D hcomm, h, h, map_zero, sub_zero]

include hcomm in
/-- 【α-IX.19】磁束凍結:F = dA、理想 MHD i_u F = 0 なら L_u F = 0 -/
theorem flux_freezing (A u : Fin n → S) (h : ∀ ν, iuOm D A u ν = 0) (μ ν : Fin n) : lieOm D A u μ ν = 0 :=
  kelvin D hcomm A u h μ ν

end Lie

/-- 【α-IX.18】純虚四元数の交換子:[v, ω] = 2 v × ω(渦度方程式の外積) -/
theorem cross_is_commutator (v w : Quaternion ℝ) (hv : v.re = 0) (hw : w.re = 0) :
    (v * w - w * v).re = 0 ∧ (v * w - w * v).imI = 2 * (v.imJ * w.imK - v.imK * w.imJ) ∧
    (v * w - w * v).imJ = 2 * (v.imK * w.imI - v.imI * w.imK) ∧
    (v * w - w * v).imK = 2 * (v.imI * w.imJ - v.imJ * w.imI) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK,
    hv, hw] <;> ring

/-! ### IX.20 ヘリシティ -/

section Helicity

variable (A : Fin 3 → S) (φ : S)
  (c10 : ∀ f, d 1 (d 0 f) = d 0 (d 1 f)) (c20 : ∀ f, d 2 (d 0 f) = d 0 (d 2 f))
  (c30 : ∀ f, d 3 (d 0 f) = d 0 (d 3 f)) (c21 : ∀ f, d 2 (d 1 f) = d 1 (d 2 f))
  (c31 : ∀ f, d 3 (d 1 f) = d 1 (d 3 f)) (c32 : ∀ f, d 3 (d 2 f) = d 2 (d 3 f))

/-- 空間の微分 ∂_i = d (i + 1) -/
def ds (i : Fin 3) : Derivation ℤ S S := d i.succ

/-- B = ∇ × A -/
def Bf : Fin 3 → S := ![ds d 1 (A 2) - ds d 2 (A 1), ds d 2 (A 0) - ds d 0 (A 2), ds d 0 (A 1) - ds d 1 (A 0)]

/-- E = −∇φ − ∂_t A -/
def Ef : Fin 3 → S := fun i => -(ds d i φ) - d 0 (A i)

include c10 c20 c30 c21 c31 c32 in
/-- 【α-IX.20】∂_t(A·B) + ∇·(φB + E×A) + 2E·B = 0 -/
theorem helicity_balance :
    let B := Bf d A
    let E := Ef d A φ
    d 0 (A 0 * B 0 + A 1 * B 1 + A 2 * B 2)
      + (ds d 0 (φ * B 0 + (E 1 * A 2 - E 2 * A 1)) + ds d 1 (φ * B 1 + (E 2 * A 0 - E 0 * A 2))
        + ds d 2 (φ * B 2 + (E 0 * A 1 - E 1 * A 0)))
      + 2 * (E 0 * B 0 + E 1 * B 1 + E 2 * B 2) = 0 := by
  intro B E
  simp only [B, E, Bf, Ef, ds, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [show (2 : Fin 3).succ = 3 from rfl, c10, c20, c30, c21, c31, c32]
  ring

end Helicity

end CFT.Fluid
