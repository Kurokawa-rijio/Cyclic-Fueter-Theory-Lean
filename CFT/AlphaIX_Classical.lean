/-
  段階 2(その 3):作用から電磁気学(電気の側)と解析力学へ(α-IX.1〜IX.3、IX.5〜IX.9)

  可換な導分 ∂₀, …, ∂₃(∂₀ = ∂_t)、Minkowski 計量 η = diag(−1, 1, 1, 1)。A_ν は下付き、J^ν は上付き。
  F_{μν} = ∂_μA_ν − ∂_νA_μ、F^{μν} = η^μη^νF_{μν}。
  A. 電磁気学
    * IX.1 first_variation:L = −¼F_{μν}F^{μν} + J^νA_ν について
        δL = Σ_ν δA_ν(∂_μF^{μν} + J^ν) − ∂_μ(F^{μν}δA_ν)(等式)。EL の式は ∂_μF^{μν} = −J^ν
    * IX.2 gauss、ampere:EL の式の ν = 0 成分は ∇·E = ρ、ν = 1 成分は (∇×B)₁ = J¹ + ∂_tE₁
      (E_i = F_{i0}、B₁ = F₂₃ など、ρ = J⁰)
    * IX.3 bianchi_div、faraday:∇·B = 0、(∇×E)₁ + ∂_tB₁ = 0 は方程式を使わない恒等式(磁気の側は位相的・幾何的)。
      charge_conservation:EL の式から ∂_νJ^ν = 0
  B. 解析力学
    * IX.6 stress_divergence:T_{μν} = Σ_α η^α F_{μα}F_{να} − ¼η_{μν}F² について
        Σ_μ η^μ ∂_μT_{μν} = Σ_α η^α F_{να}·(Σ_μ η^μ ∂_μF_{μα})(恒等式、Bianchi を使う)。
      Maxwell の式を入れると ∂^μT_{μν} = −F_{να}J^α
    * IX.7 dust_lorentz:塵 T^{μν} = ρu^μu^ν の連続の式と全体の保存から ρ(u·∂)u^ν = ρ_e F^ν{}_λu^λ
    * IX.8 particle_el:粒子の L = ½m η u u + qA·u の EL の式は m u̇_μ − qF_{μν}u^ν(世界線の連鎖律は入力)
    * IX.9 hamilton:p_μ = mη_μu^μ + qA_μ、H = (1/2m)Σ η^μ(p_μ − qA_μ)² の Hamilton の式は EL の式と同値。
      mass_shell:質量殻 (p − qA)² = −m² から (E − qφ)² = m² + |p − qA|²、(m/E_kin)² + |p_kin/E_kin|² = 1(Q の上の点)
  C. IX.5 gauss_integral:球対称で ∂_r(r²E_r) = r²ρ なら、電荷 Q(r) = 4πr²E_r は Q(b) − Q(a) = 4π∫_a^b r²ρ(力学的)。
     磁荷は Chern 数(α-VII.1 の dirac_quantization、位相的)
-/
import CFT.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Tactic.LinearCombination

namespace CFT.Classical

set_option maxHeartbeats 0

section EM
variable {S : Type*} [Field S] [CharZero S]
variable (D : Fin 4 → Derivation ℤ S S) (δ : Derivation ℤ S S) (A J : Fin 4 → S)

/-- η = diag(−1, 1, 1, 1) -/
def eta (μ : Fin 4) : S := if μ = 0 then -1 else 1

def F (μ ν : Fin 4) : S := D μ (A ν) - D ν (A μ)
def Fu (μ ν : Fin 4) : S := eta μ * eta ν * F D A μ ν

def Lag : S := -(1/4 : S) * ∑ μ, ∑ ν, Fu D A μ ν * F D A μ ν + ∑ ν, J ν * A ν

/-- EL の式 ∂_μF^{μν} + J^ν -/
def EL (ν : Fin 4) : S := ∑ μ, D μ (Fu D A μ ν) + J ν

theorem eta_const (μ ν : Fin 4) : D μ (eta ν : S) = 0 := by
  unfold eta; split_ifs
  · rw [map_neg, Derivation.map_one_eq_zero, neg_zero]
  · exact Derivation.map_one_eq_zero _

theorem eta_const' (ν : Fin 4) : δ (eta ν : S) = 0 := by
  unfold eta; split_ifs
  · rw [map_neg, Derivation.map_one_eq_zero, neg_zero]
  · exact Derivation.map_one_eq_zero _

theorem d_quarter (d : Derivation ℤ S S) : d (1/4 : S) = 0 := by
  have h := map_nsmul d 4 (1/4 : S)
  rw [nsmul_eq_mul, nsmul_eq_mul, show ((4:ℕ):S) * (1/4) = 1 by norm_num, Derivation.map_one_eq_zero] at h
  have h4 : ((4:ℕ):S) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h.symm).resolve_left h4

/-- IX.1:第一変分 -/
theorem first_variation (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (hδ : ∀ μ x, δ (D μ x) = D μ (δ x))
    (hJ : ∀ ν, δ (J ν) = 0) :
    δ (Lag D A J) = ∑ ν, δ (A ν) * EL D A J ν - ∑ μ, D μ (∑ ν, Fu D A μ ν * δ (A ν)) := by
  have h4 := d_quarter δ
  simp only [Lag, EL, Fu, F, map_add, map_sub, map_neg, map_sum, map_mul, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib, Fin.sum_univ_four, eta_const D, eta_const' δ, hδ, hJ, h4]
  simp only [eta, Fin.isValue, if_true, show ((1:Fin 4) = 0) = False by decide,
    show ((2:Fin 4) = 0) = False by decide, show ((3:Fin 4) = 0) = False by decide, if_false]
  simp only [hc 1 0, hc 2 0, hc 3 0, hc 2 1, hc 3 1, hc 3 2]
  ring

/-- 電場と磁場:E_i = F_{i0}、B = (F₂₃, F₃₁, F₁₂) -/
def Ef (i : Fin 4) : S := F D A i 0
def B1 : S := F D A 2 3
def B2 : S := F D A 3 1
def B3 : S := F D A 1 2

/-- IX.2 Gauss の法則:EL₀ = 0 ⇔ ∇·E = ρ(ρ = J⁰) -/
theorem gauss : EL D A J 0 = -(D 1 (Ef D A 1) + D 2 (Ef D A 2) + D 3 (Ef D A 3)) + J 0 := by
  simp only [EL, Fu, Ef, F, eta, Fin.sum_univ_four, map_sub, map_neg, map_mul, Derivation.leibniz,
    smul_eq_mul, Fin.isValue, if_true, show ((1:Fin 4) = 0) = False by decide,
    show ((2:Fin 4) = 0) = False by decide, show ((3:Fin 4) = 0) = False by decide, if_false,
    Derivation.map_one_eq_zero]
  ring

/-- IX.2 Ampère–Maxwell(第 1 成分):EL₁ = ∂_tE₁ − (∇×B)₁ + J¹ -/
theorem ampere : EL D A J 1 = D 0 (Ef D A 1) - (D 2 (B3 D A) - D 3 (B2 D A)) + J 1 := by
  simp only [EL, Fu, Ef, B2, B3, F, eta, Fin.sum_univ_four, map_sub, map_neg, map_mul, Derivation.leibniz,
    smul_eq_mul, Fin.isValue, if_true, show ((1:Fin 4) = 0) = False by decide,
    show ((2:Fin 4) = 0) = False by decide, show ((3:Fin 4) = 0) = False by decide, if_false,
    Derivation.map_one_eq_zero]
  ring

variable (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
include hc

/-- IX.3 ∇·B = 0(恒等式) -/
theorem bianchi_div : D 1 (B1 D A) + D 2 (B2 D A) + D 3 (B3 D A) = 0 := by
  simp only [B1, B2, B3, F, map_sub, hc 2 1, hc 3 1, hc 3 2]; ring

/-- IX.3 Faraday:(∇×E)₁ + ∂_tB₁ = 0(恒等式) -/
theorem faraday : (D 2 (Ef D A 3) - D 3 (Ef D A 2)) + D 0 (B1 D A) = 0 := by
  simp only [Ef, B1, F, map_sub, hc 2 0, hc 3 0, hc 3 2]; ring

/-- IX.3 電荷の保存:EL の式が成り立てば ∂_νJ^ν = 0 -/
theorem charge_conservation (hEL : ∀ ν, EL D A J ν = 0) : ∑ ν, D ν (J ν) = 0 := by
  have hJ : ∀ ν, J ν = -∑ μ, D μ (Fu D A μ ν) := by
    intro ν; have := hEL ν; simp only [EL] at this; linear_combination this
  simp only [hJ, map_neg, map_sum, map_zero, Fu, F, eta, Fin.sum_univ_four, map_add, map_sub, map_mul, Derivation.leibniz,
    smul_eq_mul, Fin.isValue, if_true, show ((1:Fin 4) = 0) = False by decide,
    show ((2:Fin 4) = 0) = False by decide, show ((3:Fin 4) = 0) = False by decide, if_false,
    Derivation.map_one_eq_zero, map_neg]
  simp only [hc 1 0, hc 2 0, hc 3 0, hc 2 1, hc 3 1, hc 3 2]
  ring

/-- IX.6 応力テンソル -/
def T (μ ν : Fin 4) : S :=
  ∑ α, eta α * F D A μ α * F D A ν α
    - (1/4 : S) * (if μ = ν then eta μ else 0) * ∑ ρ, ∑ σ, eta ρ * eta σ * F D A ρ σ ^ 2

/-- IX.6:Σ_μ η^μ ∂_μT_{μν} = Σ_α η^α F_{να}(Σ_μ η^μ ∂_μF_{μα})(恒等式) -/
theorem stress_divergence (ν : Fin 4) :
    ∑ μ, eta μ * D μ (T D A μ ν)
      = ∑ α, eta α * F D A ν α * ∑ μ, eta μ * D μ (F D A μ α) := by
  have h4 : ∀ μ, D μ (1/4 : S) = 0 := fun μ => d_quarter (D μ)
  rcases (show ν = 0 ∨ ν = 1 ∨ ν = 2 ∨ ν = 3 by fin_cases ν <;> simp) with h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [T, F, eta, Fin.sum_univ_four, map_add, map_sub, map_neg, map_mul,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, Fin.isValue, if_true, if_false,
    Fin.zero_eta, Fin.mk_one, Derivation.map_one_eq_zero, h4, map_zero, nsmul_eq_mul, Nat.cast_ofNat,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero] <;>
  simp only [hc 1 0, hc 2 0, hc 3 0, hc 2 1, hc 3 1, hc 3 2] <;>
  ring

end EM

/-! ### B. 塵と粒子 -/

section Mech
variable {S : Type*} [CommRing S]

/-- IX.7:∂_μ(ρu^μu^ν) = (∂_μ(ρu^μ))u^ν + ρ(u·∂)u^ν。連続の式と全体の保存から Lorentz 力 -/
theorem dust_lorentz (D : Fin 4 → Derivation ℤ S S) (ρ ρe : S) (u : Fin 4 → S) (Fmix : Fin 4 → Fin 4 → S)
    (ν : Fin 4)
    (hcont : ∑ μ, D μ (ρ * u μ) = 0)
    -- 全体の保存:∂_μ T_dust^{μν} = −∂_μ T_EM^{μν} = F^ν{}_λ J^λ、J = ρ_e u
    (hcons : ∑ μ, D μ (ρ * u μ * u ν) = ∑ k, Fmix ν k * (ρe * u k)) :
    ρ * ∑ μ, u μ * D μ (u ν) = ρe * ∑ k, Fmix ν k * u k := by
  have e : ∑ μ, D μ (ρ * u μ * u ν) = (∑ μ, D μ (ρ * u μ)) * u ν + ρ * ∑ μ, u μ * D μ (u ν) := by
    simp only [Fin.sum_univ_four, Derivation.leibniz, smul_eq_mul]; ring
  rw [e, hcont, zero_mul, zero_add] at hcons
  rw [hcons]; simp only [Fin.sum_univ_four]; ring

/-- IX.8:粒子の EL の式。世界線の導分 dτ、u^μ = dτ x^μ、場の値 A_μ と偏微分 ∂_νA_μ =: dA μ ν
  (連鎖律 dτ A_μ = Σ_ν u^ν ∂_νA_μ は入力)。L = ½m Σ η_μ(u^μ)² + qΣA_μu^μ。
  EL_μ := dτ(∂L/∂u^μ) − ∂L/∂x^μ = dτ(mη_μu^μ + qA_μ) − qΣ_ν u^ν ∂_μA_ν = mη_μ u̇^μ − qΣ_ν F_{μν}u^ν -/
theorem particle_el (dτ : Derivation ℤ S S) (m q : S) (η u : Fin 4 → S) (Aw : Fin 4 → S)
    (dA : Fin 4 → Fin 4 → S) (hm : dτ m = 0) (hq : dτ q = 0) (hη : ∀ μ, dτ (η μ) = 0)
    (hchain : ∀ μ, dτ (Aw μ) = ∑ ν, u ν * dA μ ν) (μ : Fin 4) :
    dτ (m * η μ * u μ + q * Aw μ) - q * ∑ ν, u ν * dA ν μ
      = m * η μ * dτ (u μ) - q * ∑ ν, (dA ν μ - dA μ ν) * u ν := by
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hm, hq, hη, hchain, Fin.sum_univ_four]
  ring

/-- IX.9:Hamilton の式は EL の式と同値。p_μ = mη_μu^μ + qA_μ、H = (1/2m)Ση_μ(p_μ − qA_μ)²(η_μ² = 1)。
  dx^μ/dτ = ∂H/∂p_μ = η_μ(p_μ − qA_μ)/m = u^μ、dp_μ/dτ = −∂H/∂x^μ = qΣ_ν u^ν ∂_μA_ν。
  後者は m η_μ u̇^μ = qΣ_ν(∂_μA_ν − ∂_νA_μ)u^ν と同値 -/
theorem hamilton (dτ : Derivation ℤ S S) (m q : S) (η u : Fin 4 → S) (Aw : Fin 4 → S)
    (dA : Fin 4 → Fin 4 → S) (hm : dτ m = 0) (hq : dτ q = 0) (hη : ∀ μ, dτ (η μ) = 0)
    (hchain : ∀ μ, dτ (Aw μ) = ∑ ν, u ν * dA μ ν) (μ : Fin 4) :
    (dτ (m * η μ * u μ + q * Aw μ) = q * ∑ ν, u ν * dA ν μ) ↔
      (m * η μ * dτ (u μ) = q * ∑ ν, (dA ν μ - dA μ ν) * u ν) := by
  have h := particle_el dτ m q η u Aw dA hm hq hη hchain μ
  constructor
  · intro H; rw [H, sub_self] at h; linear_combination -h
  · intro H; rw [H, sub_self] at h; linear_combination h

end Mech

/-- IX.9 質量殻:−(u⁰)² + |u|² = −1 なら、E_kin = m u⁰、p_kin = m u は E_kin² = m² + |p_kin|²、
  (m/E_kin)² + |p_kin/E_kin|² = 1(量子球面 Q の上の点、α-I.5) -/
theorem mass_shell (m u0 u1 u2 u3 : ℝ) (hm : 0 < m) (hu : 0 < u0)
    (h : -(u0 ^ 2) + u1 ^ 2 + u2 ^ 2 + u3 ^ 2 = -1) :
    (m * u0) ^ 2 = m ^ 2 + (m * u1) ^ 2 + (m * u2) ^ 2 + (m * u3) ^ 2 ∧
    (m / (m * u0)) ^ 2 + (m * u1 / (m * u0)) ^ 2 + (m * u2 / (m * u0)) ^ 2 + (m * u3 / (m * u0)) ^ 2 = 1 := by
  constructor
  · nlinarith [h]
  · have hE : m * u0 ≠ 0 := by positivity
    field_simp
    nlinarith [h]

/-- IX.5:球対称な Gauss の法則の積分形。∂_r(r²E_r) = r²ρ なら Q(b) − Q(a) = 4π∫_a^b r²ρ -/
theorem gauss_integral (E ρ : ℝ → ℝ) (a b : ℝ)
    (hE : ∀ r ∈ Set.uIcc a b, HasDerivAt (fun r => r ^ 2 * E r) (r ^ 2 * ρ r) r)
    (hρ : IntervalIntegrable (fun r => r ^ 2 * ρ r) MeasureTheory.volume a b) :
    4 * Real.pi * (b ^ 2 * E b) - 4 * Real.pi * (a ^ 2 * E a)
      = 4 * Real.pi * ∫ r in a..b, r ^ 2 * ρ r := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hE hρ]; ring

end CFT.Classical
