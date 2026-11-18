/-
  段階 6(一般相対論)その 1:線形化重力、重力波、Newton 極限(2026-11-18)

  4-2・4-5・IX(MaxwellFromAction)と同じ導分代数の流儀:可換な導分 ∂₀, …, ∂₃(∂₀ = ∂_t)、
  η = diag(−1, 1, 1, 1)、g = η + h(h_μν は下付き、対称)。添字の上げ下げは η(η^μμ = η_μμ = ±1)。
    h = η^μν h_μν、 □ = η^ρσ ∂_ρ∂_σ、 (∂·h)_ν = η^ρσ ∂_ρ h_σν、
    R_μν = ½(∂_μ(∂·h)_ν + ∂_ν(∂·h)_μ − □h_μν − ∂_μ∂_ν h)(線形化した Ricci)、
    G_μν = R_μν − ½ η_μν R。
  * `ric_gauge`:ゲージ変換 h → h + ∂_μξ_ν + ∂_νξ_μ で R_μν は変わらない(線形化した微分同相不変性)。
  * `lin_bianchi`:∂^μ G_μν = 0(線形化した縮約 Bianchi 恒等式)。系 `matter_conservation`:
    G_μν = κ T_μν なら ∂^μ T_μν = 0(物質の保存則が Einstein 方程式から出る)。
  * `G_harmonic`:h̄ = h − ½ η h とおくと
      G_μν = ½(∂_μ L_ν + ∂_ν L_μ) − ½ η_μν ∂^ρ L_ρ − ½ □h̄_μν(L_ν = ∂^ρ h̄_ρν)。
    系 `G_lorenz_gauge`:Lorenz(調和)ゲージ ∂^ρ h̄_ρν = 0 では G_μν = −½ □h̄_μν、
    `gw_vacuum`:Lorenz ゲージで □h̄ = 0(重力波)なら真空の Einstein 方程式 G = 0。
  * Newton 極限:静的な場 h_00 = −2Φ、h_ij = −2Φ δ_ij、h_0i = 0(∂₀Φ = 0)について
    `newton_G00`:G_00 = 2ΔΦ。系 `newton_poisson`:G_00 = 8πG_N ρ なら ΔΦ = 4πG_N ρ(Poisson 方程式)。
    `newton_christoffel`:線形化した Christoffel 記号 Γ^i_00 = ∂_iΦ(測地線の式 ẍ^i = −Γ^i_00 が Newton の運動方程式)。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace CFT.LinGrav

set_option maxHeartbeats 0

open Finset

variable {S : Type*} [Field S] [CharZero S]
variable (D : Fin 4 → Derivation ℤ S S)

/-- η = diag(−1, 1, 1, 1) の対角成分 -/
def eta (μ : Fin 4) : S := if μ = 0 then -1 else 1

/-- η_μν -/
def etaM (μ ν : Fin 4) : S := if μ = ν then eta μ else 0

theorem d_half (d : Derivation ℤ S S) : d (1/2 : S) = 0 := by
  have h := map_nsmul d 2 (1/2 : S)
  rw [nsmul_eq_mul, nsmul_eq_mul, show ((2:ℕ):S) * (1/2) = 1 by norm_num,
    Derivation.map_one_eq_zero] at h
  have h2 : ((2:ℕ):S) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h.symm).resolve_left h2

variable (h : Fin 4 → Fin 4 → S)

/-- トレース h = η^μν h_μν -/
def tr : S := ∑ μ, eta μ * h μ μ

/-- □f = η^ρσ ∂_ρ∂_σ f -/
def box (f : S) : S := ∑ ρ, eta ρ * D ρ (D ρ f)

/-- 発散 (∂·h)_ν = η^ρσ ∂_ρ h_σν -/
def dv (ν : Fin 4) : S := ∑ ρ, eta ρ * D ρ (h ρ ν)

/-- 線形化した Ricci テンソル -/
def Ric (μ ν : Fin 4) : S :=
  (1/2 : S) * (D μ (dv D h ν) + D ν (dv D h μ) - box D (h μ ν) - D μ (D ν (tr h)))

/-- スカラー曲率 -/
def Rs : S := ∑ μ, eta μ * Ric D h μ μ

/-- 線形化した Einstein テンソル -/
def Gt (μ ν : Fin 4) : S := Ric D h μ ν - (1/2 : S) * etaM μ ν * Rs D h

/-- トレースを反転した摂動 h̄ = h − ½ η h -/
def hbar (μ ν : Fin 4) : S := h μ ν - (1/2 : S) * etaM μ ν * tr h

/-- ゲージ不変性:R_μν(∂ξ + ∂ξ) = 0 -/
theorem ric_gauge (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (ξ : Fin 4 → S) (μ ν : Fin 4) :
    Ric D (fun a b => D a (ξ b) + D b (ξ a)) μ ν = 0 := by
  fin_cases μ <;> fin_cases ν <;>
  simp (config := { decide := true }) only [Ric, dv, box, tr, eta, map_add, map_sub, map_sum,
    map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, Fin.sum_univ_four,
    Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, mul_zero, add_zero,
    neg_zero, hc 1 0, hc 2 0, hc 3 0, hc 2 1, hc 3 1, hc 3 2] <;>
  ring

/-- 線形化した縮約 Bianchi 恒等式 ∂^μ G_μν = 0 -/
theorem lin_bianchi (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (hs : ∀ μ ν, h μ ν = h ν μ)
    (ν : Fin 4) : ∑ μ, eta μ * D μ (Gt D h μ ν) = 0 := by
  have h12 : ∀ μ, D μ (1/2 : S) = 0 := fun μ => d_half (D μ)
  fin_cases ν <;>
  simp (config := { decide := true }) only [Gt, Rs, Ric, dv, box, tr, etaM, eta, map_add, map_sub,
    map_sum, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero,
    Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, h12, hc 1 0, hc 2 0, hc 3 0,
    hc 2 1, hc 3 1, hc 3 2, hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2] <;>
  ring

/-- 物質の保存則:G_μν = κ T_μν(κ は定数)なら ∂^μ T_μν = 0 -/
theorem matter_conservation (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (hs : ∀ μ ν, h μ ν = h ν μ) (T : Fin 4 → Fin 4 → S) (κ : S) (hκ : κ ≠ 0)
    (hκc : ∀ μ, D μ κ = 0) (hE : ∀ μ ν, Gt D h μ ν = κ * T μ ν) (ν : Fin 4) :
    ∑ μ, eta μ * D μ (T μ ν) = 0 := by
  have hb := lin_bianchi D h hc hs ν
  simp only [hE, Derivation.leibniz, smul_eq_mul, hκc, mul_zero, add_zero] at hb
  have hk : κ * ∑ μ, eta μ * D μ (T μ ν) = 0 := by
    calc κ * ∑ μ, eta μ * D μ (T μ ν) = ∑ μ, eta μ * (κ * D μ (T μ ν)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun μ _ => by ring)
      _ = 0 := hb
  exact (mul_eq_zero.mp hk).resolve_left hκ

/-- L_ν = ∂^ρ h̄_ρν -/
def Lg (ν : Fin 4) : S := ∑ ρ, eta ρ * D ρ (hbar h ρ ν)

/-- G_μν を h̄ と L で書く恒等式 -/
theorem G_harmonic (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (μ ν : Fin 4) :
    Gt D h μ ν = (1/2 : S) * (D μ (Lg D h ν) + D ν (Lg D h μ))
      - (1/2 : S) * etaM μ ν * (∑ ρ, eta ρ * D ρ (Lg D h ρ)) - (1/2 : S) * box D (hbar h μ ν) := by
  have h12 : ∀ μ, D μ (1/2 : S) = 0 := fun μ => d_half (D μ)
  fin_cases μ <;> fin_cases ν <;>
  simp (config := { decide := true }) only [Gt, Rs, Ric, dv, box, tr, Lg, hbar, etaM, eta,
    map_add, map_sub, map_sum, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero,
    Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, h12, hc 1 0, hc 2 0, hc 3 0,
    hc 2 1, hc 3 1, hc 3 2] <;>
  ring

/-- Lorenz(調和)ゲージでは G_μν = −½ □h̄_μν -/
theorem G_lorenz_gauge (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (hL : ∀ ν, Lg D h ν = 0) (μ ν : Fin 4) :
    Gt D h μ ν = -((1/2 : S) * box D (hbar h μ ν)) := by
  rw [G_harmonic D h hc μ ν]
  simp only [hL, map_zero, add_zero, mul_zero, Finset.sum_const_zero, sub_zero, zero_sub]

/-- 重力波:Lorenz ゲージで □h̄ = 0 なら真空の Einstein 方程式 G = 0 -/
theorem gw_vacuum (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (hL : ∀ ν, Lg D h ν = 0) (hbox : ∀ μ ν, box D (hbar h μ ν) = 0) (μ ν : Fin 4) :
    Gt D h μ ν = 0 := by
  rw [G_lorenz_gauge D h hc hL μ ν, hbox, mul_zero, neg_zero]

/-! ### Newton 極限 -/

/-- 静的な弱い場:h_00 = −2Φ、h_ij = −2Φ δ_ij、h_0i = 0 -/
def hN (Φ : S) : Fin 4 → Fin 4 → S := fun μ ν => if μ = ν then -(Φ + Φ) else 0

/-- 空間の Laplacian ΔΦ -/
def lap (Φ : S) : S := D 1 (D 1 Φ) + D 2 (D 2 Φ) + D 3 (D 3 Φ)

theorem newton_G00 (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (Φ : S) (hst : D 0 Φ = 0) :
    Gt D (hN Φ) 0 0 = 2 * lap D Φ := by
  have h12 : ∀ μ, D μ (1/2 : S) = 0 := fun μ => d_half (D μ)
  have hst' : ∀ i, D 0 (D i Φ) = 0 := fun i => by rw [hc 0 i, hst, map_zero]
  simp (config := { decide := true }) only [Gt, Rs, Ric, dv, box, tr, hN, lap, etaM, eta,
    map_add, map_sub, map_sum, map_neg, map_zero, hst, hst' 1, hst' 2, hst' 3, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero,
    Fin.sum_univ_four, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, h12, hc 1 0, hc 2 0, hc 3 0,
    hc 2 1, hc 3 1, hc 3 2]
  ring

/-- Poisson 方程式:G_00 = 8k ρ(k = πG_N)なら ΔΦ = 4k ρ -/
theorem newton_poisson (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (Φ ρ k : S)
    (hst : D 0 Φ = 0) (hE : Gt D (hN Φ) 0 0 = 8 * k * ρ) : lap D Φ = 4 * k * ρ := by
  rw [newton_G00 D hc Φ hst] at hE
  linear_combination (1/2 : S) * hE

/-- 線形化した Christoffel 記号 Γ^λ_μν = ½ η^λλ (∂_μ h_λν + ∂_ν h_λμ − ∂_λ h_μν) -/
def Γlin (lam μ ν : Fin 4) : S :=
  (1/2 : S) * eta lam * (D μ (h lam ν) + D ν (h lam μ) - D lam (h μ ν))

/-- 静的な弱い場では Γ^i_00 = ∂_iΦ(測地線の式 ẍ^i = −Γ^i_00 は Newton の ẍ = −∇Φ) -/
theorem newton_christoffel (Φ : S) (i : Fin 4) (hi : i ≠ 0) :
    Γlin D (hN Φ) i 0 0 = D i Φ := by
  fin_cases i
  · exact absurd rfl hi
  all_goals
    simp (config := { decide := true }) only [Γlin, hN, eta, map_add, map_neg, map_zero,
      Fin.isValue, ↓reduceIte, Fin.mk_one, Fin.reduceFinMk]
    ring

end CFT.LinGrav
