/-
  段階 3(静電場)と段階 5(連続体)の有名方程式(2026-11-18)

  可換な導分 ∂₀, …, ∂₃(∂₀ = ∂_t)の上の代数で述べる。空間の和は Σ_j = j = 1, 2, 3。
  * `navier_stokes`:連続の式 ∂_tρ + ∂_j(ρu_j) = 0、非圧縮 ∂_ju_j = 0、運動量の保存形
      ∂_t(ρu_i) + ∂_j(ρu_iu_j − μ(∂_ju_i + ∂_iu_j)) + ∂_ip = 0(μ は定数)
    から Navier–Stokes 方程式 ρ(∂_tu_i + u_j∂_ju_i) = −∂_ip + μΔu_i。
  * `bernoulli`:定常・非粘性・非圧縮(ρ は定数)・渦なし(∂_iu_j = ∂_ju_i、j = 1, 2, 3)の Euler 方程式
      ρ u_j∂_ju_i = −∂_ip − ρ∂_iΦ から ∂_i(½|u|² + p/ρ + Φ) = 0(Bernoulli の定理)。
  * `navier_cauchy`:等方弾性体 σ_ij = λδ_ij θ + μ(∂_iu_j + ∂_ju_i)(θ = ∂_ku_k)について
      ∂_jσ_ij = (λ + μ)∂_iθ + μΔu_i(Navier–Cauchy 方程式の左辺)。
  * `sound_wave`:線形音響(ρ₀、c² は定数)∂_tρ₁ + ρ₀∂_ju_j = 0、ρ₀∂_tu_i = −c²∂_iρ₁ から
      ∂_t²ρ₁ = c²Δρ₁(音波の波動方程式)。
  * `coulomb_harmonic`:r = |x|、ri = 1/r(∂_i ri = −x_i ri³、|x|² ri² = 1)について Δ(q/r) = 0(r ≠ 0)。
    `coulomb_field`:E_i = −∂_i(q/r) = q x_i/r³(Coulomb の法則)。
    注意(独立点検 2026-11-18):`coulomb_harmonic` の仮定 `hx`(∂_j x_j = 1)と `hri`(∂_j ri = −x_j ri³)は
    時間の添字 j = 0 も含む Fin 4 全体で置いている。静的なポテンシャル(∂₀ ri = 0)では、`hri` の j = 0 から
    x₀ ri³ = 0、つまり x₀ = 0 が出て、`hx` の j = 0(∂₀ x₀ = 1)と矛盾する。したがってこの定理は、∂₀ = ∂_t の
    ふつうの静的モデルには当てはめられない(証明が使うのは j = 1, 2, 3 だけなので、仮定を j ≠ 0 に制限すれば直る)。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace CFT.Continuum

variable {S : Type*} [Field S] [CharZero S]
variable (D : Fin 4 → Derivation ℤ S S)

/-- 空間の和 Σ_{j=1}^{3} -/
def ssum (f : Fin 4 → S) : S := f 1 + f 2 + f 3

theorem d_half' (d : Derivation ℤ S S) : d (1/2 : S) = 0 := by
  have h := map_nsmul d 2 (1/2 : S)
  rw [nsmul_eq_mul, nsmul_eq_mul, show ((2:ℕ):S) * (1/2) = 1 by norm_num,
    Derivation.map_one_eq_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- Navier–Stokes 方程式 -/
theorem navier_stokes (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (ρ p μ : S) (u : Fin 4 → S)
    (hμ : ∀ j, D j μ = 0)
    (hcont : D 0 ρ + ssum (fun j => D j (ρ * u j)) = 0)
    (hdiv : ssum (fun j => D j (u j)) = 0) (i : Fin 4)
    (hmom : D 0 (ρ * u i) + ssum (fun j => D j (ρ * u i * u j - μ * (D j (u i) + D i (u j))))
      + D i p = 0) :
    ρ * (D 0 (u i) + ssum (fun j => u j * D j (u i)))
      = -(D i p) + μ * ssum (fun j => D j (D j (u i))) := by
  have hdiv' := congrArg (D i) hdiv
  unfold ssum at hcont hdiv' hmom ⊢
  simp only [map_add, map_sub, map_zero, Derivation.leibniz, smul_eq_mul, hμ, mul_zero,
    add_zero] at hcont hdiv' hmom ⊢
  rw [hc 1 i, hc 2 i, hc 3 i] at hmom
  linear_combination hmom - u i * hcont + μ * hdiv'

/-- Bernoulli の定理 -/
theorem bernoulli (ρ p Φ : S) (u : Fin 4 → S) (i : Fin 4) (hρ : ρ ≠ 0) (hρc : D i ρ = 0)
    (hirr1 : D i (u 1) = D 1 (u i)) (hirr2 : D i (u 2) = D 2 (u i))
    (hirr3 : D i (u 3) = D 3 (u i))
    (heuler : ρ * ssum (fun j => u j * D j (u i)) = -(D i p) - ρ * D i Φ) :
    D i ((1/2 : S) * ssum (fun j => u j * u j) + p * ρ⁻¹ + Φ) = 0 := by
  have hinv : D i ρ⁻¹ = 0 := by
    have e := congrArg (D i) (mul_inv_cancel₀ hρ)
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul, hρc,
      mul_zero, add_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hρ
  have hρi : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ
  unfold ssum at heuler ⊢
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hinv, d_half' (D i), mul_zero, add_zero]
  rw [hirr1, hirr2, hirr3]
  linear_combination ρ⁻¹ * heuler
    - (u 1 * D 1 (u i) + u 2 * D 2 (u i) + u 3 * D 3 (u i) + D i Φ) * hρi

/-- Navier–Cauchy:等方弾性体の応力の発散 -/
theorem navier_cauchy (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (lam mu : S) (u : Fin 4 → S)
    (hl : ∀ j, D j lam = 0) (hm : ∀ j, D j mu = 0) (i : Fin 4) :
    D i (lam * ssum (fun k => D k (u k))) + ssum (fun j => D j (mu * (D i (u j) + D j (u i))))
      = (lam + mu) * D i (ssum (fun k => D k (u k))) + mu * ssum (fun j => D j (D j (u i))) := by
  unfold ssum
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hl, hm, mul_zero, add_zero]
  rw [hc 1 i, hc 2 i, hc 3 i]
  ring

/-- 音波の波動方程式 -/
theorem sound_wave (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (ρ1 ρ0 c2 : S) (u : Fin 4 → S)
    (h0 : ∀ j, D j ρ0 = 0) (h2 : ∀ j, D j c2 = 0)
    (hcont : D 0 ρ1 + ρ0 * ssum (fun j => D j (u j)) = 0)
    (hmom : ∀ i, ρ0 * D 0 (u i) = -(c2 * D i ρ1)) :
    D 0 (D 0 ρ1) = c2 * ssum (fun j => D j (D j ρ1)) := by
  have e0 := congrArg (D 0) hcont
  have e1 := congrArg (D 1) (hmom 1)
  have e2 := congrArg (D 2) (hmom 2)
  have e3 := congrArg (D 3) (hmom 3)
  unfold ssum at e0 ⊢
  simp only [map_add, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, h0, h2, mul_zero,
    add_zero] at e0 e1 e2 e3
  rw [hc 0 1, hc 0 2, hc 0 3] at e0
  linear_combination e0 - e1 - e2 - e3

/-- Coulomb ポテンシャル q/r は r ≠ 0 で調和 -/
theorem coulomb_harmonic (q ri : S) (x : Fin 4 → S) (hq : ∀ j, D j q = 0)
    (hx : ∀ j, D j (x j) = 1) (hri : ∀ j, D j ri = -(x j * (ri * ri * ri)))
    (hnorm : (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * ri ^ 2 = 1) :
    ssum (fun j => D j (D j (q * ri))) = 0 := by
  unfold ssum
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hq, hx, hri, mul_zero, add_zero]
  linear_combination (3 * q * ri ^ 3) * hnorm

/-- Coulomb の法則 E_i = −∂_i(q/r) = q x_i / r³ -/
theorem coulomb_field (q ri : S) (x : Fin 4 → S) (hq : ∀ j, D j q = 0)
    (hri : ∀ j, D j ri = -(x j * (ri * ri * ri))) (j : Fin 4) :
    -(D j (q * ri)) = q * x j * (ri * ri * ri) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hq, hri]
  ring

end CFT.Continuum
