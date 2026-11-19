import Mathlib.Tactic

/-
# Einstein equations from the Cartan–Palatini action (Euclidean frame)

Orthonormal frame in four dimensions, curvature R_{cdρσ} with the two antisymmetries.
ε is the Levi-Civita symbol (built from the Vandermonde product, so its antisymmetry is `ring`).
* `cartan_einstein`: Σ ε_{μνρσ} ε_{aνcd} R_{cdρσ} = −4 G_{μa}.
* The density L(e) = Σ ε ε R e e and its first variation at e = δ in a direction k:
  V(k) = −8 Σ k_{aμ} G_{μa} (`first_variation`), so stationarity in all directions ⇔ G = 0
  (`einstein_iff_stationary`), and with a source, 8 G = T (`einstein_with_matter`).
The variation is pointwise and finite dimensional (no functional derivative, no integration
by parts).
-/

namespace FieldEquations.CartanPalatini

open Finset

set_option maxHeartbeats 0

def iv (a : Fin 4) : ℝ := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 3

noncomputable def eps (a b c d : Fin 4) : ℝ :=
  (iv b - iv a) * (iv c - iv a) * (iv d - iv a) * (iv c - iv b) * (iv d - iv b)
    * (iv d - iv c) / 12

theorem eps_0123 : eps 0 1 2 3 = 1 := by
  simp (config := { decide := true }) only [eps, iv, ↓reduceIte]
  norm_num

theorem eps_swap12 (a b c d : Fin 4) : eps a b c d = -eps b a c d := by unfold eps; ring
theorem eps_swap23 (a b c d : Fin 4) : eps a b c d = -eps a c b d := by unfold eps; ring
theorem eps_swap34 (a b c d : Fin 4) : eps a b c d = -eps a b d c := by unfold eps; ring

variable (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)

def Ric (μ a : Fin 4) : ℝ := ∑ d, R μ d a d

def Rs : ℝ := ∑ μ, Ric R μ μ

noncomputable def Gt (μ a : Fin 4) : ℝ := Ric R μ a - (1/2 : ℝ) * (if μ = a then 1 else 0) * Rs R

noncomputable def E (μ a : Fin 4) : ℝ :=
  ∑ ν, ∑ ρ, ∑ σ, ∑ c, ∑ d, eps μ ν ρ σ * eps a ν c d * R c d ρ σ

/-- εεR = −4G for curvature with the two antisymmetries. -/
theorem cartan_einstein (hR1 : ∀ c d x y, R c d x y = -R d c x y)
    (hR2 : ∀ c d x y, R c d x y = -R c d y x) (μ a : Fin 4) :
    E R μ a = -4 * Gt R μ a := by
  have z1 : ∀ c x y, R c c x y = 0 := fun c x y => by linarith [hR1 c c x y]
  have z2 : ∀ c d x, R c d x x = 0 := fun c d x => by linarith [hR2 c d x x]
  fin_cases μ <;> fin_cases a <;>
  simp (config := { decide := true }) only [E, Gt, Ric, Rs, eps, iv, Fin.sum_univ_four,
    Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, z1, z2,
    hR1 1 0, hR1 2 0, hR1 3 0, hR1 2 1, hR1 3 1, hR1 3 2,
    fun c d => hR2 c d 1 0, fun c d => hR2 c d 2 0, fun c d => hR2 c d 3 0,
    fun c d => hR2 c d 2 1, fun c d => hR2 c d 3 1, fun c d => hR2 c d 3 2] <;>
  ring

noncomputable def Lb (e1 e2 : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ a, ∑ ν, ∑ b, ∑ ρ, ∑ σ, ∑ c, ∑ d,
    eps μ ν ρ σ * eps a b c d * e1 a μ * e2 b ν * R c d ρ σ

def delta (a μ : Fin 4) : ℝ := if a = μ then 1 else 0

noncomputable def V (k : Fin 4 → Fin 4 → ℝ) : ℝ := Lb R k delta + Lb R delta k

theorem quad_expansion (k : Fin 4 → Fin 4 → ℝ) (t : ℝ) :
    Lb R (fun a μ => delta a μ + t * k a μ) (fun a μ => delta a μ + t * k a μ)
      = Lb R delta delta + t * V R k + t ^ 2 * Lb R k k := by
  unfold V Lb
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem first_variation_hasDerivAt (k : Fin 4 → Fin 4 → ℝ) :
    HasDerivAt (fun t => Lb R (fun a μ => delta a μ + t * k a μ) (fun a μ => delta a μ + t * k a μ))
      (V R k) 0 := by
  have e : (fun t => Lb R (fun a μ => delta a μ + t * k a μ) (fun a μ => delta a μ + t * k a μ))
      = fun t => Lb R delta delta + t * V R k + t ^ 2 * Lb R k k :=
    funext (quad_expansion R k)
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => t * V R k) (1 * V R k) 0 := (hasDerivAt_id 0).mul_const _
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * Lb R k k) ((↑2 * 0 ^ (2 - 1) * 1) * Lb R k k) 0 :=
    ((hasDerivAt_id 0).pow 2).mul_const _
  have h := ((hasDerivAt_const (0:ℝ) (Lb R delta delta)).add h1).add h2
  convert h using 1
  simp

theorem Lb_k_delta (k : Fin 4 → Fin 4 → ℝ) :
    Lb R k delta = ∑ μ, ∑ a, k a μ * E R μ a := by
  unfold Lb E delta
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Fintype.sum_ite_eq, Fintype.sum_ite_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ =>
    Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

theorem Lb_delta_k (k : Fin 4 → Fin 4 → ℝ) :
    Lb R delta k = ∑ μ, ∑ a, k a μ * E R μ a := by
  have e1 : Lb R delta k = ∑ μ, ∑ ν, ∑ b, ∑ ρ, ∑ σ, ∑ c, ∑ d,
      eps μ ν ρ σ * eps μ b c d * k b ν * R c d ρ σ := by
    unfold Lb delta
    simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq, Fintype.sum_ite_eq']
  rw [e1]
  calc ∑ μ, ∑ ν, ∑ b, ∑ ρ, ∑ σ, ∑ c, ∑ d, eps μ ν ρ σ * eps μ b c d * k b ν * R c d ρ σ
      = ∑ ν, ∑ μ, ∑ b, ∑ ρ, ∑ σ, ∑ c, ∑ d, eps μ ν ρ σ * eps μ b c d * k b ν * R c d ρ σ :=
        Finset.sum_comm
    _ = ∑ ν, ∑ b, ∑ μ, ∑ ρ, ∑ σ, ∑ c, ∑ d, eps μ ν ρ σ * eps μ b c d * k b ν * R c d ρ σ :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_comm
    _ = ∑ ν, ∑ b, k b ν * E R ν b := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => ?_
        unfold E
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun d _ => ?_
        rw [eps_swap12 μ ν ρ σ, eps_swap12 μ b c d]
        ring

/-- First variation of the Cartan–Palatini density at e = δ. -/
theorem first_variation (hR1 : ∀ c d x y, R c d x y = -R d c x y)
    (hR2 : ∀ c d x y, R c d x y = -R c d y x) (k : Fin 4 → Fin 4 → ℝ) :
    V R k = -8 * ∑ μ, ∑ a, k a μ * Gt R μ a := by
  unfold V
  rw [Lb_k_delta, Lb_delta_k]
  simp only [cartan_einstein R hR1 hR2, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem pick (F : Fin 4 → Fin 4 → ℝ) (μ a : Fin 4) :
    ∑ μ', ∑ a', ((if a' = a then 1 else 0) * (if μ' = μ then 1 else 0)) * F μ' a' = F μ a := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Fintype.sum_ite_eq, Fintype.sum_ite_eq']

/-- Stationarity ⇔ G = 0. -/
theorem einstein_iff_stationary (hR1 : ∀ c d x y, R c d x y = -R d c x y)
    (hR2 : ∀ c d x y, R c d x y = -R c d y x) :
    (∀ k, V R k = 0) ↔ ∀ μ a, Gt R μ a = 0 := by
  constructor
  · intro h μ a
    have hk := h (fun b ν => (if b = a then 1 else 0) * (if ν = μ then 1 else 0))
    rw [first_variation R hR1 hR2, pick] at hk
    linarith
  · intro h k
    rw [first_variation R hR1 hR2]
    simp [h]

theorem einstein_with_matter (hR1 : ∀ c d x y, R c d x y = -R d c x y)
    (hR2 : ∀ c d x y, R c d x y = -R c d y x) (T : Fin 4 → Fin 4 → ℝ) :
    (∀ k, V R k + ∑ μ, ∑ a, k a μ * T μ a = 0) ↔ ∀ μ a, 8 * Gt R μ a = T μ a := by
  constructor
  · intro h μ a
    have hk := h (fun b ν => (if b = a then 1 else 0) * (if ν = μ then 1 else 0))
    rw [first_variation R hR1 hR2, pick, pick] at hk
    linarith
  · intro h k
    rw [first_variation R hR1 hR2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← h μ a]
    ring

end FieldEquations.CartanPalatini
