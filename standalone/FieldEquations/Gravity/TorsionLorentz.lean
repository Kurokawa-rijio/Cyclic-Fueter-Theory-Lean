import FieldEquations.Gravity.CartanPalatini
import FieldEquations.Gravity.BianchiSecond

/-
# Torsion, Lorentz signature and gauge covariance of the curvature

* `Ktor` is the Euler–Lagrange expression of the Cartan–Palatini action with respect to the
  connection, in its standard form after integration by parts, at e = δ (integration by parts
  itself is not formalized). `torsion_contraction`: K = 2(T − δ tr T + δ tr T), hence K = 0 ⇒
  T = 0 (`torsion_free_of_stationary`). `levi_civita_unique`: the Koszul formula.
* η = diag(−1,1,1,1): raising all four indices of ε gives −ε (`eps_raise`); for
  R̃ = ηηR the εεR identity becomes 4ηG^L (`cartan_einstein_lorentz`) and stationarity,
  expressed as V(R̃) = 0, is equivalent to G^L = 0 (`einstein_lorentz_iff`).
* `curv_gauge_covariant`: for A' = g⁻¹ A g + g⁻¹ ∂g in an arbitrary ring (with g g⁻¹ = 1 and
  ∂∂g symmetric, ∂g⁻¹ entered as −g⁻¹(∂g)g⁻¹), F(A') = g⁻¹ F(A) g.
-/

namespace FieldEquations.CartanPalatini

open Finset

set_option maxHeartbeats 0

noncomputable def Ktor (T : Fin 4 → Fin 4 → Fin 4 → ℝ) (μ c d : Fin 4) : ℝ :=
  ∑ a, ∑ ν, ∑ ρ, ∑ b, eps μ ν ρ b * eps a b c d * T a ν ρ

def ttr (T : Fin 4 → Fin 4 → Fin 4 → ℝ) (d : Fin 4) : ℝ := ∑ a, T a a d

theorem torsion_contraction (T : Fin 4 → Fin 4 → Fin 4 → ℝ) (hT : ∀ a x y, T a x y = -T a y x)
    (μ c d : Fin 4) :
    Ktor T μ c d = 2 * (T μ c d - (if μ = c then ttr T d else 0) + (if μ = d then ttr T c else 0)) := by
  have z : ∀ a x, T a x x = 0 := fun a x => by linarith [hT a x x]
  fin_cases μ <;> fin_cases c <;> fin_cases d <;>
  simp (config := { decide := true }) only [Ktor, ttr, eps, iv, Fin.sum_univ_four, Fin.isValue,
    ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, z,
    fun a => hT a 1 0, fun a => hT a 2 0, fun a => hT a 3 0, fun a => hT a 2 1,
    fun a => hT a 3 1, fun a => hT a 3 2] <;>
  ring

/-- Vanishing of the connection variation forces zero torsion. -/
theorem torsion_free_of_stationary (T : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hT : ∀ a x y, T a x y = -T a y x) (hK : ∀ μ c d, Ktor T μ c d = 0) :
    ∀ a x y, T a x y = 0 := by
  have h1 : ∀ μ c d, T μ c d = (if μ = c then ttr T d else 0) - (if μ = d then ttr T c else 0) :=
    fun μ c d => by
      have := torsion_contraction T hT μ c d
      rw [hK] at this
      linarith
  have ht : ∀ d, ttr T d = 0 := by
    intro d
    have e : ttr T d = ∑ c, ((if c = c then ttr T d else 0) - (if c = d then ttr T c else 0)) := by
      unfold ttr
      exact Finset.sum_congr rfl fun c _ => h1 c c d
    simp only [eq_self_iff_true, if_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Fintype.sum_ite_eq', nsmul_eq_mul] at e
    push_cast at e
    linarith
  intro a x y
  rw [h1, ht, ht]
  simp

theorem levi_civita_unique {ι : Type*} (w C : ι → ι → ι → ℝ)
    (hanti : ∀ a b c, w a b c = -w b a c) (htf : ∀ a b c, w a b c - w a c b = C a b c)
    (a b c : ι) : w a b c = (1/2 : ℝ) * (C b c a - C c a b + C a b c) := by
  linear_combination (1/2 : ℝ) * htf b c a - (1/2 : ℝ) * htf c a b + (1/2 : ℝ) * htf a b c
    + (1/2 : ℝ) * hanti b a c - (1/2 : ℝ) * hanti c b a + (1/2 : ℝ) * hanti a c b

def etaL (μ : Fin 4) : ℝ := if μ = 0 then -1 else 1

theorem etaL_sq (μ : Fin 4) : etaL μ * etaL μ = 1 := by
  unfold etaL; split_ifs <;> norm_num

theorem eps_raise (μ ν ρ σ : Fin 4) :
    etaL μ * etaL ν * etaL ρ * etaL σ * eps μ ν ρ σ = -eps μ ν ρ σ := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;>
  simp (config := { decide := true }) only [etaL, eps, iv, Fin.isValue, ↓reduceIte,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
  norm_num

variable (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)

def Rt (c d ρ σ : Fin 4) : ℝ := etaL c * etaL d * R c d ρ σ

def RicL (μ a : Fin 4) : ℝ := ∑ d, etaL d * R μ d a d

def RsL : ℝ := ∑ μ, etaL μ * RicL R μ μ

noncomputable def GLor (μ a : Fin 4) : ℝ :=
  RicL R μ a - (1/2 : ℝ) * (if μ = a then etaL μ else 0) * RsL R

noncomputable def EL (μ a : Fin 4) : ℝ :=
  ∑ ν, ∑ ρ, ∑ σ, ∑ c, ∑ d,
    (etaL μ * etaL ν * etaL ρ * etaL σ * eps μ ν ρ σ) * eps a ν c d * Rt R c d ρ σ

theorem Gt_Rt (μ a : Fin 4) : Gt (Rt R) μ a = etaL μ * GLor R μ a := by
  have hRic : ∀ x y, Ric (Rt R) x y = etaL x * RicL R x y := fun x y => by
    unfold Ric RicL Rt
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hRs : Rs (Rt R) = RsL R := by
    unfold Rs RsL
    exact Finset.sum_congr rfl fun x _ => hRic x x
  unfold Gt GLor
  rw [hRic, hRs]
  split_ifs with h
  · subst h
    have := etaL_sq μ
    linear_combination ((1/2 : ℝ) * RsL R) * this
  · ring

theorem cartan_einstein_lorentz (hR1 : ∀ c d x y, R c d x y = -R d c x y)
    (hR2 : ∀ c d x y, R c d x y = -R c d y x) (μ a : Fin 4) :
    EL R μ a = 4 * etaL μ * GLor R μ a := by
  have h1 : ∀ c d x y, Rt R c d x y = -Rt R d c x y := fun c d x y => by
    unfold Rt; rw [hR1 c d x y]; ring
  have h2 : ∀ c d x y, Rt R c d x y = -Rt R c d y x := fun c d x y => by
    unfold Rt; rw [hR2 c d x y]; ring
  have e : EL R μ a = -E (Rt R) μ a := by
    unfold EL E
    simp only [eps_raise, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  rw [e, cartan_einstein (Rt R) h1 h2, Gt_Rt]
  ring

/-- Lorentzian stationarity (as V(R̃) = 0) ⇔ G^L = 0. -/
theorem einstein_lorentz_iff (hR1 : ∀ c d x y, R c d x y = -R d c x y)
    (hR2 : ∀ c d x y, R c d x y = -R c d y x) :
    (∀ k, V (Rt R) k = 0) ↔ ∀ μ a, GLor R μ a = 0 := by
  have h1 : ∀ c d x y, Rt R c d x y = -Rt R d c x y := fun c d x y => by
    unfold Rt; rw [hR1 c d x y]; ring
  have h2 : ∀ c d x y, Rt R c d x y = -Rt R c d y x := fun c d x y => by
    unfold Rt; rw [hR2 c d x y]; ring
  rw [einstein_iff_stationary (Rt R) h1 h2]
  constructor
  · intro h μ a
    have := h μ a
    rw [Gt_Rt] at this
    have hs := etaL_sq μ
    have hne : etaL μ ≠ 0 := fun h0 => by rw [h0] at hs; norm_num at hs
    exact (mul_eq_zero.mp this).resolve_left hne
  · intro h μ a
    rw [Gt_Rt, h, mul_zero]

end FieldEquations.CartanPalatini

namespace FieldEquations.Curvature

variable {ι R : Type*} [Ring R]

def Aprime (A : ι → R) (g gi : R) (dg : ι → R) (c : ι) : R := gi * A c * g + gi * dg c

def dAprime (A : ι → R) (dA : ι → ι → R) (g gi : R) (dg : ι → R) (ddg : ι → ι → R)
    (c d : ι) : R :=
  -(gi * dg c * gi) * A d * g + gi * dA c d * g + gi * A d * dg c
    + -(gi * dg c * gi) * dg d + gi * ddg c d

/-- Gauge covariance of the curvature. -/
theorem curv_gauge_covariant (A : ι → R) (dA : ι → ι → R) (g gi : R) (dg : ι → R)
    (ddg : ι → ι → R) (hg : g * gi = 1) (hsym : ∀ c d, ddg c d = ddg d c) (c d : ι) :
    curv (Aprime A g gi dg) (dAprime A dA g gi dg ddg) c d = gi * curv A dA c d * g := by
  have hAA : ∀ x y, Aprime A g gi dg x * Aprime A g gi dg y
      = gi * A x * A y * g + gi * A x * dg y + gi * dg x * gi * A y * g
        + gi * dg x * gi * dg y := fun x y => by
    unfold Aprime
    calc (gi * A x * g + gi * dg x) * (gi * A y * g + gi * dg y)
        = gi * A x * (g * gi) * A y * g + gi * A x * (g * gi) * dg y
          + gi * dg x * gi * A y * g + gi * dg x * gi * dg y := by noncomm_ring
      _ = _ := by rw [hg]; noncomm_ring
  unfold curv
  rw [hAA c d, hAA d c]
  unfold dAprime
  rw [hsym d c]
  noncomm_ring

end FieldEquations.Curvature
