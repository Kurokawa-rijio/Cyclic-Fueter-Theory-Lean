import Mathlib
import FieldEquations.Gravity.CurvatureJet

/-
# The second Bianchi identity

`gauge_bianchi`: for a connection A_c with values in an arbitrary (noncommutative) ring and
F_{cd} = ∂_c A_d − ∂_d A_c + A_c A_d − A_d A_c, the covariant derivatives satisfy
D_c F_{de} + D_d F_{ec} + D_e F_{cd} = 0. `bianchi_second` is the component form for the
Riemann tensor of a connection in coordinates (index convention of `CurvatureJet.riemann`).
-/

open Finset BigOperators

namespace FieldEquations.Curvature

section Gauge

variable {ι R : Type*} [Ring R]

def curv (A : ι → R) (dA : ι → ι → R) (c d : ι) : R :=
  dA c d - dA d c + A c * A d - A d * A c

def dcurv (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R) (e c d : ι) : R :=
  ddA e c d - ddA e d c + (dA e c * A d + A c * dA e d) - (dA e d * A c + A d * dA e c)

def Dcurv (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R) (e c d : ι) : R :=
  dcurv A dA ddA e c d + (A e * curv A dA c d - curv A dA c d * A e)

/-- Second Bianchi identity in gauge form, over an arbitrary ring. -/
theorem gauge_bianchi (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R)
    (hsym : ∀ i j k, ddA i j k = ddA j i k) (e c d : ι) :
    Dcurv A dA ddA e c d + Dcurv A dA ddA c d e + Dcurv A dA ddA d e c = 0 := by
  unfold Dcurv dcurv curv
  rw [hsym e c d, hsym c d e, hsym d e c]
  noncomm_ring

end Gauge

section Components

variable {n : ℕ}

def Amat (Γ : Fin n → Fin n → Fin n → ℝ) (c : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => Γ a c b

def dAmat (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (e c : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => dΓ e a c b

def ddAmat (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (e f c : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => ddΓ e f a c b

theorem curv_apply (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (c d a b : Fin n) : curv (Amat Γ) (dAmat dΓ) c d a b = riemann Γ dΓ a b c d := by
  simp only [curv, Amat, dAmat, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.of_apply, riemann, Finset.sum_sub_distrib]
  ring

noncomputable def nablaR (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (e a b c d : Fin n) : ℝ :=
  Dcurv (Amat Γ) (dAmat dΓ) (ddAmat ddΓ) e c d a b
    - ∑ f, Γ f e c * riemann Γ dΓ a b f d - ∑ f, Γ f e d * riemann Γ dΓ a b c f

theorem nablaR_explicit (Γ : Fin n → Fin n → Fin n → ℝ)
    (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (e a b c d : Fin n) :
    nablaR Γ dΓ ddΓ e a b c d
      = (ddΓ e c a d b - ddΓ e d a c b
          + ∑ g, (dΓ e a c g * Γ g d b + Γ a c g * dΓ e g d b)
          - ∑ g, (dΓ e a d g * Γ g c b + Γ a d g * dΓ e g c b))
        + ∑ f, Γ a e f * riemann Γ dΓ f b c d - ∑ f, riemann Γ dΓ a f c d * Γ f e b
        - ∑ f, Γ f e c * riemann Γ dΓ a b f d - ∑ f, Γ f e d * riemann Γ dΓ a b c f := by
  simp only [nablaR, Dcurv, dcurv, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    curv_apply]
  simp only [Amat, dAmat, ddAmat, Matrix.of_apply, Finset.sum_add_distrib]
  ring

/-- Second Bianchi identity for the Riemann tensor in components. -/
theorem bianchi_second (Γ : Fin n → Fin n → Fin n → ℝ)
    (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdd : ∀ e f a b c, ddΓ e f a b c = ddΓ f e a b c)
    (e a b c d : Fin n) :
    nablaR Γ dΓ ddΓ e a b c d + nablaR Γ dΓ ddΓ c a b d e + nablaR Γ dΓ ddΓ d a b e c = 0 := by
  have hsym : ∀ i j k, ddAmat ddΓ i j k = ddAmat ddΓ j i k := fun i j k => by
    ext x y
    simp only [ddAmat, Matrix.of_apply]
    exact hdd i j x k y
  have hg := congrFun (congrFun
    (gauge_bianchi (Amat Γ) (dAmat dΓ) (ddAmat ddΓ) hsym e c d) a) b
  simp only [Matrix.add_apply, Matrix.zero_apply] at hg
  have hx : ∑ f, (Γ f e c * riemann Γ dΓ a b f d + Γ f e d * riemann Γ dΓ a b c f
      + Γ f c d * riemann Γ dΓ a b f e + Γ f c e * riemann Γ dΓ a b d f
      + Γ f d e * riemann Γ dΓ a b f c + Γ f d c * riemann Γ dΓ a b e f) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    rw [hΓ f c e, hΓ f d e, hΓ f d c, riemann_antisymm Γ dΓ a b d f,
      riemann_antisymm Γ dΓ a b f c, riemann_antisymm Γ dΓ a b e f]
    ring
  simp only [Finset.sum_add_distrib] at hx
  unfold nablaR
  linarith

end Components

end FieldEquations.Curvature
