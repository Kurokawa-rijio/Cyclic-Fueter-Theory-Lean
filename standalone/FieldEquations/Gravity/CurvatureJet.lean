import Mathlib.Tactic

/-
# Curvature from connection and metric jets at a point

`riemann`: R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb}, built from the
values of a connection and its first derivatives at a point; antisymmetry in (c,d) and the
first Bianchi identity for torsion-free connections (`bianchi_first`).
`MetricJet` holds an inverse metric, metric derivatives and second derivatives at a point
(it does not hold the metric itself and does not impose g g⁻¹ = 1 or ∂g⁻¹ = −g⁻¹(∂g)g⁻¹);
Christoffel symbols and their derivatives are built from it, and the resulting curvature
satisfies the first Bianchi identity (`bianchi_first_metric`).
-/

open Finset BigOperators

namespace FieldEquations.Curvature

variable {n : ℕ}

section General

variable {R : Type*} [CommRing R]

/-- Riemann tensor R^a_{bcd} from connection values and first derivatives at a point. -/
def riemann (Γ : Fin n → Fin n → Fin n → R) (dΓ : Fin n → Fin n → Fin n → Fin n → R)
    (a b c d : Fin n) : R :=
  dΓ c a d b - dΓ d a c b + ∑ e, (Γ a c e * Γ e d b - Γ a d e * Γ e c b)

theorem riemann_antisymm (Γ : Fin n → Fin n → Fin n → R)
    (dΓ : Fin n → Fin n → Fin n → Fin n → R) (a b c d : Fin n) :
    riemann Γ dΓ a b c d = -riemann Γ dΓ a b d c := by
  simp only [riemann, Finset.sum_sub_distrib]
  ring

/-- First Bianchi identity for a torsion-free connection. -/
theorem bianchi_first (Γ : Fin n → Fin n → Fin n → R)
    (dΓ : Fin n → Fin n → Fin n → Fin n → R)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ c a b d, dΓ c a b d = dΓ c a d b)
    (a b c d : Fin n) :
    riemann Γ dΓ a b c d + riemann Γ dΓ a c d b + riemann Γ dΓ a d b c = 0 := by
  have s : ∀ x y z w : Fin n,
      ∑ e, Γ x y e * Γ e z w = ∑ e, Γ x y e * Γ e w z :=
    fun x y z w => Finset.sum_congr rfl (fun e _ => by rw [hΓ e z w])
  simp only [riemann, Finset.sum_sub_distrib]
  rw [hdΓ d a b c, hdΓ b a c d, hdΓ c a b d, s a d c b, s a b d c, s a c b d]
  ring

end General

section Metric

structure MetricJet (n : ℕ) where
  ginv : Fin n → Fin n → ℝ
  dginv : Fin n → Fin n → Fin n → ℝ
  dg : Fin n → Fin n → Fin n → ℝ
  ddg : Fin n → Fin n → Fin n → Fin n → ℝ
  dg_symm : ∀ c a b, dg c a b = dg c b a
  ddg_symm : ∀ e c a b, ddg e c a b = ddg e c b a

namespace MetricJet

variable (J : MetricJet n)

noncomputable def chr1 (a b c : Fin n) : ℝ := (J.dg b a c + J.dg c a b - J.dg a b c) / 2

noncomputable def dchr1 (e a b c : Fin n) : ℝ := (J.ddg e b a c + J.ddg e c a b - J.ddg e a b c) / 2

noncomputable def chr2 (a b c : Fin n) : ℝ := ∑ d, J.ginv a d * J.chr1 d b c

noncomputable def dchr2 (e a b c : Fin n) : ℝ :=
  ∑ d, (J.dginv e a d * J.chr1 d b c + J.ginv a d * J.dchr1 e d b c)

theorem chr1_symm (a b c : Fin n) : J.chr1 a b c = J.chr1 a c b := by
  unfold chr1
  rw [J.dg_symm a b c]
  ring

theorem metric_compat (a b c : Fin n) : J.dg c a b = J.chr1 a b c + J.chr1 b a c := by
  unfold chr1
  rw [J.dg_symm c b a]
  ring

theorem dchr1_symm (e a b c : Fin n) : J.dchr1 e a b c = J.dchr1 e a c b := by
  unfold dchr1
  rw [J.ddg_symm e a b c]
  ring

theorem chr2_symm (a b c : Fin n) : J.chr2 a b c = J.chr2 a c b := by
  unfold chr2
  exact Finset.sum_congr rfl (fun d _ => by rw [J.chr1_symm d b c])

theorem dchr2_symm (e a b c : Fin n) : J.dchr2 e a b c = J.dchr2 e a c b := by
  unfold dchr2
  exact Finset.sum_congr rfl (fun d _ => by rw [J.chr1_symm d b c, J.dchr1_symm e d b c])

noncomputable def riem (a b c d : Fin n) : ℝ := riemann J.chr2 J.dchr2 a b c d

/-- First Bianchi identity for the curvature built from metric jets. -/
theorem bianchi_first_metric (a b c d : Fin n) :
    J.riem a b c d + J.riem a c d b + J.riem a d b c = 0 :=
  bianchi_first J.chr2 J.dchr2 J.chr2_symm J.dchr2_symm a b c d

theorem riem_antisymm (a b c d : Fin n) : J.riem a b c d = -J.riem a b d c :=
  riemann_antisymm J.chr2 J.dchr2 a b c d

end MetricJet

end Metric

end FieldEquations.Curvature
