import FieldEquations.SphericalEYM.System
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-
# Reduction of the Einstein equations to the double-null system

Setting: a field S of characteristic zero with four commuting derivations D₀, D₁, D₂, D₃ (the coordinate derivatives
∂_u, ∂_v, ∂_θ, ∂_φ). The metric is
  ds² = −2Ω du dv + r² (dθ² + sin²θ dφ²),
where Ω and r depend on (u, v) only, and `sn`, `cs` stand for sin θ and cos θ
(D₂ sn = cs, D₂ cs = −sn, independent of u, v, φ). These conditions are the structure `Ansatz`.

* `Γ` is the Levi-Civita connection Γ^a_{bc} = ½ g^{ad}(∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc}) of this
  metric, `christoffel` computes all 64 components, `Riem`, `Ric`, `Rs`, `Gt` are the Riemann,
  Ricci, scalar and Einstein tensors (R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce}Γ^e_{db}
  − Γ^a_{de}Γ^e_{cb}, Ric_{bd} = R^a_{bad}).
* `G00`, `G11`, `G01`, `G22`, `G33`: the nonzero components
    G_uu = −(2/r)(r_uu − (Ω_u/Ω) r_u),  G_vv = −(2/r)(r_vv − (Ω_v/Ω) r_v),
    G_uv = (2/r) r_uv + (2/r²) r_u r_v + Ω/r²,
    G_θθ = −(r²/Ω)(log Ω)_uv − (2r/Ω) r_uv,  G_φφ = sin²θ G_θθ;
  `G_offdiag`: the other off-diagonal components vanish.
* `T00`, `T11`, `T01`, `T22` are the components of the Yang–Mills stress tensor of the spherically
  symmetric magnetic SU(2) ansatz with one function W(u, v) (the standard expressions
  T_uu = 2W_u²/r², T_vv = 2W_v²/r², T_uv = Ω(1−W²)²/(2r⁴), T_θθ = (1−W²)²/(2r²), T_φφ = sin²θ T_θθ,
  other components zero). They are taken as definitions here; deriving them from the
  Yang–Mills field strength is not formalized.
* `einstein_iff_system`: with these components, the Einstein equations G = 2T are equivalent to
  the two constraint equations and the r- and Ω-evolution equations, with exactly the
  right-hand sides `rhsR`, `rhsOm` of `FieldEquations.SphericalEYM.System`.
-/

open Finset FieldEquations.SphericalEYM

namespace FieldEquations.SphericalReduction

variable {S : Type*} [Field S] [CharZero S]

/-- The derivative of an inverse. -/
theorem D_inv (d : Derivation ℤ S S) {x : S} (hx : x ≠ 0) : d x⁻¹ = -(x⁻¹ * x⁻¹) * d x := by
  have h := d.leibniz x x⁻¹
  rw [mul_inv_cancel₀ hx, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
  have h2 : x * d x⁻¹ = -(x⁻¹ * d x) := by linear_combination -h
  calc d x⁻¹ = x⁻¹ * (x * d x⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
    _ = -(x⁻¹ * x⁻¹) * d x := by rw [h2]; ring

/-- The spherically symmetric double-null ansatz. -/
structure Ansatz (D : Fin 4 → Derivation ℤ S S) (Om r sn cs : S) : Prop where
  comm : ∀ i j x, D i (D j x) = D j (D i x)
  Om2 : D 2 Om = 0
  Om3 : D 3 Om = 0
  r2 : D 2 r = 0
  r3 : D 3 r = 0
  sn0 : D 0 sn = 0
  sn1 : D 1 sn = 0
  sn2 : D 2 sn = cs
  sn3 : D 3 sn = 0
  cs0 : D 0 cs = 0
  cs1 : D 1 cs = 0
  cs2 : D 2 cs = -sn
  cs3 : D 3 cs = 0
  hOm : Om ≠ 0
  hr : r ≠ 0
  hsn : sn ≠ 0

variable (D : Fin 4 → Derivation ℤ S S) (Om r sn cs : S)

/-- The metric −2Ω du dv + r²(dθ² + sin²θ dφ²) in the coordinates (u, v, θ, φ). -/
def gm (a b : Fin 4) : S :=
  if a = 0 then (if b = 1 then -Om else 0)
  else if a = 1 then (if b = 0 then -Om else 0)
  else if a = 2 then (if b = 2 then r * r else 0)
  else (if b = 3 then r * r * (sn * sn) else 0)

/-- The inverse metric. -/
noncomputable def gi (a b : Fin 4) : S :=
  if a = 0 then (if b = 1 then -Om⁻¹ else 0)
  else if a = 1 then (if b = 0 then -Om⁻¹ else 0)
  else if a = 2 then (if b = 2 then r⁻¹ * r⁻¹ else 0)
  else (if b = 3 then r⁻¹ * r⁻¹ * (sn⁻¹ * sn⁻¹) else 0)

/-- The Levi-Civita connection of `gm`. -/
noncomputable def Γ (a b c : Fin 4) : S :=
  (1/2 : S) * ∑ d, gi Om r sn a d * (D b (gm Om r sn d c) + D c (gm Om r sn d b)
    - D d (gm Om r sn b c))

/-- The Christoffel symbols in closed form. -/
noncomputable def Γe (a b c : Fin 4) : S :=
  if a = 0 then
    (if b = 0 then (if c = 0 then D 0 Om * Om⁻¹ else 0)
     else if b = 2 then (if c = 2 then r * D 1 r * Om⁻¹ else 0)
     else if b = 3 then (if c = 3 then r * D 1 r * (sn * sn) * Om⁻¹ else 0) else 0)
  else if a = 1 then
    (if b = 1 then (if c = 1 then D 1 Om * Om⁻¹ else 0)
     else if b = 2 then (if c = 2 then r * D 0 r * Om⁻¹ else 0)
     else if b = 3 then (if c = 3 then r * D 0 r * (sn * sn) * Om⁻¹ else 0) else 0)
  else if a = 2 then
    (if b = 0 then (if c = 2 then D 0 r * r⁻¹ else 0)
     else if b = 1 then (if c = 2 then D 1 r * r⁻¹ else 0)
     else if b = 2 then (if c = 0 then D 0 r * r⁻¹ else if c = 1 then D 1 r * r⁻¹ else 0)
     else (if c = 3 then -(sn * cs) else 0))
  else
    (if b = 0 then (if c = 3 then D 0 r * r⁻¹ else 0)
     else if b = 1 then (if c = 3 then D 1 r * r⁻¹ else 0)
     else if b = 2 then (if c = 3 then cs * sn⁻¹ else 0)
     else (if c = 0 then D 0 r * r⁻¹ else if c = 1 then D 1 r * r⁻¹
       else if c = 2 then cs * sn⁻¹ else 0))

variable {D Om r sn cs}

theorem christoffel (A : Ansatz D Om r sn cs) (a b c : Fin 4) :
    Γ D Om r sn a b c = Γe D Om r sn cs a b c := by
  have hOm := A.hOm
  have hr := A.hr
  have hsn := A.hsn
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
  simp (config := { decide := true }) only [Γ, Γe, gm, gi, Fin.sum_univ_four, Fin.isValue,
    ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, map_neg, map_zero, Derivation.leibniz,
    smul_eq_mul, A.Om2, A.Om3, A.r2, A.r3, A.sn0, A.sn1, A.sn2, A.sn3, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero] <;>
  (try field_simp) <;> ring

variable (D Om r sn cs)

/-- The Riemann tensor R^a_{bcd} of `Γ`. -/
noncomputable def Riem (a b c d : Fin 4) : S :=
  D c (Γ D Om r sn a d b) - D d (Γ D Om r sn a c b)
    + ∑ e, (Γ D Om r sn a c e * Γ D Om r sn e d b - Γ D Om r sn a d e * Γ D Om r sn e c b)

/-- The Ricci tensor Ric_{bd} = R^a_{bad}. -/
noncomputable def Ric (b d : Fin 4) : S := ∑ a, Riem D Om r sn a b a d

/-- The scalar curvature. -/
noncomputable def Rs : S := ∑ b, ∑ d, gi Om r sn b d * Ric D Om r sn b d

/-- The Einstein tensor. -/
noncomputable def Gt (b d : Fin 4) : S := Ric D Om r sn b d - (1/2 : S) * gm Om r sn b d * Rs D Om r sn

variable {D Om r sn cs}

/-- (log Ω)_uv. -/
noncomputable def logOuv (D : Fin 4 → Derivation ℤ S S) (Om : S) : S :=
  D 0 (D 1 Om) * Om⁻¹ - D 0 Om * D 1 Om * (Om⁻¹ * Om⁻¹)

theorem ric_eq (A : Ansatz D Om r sn cs) (b d : Fin 4) :
    Ric D Om r sn b d =
      if b = 0 then
        (if d = 0 then -(2 * r⁻¹) * (D 0 (D 0 r) - D 0 Om * Om⁻¹ * D 0 r)
         else if d = 1 then -logOuv D Om - 2 * r⁻¹ * D 0 (D 1 r) else 0)
      else if b = 1 then
        (if d = 1 then -(2 * r⁻¹) * (D 1 (D 1 r) - D 1 Om * Om⁻¹ * D 1 r)
         else if d = 0 then -logOuv D Om - 2 * r⁻¹ * D 0 (D 1 r) else 0)
      else if b = 2 then
        (if d = 2 then 1 + 2 * Om⁻¹ * (r * D 0 (D 1 r) + D 0 r * D 1 r) else 0)
      else
        (if d = 3 then sn * sn * (1 + 2 * Om⁻¹ * (r * D 0 (D 1 r) + D 0 r * D 1 r)) else 0) := by
  have hOm := A.hOm
  have hr := A.hr
  have hsn := A.hsn
  have c2O : ∀ j, D 2 (D j Om) = 0 := fun j => by rw [A.comm, A.Om2, map_zero]
  have c3O : ∀ j, D 3 (D j Om) = 0 := fun j => by rw [A.comm, A.Om3, map_zero]
  have c2r : ∀ j, D 2 (D j r) = 0 := fun j => by rw [A.comm, A.r2, map_zero]
  have c3r : ∀ j, D 3 (D j r) = 0 := fun j => by rw [A.comm, A.r3, map_zero]
  have c10O : D 1 (D 0 Om) = D 0 (D 1 Om) := A.comm 1 0 Om
  have c10r : D 1 (D 0 r) = D 0 (D 1 r) := A.comm 1 0 r
  have iO := fun i => D_inv (D i) hOm
  have ir := fun i => D_inv (D i) hr
  have isn := fun i => D_inv (D i) hsn
  unfold Ric Riem logOuv
  simp only [christoffel A]
  fin_cases b <;> fin_cases d <;>
  simp (config := { decide := true }) only [Γe, Fin.sum_univ_four, Fin.isValue,
    ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, map_neg, map_zero, Derivation.leibniz,
    smul_eq_mul, A.Om2, A.Om3, A.r2, A.r3, A.sn0, A.sn1, A.sn2, A.sn3, A.cs0, A.cs1, A.cs2, A.cs3,
    c2O, c3O, c2r, c3r, c10O, c10r, iO, ir, isn, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, neg_neg] <;>
  (try field_simp) <;> ring

theorem rs_eq (A : Ansatz D Om r sn cs) :
    Rs D Om r sn = -(2 * Om⁻¹) * (-logOuv D Om - 2 * r⁻¹ * D 0 (D 1 r))
      + 2 * (r⁻¹ * r⁻¹) * (1 + 2 * Om⁻¹ * (r * D 0 (D 1 r) + D 0 r * D 1 r)) := by
  have hOm := A.hOm
  have hr := A.hr
  have hsn := A.hsn
  unfold Rs
  simp (config := { decide := true }) only [ric_eq A, gi, Fin.sum_univ_four, Fin.isValue,
    ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, mul_zero, zero_mul, add_zero, zero_add]
  field_simp
  ring

theorem G00 (A : Ansatz D Om r sn cs) :
    Gt D Om r sn 0 0 = -(2 * r⁻¹) * (D 0 (D 0 r) - D 0 Om * Om⁻¹ * D 0 r) := by
  unfold Gt
  simp (config := { decide := true }) only [ric_eq A, gm, Fin.isValue, ↓reduceIte, mul_zero,
    zero_mul, sub_zero]

theorem G11 (A : Ansatz D Om r sn cs) :
    Gt D Om r sn 1 1 = -(2 * r⁻¹) * (D 1 (D 1 r) - D 1 Om * Om⁻¹ * D 1 r) := by
  unfold Gt
  simp (config := { decide := true }) only [ric_eq A, gm, Fin.isValue, ↓reduceIte, mul_zero,
    zero_mul, sub_zero]

theorem G01 (A : Ansatz D Om r sn cs) :
    Gt D Om r sn 0 1 = 2 * r⁻¹ * D 0 (D 1 r) + 2 * (r⁻¹ * r⁻¹) * (D 0 r * D 1 r)
      + Om * (r⁻¹ * r⁻¹) := by
  have hOm := A.hOm
  have hr := A.hr
  unfold Gt
  rw [rs_eq A]
  simp (config := { decide := true }) only [ric_eq A, gm, Fin.isValue, ↓reduceIte, logOuv]
  field_simp
  ring

theorem G22 (A : Ansatz D Om r sn cs) :
    Gt D Om r sn 2 2 = -(r * r * Om⁻¹) * logOuv D Om - 2 * r * Om⁻¹ * D 0 (D 1 r) := by
  have hOm := A.hOm
  have hr := A.hr
  unfold Gt
  rw [rs_eq A]
  simp (config := { decide := true }) only [ric_eq A, gm, Fin.isValue, ↓reduceIte, logOuv]
  field_simp
  ring

theorem G33 (A : Ansatz D Om r sn cs) :
    Gt D Om r sn 3 3 = sn * sn * Gt D Om r sn 2 2 := by
  have hOm := A.hOm
  have hr := A.hr
  unfold Gt
  rw [rs_eq A]
  simp (config := { decide := true }) only [ric_eq A, gm, Fin.isValue, ↓reduceIte, logOuv]
  ring

theorem G_offdiag (A : Ansatz D Om r sn cs) (b d : Fin 4) (hbd : b ≠ d)
    (h01 : ¬ (b = 0 ∧ d = 1)) (h10 : ¬ (b = 1 ∧ d = 0)) : Gt D Om r sn b d = 0 := by
  unfold Gt
  fin_cases b <;> fin_cases d <;>
  simp (config := { decide := true }) only [ric_eq A, gm, Fin.isValue, ↓reduceIte, mul_zero,
    zero_mul, sub_zero] at hbd h01 h10 ⊢

/-! ### The Yang–Mills source and the reduced system -/

variable (D Om r)

/-- T_uu of the magnetic ansatz. -/
noncomputable def T00 (W : S) : S := 2 * (D 0 W) ^ 2 / r ^ 2
/-- T_vv of the magnetic ansatz. -/
noncomputable def T11 (W : S) : S := 2 * (D 1 W) ^ 2 / r ^ 2
/-- T_uv of the magnetic ansatz. -/
noncomputable def T01 (W : S) : S := Om * (1 - W ^ 2) ^ 2 / (2 * r ^ 4)
/-- T_θθ of the magnetic ansatz. -/
noncomputable def T22 (W : S) : S := (1 - W ^ 2) ^ 2 / (2 * r ^ 2)

variable {D Om r}

theorem uu_eq (A : Ansatz D Om r sn cs) (W : S) :
    Gt D Om r sn 0 0 - 2 * T00 D r W
      = -(2 / r) * (D 0 (D 0 r) - (D 0 Om / Om) * D 0 r + 2 * (D 0 W) ^ 2 / r) := by
  have hOm := A.hOm
  have hr := A.hr
  rw [G00 A]
  unfold T00
  field_simp
  ring

theorem vv_eq (A : Ansatz D Om r sn cs) (W : S) :
    Gt D Om r sn 1 1 - 2 * T11 D r W
      = -(2 / r) * (D 1 (D 1 r) - (D 1 Om / Om) * D 1 r + 2 * (D 1 W) ^ 2 / r) := by
  have hOm := A.hOm
  have hr := A.hr
  rw [G11 A]
  unfold T11
  field_simp
  ring

theorem uv_eq (A : Ansatz D Om r sn cs) (W : S) :
    Gt D Om r sn 0 1 - 2 * T01 Om r W
      = (2 / r) * (D 0 (D 1 r) - rhsR Om W (D 0 r) (D 1 r) r) := by
  have hOm := A.hOm
  have hr := A.hr
  rw [G01 A]
  unfold T01 rhsR
  field_simp
  ring

theorem thth_eq (A : Ansatz D Om r sn cs) (W : S) :
    Gt D Om r sn 2 2 - 2 * T22 r W
      = -(r ^ 2 / Om ^ 2) * (D 0 (D 1 Om) - rhsOm Om (D 0 Om) (D 1 Om) (D 0 (D 1 r)) r W) := by
  have hOm := A.hOm
  have hr := A.hr
  rw [G22 A]
  unfold T22 rhsOm logOuv
  field_simp
  ring

/-- The Einstein equations G = 2T for the magnetic Yang–Mills source are equivalent to the two
constraint equations and the r- and Ω-evolution equations of the double-null system. -/
theorem einstein_iff_system (A : Ansatz D Om r sn cs) (W : S) :
    (Gt D Om r sn 0 0 = 2 * T00 D r W ∧ Gt D Om r sn 1 1 = 2 * T11 D r W
      ∧ Gt D Om r sn 0 1 = 2 * T01 Om r W ∧ Gt D Om r sn 2 2 = 2 * T22 r W)
    ↔ (D 0 (D 0 r) - (D 0 Om / Om) * D 0 r + 2 * (D 0 W) ^ 2 / r = 0
      ∧ D 1 (D 1 r) - (D 1 Om / Om) * D 1 r + 2 * (D 1 W) ^ 2 / r = 0
      ∧ D 0 (D 1 r) = rhsR Om W (D 0 r) (D 1 r) r
      ∧ D 0 (D 1 Om) = rhsOm Om (D 0 Om) (D 1 Om) (D 0 (D 1 r)) r W) := by
  have hOm := A.hOm
  have hr := A.hr
  have k1 : -(2 / r) ≠ 0 := neg_ne_zero.mpr (div_ne_zero two_ne_zero hr)
  have k2 : (2 / r) ≠ 0 := div_ne_zero two_ne_zero hr
  have k3 : -(r ^ 2 / Om ^ 2) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hr) (pow_ne_zero 2 hOm))
  rw [← sub_eq_zero (a := Gt D Om r sn 0 0), uu_eq A W, mul_eq_zero, or_iff_right k1,
    ← sub_eq_zero (a := Gt D Om r sn 1 1), vv_eq A W, mul_eq_zero, or_iff_right k1,
    ← sub_eq_zero (a := Gt D Om r sn 0 1), uv_eq A W, mul_eq_zero, or_iff_right k2, sub_eq_zero,
    ← sub_eq_zero (a := Gt D Om r sn 2 2), thth_eq A W, mul_eq_zero, or_iff_right k3, sub_eq_zero]

end FieldEquations.SphericalReduction
