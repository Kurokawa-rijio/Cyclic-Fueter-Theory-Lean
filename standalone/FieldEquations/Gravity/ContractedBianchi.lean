import Mathlib.Tactic

/-
# The contracted Bianchi identity in normal coordinates

At a point where Γ = 0 and ∂g = 0, with second and third metric derivatives as data,
∇^a G_{ab} = 0 (`contracted_bianchi_normal`). Only the pointwise statement in normal
coordinates is proved; the passage to a general chart (tensoriality) is not formalized.
-/

namespace FieldEquations.ContractedBianchi

open Finset

variable {n : ℕ}

def S4 (F : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ := ∑ a, ∑ b, ∑ c, ∑ e, F a b c e

theorem relabel_pairs (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    S4 (fun a b c e => F c e a b) = S4 F := by
  unfold S4
  calc ∑ a, ∑ b, ∑ c, ∑ e, F c e a b
      = ∑ a, ∑ c, ∑ b, ∑ e, F c e a b := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, ∑ e, F c e a b := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, F c e a b :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ c, ∑ e, ∑ a, ∑ b, F c e a b := Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

theorem relabel_within (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    S4 (fun a b c e => F b a e c) = S4 F := by
  unfold S4
  calc ∑ a, ∑ b, ∑ c, ∑ e, F b a e c
      = ∑ b, ∑ a, ∑ c, ∑ e, F b a e c := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ e, ∑ c, F b a e c :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))

theorem relabel_reverse (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    S4 (fun a b c e => F e c b a) = S4 F := by
  have h := relabel_within (fun a b c e => F c e a b)
  simp only at h
  rw [h, relabel_pairs]

theorem S4_congr {F G : Fin n → Fin n → Fin n → Fin n → ℝ} (h : ∀ a b c e, F a b c e = G a b c e) :
    S4 F = S4 G := by
  unfold S4
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => h a b c e

variable (gi : Fin n → Fin n → ℝ) (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)

noncomputable def ddchr1 (b c e d a : Fin n) : ℝ :=
  (1/2 : ℝ) * (H e a d b c + H e d a b c - H d a e b c)

noncomputable def ddchr2 (b c x d a : Fin n) : ℝ := ∑ e, gi x e * ddchr1 H b c e d a

noncomputable def dRic (b a d : Fin n) : ℝ :=
  ∑ c, (ddchr2 gi H b c c d a - ddchr2 gi H b d c c a)

noncomputable def divG (d : Fin n) : ℝ :=
  ∑ a, ∑ b, gi a b * dRic gi H b a d - (1/2 : ℝ) * ∑ a, ∑ b, gi a b * dRic gi H d a b

/-- ∇^a G_{ab} = 0 at a point in normal coordinates. -/
theorem contracted_bianchi_normal (hgi : ∀ a b, gi a b = gi b a)
    (hH1 : ∀ x y u v w, H x y u v w = H y x u v w)
    (hH2 : ∀ x y u v w, H x y u v w = H x y v u w)
    (hH3 : ∀ x y u v w, H x y u v w = H x y u w v) (d : Fin n) :
    divG gi H d = 0 := by

  have hexp : divG gi H d = S4 (fun a b c e => gi a b * gi c e *
      (ddchr1 H b c e d a - ddchr1 H b d e c a
        - (1/2 : ℝ) * ddchr1 H d c e b a + (1/2 : ℝ) * ddchr1 H d b e c a)) := by
    unfold divG dRic ddchr2 S4
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    ring

  let W : Fin n → Fin n → Fin n → Fin n → ℝ := fun a b c e => gi a b * gi c e
  have hsplit : S4 (fun a b c e => gi a b * gi c e *
      (ddchr1 H b c e d a - ddchr1 H b d e c a
        - (1/2 : ℝ) * ddchr1 H d c e b a + (1/2 : ℝ) * ddchr1 H d b e c a))
      = (1/2 : ℝ) * (S4 (fun a b c e => W a b c e * H e a d b c)
          - S4 (fun a b c e => W a b c e * H e a c b d))
        + (1/2 : ℝ) * (S4 (fun a b c e => W a b c e * H e d a b c)
          - S4 (fun a b c e => W a b c e * H d a e b c))
        - (1/2 : ℝ) * S4 (fun a b c e => W a b c e * H e c a b d)
        + (1/2 : ℝ) * S4 (fun a b c e => W a b c e * H c a e b d)
        - (1/4 : ℝ) * (S4 (fun a b c e => W a b c e * H e a b d c)
          - S4 (fun a b c e => W a b c e * H e a c d b))
        - (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H e b a d c)
        + (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H b a e d c)
        + (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H e c a d b)
        - (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H c a e d b) := by
    unfold S4
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [W, ddchr1]
    ring

  have hcyc : ∀ x y u v w, H x y u v w = H x y v w u := fun x y u v w => by
    rw [hH2 x y u v w, hH3 x y v u w]

  have p1 : S4 (fun a b c e => W a b c e * H e a c b d)
      = S4 (fun a b c e => W a b c e * H e a d b c) := S4_congr fun a b c e => by
    rw [hH2 e a c b d, hH3 e a b c d, hH2 e a b d c]
  have p2 : S4 (fun a b c e => W a b c e * H e a c d b)
      = S4 (fun a b c e => W a b c e * H e a b d c) := S4_congr fun a b c e => by
    rw [hH3 e a c d b, hH2 e a c b d, hH3 e a b c d]
  have p3 : S4 (fun a b c e => W a b c e * H e c a d b)
      = S4 (fun a b c e => W a b c e * H e c a b d) := S4_congr fun a b c e => by
    rw [hH3 e c a d b]
  have p4 : S4 (fun a b c e => W a b c e * H c a e d b)
      = S4 (fun a b c e => W a b c e * H c a e b d) := S4_congr fun a b c e => by
    rw [hH3 c a e d b]

  have r1 : S4 (fun a b c e => W a b c e * H d a e b c)
      = S4 (fun a b c e => W a b c e * H e d a b c) := by
    rw [← relabel_reverse (fun a b c e => W a b c e * H d a e b c)]
    exact S4_congr fun a b c e => by
      simp only [W]
      rw [hgi e c, hgi b a, hH3 d e a c b, hH1 d e a b c]
      ring
  have r2 : S4 (fun a b c e => W a b c e * H b a e d c)
      = S4 (fun a b c e => W a b c e * H e c a b d) := by
    rw [← relabel_pairs (fun a b c e => W a b c e * H e c a b d)]
    exact S4_congr fun a b c e => by
      simp only [W]
      rw [hcyc b a e d c, hcyc b a d c e]
      ring
  have r3 : S4 (fun a b c e => W a b c e * H e b a d c)
      = S4 (fun a b c e => W a b c e * H c a e b d) := by
    rw [← relabel_within (fun a b c e => W a b c e * H c a e b d)]
    exact S4_congr fun a b c e => by
      simp only [W]
      (rw [hgi a b, hgi c e, hcyc e b a d c, hcyc e b d c a]) <;> ring
  rw [hexp, hsplit, p1, p2, p3, p4, r1, r2, r3]
  ring

end FieldEquations.ContractedBianchi
