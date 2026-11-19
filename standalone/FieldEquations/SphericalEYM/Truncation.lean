import FieldEquations.Characteristic.Goursat
import FieldEquations.SphericalEYM.Uniqueness

/-
# Truncated right-hand sides

`trunc B m` clamps the seven quantities into the box `Good B m`; the truncated right-hand side
`Fw B m` is globally Lipschitz (`Fw_lip`), so the Goursat existence theorem applies to it.
Where a solution of the truncated system stays inside the box, it solves the original system
(`trunc_of`).
-/

open Real Set Filter Topology FieldEquations.SphericalEYM FieldEquations.CharacteristicUniqueness FieldEquations.Goursat FieldEquations.EYMUniqueness

namespace FieldEquations.EYMTruncation

noncomputable def clampIcc (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clampIcc_lip (lo hi x y : ℝ) : |clampIcc lo hi x - clampIcc lo hi y| ≤ |x - y| := by
  unfold clampIcc
  have h1 := abs_max_sub_max_le_max lo (min hi x) lo (min hi y)
  have h2 := abs_min_sub_min_le_max hi x hi y
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min hi x - min hi y))] at h1
  rw [max_eq_right (abs_nonneg (x - y))] at h2
  exact h1.trans h2

theorem clampIcc_ge (lo hi x : ℝ) : lo ≤ clampIcc lo hi x := le_max_left _ _

theorem clampIcc_le {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clampIcc lo hi x ≤ hi :=
  max_le h (min_le_left _ _)

theorem clampIcc_of {lo hi x : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) : clampIcc lo hi x = x := by
  unfold clampIcc
  rw [min_eq_right h2, max_eq_right h1]

noncomputable def trunc (B m : ℝ) (p : Pt) : Pt :=
  ⟨clampIcc m B p.Om, clampIcc (-B) B p.W, clampIcc (-B) B p.ru, clampIcc (-B) B p.rv,
    clampIcc m B p.r, clampIcc (-B) B p.Ou, clampIcc (-B) B p.Ov⟩

theorem trunc_good {B m : ℝ} (hm : 0 < m) (hmB : m ≤ B) (p : Pt) : Good B m (trunc B m p) := by
  have a1 : ∀ x, |clampIcc (-B) B x| ≤ B := fun x =>
    abs_le.mpr ⟨clampIcc_ge _ _ _, clampIcc_le (by linarith) x⟩
  have a2 : ∀ x, |clampIcc m B x| ≤ B := fun x =>
    abs_le.mpr ⟨by linarith [clampIcc_ge m B x], clampIcc_le hmB x⟩
  exact ⟨a2 _, a1 _, a1 _, a1 _, a1 _, a1 _, clampIcc_ge _ _ _, clampIcc_ge _ _ _⟩

theorem trunc_pdist (B m : ℝ) (p q : Pt) : pdist (trunc B m p) (trunc B m q) ≤ pdist p q := by
  simp only [pdist, trunc]
  have := clampIcc_lip m B p.Om q.Om
  have := clampIcc_lip (-B) B p.W q.W
  have := clampIcc_lip (-B) B p.ru q.ru
  have := clampIcc_lip (-B) B p.rv q.rv
  have := clampIcc_lip m B p.r q.r
  have := clampIcc_lip (-B) B p.Ou q.Ou
  have := clampIcc_lip (-B) B p.Ov q.Ov
  linarith

/-- Truncation is the identity inside the box. -/
theorem trunc_of {B m : ℝ} {p : Pt} (h1 : m ≤ p.Om) (h2 : p.Om ≤ B) (hW : |p.W| ≤ B)
    (hru : |p.ru| ≤ B) (hrv : |p.rv| ≤ B) (h6 : m ≤ p.r) (h7 : p.r ≤ B) (hOu : |p.Ou| ≤ B)
    (hOv : |p.Ov| ≤ B) : trunc B m p = p := by
  have c : ∀ x, |x| ≤ B → clampIcc (-B) B x = x := fun x hx =>
    clampIcc_of (abs_le.mp hx).1 (abs_le.mp hx).2
  unfold trunc
  (rw [clampIcc_of h1 h2, c _ hW, c _ hru, c _ hrv, clampIcc_of h6 h7, c _ hOu, c _ hOv]) <;> rfl

theorem lip_trunc {B m : ℝ} {e : Pt → ℝ} (hm : 0 < m) (hmB : m ≤ B) (h : UL B m e) :
    ∃ Λ, 0 ≤ Λ ∧ ∀ p q, |e (trunc B m p) - e (trunc B m q)| ≤ Λ * pdist p q := by
  obtain ⟨Λ, hΛ, hl⟩ := h
  exact ⟨Λ, hΛ, fun p q => ((hl _ _ (trunc_good hm hmB p) (trunc_good hm hmB q)).2.2).trans
    (mul_le_mul_of_nonneg_left (trunc_pdist B m p q) hΛ)⟩

def toPt (x y z : Fin 3 → ℝ) : Pt := ⟨x 1, x 2, y 0, z 0, x 0, y 1, z 1⟩

theorem toPt_pdist (x1 y1 z1 x2 y2 z2 : Fin 3 → ℝ) :
    pdist (toPt x1 y1 z1) (toPt x2 y2 z2)
      ≤ ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|) := by
  rw [Fin.sum_univ_three]
  simp only [pdist, toPt]
  linarith [abs_nonneg (y1 2 - y2 2), abs_nonneg (z1 2 - z2 2)]

noncomputable def eVec : Fin 3 → Pt → ℝ := ![eR, eOm, eW]

noncomputable def Fw (B m : ℝ) (i : Fin 3) (x y z : Fin 3 → ℝ) : ℝ :=
  eVec i (trunc B m (toPt x y z))

/-- The truncated right-hand side is globally Lipschitz. -/
theorem Fw_lip {B m : ℝ} (hm : 0 < m) (hmB : m ≤ B) :
    ∃ L, 0 ≤ L ∧ ∀ i x1 y1 z1 x2 y2 z2, |Fw B m i x1 y1 z1 - Fw B m i x2 y2 z2|
      ≤ L * ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|) := by
  obtain ⟨Λ0, h0n, h0⟩ := lip_trunc hm hmB (UL_rhsR (B := B) hm)
  obtain ⟨Λ1, h1n, h1⟩ := lip_trunc hm hmB (UL_rhsOm (B := B) hm)
  obtain ⟨Λ2, h2n, h2⟩ := lip_trunc hm hmB (UL_rhsW (B := B) hm)
  refine ⟨Λ0 + Λ1 + Λ2, by linarith, fun i x1 y1 z1 x2 y2 z2 => ?_⟩
  have hp := toPt_pdist x1 y1 z1 x2 y2 z2
  have hpn := pdist_nonneg (toPt x1 y1 z1) (toPt x2 y2 z2)
  have lift : ∀ Λ : ℝ, 0 ≤ Λ → Λ ≤ Λ0 + Λ1 + Λ2 →
      Λ * pdist (toPt x1 y1 z1) (toPt x2 y2 z2)
        ≤ (Λ0 + Λ1 + Λ2) * ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|) :=
    fun Λ ha hb => mul_le_mul hb hp hpn (by linarith)
  fin_cases i
  · show |eR (trunc B m (toPt x1 y1 z1)) - eR (trunc B m (toPt x2 y2 z2))| ≤ _
    exact (h0 _ _).trans (lift Λ0 h0n (by linarith))
  · show |eOm (trunc B m (toPt x1 y1 z1)) - eOm (trunc B m (toPt x2 y2 z2))| ≤ _
    exact (h1 _ _).trans (lift Λ1 h1n (by linarith))
  · show |eW (trunc B m (toPt x1 y1 z1)) - eW (trunc B m (toPt x2 y2 z2))| ≤ _
    exact (h2 _ _).trans (lift Λ2 h2n (by linarith))

end FieldEquations.EYMTruncation
