/-
  α-I.5(Y4)の残り:Q(p) = (m/E, p/E)(AlphaI の qD と同じ向き)は R³ から開いた上半球
      S³₊ = {(w, x) : w > 0、w² + |x|² = 1}
  への全単射(監査で欠けていると指摘された部分)。逆写像は p = m x/w。
  局所的な等長(pullback_metric、radial_metric)と合わせると、(R³, g^Q) は開半球と等長同型。
    * qmap_maps:像は開半球に入る
    * qmap_inj:単射
    * qmap_surj:全射(逆写像 qinv の明示)
    * qmap_bij:Set.BijOn
    * qinv_left、qinv_right:qinv ∘ qmap = id、qmap ∘ qinv = id(半球の上)
  B(ダンベルの基礎)の AlphaB_QH と合わせて:この半球は質量殻 H³ と同じ空間(半球模型)で、
  計量は H³ の計量の 1/E² 倍。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

namespace CFT.QBij

/-- E = √(m² + |p|²) -/
noncomputable def En (m : ℝ) (p : Fin 3 → ℝ) : ℝ := √(m ^ 2 + ∑ i, p i ^ 2)

noncomputable def qmap (m : ℝ) (p : Fin 3 → ℝ) : ℝ × (Fin 3 → ℝ) :=
  (m / En m p, fun i => p i / En m p)

def hemi : Set (ℝ × (Fin 3 → ℝ)) := {q | 0 < q.1 ∧ q.1 ^ 2 + ∑ i, q.2 i ^ 2 = 1}

noncomputable def qinv (m : ℝ) (q : ℝ × (Fin 3 → ℝ)) : Fin 3 → ℝ := fun i => m * q.2 i / q.1

theorem sum_nonneg' (p : Fin 3 → ℝ) : 0 ≤ ∑ i, p i ^ 2 :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (p i))

theorem En_pos (m : ℝ) (hm : 0 < m) (p : Fin 3 → ℝ) : 0 < En m p :=
  Real.sqrt_pos.2 (by have := sum_nonneg' p; positivity)

theorem En_sq (m : ℝ) (p : Fin 3 → ℝ) : En m p ^ 2 = m ^ 2 + ∑ i, p i ^ 2 :=
  Real.sq_sqrt (by have := sum_nonneg' p; positivity)

theorem qmap_maps (m : ℝ) (hm : 0 < m) (p : Fin 3 → ℝ) : qmap m p ∈ hemi := by
  have hE := En_pos m hm p
  refine ⟨div_pos hm hE, ?_⟩
  simp only [qmap]
  have : ∑ i, (p i / En m p) ^ 2 = (∑ i, p i ^ 2) / En m p ^ 2 := by
    rw [Finset.sum_div]; congr 1; funext i; rw [div_pow]
  rw [this, div_pow, ← add_div, En_sq]
  exact div_self (by have := sum_nonneg' p; positivity)

theorem qinv_left (m : ℝ) (hm : 0 < m) (p : Fin 3 → ℝ) : qinv m (qmap m p) = p := by
  have hE := (En_pos m hm p).ne'
  funext i; simp only [qinv, qmap]; field_simp

theorem qmap_inj (m : ℝ) (hm : 0 < m) : Function.Injective (qmap m) := by
  intro p p' h
  rw [← qinv_left m hm p, ← qinv_left m hm p', h]

theorem qinv_right (m : ℝ) (hm : 0 < m) (q : ℝ × (Fin 3 → ℝ)) (hq : q ∈ hemi) :
    qmap m (qinv m q) = q := by
  obtain ⟨h1, h2⟩ := hq
  have hw := h1.ne'
  -- E(qinv q) = m/w
  have hs : ∑ i, qinv m q i ^ 2 = m ^ 2 * (∑ i, q.2 i ^ 2) / q.1 ^ 2 := by
    simp only [qinv]; rw [Finset.mul_sum, Finset.sum_div]; congr 1; funext i; field_simp; ring
  have hE : En m (qinv m q) = m / q.1 := by
    unfold En
    rw [hs, show ∑ i, q.2 i ^ 2 = 1 - q.1 ^ 2 by linarith]
    rw [show m ^ 2 + m ^ 2 * (1 - q.1 ^ 2) / q.1 ^ 2 = (m / q.1) ^ 2 by field_simp; ring]
    exact Real.sqrt_sq (div_pos hm h1).le
  ext
  · simp only [qmap, hE]; field_simp
  · simp only [qmap, hE, qinv]; field_simp

theorem qmap_surj (m : ℝ) (hm : 0 < m) : Set.SurjOn (qmap m) Set.univ hemi := by
  intro q hq
  exact ⟨qinv m q, Set.mem_univ _, qinv_right m hm q hq⟩

theorem qmap_bij (m : ℝ) (hm : 0 < m) : Set.BijOn (qmap m) Set.univ hemi :=
  ⟨fun p _ => qmap_maps m hm p, (qmap_inj m hm).injOn, qmap_surj m hm⟩

end CFT.QBij
