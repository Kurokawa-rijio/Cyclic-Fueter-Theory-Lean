/-
  α-II.4:Bochner 恒等式の各点での帰結

  U の点 p での評価 ev : R →+* ℝ(滑らかな関数 f ↦ f(p))をとると、
    κ(p) = Σ_{i<j}(λ_i + λ_j − R/2)(λ_i − λ_j)² = −|∇Ric|²(p) ≤ 0。
  κ = σ₁³ − 4σ₁σ₂ + 9σ₃(kappa_sym)と (I) のもとでの閉じた式(kappa_closed)、
  窓定理(window, window_cos)と合わせると、C2 の必要条件 0 < Rℓ² < 2 などが出る。
-/
import CFT.Cartan.C2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace CFT.Cartan

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem ev_half (ev : R →+* ℝ) : ev half = 1 / 2 := by
  have h := congrArg ev (two_mul_half (R := R))
  rw [map_mul, map_one, map_ofNat] at h
  linarith

namespace C2

variable {F : Frame R} {lam : Fin 3 → R} (H : C2 F lam)
include H

/-- 各点で κ = −|∇Ric|² ≤ 0 -/
theorem kappa_eq_neg_grad (ev : R →+* ℝ) :
    let l := fun i => ev (lam i)
    let s1 := l 0 + l 1 + l 2
    (l 0 + l 1 - s1 / 2) * (l 0 - l 1) ^ 2 + (l 0 + l 2 - s1 / 2) * (l 0 - l 2) ^ 2
      + (l 1 + l 2 - s1 / 2) * (l 1 - l 2) ^ 2
      = -(∑ k, ∑ i, ∑ j, ev (F.nablaRic lam k i j) ^ 2) := by
  intro l s1
  have h := congrArg ev H.bochner
  simp only [Frame.gradRic2, kappaSum, Kcurv, map_add, map_sum, map_mul, map_sub, map_pow,
    map_zero, ev_half] at h
  simp only [l, s1, sq]
  linarith

theorem kappa_nonpos (ev : R →+* ℝ) :
    let l := fun i => ev (lam i)
    let s1 := l 0 + l 1 + l 2
    (l 0 + l 1 - s1 / 2) * (l 0 - l 1) ^ 2 + (l 0 + l 2 - s1 / 2) * (l 0 - l 2) ^ 2
      + (l 1 + l 2 - s1 / 2) * (l 1 - l 2) ^ 2 ≤ 0 := by
  intro l s1
  rw [H.kappa_eq_neg_grad ev]
  have : 0 ≤ ∑ k, ∑ i, ∑ j, ev (F.nablaRic lam k i j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

end C2

end CFT.Cartan
