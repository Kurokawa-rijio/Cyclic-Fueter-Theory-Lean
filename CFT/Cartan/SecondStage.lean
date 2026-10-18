/- α-II.5:まとめ。Bj が C2 枠で 0 になること(Bj_frame)。
  本体:SSJet(2 段目の式 n0〜n11、Bj、L0j)、SSFirst(1 段目の解 fs*)、SSRows*(row0〜row11)、SSK(K0〜K3)、SSCoef*(係数の分割) -/
import CFT.Cartan.SSK
import CFT.Cartan.SSCoefBj
import CFT.Cartan.SSRows0
import CFT.Cartan.SSRows1a
import CFT.Cartan.SSRows1b
import CFT.Cartan.SSRows2a
import CFT.Cartan.SSRows2b
import CFT.Cartan.SSRows3

namespace CFT.Cartan

set_option maxHeartbeats 0

variable {R : Type*} [CommRing R] [Algebra ℚ R]

namespace C2

variable {F : Frame R} {lam : Fin 3 → R} (H : C2 F lam)
include H

/-- 任意の C2 枠で Bj = 0:2(λ₀−λ₁)²(λ₀−λ₂)²·Bj = 曲率の構造式 S1212 と 1 段目の解 fs の一次結合 -/
theorem Bj_frame : Bj (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) = 0 := by
  have key : (2 * (lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) ^ 2) * Bj (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) = 0 := by
    have g0 : 1 * (Bj (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) + (cfbj_0 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfbj_0, Bj]
      ring
    have g1 : (cfbj_2 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfbj_3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfbj_4 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (half : R) + (cfbj_5 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfbj_2, cfbj_3, cfbj_4, cfbj_5]
      linear_combination H.S1212
    have g2 : 2 * (half : R) + (-1) * 1 = 0 := by
      linear_combination H.hhf
    have g3 : (cfbj_8 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfbj_9 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfbj_10 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfbj_8, cfbj_9, cfbj_10]
      linear_combination H.fs1be
    have k0 := cfbj_k0 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k1 := cfbj_k1 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k2 := cfbj_k2 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k3 := cfbj_k3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k4 := cfbj_k4 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    linear_combination ((cfbj_1 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g0 + ((cfbj_6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g1 + ((cfbj_7 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g2 + ((cfbj_11 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g3 + 1 * k0 + (Bj (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * k1 + (half : R) * k2 + (F.e 2 (gamma F lam)) * k3 + (F.e 1 (beta F lam)) * k4
  have hU : IsUnit (2 * (lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) ^ 2 : R) := by
    have e : (2 * (lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) ^ 2 : R) = ((2 : R) ^ 1 * (lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) ^ 2 * (lam 1 - lam 2) ^ 0) := by ring
    rw [e]; exact H.unit_prod 1 2 2 0
  exact hU.mul_right_eq_zero.mp key

end C2

end CFT.Cartan
