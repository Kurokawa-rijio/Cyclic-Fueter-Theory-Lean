/-
  α-IX.4:SU(2) = Q の Yang–Mills の第一変分(非可換の電気の側)

  F^a_{μν} = ∂_μA^a_ν − ∂_νA^a_μ + ε^{abc}A^b_μA^c_ν(構造定数は四元数の交換子、段階 1 の su_two_bracket)。
  L = −¼ Σ_a F^a_{μν}F^{aμν} + Σ J^{aν}A^a_ν について
    δL = Σ δA^a_ν (D_μF^{aμν} + J^{aν}) − ∂_μ(Σ F^{aμν}δA^a_ν)、 D_μF^{aμν} = ∂_μF^{aμν} + ε^{abc}A^b_μF^{cμν}
  (等式)。EL の式は D_μF^{μν} = −J^ν(非可換の Gauss・Ampère)。
  U(1) ⊂ SU(2) への射影(A^b = 0、b ≠ 0)では a = 0 の成分が α-IX.1 の Maxwell の式になる(u1_projection)。
  証明は手計算の順:δF = ∇δA − ∇δA(dF_cov)、反対称性(antisym_sum)、Leibniz、構造定数の付け替え(relabel)。
-/
import CFT.AlphaIX_Classical
import CFT.AlphaS1_Derivation

namespace CFT.IXYM

open CFT.Classical

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]
variable (D : Fin 4 → Derivation ℤ S S) (δ : Derivation ℤ S S) (A J : Fin 3 → Fin 4 → S)

def Fa (a : Fin 3) (μ ν : Fin 4) : S := CFT.S1.F D A a μ ν
def Fau (a : Fin 3) (μ ν : Fin 4) : S := CFT.Classical.eta μ * CFT.Classical.eta ν * Fa D A a μ ν

def LagYM : S := -(1/4 : S) * ∑ a, ∑ μ, ∑ ν, Fau D A a μ ν * Fa D A a μ ν + ∑ a, ∑ ν, J a ν * A a ν

def ELYM (a : Fin 3) (ν : Fin 4) : S :=
  ∑ μ, (D μ (Fau D A a μ ν) + ∑ b, ∑ c, CFT.S1.f3 a b c * A b μ * Fau D A c μ ν) + J a ν

/-- 変分の共変微分 (∇_μ X)^a_ν = ∂_μX^a_ν + ε^{abc}A^b_μX^c_ν -/
def Cov (X : Fin 3 → Fin 4 → S) (a : Fin 3) (μ ν : Fin 4) : S :=
  D μ (X a ν) + ∑ b, ∑ c, CFT.S1.f3 a b c * A b μ * X c ν

/-- 補題 A:δF^a_{μν} = (∇_μ δA)^a_ν − (∇_ν δA)^a_μ -/
theorem dF_cov (hδ : ∀ μ x, δ (D μ x) = D μ (δ x)) (a : Fin 3) (μ ν : Fin 4) :
    δ (Fa D A a μ ν) = Cov D A (fun b ρ => δ (A b ρ)) a μ ν - Cov D A (fun b ρ => δ (A b ρ)) a ν μ := by
  fin_cases a <;>
  simp [Fa, CFT.S1.F, Cov, CFT.S1.f3, Fin.sum_univ_three, map_add, map_sub, Derivation.leibniz, smul_eq_mul, hδ] <;>
  ring

/-- 反対称性 F^a_{νμ} = −F^a_{μν} -/
theorem Fa_antisym (a : Fin 3) (μ ν : Fin 4) : Fa D A a ν μ = -Fa D A a μ ν := by
  fin_cases a <;> simp [Fa, CFT.S1.F, CFT.S1.f3, Fin.sum_univ_three] <;> ring

theorem Fau_antisym (a : Fin 3) (μ ν : Fin 4) : Fau D A a ν μ = -Fau D A a μ ν := by
  simp only [Fau, Fa_antisym D A a μ ν]; ring

/-- 補題 C:Σ_{μν} F^{μν}(X_{μν} − X_{νμ}) = 2Σ F^{μν}X_{μν} -/
theorem antisym_sum (a : Fin 3) (X : Fin 4 → Fin 4 → S) :
    ∑ μ, ∑ ν, Fau D A a μ ν * (X μ ν - X ν μ) = 2 * ∑ μ, ∑ ν, Fau D A a μ ν * X μ ν := by
  have h : ∑ μ, ∑ ν, Fau D A a μ ν * X ν μ = -∑ μ, ∑ ν, Fau D A a μ ν * X μ ν := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Fau_antisym D A a ν μ]; ring
  simp only [mul_sub, Finset.sum_sub_distrib, h]; ring

/-- 補題 E:構造定数の付け替え Σ_{abc} ε^{abc}F^a A^b X^c = −Σ_{abc} ε^{abc}X^a A^b F^c -/
theorem relabel (Fv Av Xv : Fin 3 → S) :
    ∑ a, Fv a * ∑ b, ∑ c, CFT.S1.f3 a b c * Av b * Xv c
      = -∑ a, Xv a * ∑ b, ∑ c, CFT.S1.f3 a b c * Av b * Fv c := by
  simp [CFT.S1.f3, Fin.sum_univ_three]; ring

theorem Fau_diag (a : Fin 3) (μ : Fin 4) : Fau D A a μ μ = 0 := by
  have h := Fau_antisym D A a μ μ
  have : (2 : S) * Fau D A a μ μ = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

theorem ym_first_variation (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (hδ : ∀ μ x, δ (D μ x) = D μ (δ x))
    (hJ : ∀ a ν, δ (J a ν) = 0) :
    δ (LagYM D A J) = ∑ a, ∑ ν, δ (A a ν) * ELYM D A J a ν
      - ∑ μ, D μ (∑ a, ∑ ν, Fau D A a μ ν * δ (A a ν)) := by
  have h4 := d_quarter δ
  have hterm : ∀ a μ ν, δ (Fau D A a μ ν * Fa D A a μ ν) = 2 * (Fau D A a μ ν * δ (Fa D A a μ ν)) := by
    intro a μ ν
    simp only [Fau, Derivation.leibniz, smul_eq_mul, eta_const' δ]; ring
  have hB : δ (LagYM D A J) = -(1/2 : S) * ∑ a, ∑ μ, ∑ ν, Fau D A a μ ν * δ (Fa D A a μ ν)
      + ∑ a, ∑ ν, J a ν * δ (A a ν) := by
    have h4' : δ (-1/4 : S) = 0 := by rw [show (-1/4 : S) = -(1/4) by ring, map_neg, h4, neg_zero]
    simp only [LagYM, map_add, map_neg, Derivation.leibniz, smul_eq_mul, h4, h4', map_sum, hterm, hJ, neg_zero, mul_zero, add_zero]
    simp only [← Finset.mul_sum]; ring
  rw [hB]
  simp only [dF_cov D δ A hδ]
  have a10 := fun a => Fau_antisym D A a 0 1
  have a20 := fun a => Fau_antisym D A a 0 2
  have a30 := fun a => Fau_antisym D A a 0 3
  have a21 := fun a => Fau_antisym D A a 1 2
  have a31 := fun a => Fau_antisym D A a 1 3
  have a32 := fun a => Fau_antisym D A a 2 3
  have dg := Fau_diag D A
  simp (config := {decide := true}) only [Cov, ELYM, Fin.sum_univ_four, Fin.sum_univ_three, CFT.S1.f3,
    map_add, map_sub, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, a10, a20, a30, a21, a31, a32, dg,
    if_true, if_false, Fin.isValue, mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero]
  ring

/-- U(1) ⊂ SU(2) への射影:A² = A³ = 0、J² = J³ = 0 なら a = 0 成分の EL の式は Maxwell の EL の式 -/
theorem u1_projection (h1 : ∀ μ, A 1 μ = 0) (h2 : ∀ μ, A 2 μ = 0) (ν : Fin 4) :
    ELYM D A J 0 ν = CFT.Classical.EL D (A 0) (J 0) ν := by
  simp (config := {decide := true}) only [ELYM, CFT.Classical.EL, Fau, Fa, CFT.S1.F, CFT.Classical.Fu,
    CFT.Classical.F, CFT.S1.f3, Fin.sum_univ_three, h1, h2, if_true, if_false, Fin.isValue,
    mul_zero, zero_mul, add_zero, zero_add, Finset.sum_const_zero]

end CFT.IXYM
