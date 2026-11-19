import FieldEquations.Characteristic.Dependence
import FieldEquations.SphericalEYM.Uniqueness

/-
# Continuous dependence for the spherically symmetric EYM Goursat problem

`eym_dependence`: for fixed bounds B, m > 0 there is C ≥ 0 such that any two solutions on
[0,a]×[0,b] staying in the box `Good B m` satisfy
  |δr| + |δΩ| + |δW| ≤ C E
whenever their C¹ traces on the edges (values and ∂_u on v = 0, ∂_v on u = 0) differ by at
most E. C depends on B, m, a, b.
-/

open Real Set FieldEquations.SphericalEYM FieldEquations.CharacteristicUniqueness FieldEquations.CharacteristicDependence FieldEquations.EYMUniqueness

namespace FieldEquations.EYMDependence

/-- Lipschitz dependence on the characteristic data for solutions in a fixed box. -/
theorem eym_dependence {a b B m : ℝ} (hm : 0 < m) :
    ∃ C, 0 ≤ C ∧ ∀ (F G : EYMFields) (E : ℝ), 0 ≤ E →
      EYMEqsOn a b F → EYMEqsOn a b G →
      C2On a b F.r → C2On a b F.Om → C2On a b F.W →
      C2On a b G.r → C2On a b G.Om → C2On a b G.W →
      (∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, Good B m (ptOf F u v) ∧ Good B m (ptOf G u v)) →
      (∀ u ∈ Icc (0:ℝ) a, |F.r u 0 - G.r u 0| ≤ E ∧ |F.Om u 0 - G.Om u 0| ≤ E
        ∧ |F.W u 0 - G.W u 0| ≤ E) →
      (∀ u ∈ Icc (0:ℝ) a, |Du F.r u 0 - Du G.r u 0| ≤ E ∧ |Du F.Om u 0 - Du G.Om u 0| ≤ E
        ∧ |Du F.W u 0 - Du G.W u 0| ≤ E) →
      (∀ v ∈ Icc (0:ℝ) b, |Dv F.r 0 v - Dv G.r 0 v| ≤ E ∧ |Dv F.Om 0 v - Dv G.Om 0 v| ≤ E
        ∧ |Dv F.W 0 v - Dv G.W 0 v| ≤ E) →
      ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
        |F.r u v - G.r u v| + |F.Om u v - G.Om u v| + |F.W u v - G.W u v| ≤ C * E := by
  obtain ⟨ΛR, hRn, hR⟩ := UL_rhsR (B := B) hm
  obtain ⟨ΛO, hOn, hO⟩ := UL_rhsOm (B := B) hm
  obtain ⟨ΛW, hWn, hW⟩ := UL_rhsW (B := B) hm
  refine ⟨2 * (3 * 3) * exp ((4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1) * (max a 0 + max b 0)),
    by positivity, ?_⟩
  intro F G E hE eF eG rFr rFO rFW rGr rGO rGW hgood hE1 hE2 hE3 u hu v hv
  have hC : ∀ i, C2Data a b (dd F G i) (ddu F G i) (ddv F G i) (dduv F G i) := by
    intro i
    fin_cases i
    · exact rFr.sub rGr
    · exact rFO.sub rGO
    · exact rFW.sub rGW
  have hpd : ∀ u v, pdist (ptOf F u v) (ptOf G u v)
      ≤ ∑ j, (|dd F G j u v| + |ddu F G j u v| + |ddv F G j u v|) := by
    intro u v
    rw [Fin.sum_univ_three]
    simp only [pdist, ptOf, dd, ddu, ddv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linarith [abs_nonneg (Du F.W u v - Du G.W u v), abs_nonneg (Dv F.W u v - Dv G.W u v)]
  have key := char_dependence (n := 3) (a := a) (b := b) (L := ΛR + ΛO + ΛW) (by linarith) hE
    (dd F G) (ddu F G) (ddv F G) (dduv F G) hC
    (fun i u hu => by
      fin_cases i
      exacts [(hE1 u hu).1, (hE1 u hu).2.1, (hE1 u hu).2.2])
    (fun i u hu => by
      fin_cases i
      exacts [(hE2 u hu).1, (hE2 u hu).2.1, (hE2 u hu).2.2])
    (fun i v hv => by
      fin_cases i
      exacts [(hE3 v hv).1, (hE3 v hv).2.1, (hE3 v hv).2.2])
    (fun i u hu v hv => by
      obtain ⟨gF, gG⟩ := hgood u hu v hv
      have hp := hpd u v
      have lift : ∀ Λ : ℝ, 0 ≤ Λ → Λ ≤ ΛR + ΛO + ΛW →
          Λ * pdist (ptOf F u v) (ptOf G u v)
            ≤ (ΛR + ΛO + ΛW) * ∑ j, (|dd F G j u v| + |ddu F G j u v| + |ddv F G j u v|) :=
        fun Λ h0 h1 => mul_le_mul h1 hp (pdist_nonneg _ _) (by linarith)
      fin_cases i
      · show |Duv F.r u v - Duv G.r u v| ≤ _
        rw [(eF u hu v hv).1, (eG u hu v hv).1]
        exact (hR _ _ gF gG).2.2.trans (lift ΛR hRn (by linarith))
      · show |Duv F.Om u v - Duv G.Om u v| ≤ _
        rw [(eF u hu v hv).2.1, (eG u hu v hv).2.1, (eF u hu v hv).1, (eG u hu v hv).1]
        exact (hO _ _ gF gG).2.2.trans (lift ΛO hOn (by linarith))
      · show |Duv F.W u v - Duv G.W u v| ≤ _
        rw [(eF u hu v hv).2.2, (eG u hu v hv).2.2]
        exact (hW _ _ gF gG).2.2.trans (lift ΛW hWn (by linarith)))
    u hu v hv
  have hsum3 : |F.r u v - G.r u v| + |F.Om u v - G.Om u v| + |F.W u v - G.W u v|
      ≤ ∑ j, (|dd F G j u v| + |ddu F G j u v| + |ddv F G j u v|) := by
    rw [Fin.sum_univ_three]
    simp only [dd, ddu, ddv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linarith [abs_nonneg (Du F.r u v - Du G.r u v), abs_nonneg (Dv F.r u v - Dv G.r u v),
      abs_nonneg (Du F.Om u v - Du G.Om u v), abs_nonneg (Dv F.Om u v - Dv G.Om u v),
      abs_nonneg (Du F.W u v - Du G.W u v), abs_nonneg (Dv F.W u v - Dv G.W u v)]
  have hlam : 0 ≤ 4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1 := by positivity
  have hexp : exp ((4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1) * (u + v))
      ≤ exp ((4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1) * (max a 0 + max b 0)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (add_le_add (hu.2.trans (le_max_left _ _)) (hv.2.trans (le_max_left _ _))) hlam)
  push_cast at key
  calc |F.r u v - G.r u v| + |F.Om u v - G.Om u v| + |F.W u v - G.W u v|
      ≤ 2 * (3 * 3 * E) * exp ((4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1) * (u + v)) :=
        hsum3.trans key
    _ ≤ 2 * (3 * 3 * E) * exp ((4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1) * (max a 0 + max b 0)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * (3 * 3) * exp ((4 * max (3 * (1 + (ΛR + ΛO + ΛW))) 1) * (max a 0 + max b 0)) * E := by
        ring

end FieldEquations.EYMDependence
