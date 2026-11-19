import FieldEquations.Characteristic.Uniqueness

/-
# Continuous dependence for semilinear Goursat problems

`char_gronwall_inhom` is the inhomogeneous characteristic Grönwall inequality
(f ≤ D + K(∫ + ∫) gives f ≤ 2D e^{4 max(K,1)(u+v)}). `char_dependence` bounds a difference
of two solutions on the rectangle by its C¹ traces on the characteristic edges
(values and u-derivative on v = 0, v-derivative on u = 0).
-/

open Real Set
open FieldEquations.CharacteristicUniqueness FieldEquations.CharacteristicGronwall

namespace FieldEquations.CharacteristicDependence

theorem char_gronwall_inhom {a b K D : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)) (hD : 0 ≤ D)
    (hnn : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, 0 ≤ f u v)
    (hK : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      f u v ≤ D + K * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, f u v ≤ 2 * D * exp ((4 * max K 1) * (u + v)) := by
  intro u hu v hv
  have hc1 : ∀ x ∈ Icc (0:ℝ) a, ContinuousOn (fun s => f x s) (Icc (0:ℝ) b) := fun x hx =>
    hf.comp (continuousOn_const.prod continuousOn_id) (fun s hs => Set.mk_mem_prod hx hs)
  have hc2 : ∀ y ∈ Icc (0:ℝ) b, ContinuousOn (fun t => f t y) (Icc (0:ℝ) a) := fun y hy =>
    hf.comp (continuousOn_id.prod continuousOn_const) (fun t ht => Set.mk_mem_prod ht hy)

  have hint1 : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b, 0 ≤ ∫ s in (0:ℝ)..y, f x s :=
    fun x hx y hy => intervalIntegral.integral_nonneg hy.1
      (fun s hs => hnn x hx s ⟨hs.1, hs.2.trans hy.2⟩)
  have hint2 : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b, 0 ≤ ∫ t in (0:ℝ)..x, f t y :=
    fun x hx y hy => intervalIntegral.integral_nonneg hx.1
      (fun t ht => hnn t ⟨ht.1, ht.2.trans hx.2⟩ y hy)
  have hK'pos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK2 : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b,
      f x y ≤ D + max K 1 * ((∫ s in (0:ℝ)..y, f x s) + ∫ t in (0:ℝ)..x, f t y) :=
    fun x hx y hy => (hK x hx y hy).trans (add_le_add_left (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (add_nonneg (hint1 x hx y hy) (hint2 x hx y hy))) D)

  have hlpos : 0 < 4 * max K 1 := by positivity
  let g : ℝ × ℝ → ℝ := fun p => exp (-((4 * max K 1) * (p.1 + p.2))) * Function.uncurry f p
  have hg : ContinuousOn g (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.add continuous_snd)).neg).continuousOn.mul hf
  have hR : IsCompact (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b).Nonempty := ⟨(u, v), hu, hv⟩
  obtain ⟨p, hp, hmax⟩ := hR.exists_isMaxOn hne hg
  have hmax' : ∀ q ∈ Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b, g q ≤ g p := fun q hq => isMaxOn_iff.mp hmax q hq
  obtain ⟨hp1, hp2⟩ := hp
  have hgq : ∀ x y, g (x, y) = exp (-((4 * max K 1) * (x + y))) * f x y := fun x y => rfl
  have hN0 : 0 ≤ g p := by
    have h0 : 0 ≤ g (u, v) := by
      rw [hgq]
      exact mul_nonneg (Real.exp_pos _).le (hnn u hu v hv)
    exact h0.trans (hmax' (u, v) ⟨hu, hv⟩)

  have hbound : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b,
      f x y ≤ g p * exp ((4 * max K 1) * (x + y)) := by
    intro x hx y hy
    have h := hmax' (x, y) ⟨hx, hy⟩
    rw [hgq] at h
    have hE := Real.exp_pos ((4 * max K 1) * (x + y))
    have hinv : exp (-((4 * max K 1) * (x + y))) * exp ((4 * max K 1) * (x + y)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc f x y = (exp (-((4 * max K 1) * (x + y))) * f x y) * exp ((4 * max K 1) * (x + y)) := by
          rw [mul_comm (exp _) (f x y), mul_assoc, hinv, mul_one]
      _ ≤ g p * exp ((4 * max K 1) * (x + y)) := mul_le_mul_of_nonneg_right h hE.le
  have hcont_e : ∀ c : ℝ, Continuous (fun s => g p * exp ((4 * max K 1) * (c + s))) := fun c =>
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.add continuous_id)))

  have hI1 : ∫ s in (0:ℝ)..p.2, f p.1 s
      ≤ g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) := by
    calc ∫ s in (0:ℝ)..p.2, f p.1 s
        ≤ ∫ s in (0:ℝ)..p.2, g p * exp ((4 * max K 1) * (p.1 + s)) :=
          intervalIntegral.integral_mono_on hp2.1 (((hc1 p.1 hp1).mono (Icc_subset_Icc le_rfl hp2.2)).intervalIntegrable_of_Icc hp2.1)
            ((hcont_e p.1).intervalIntegrable _ _)
            (fun s hs => hbound p.1 hp1 s ⟨hs.1, hs.2.trans hp2.2⟩)
      _ = g p * ∫ s in (0:ℝ)..p.2, exp ((4 * max K 1) * (p.1 + s)) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) :=
          mul_le_mul_of_nonneg_left (exp_int_le _ p.1 p.2 hlpos) hN0
  have hI2 : ∫ t in (0:ℝ)..p.1, f t p.2
      ≤ g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) := by
    calc ∫ t in (0:ℝ)..p.1, f t p.2
        ≤ ∫ t in (0:ℝ)..p.1, g p * exp ((4 * max K 1) * (p.2 + t)) :=
          intervalIntegral.integral_mono_on hp1.1 (((hc2 p.2 hp2).mono (Icc_subset_Icc le_rfl hp1.2)).intervalIntegrable_of_Icc hp1.1)
            ((hcont_e p.2).intervalIntegrable _ _)
            (fun t ht => by
              have h := hbound t ⟨ht.1, ht.2.trans hp1.2⟩ p.2 hp2
              rwa [add_comm t p.2] at h)
      _ = g p * ∫ t in (0:ℝ)..p.1, exp ((4 * max K 1) * (p.2 + t)) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ g p * (exp ((4 * max K 1) * (p.2 + p.1)) / (4 * max K 1)) :=
          mul_le_mul_of_nonneg_left (exp_int_le _ p.2 p.1 hlpos) hN0
      _ = g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) := by rw [add_comm p.2 p.1]

  have hfp : f p.1 p.2 = g p * exp ((4 * max K 1) * (p.1 + p.2)) := by
    have hinv : exp (-((4 * max K 1) * (p.1 + p.2))) * exp ((4 * max K 1) * (p.1 + p.2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hgp : g p = exp (-((4 * max K 1) * (p.1 + p.2))) * f p.1 p.2 := rfl
    rw [hgp, mul_comm (exp _) (f p.1 p.2), mul_assoc, hinv, mul_one]
  have hmain : g p * exp ((4 * max K 1) * (p.1 + p.2))
      ≤ D + max K 1 * (g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1))
        + g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1))) := by
    rw [← hfp]
    exact (hK2 p.1 hp1 p.2 hp2).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add hI1 hI2) hK'pos.le) D)
  have hsimp : max K 1 * (g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1))
        + g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)))
      = g p * exp ((4 * max K 1) * (p.1 + p.2)) / 2 := by
    have hne' : max K 1 ≠ 0 := hK'pos.ne'
    field_simp
    ring
  have hNE : g p * exp ((4 * max K 1) * (p.1 + p.2)) ≤ 2 * D := by linarith
  have hE1 : 1 ≤ exp ((4 * max K 1) * (p.1 + p.2)) :=
    Real.one_le_exp (mul_nonneg hlpos.le (add_nonneg hp1.1 hp2.1))
  have hNp : g p ≤ 2 * D := (le_mul_of_one_le_right hN0 hE1).trans hNE

  exact (hbound u hu v hv).trans (mul_le_mul_of_nonneg_right hNp (Real.exp_pos _).le)

theorem abs_le_add_integral_abs {g g' : ℝ → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hd : ∀ s ∈ Icc (0:ℝ) v, HasDerivAt g (g' s) s) (hc : ContinuousOn g' (Icc (0:ℝ) v)) :
    |g v| ≤ |g 0| + ∫ s in (0:ℝ)..v, |g' s| := by
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by rwa [uIcc_of_le hv] at hs)) (hc.intervalIntegrable_of_Icc hv)
  have h1 : g v = g 0 + ∫ s in (0:ℝ)..v, g' s := by rw [e]; ring
  rw [h1]
  exact (abs_add _ _).trans (add_le_add_left (intervalIntegral.abs_integral_le_integral_abs hv) _)

/-- Continuous dependence on the characteristic data: the C¹ size of a difference is bounded by its edge traces times an explicit exponential. -/
theorem char_dependence {n : ℕ} {a b L E : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E)
    (d du dv duv : Fin n → ℝ → ℝ → ℝ)
    (hC : ∀ i, C2Data a b (d i) (du i) (dv i) (duv i))
    (hE1 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, |d i u 0| ≤ E)
    (hE2 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, |du i u 0| ≤ E)
    (hE3 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, |dv i 0 v| ≤ E)
    (hlip : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      |duv i u v| ≤ L * ∑ j, (|d j u v| + |du j u v| + |dv j u v|)) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      ∑ j, (|d j u v| + |du j u v| + |dv j u v|)
        ≤ 2 * (3 * n * E) * exp ((4 * max (n * (1 + L)) 1) * (u + v)) := by
  let A : Fin n → ℝ → ℝ → ℝ := fun j u v => |d j u v| + |du j u v| + |dv j u v|
  let f : ℝ → ℝ → ℝ := fun u v => ∑ j, A j u v
  have hA : ∀ j, ContinuousOn (Function.uncurry (A j)) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := fun j =>
    (((hC j).cont.abs).add ((hC j).cont_u.abs)).add ((hC j).cont_v.abs)
  have hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := by
    have : Function.uncurry f = fun p => ∑ j, Function.uncurry (A j) p := rfl
    rw [this]
    exact continuousOn_finset_sum _ (fun j _ => hA j)
  have hAnn : ∀ j u v, 0 ≤ A j u v := fun j u v => by
    show 0 ≤ |d j u v| + |du j u v| + |dv j u v|
    positivity
  have hfnn : ∀ u v, 0 ≤ f u v := fun u v => Finset.sum_nonneg (fun j _ => hAnn j u v)
  have hAf : ∀ j u v, A j u v ≤ f u v := fun j u v =>
    Finset.single_le_sum (fun k _ => hAnn k u v) (Finset.mem_univ j)
  have hK : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      f u v ≤ 3 * n * E + (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
    intro u hu v hv
    have I1nn : 0 ≤ ∫ s in (0:ℝ)..v, f u s :=
      intervalIntegral.integral_nonneg hv.1 (fun s _ => hfnn u s)
    have I2nn : 0 ≤ ∫ t in (0:ℝ)..u, f t v :=
      intervalIntegral.integral_nonneg hu.1 (fun t _ => hfnn t v)
    have subv : Icc (0:ℝ) v ⊆ Icc (0:ℝ) b := Icc_subset_Icc le_rfl hv.2
    have subu : Icc (0:ℝ) u ⊆ Icc (0:ℝ) a := Icc_subset_Icc le_rfl hu.2
    have hfs : ContinuousOn (fun s => f u s) (Icc (0:ℝ) v) := (sliceOn1 hf hu).mono subv
    have hft : ContinuousOn (fun t => f t v) (Icc (0:ℝ) u) := (sliceOn2 hf hv).mono subu
    have hj : ∀ j, A j u v
        ≤ 3 * E + (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
      intro j
      have c1 : ContinuousOn (fun s => dv j u s) (Icc (0:ℝ) v) :=
        (sliceOn1 (hC j).cont_v hu).mono subv
      have b1 : |d j u v| ≤ E + ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_add_integral_abs hv.1
          (fun s hs => (hC j).deriv_v u hu s (subv hs)) c1).trans (add_le_add (hE1 j u hu) ?_)
        exact intervalIntegral.integral_mono_on hv.1 (c1.abs.intervalIntegrable_of_Icc hv.1)
          (hfs.intervalIntegrable_of_Icc hv.1)
          (fun s _ => by
            have h1 : |dv j u s| ≤ A j u s := by
              show |dv j u s| ≤ |d j u s| + |du j u s| + |dv j u s|
              have := abs_nonneg (d j u s); have := abs_nonneg (du j u s); linarith
            exact h1.trans (hAf j u s))
      have c2 : ContinuousOn (fun s => duv j u s) (Icc (0:ℝ) v) :=
        (sliceOn1 (hC j).cont_uv hu).mono subv
      have b2 : |du j u v| ≤ E + L * ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_add_integral_abs hv.1
          (fun s hs => (hC j).deriv_uv_v u hu s (subv hs)) c2).trans (add_le_add (hE2 j u hu) ?_)
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hv.1 (c2.abs.intervalIntegrable_of_Icc hv.1)
          ((continuousOn_const.mul hfs).intervalIntegrable_of_Icc hv.1)
          (fun s hs => hlip j u hu s (subv hs))
      have c3 : ContinuousOn (fun t => duv j t v) (Icc (0:ℝ) u) :=
        (sliceOn2 (hC j).cont_uv hv).mono subu
      have b3 : |dv j u v| ≤ E + L * ∫ t in (0:ℝ)..u, f t v := by
        refine (abs_le_add_integral_abs hu.1
          (fun t ht => (hC j).deriv_uv_u t (subu ht) v hv) c3).trans (add_le_add (hE3 j v hv) ?_)
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hu.1 (c3.abs.intervalIntegrable_of_Icc hu.1)
          ((continuousOn_const.mul hft).intervalIntegrable_of_Icc hu.1)
          (fun t ht => hlip j t (subu ht) v hv)
      show |d j u v| + |du j u v| + |dv j u v|
        ≤ 3 * E + (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)
      nlinarith [mul_nonneg hL I1nn, mul_nonneg hL I2nn]
    calc f u v = ∑ j, A j u v := rfl
      _ ≤ ∑ _j : Fin n, (3 * E + (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)) :=
          Finset.sum_le_sum (fun j _ => hj j)
      _ = 3 * n * E + (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hD : 0 ≤ 3 * (n : ℝ) * E := by positivity
  exact char_gronwall_inhom hf hD (fun u _ v _ => hfnn u v) hK

end FieldEquations.CharacteristicDependence
