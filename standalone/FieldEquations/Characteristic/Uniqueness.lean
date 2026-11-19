import FieldEquations.Characteristic.Gronwall

/-
# Uniqueness for semilinear characteristic (Goursat) problems

`C2Data a b d du dv duv` packages a function d on [0,a]×[0,b] together with its partial
derivatives d_u, d_v and the mixed derivative d_{uv}: all four are continuous on the closed
rectangle, d_u and d_v are derivatives of d, and d_{uv} is the derivative of d_v in u and of
d_u in v. The pure second derivatives d_{uu}, d_{vv} are not required ("mixed C²").
The derivatives are taken as two-sided `HasDerivAt` also at edge points of the rectangle.

`char_uniqueness`: if an ℝⁿ-valued difference d vanishes on the two characteristic edges
u = 0 and v = 0 and |d_{uv}| ≤ L Σ (|d| + |d_u| + |d_v|) on the rectangle, then d ≡ 0.
-/

open Real Set

namespace FieldEquations.CharacteristicUniqueness

/-- A function on [0,a]×[0,b] with continuous first partial derivatives and continuous mixed derivative (pure second derivatives not required). -/
structure C2Data (a b : ℝ) (d du dv duv : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry d) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  cont_u : ContinuousOn (Function.uncurry du) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  cont_v : ContinuousOn (Function.uncurry dv) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  cont_uv : ContinuousOn (Function.uncurry duv) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  deriv_u : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun t => d t v) (du u v) u
  deriv_v : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun s => d u s) (dv u v) v
  deriv_uv_u : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun t => dv t v) (duv u v) u
  deriv_uv_v : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun s => du u s) (duv u v) v

theorem C2Data.sub {a b : ℝ} {d du dv duv d' du' dv' duv' : ℝ → ℝ → ℝ}
    (h : C2Data a b d du dv duv) (h' : C2Data a b d' du' dv' duv') :
    C2Data a b (fun s t => d s t - d' s t) (fun s t => du s t - du' s t)
      (fun s t => dv s t - dv' s t) (fun s t => duv s t - duv' s t) where
  cont := h.cont.sub h'.cont
  cont_u := h.cont_u.sub h'.cont_u
  cont_v := h.cont_v.sub h'.cont_v
  cont_uv := h.cont_uv.sub h'.cont_uv
  deriv_u := fun u hu v hv => (h.deriv_u u hu v hv).sub (h'.deriv_u u hu v hv)
  deriv_v := fun u hu v hv => (h.deriv_v u hu v hv).sub (h'.deriv_v u hu v hv)
  deriv_uv_u := fun u hu v hv => (h.deriv_uv_u u hu v hv).sub (h'.deriv_uv_u u hu v hv)
  deriv_uv_v := fun u hu v hv => (h.deriv_uv_v u hu v hv).sub (h'.deriv_uv_v u hu v hv)

theorem abs_le_integral_abs {g g' : ℝ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : g 0 = 0)
    (hd : ∀ s ∈ Icc (0:ℝ) v, HasDerivAt g (g' s) s) (hc : ContinuousOn g' (Icc (0:ℝ) v)) :
    |g v| ≤ ∫ s in (0:ℝ)..v, |g' s| := by
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by rwa [uIcc_of_le hv] at hs)) (hc.intervalIntegrable_of_Icc hv)
  rw [h0, sub_zero] at e
  rw [← e]
  exact intervalIntegral.abs_integral_le_integral_abs hv

theorem sliceOn1 {F : ℝ → ℝ → ℝ} {a b x : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)) (hx : x ∈ Icc (0:ℝ) a) :
    ContinuousOn (fun s => F x s) (Icc (0:ℝ) b) :=
  hF.comp (continuousOn_const.prod continuousOn_id) (fun _ hs => Set.mk_mem_prod hx hs)

theorem sliceOn2 {F : ℝ → ℝ → ℝ} {a b y : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)) (hy : y ∈ Icc (0:ℝ) b) :
    ContinuousOn (fun t => F t y) (Icc (0:ℝ) a) :=
  hF.comp (continuousOn_id.prod continuousOn_const) (fun _ ht => Set.mk_mem_prod ht hy)

theorem edge_deriv_zero {g : ℝ → ℝ} {g' a x : ℝ} (ha : 0 < a) (hx : x ∈ Icc (0:ℝ) a)
    (h0 : ∀ t ∈ Icc (0:ℝ) a, g t = 0) (hd : HasDerivAt g g' x) : g' = 0 := by
  have h2 : HasDerivWithinAt g 0 (Icc (0:ℝ) a) x :=
    (hasDerivWithinAt_const x (Icc (0:ℝ) a) (0:ℝ)).congr (fun t ht => h0 t ht) (h0 x hx)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc ha x hx) hd.hasDerivWithinAt h2

/-- Uniqueness for semilinear Goursat problems: zero characteristic data and a Lipschitz bound on the mixed derivative force the difference to vanish on the rectangle. -/
theorem char_uniqueness {n : ℕ} {a b L : ℝ} (hL : 0 ≤ L) (d du dv duv : Fin n → ℝ → ℝ → ℝ)
    (hC : ∀ i, C2Data a b (d i) (du i) (dv i) (duv i))
    (hu0 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, d i u 0 = 0) (hv0 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, d i 0 v = 0)
    (hlip : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      |duv i u v| ≤ L * ∑ j, (|d j u v| + |du j u v| + |dv j u v|)) :
    ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, d i u v = 0 := by

  rcases lt_or_le 0 a with ha | ha
  swap
  · intro i u hu v hv
    have : u = 0 := le_antisymm (hu.2.trans ha) hu.1
    subst this
    exact hv0 i v hv
  rcases lt_or_le 0 b with hb | hb
  swap
  · intro i u hu v hv
    have : v = 0 := le_antisymm (hv.2.trans hb) hv.1
    subst this
    exact hu0 i u hu
  have hb0 : (0:ℝ) ∈ Icc (0:ℝ) b := ⟨le_rfl, hb.le⟩
  have ha0 : (0:ℝ) ∈ Icc (0:ℝ) a := ⟨le_rfl, ha.le⟩

  have hDu0 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, du i u 0 = 0 := fun i u hu =>
    edge_deriv_zero ha hu (hu0 i) ((hC i).deriv_u u hu 0 hb0)
  have hDv0 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, dv i 0 v = 0 := fun i v hv =>
    edge_deriv_zero hb hv (hv0 i) ((hC i).deriv_v 0 ha0 v hv)
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
      f u v ≤ (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
    intro u hu v hv
    have I1nn : 0 ≤ ∫ s in (0:ℝ)..v, f u s :=
      intervalIntegral.integral_nonneg hv.1 (fun s _ => hfnn u s)
    have I2nn : 0 ≤ ∫ t in (0:ℝ)..u, f t v :=
      intervalIntegral.integral_nonneg hu.1 (fun t _ => hfnn t v)
    have subv : Icc (0:ℝ) v ⊆ Icc (0:ℝ) b := Icc_subset_Icc le_rfl hv.2
    have subu : Icc (0:ℝ) u ⊆ Icc (0:ℝ) a := Icc_subset_Icc le_rfl hu.2
    have hfs : ContinuousOn (fun s => f u s) (Icc (0:ℝ) v) := (sliceOn1 hf hu).mono subv
    have hft : ContinuousOn (fun t => f t v) (Icc (0:ℝ) u) := (sliceOn2 hf hv).mono subu
    have hj : ∀ j, A j u v ≤ (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
      intro j

      have c1 : ContinuousOn (fun s => dv j u s) (Icc (0:ℝ) v) :=
        (sliceOn1 (hC j).cont_v hu).mono subv
      have b1 : |d j u v| ≤ ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_integral_abs hv.1 (hu0 j u hu)
          (fun s hs => (hC j).deriv_v u hu s (subv hs)) c1).trans ?_
        exact intervalIntegral.integral_mono_on hv.1 (c1.abs.intervalIntegrable_of_Icc hv.1)
          (hfs.intervalIntegrable_of_Icc hv.1)
          (fun s _ => by
            have h1 : |dv j u s| ≤ A j u s := by
              show |dv j u s| ≤ |d j u s| + |du j u s| + |dv j u s|
              have := abs_nonneg (d j u s); have := abs_nonneg (du j u s); linarith
            exact h1.trans (hAf j u s))

      have c2 : ContinuousOn (fun s => duv j u s) (Icc (0:ℝ) v) :=
        (sliceOn1 (hC j).cont_uv hu).mono subv
      have b2 : |du j u v| ≤ L * ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_integral_abs hv.1 (hDu0 j u hu)
          (fun s hs => (hC j).deriv_uv_v u hu s (subv hs)) c2).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hv.1 (c2.abs.intervalIntegrable_of_Icc hv.1)
          ((continuousOn_const.mul hfs).intervalIntegrable_of_Icc hv.1)
          (fun s hs => hlip j u hu s (subv hs))

      have c3 : ContinuousOn (fun t => duv j t v) (Icc (0:ℝ) u) :=
        (sliceOn2 (hC j).cont_uv hv).mono subu
      have b3 : |dv j u v| ≤ L * ∫ t in (0:ℝ)..u, f t v := by
        refine (abs_le_integral_abs hu.1 (hDv0 j v hv)
          (fun t ht => (hC j).deriv_uv_u t (subu ht) v hv) c3).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hu.1 (c3.abs.intervalIntegrable_of_Icc hu.1)
          ((continuousOn_const.mul hft).intervalIntegrable_of_Icc hu.1)
          (fun t ht => hlip j t (subu ht) v hv)
      show |d j u v| + |du j u v| + |dv j u v|
        ≤ (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)
      nlinarith [mul_nonneg hL I1nn, mul_nonneg hL I2nn]
    calc f u v = ∑ j, A j u v := rfl
      _ ≤ ∑ _j : Fin n, (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) :=
          Finset.sum_le_sum (fun j _ => hj j)
      _ = (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hzero := FieldEquations.CharacteristicGronwall.char_gronwall_on hf (fun u _ v _ => hfnn u v) hK
  intro i u hu v hv
  have h0 : f u v = 0 := hzero u hu v hv
  have hAi : A i u v = 0 := le_antisymm (h0 ▸ hAf i u v) (hAnn i u v)
  have : |d i u v| + |du i u v| + |dv i u v| = 0 := hAi
  have h1 := abs_nonneg (du i u v)
  have h2 := abs_nonneg (dv i u v)
  exact abs_eq_zero.mp (by linarith [abs_nonneg (d i u v)])

end FieldEquations.CharacteristicUniqueness
