import FieldEquations.Characteristic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.CompactConvergence

/-
# Existence for semilinear Goursat problems

For a system w_{uv} = F(w, w_u, w_v) with values in ℝⁿ, F globally Lipschitz
(constant L, sum norm) and C¹ characteristic data φ on {v = 0}, ψ on {u = 0} with φ(0) = ψ(0),
`goursat_exists` gives a solution on [0,a]×[0,b] with continuous first and mixed derivatives
that attains the data. The unknown is the mixed derivative w_{uv}; the solution is recovered
from it by the integral representation
  w(u,v) = φ(u) + ψ(v) − φ(0) + ∫₀^u ∫₀^v w_{uv}.
The fixed point is obtained from the Banach fixed-point theorem (`ContractingWith`) in
C(R, ℝ)ⁿ with the weighted sup norm sup e^{−λ(u+v)} |·| for large λ.
-/

open Real Set MeasureTheory Filter Topology
open FieldEquations.CharacteristicUniqueness

namespace FieldEquations.Goursat

noncomputable def primV (f : ℝ → ℝ → ℝ) (t v : ℝ) : ℝ := ∫ s in (0:ℝ)..v, f t s

noncomputable def primU (f : ℝ → ℝ → ℝ) (u s : ℝ) : ℝ := ∫ t in (0:ℝ)..u, f t s

noncomputable def primUV (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := primU (primV f)

theorem slice_v {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) (t : ℝ) :
    Continuous fun s => f t s :=
  hf.comp (continuous_const.prod_mk continuous_id)

theorem slice_u {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) (s : ℝ) :
    Continuous fun t => f t s :=
  hf.comp (continuous_id.prod_mk continuous_const)

theorem primV_cont {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry (primV f)) :=
  intervalIntegral.continuous_parametric_primitive_of_continuous (a₀ := 0) hf

theorem primU_cont {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry (primU f)) := by
  have h : Continuous (Function.uncurry (fun (x : ℝ × ℝ) (t : ℝ) => f t x.2)) :=
    hf.comp (continuous_snd.prod_mk (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) h
    continuous_fst

theorem primUV_cont {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry (primUV f)) :=
  primU_cont (primV_cont hf)

theorem primV_deriv {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) (t v : ℝ) :
    HasDerivAt (fun s => primV f t s) (f t v) v :=
  ((slice_v hf t).integral_hasStrictDerivAt 0 v).hasDerivAt

theorem primU_deriv {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) (s u : ℝ) :
    HasDerivAt (fun t => primU f t s) (f u s) u :=
  ((slice_u hf s).integral_hasStrictDerivAt 0 u).hasDerivAt

theorem primUV_deriv_u {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) (u v : ℝ) :
    HasDerivAt (fun t => primUV f t v) (primV f u v) u :=
  primU_deriv (primV_cont hf) v u

theorem primUV_deriv_v {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) (u v : ℝ) :
    HasDerivAt (fun s => primUV f u s) (primU f u v) v := by
  have hP := primV_cont hf
  obtain ⟨M, hM⟩ := (isCompact_uIcc.prod (isCompact_closedBall v 1)).exists_bound_of_continuousOn
    (s := uIcc 0 u ×ˢ Metric.closedBall v 1) hf.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := u) (F := fun x t => primV f t x) (F' := fun x t => f t x)
    (x₀ := v) (bound := fun _ => M) zero_lt_one
    (Eventually.of_forall (fun x => (slice_u hP x).aestronglyMeasurable))
    ((slice_u hP v).intervalIntegrable _ _)
    ((slice_u hf v).aestronglyMeasurable)
    (ae_of_all _ (fun t ht x hx => by
      have := hM (t, x) (Set.mk_mem_prod (uIoc_subset_uIcc ht) (Metric.ball_subset_closedBall hx))
      exact this))
    intervalIntegrable_const
    (ae_of_all _ (fun t _ x _ => primV_deriv hf t x))
  exact key.2

theorem primUV_zero_right (f : ℝ → ℝ → ℝ) (u : ℝ) : primUV f u 0 = 0 := by
  simp [primUV, primU, primV]

theorem primUV_zero_left (f : ℝ → ℝ → ℝ) (v : ℝ) : primUV f 0 v = 0 := by
  simp [primUV, primU]

theorem primV_sub {f1 f2 : ℝ → ℝ → ℝ} (h1 : Continuous (Function.uncurry f1))
    (h2 : Continuous (Function.uncurry f2)) (u v : ℝ) :
    primV f1 u v - primV f2 u v = primV (fun t s => f1 t s - f2 t s) u v :=
  (intervalIntegral.integral_sub ((slice_v h1 u).intervalIntegrable _ _)
    ((slice_v h2 u).intervalIntegrable _ _)).symm

theorem primU_sub {f1 f2 : ℝ → ℝ → ℝ} (h1 : Continuous (Function.uncurry f1))
    (h2 : Continuous (Function.uncurry f2)) (u v : ℝ) :
    primU f1 u v - primU f2 u v = primU (fun t s => f1 t s - f2 t s) u v :=
  (intervalIntegral.integral_sub ((slice_u h1 v).intervalIntegrable _ _)
    ((slice_u h2 v).intervalIntegrable _ _)).symm

theorem primUV_sub {f1 f2 : ℝ → ℝ → ℝ} (h1 : Continuous (Function.uncurry f1))
    (h2 : Continuous (Function.uncurry f2)) (u v : ℝ) :
    primUV f1 u v - primUV f2 u v = primUV (fun t s => f1 t s - f2 t s) u v := by
  unfold primUV
  rw [primU_sub (primV_cont h1) (primV_cont h2)]
  have e : (fun t s => primV f1 t s - primV f2 t s) = primV (fun t s => f1 t s - f2 t s) := by
    funext t s
    exact primV_sub h1 h2 t s
  rw [e]

theorem exp_cont_aux (lam c : ℝ) (M : ℝ) : Continuous fun s : ℝ => M * exp (lam * (c + s)) :=
  continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.add continuous_id)))

theorem primV_bound {f : ℝ → ℝ → ℝ} {lam M u v : ℝ} (hl : 0 < lam) (hM : 0 ≤ M) (hv : 0 ≤ v)
    (hc : Continuous fun s => f u s)
    (hb : ∀ s ∈ Icc (0:ℝ) v, |f u s| ≤ M * exp (lam * (u + s))) :
    |primV f u v| ≤ M * exp (lam * (u + v)) / lam := by
  calc |primV f u v| ≤ ∫ s in (0:ℝ)..v, |f u s| :=
        intervalIntegral.abs_integral_le_integral_abs hv
    _ ≤ ∫ s in (0:ℝ)..v, M * exp (lam * (u + s)) :=
        intervalIntegral.integral_mono_on hv (hc.abs.intervalIntegrable _ _)
          ((exp_cont_aux lam u M).intervalIntegrable _ _) hb
    _ = M * ∫ s in (0:ℝ)..v, exp (lam * (u + s)) := intervalIntegral.integral_const_mul _ _
    _ ≤ M * (exp (lam * (u + v)) / lam) :=
        mul_le_mul_of_nonneg_left (FieldEquations.CharacteristicGronwall.exp_int_le lam u v hl) hM
    _ = M * exp (lam * (u + v)) / lam := by ring

theorem primU_bound {f : ℝ → ℝ → ℝ} {lam M u v : ℝ} (hl : 0 < lam) (hM : 0 ≤ M) (hu : 0 ≤ u)
    (hc : Continuous fun t => f t v)
    (hb : ∀ t ∈ Icc (0:ℝ) u, |f t v| ≤ M * exp (lam * (t + v))) :
    |primU f u v| ≤ M * exp (lam * (u + v)) / lam := by
  calc |primU f u v| ≤ ∫ t in (0:ℝ)..u, |f t v| :=
        intervalIntegral.abs_integral_le_integral_abs hu
    _ ≤ ∫ t in (0:ℝ)..u, M * exp (lam * (v + t)) :=
        intervalIntegral.integral_mono_on hu (hc.abs.intervalIntegrable _ _)
          ((exp_cont_aux lam v M).intervalIntegrable _ _)
          (fun t ht => by rw [add_comm v t]; exact hb t ht)
    _ = M * ∫ t in (0:ℝ)..u, exp (lam * (v + t)) := intervalIntegral.integral_const_mul _ _
    _ ≤ M * (exp (lam * (v + u)) / lam) :=
        mul_le_mul_of_nonneg_left (FieldEquations.CharacteristicGronwall.exp_int_le lam v u hl) hM
    _ = M * exp (lam * (u + v)) / lam := by rw [add_comm v u]; ring

theorem primUV_bound {f : ℝ → ℝ → ℝ} {lam M u v : ℝ} (hl : 0 < lam) (hM : 0 ≤ M) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hf : Continuous (Function.uncurry f))
    (hb : ∀ t ∈ Icc (0:ℝ) u, ∀ s ∈ Icc (0:ℝ) v, |f t s| ≤ M * exp (lam * (t + s))) :
    |primUV f u v| ≤ M * exp (lam * (u + v)) / lam / lam := by
  have h := primU_bound (f := primV f) (M := M / lam) hl (div_nonneg hM hl.le) hu
    (slice_u (primV_cont hf) v)
    (fun t ht => by
      have := primV_bound hl hM hv (slice_v hf t) (fun s hs => hb t ht s hs)
      calc |primV f t v| ≤ M * exp (lam * (t + v)) / lam := this
        _ = M / lam * exp (lam * (t + v)) := by ring)
  calc |primUV f u v| = |primU (primV f) u v| := rfl
    _ ≤ M / lam * exp (lam * (u + v)) / lam := h
    _ = M * exp (lam * (u + v)) / lam / lam := by ring

/-- Global version of `C2Data`: continuity and derivative relations on all of ℝ². -/
structure GlobalC2 (d du dv duv : ℝ → ℝ → ℝ) : Prop where
  cont : Continuous (Function.uncurry d)
  cont_u : Continuous (Function.uncurry du)
  cont_v : Continuous (Function.uncurry dv)
  cont_uv : Continuous (Function.uncurry duv)
  deriv_u : ∀ u v, HasDerivAt (fun t => d t v) (du u v) u
  deriv_v : ∀ u v, HasDerivAt (fun s => d u s) (dv u v) v
  deriv_uv_u : ∀ u v, HasDerivAt (fun t => dv t v) (duv u v) u
  deriv_uv_v : ∀ u v, HasDerivAt (fun s => du u s) (duv u v) v

theorem GlobalC2.toC2Data {d du dv duv : ℝ → ℝ → ℝ} (h : GlobalC2 d du dv duv) (a b : ℝ) :
    C2Data a b d du dv duv where
  cont := h.cont.continuousOn
  cont_u := h.cont_u.continuousOn
  cont_v := h.cont_v.continuousOn
  cont_uv := h.cont_uv.continuousOn
  deriv_u := fun u _ v _ => h.deriv_u u v
  deriv_v := fun u _ v _ => h.deriv_v u v
  deriv_uv_u := fun u _ v _ => h.deriv_uv_u u v
  deriv_uv_v := fun u _ v _ => h.deriv_uv_v u v

noncomputable def Uof {n : ℕ} (φ ψ : Fin n → ℝ → ℝ) (w : Fin n → ℝ → ℝ → ℝ) (i : Fin n)
    (u v : ℝ) : ℝ :=
  φ i u + ψ i v - φ i 0 + primUV (w i) u v

noncomputable def Uuof {n : ℕ} (φ' : Fin n → ℝ → ℝ) (w : Fin n → ℝ → ℝ → ℝ) (i : Fin n)
    (u v : ℝ) : ℝ :=
  φ' i u + primV (w i) u v

noncomputable def Uvof {n : ℕ} (ψ' : Fin n → ℝ → ℝ) (w : Fin n → ℝ → ℝ → ℝ) (i : Fin n)
    (u v : ℝ) : ℝ :=
  ψ' i v + primU (w i) u v

theorem Uof_C2 {n : ℕ} {φ ψ φ' ψ' : Fin n → ℝ → ℝ} {w : Fin n → ℝ → ℝ → ℝ} {i : Fin n}
    (hφ : ∀ i x, HasDerivAt (φ i) (φ' i x) x) (hψ : ∀ i x, HasDerivAt (ψ i) (ψ' i x) x)
    (hφc : ∀ i, Continuous (φ' i)) (hψc : ∀ i, Continuous (ψ' i))
    (hw : Continuous (Function.uncurry (w i))) :
    GlobalC2 (Uof φ ψ w i) (Uuof φ' w i) (Uvof ψ' w i) (w i) where
  cont := by
    have h1 : Continuous (φ i) := continuous_iff_continuousAt.mpr fun x => (hφ i x).continuousAt
    have h2 : Continuous (ψ i) := continuous_iff_continuousAt.mpr fun x => (hψ i x).continuousAt
    exact (((h1.comp continuous_fst).add (h2.comp continuous_snd)).sub continuous_const).add
      (primUV_cont hw)
  cont_u := ((hφc i).comp continuous_fst).add (primV_cont hw)
  cont_v := ((hψc i).comp continuous_snd).add (primU_cont hw)
  cont_uv := hw
  deriv_u := fun u v =>
    ((((hφ i u).add_const (ψ i v)).sub_const (φ i 0)).add (primUV_deriv_u hw u v))
  deriv_v := fun u v =>
    ((((hψ i v).const_add (φ i u)).sub_const (φ i 0)).add (primUV_deriv_v hw u v))
  deriv_uv_u := fun u v => (primU_deriv hw v u).const_add (ψ' i v)
  deriv_uv_v := fun u v => (primV_deriv hw u v).const_add (φ' i u)

theorem cont_of_lip {n : ℕ} {L : ℝ} {G : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hG : ∀ x1 y1 z1 x2 y2 z2, |G x1 y1 z1 - G x2 y2 z2|
      ≤ L * ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|))
    {X Y Z : ℝ × ℝ → Fin n → ℝ} (hX : ∀ j, Continuous fun q => X q j)
    (hY : ∀ j, Continuous fun q => Y q j) (hZ : ∀ j, Continuous fun q => Z q j) :
    Continuous fun q => G (X q) (Y q) (Z q) := by
  rw [continuous_iff_continuousAt]
  intro q0
  have hg : Continuous fun q => L * ∑ j, (|X q j - X q0 j| + |Y q j - Y q0 j| + |Z q j - Z q0 j|) :=
    continuous_const.mul (continuous_finset_sum _ (fun j _ =>
      ((((hX j).sub continuous_const).abs.add ((hY j).sub continuous_const).abs).add
        ((hZ j).sub continuous_const).abs)))
  have ht := hg.tendsto q0
  simp only [sub_self, abs_zero, add_zero, Finset.sum_const_zero, mul_zero] at ht
  exact tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun _ => dist_nonneg) (fun q => by rw [Real.dist_eq]; exact hG _ _ _ _ _ _) ht)

noncomputable def Gof {n : ℕ} (F : Fin n → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (φ ψ φ' ψ' : Fin n → ℝ → ℝ) (w : Fin n → ℝ → ℝ → ℝ) (i : Fin n) (q : ℝ × ℝ) : ℝ :=
  F i (fun j => Uof φ ψ w j q.1 q.2) (fun j => Uuof φ' w j q.1 q.2)
    (fun j => Uvof ψ' w j q.1 q.2)

abbrev Rect (a b : ℝ) := Icc (0:ℝ) a × Icc (0:ℝ) b

noncomputable def extR {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : C(Rect a b, ℝ)) (t s : ℝ) : ℝ :=
  z (projIcc 0 a ha t, projIcc 0 b hb s)

theorem extR_cont {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : C(Rect a b, ℝ)) :
    Continuous (Function.uncurry (extR ha hb z)) :=
  z.continuous.comp ((continuous_projIcc.comp continuous_fst).prod_mk
    (continuous_projIcc.comp continuous_snd))

noncomputable def wz {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (lam : ℝ)
    (z : Fin n → C(Rect a b, ℝ)) (i : Fin n) (t s : ℝ) : ℝ :=
  exp (lam * (t + s)) * extR ha hb (z i) t s

theorem wz_cont {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (lam : ℝ)
    (z : Fin n → C(Rect a b, ℝ)) (i : Fin n) : Continuous (Function.uncurry (wz ha hb lam z i)) :=
  (Real.continuous_exp.comp (continuous_const.mul (continuous_fst.add continuous_snd))).mul
    (extR_cont ha hb (z i))

/-- Existence for the semilinear Goursat problem w_{uv} = F(w, w_u, w_v) with F globally Lipschitz and C¹ characteristic data (Banach fixed point in a weighted sup norm). -/
theorem goursat_exists {n : ℕ} {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (F : Fin n → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hF : ∀ i x1 y1 z1 x2 y2 z2, |F i x1 y1 z1 - F i x2 y2 z2|
      ≤ L * ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|))
    (φ ψ φ' ψ' : Fin n → ℝ → ℝ)
    (hφ : ∀ i x, HasDerivAt (φ i) (φ' i x) x) (hψ : ∀ i x, HasDerivAt (ψ i) (ψ' i x) x)
    (hφc : ∀ i, Continuous (φ' i)) (hψc : ∀ i, Continuous (ψ' i))
    (h00 : ∀ i, φ i 0 = ψ i 0) :
    ∃ U Uu Uv Uuv : Fin n → ℝ → ℝ → ℝ,
      (∀ i, GlobalC2 (U i) (Uu i) (Uv i) (Uuv i))
      ∧ (∀ i u, U i u 0 = φ i u) ∧ (∀ i v, U i 0 v = ψ i v)
      ∧ ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
        Uuv i u v = F i (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v) := by
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 6 * L * n + 1 := ⟨_, rfl⟩
  have hLn : 0 ≤ L * n := mul_nonneg hL (Nat.cast_nonneg n)
  have hlam1 : 1 ≤ lam := by rw [hlam]; nlinarith
  have hl : 0 < lam := by linarith
  have hw : ∀ (z : Fin n → C(Rect a b, ℝ)) i, Continuous (Function.uncurry (wz ha hb lam z i)) :=
    fun z i => wz_cont ha hb lam z i
  have hC2 : ∀ (z : Fin n → C(Rect a b, ℝ)) i,
      GlobalC2 (Uof φ ψ (wz ha hb lam z) i) (Uuof φ' (wz ha hb lam z) i)
        (Uvof ψ' (wz ha hb lam z) i) (wz ha hb lam z i) :=
    fun z i => Uof_C2 hφ hψ hφc hψc (hw z i)
  have hG : ∀ (z : Fin n → C(Rect a b, ℝ)) i, Continuous (Gof F φ ψ φ' ψ' (wz ha hb lam z) i) :=
    fun z i => cont_of_lip (hF i)
      (X := fun q j => Uof φ ψ (wz ha hb lam z) j q.1 q.2)
      (Y := fun q j => Uuof φ' (wz ha hb lam z) j q.1 q.2)
      (Z := fun q j => Uvof ψ' (wz ha hb lam z) j q.1 q.2)
      (fun j => (hC2 z j).cont) (fun j => (hC2 z j).cont_u) (fun j => (hC2 z j).cont_v)
  have h1 : Continuous fun p : Rect a b => ((p.1 : ℝ), (p.2 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prod_mk (continuous_subtype_val.comp continuous_snd)
  let T : (Fin n → C(Rect a b, ℝ)) → (Fin n → C(Rect a b, ℝ)) := fun z i =>
    ⟨fun p => exp (-(lam * ((p.1 : ℝ) + (p.2 : ℝ))))
        * Gof F φ ψ φ' ψ' (wz ha hb lam z) i ((p.1 : ℝ), (p.2 : ℝ)),
      (Real.continuous_exp.comp (continuous_const.mul (h1.fst.add h1.snd)).neg).mul
        ((hG z i).comp h1)⟩

  have hTlip : ∀ z1 z2, dist (T z1) (T z2) ≤ 2⁻¹ * dist z1 z2 := by
    intro z1 z2
    rw [dist_eq_norm, dist_eq_norm]
    have hδ0 : 0 ≤ ‖z1 - z2‖ := norm_nonneg _
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
    refine (ContinuousMap.norm_le _ (by positivity)).mpr (fun p => ?_)
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
    rw [Pi.sub_apply, ContinuousMap.sub_apply, Real.norm_eq_abs]
    have hD : ∀ j t s, |wz ha hb lam z1 j t s - wz ha hb lam z2 j t s|
        ≤ ‖z1 - z2‖ * exp (lam * (t + s)) := by
      intro j t s
      have e : wz ha hb lam z1 j t s - wz ha hb lam z2 j t s
          = exp (lam * (t + s)) * ((z1 - z2) j (projIcc 0 a ha t, projIcc 0 b hb s)) := by
        simp only [wz, extR, Pi.sub_apply, ContinuousMap.sub_apply]
        ring
      rw [e, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      calc |(z1 - z2) j (projIcc 0 a ha t, projIcc 0 b hb s)| ≤ ‖(z1 - z2) j‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousMap.norm_coe_le_norm _ _
        _ ≤ ‖z1 - z2‖ := norm_le_pi_norm (z1 - z2) j
    have hB : ∀ j, |Uof φ ψ (wz ha hb lam z1) j u v - Uof φ ψ (wz ha hb lam z2) j u v|
        + |Uuof φ' (wz ha hb lam z1) j u v - Uuof φ' (wz ha hb lam z2) j u v|
        + |Uvof ψ' (wz ha hb lam z1) j u v - Uvof ψ' (wz ha hb lam z2) j u v|
        ≤ 3 * (‖z1 - z2‖ * exp (lam * (u + v)) / lam) := by
      intro j
      have hDc : Continuous (Function.uncurry
          (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s)) :=
        (hw z1 j).sub (hw z2 j)
      have e1 : Uof φ ψ (wz ha hb lam z1) j u v - Uof φ ψ (wz ha hb lam z2) j u v
          = primUV (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s) u v := by
        rw [← primUV_sub (hw z1 j) (hw z2 j)]
        simp only [Uof]
        ring
      have e2 : Uuof φ' (wz ha hb lam z1) j u v - Uuof φ' (wz ha hb lam z2) j u v
          = primV (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s) u v := by
        rw [← primV_sub (hw z1 j) (hw z2 j)]
        simp only [Uuof]
        ring
      have e3 : Uvof ψ' (wz ha hb lam z1) j u v - Uvof ψ' (wz ha hb lam z2) j u v
          = primU (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s) u v := by
        rw [← primU_sub (hw z1 j) (hw z2 j)]
        simp only [Uvof]
        ring
      have b1 := primUV_bound (f := (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s)) hl hδ0 hu.1 hv.1 hDc (fun t _ s _ => hD j t s)
      have b2 := primV_bound (f := (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s)) (u := u) hl hδ0 hv.1 (slice_v hDc u)
        (fun s _ => hD j u s)
      have b3 := primU_bound (f := (fun t s => wz ha hb lam z1 j t s - wz ha hb lam z2 j t s)) (v := v) hl hδ0 hu.1 (slice_u hDc v)
        (fun t _ => hD j t v)
      have hq : 0 ≤ ‖z1 - z2‖ * exp (lam * (u + v)) / lam := by positivity
      have b1' : ‖z1 - z2‖ * exp (lam * (u + v)) / lam / lam
          ≤ ‖z1 - z2‖ * exp (lam * (u + v)) / lam := div_le_self hq hlam1
      rw [e1, e2, e3]
      linarith
    have hsum : ∑ j, (|Uof φ ψ (wz ha hb lam z1) j u v - Uof φ ψ (wz ha hb lam z2) j u v|
        + |Uuof φ' (wz ha hb lam z1) j u v - Uuof φ' (wz ha hb lam z2) j u v|
        + |Uvof ψ' (wz ha hb lam z1) j u v - Uvof ψ' (wz ha hb lam z2) j u v|)
        ≤ n * (3 * (‖z1 - z2‖ * exp (lam * (u + v)) / lam)) := by
      calc _ ≤ ∑ _j : Fin n, 3 * (‖z1 - z2‖ * exp (lam * (u + v)) / lam) :=
            Finset.sum_le_sum (fun j _ => hB j)
        _ = n * (3 * (‖z1 - z2‖ * exp (lam * (u + v)) / lam)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hGd : |Gof F φ ψ φ' ψ' (wz ha hb lam z1) i (u, v) - Gof F φ ψ φ' ψ' (wz ha hb lam z2) i (u, v)|
        ≤ L * (n * (3 * (‖z1 - z2‖ * exp (lam * (u + v)) / lam))) :=
      (hF i _ _ _ _ _ _).trans (mul_le_mul_of_nonneg_left hsum hL)
    have hinv : exp (-(lam * (u + v))) * exp (lam * (u + v)) = 1 := by
      rw [← Real.exp_add]
      simp
    show |exp (-(lam * (u + v))) * Gof F φ ψ φ' ψ' (wz ha hb lam z1) i (u, v)
        - exp (-(lam * (u + v))) * Gof F φ ψ φ' ψ' (wz ha hb lam z2) i (u, v)| ≤ 2⁻¹ * ‖z1 - z2‖
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc exp (-(lam * (u + v)))
          * |Gof F φ ψ φ' ψ' (wz ha hb lam z1) i (u, v) - Gof F φ ψ φ' ψ' (wz ha hb lam z2) i (u, v)|
        ≤ exp (-(lam * (u + v))) * (L * (n * (3 * (‖z1 - z2‖ * exp (lam * (u + v)) / lam)))) :=
          mul_le_mul_of_nonneg_left hGd (Real.exp_pos _).le
      _ = (exp (-(lam * (u + v))) * exp (lam * (u + v))) * (3 * (L * n) * ‖z1 - z2‖ / lam) := by
          ring
      _ = 3 * (L * n) * ‖z1 - z2‖ / lam := by rw [hinv, one_mul]
      _ ≤ 2⁻¹ * ‖z1 - z2‖ := by
          rw [div_le_iff₀ hl, hlam]
          nlinarith [mul_nonneg hLn hδ0]
  have hT : ContractingWith (2⁻¹ : NNReal) T := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun z1 z2 => ?_⟩
    push_cast
    exact hTlip z1 z2
  haveI : Nonempty (Fin n → C(Rect a b, ℝ)) := ⟨0⟩
  obtain ⟨z, hz⟩ : ∃ z, T z = z := ⟨_, hT.fixedPoint_isFixedPt⟩
  refine ⟨Uof φ ψ (wz ha hb lam z), Uuof φ' (wz ha hb lam z), Uvof ψ' (wz ha hb lam z),
    wz ha hb lam z, fun i => hC2 z i, fun i u => ?_, fun i v => ?_, fun i u hu v hv => ?_⟩
  · simp only [Uof, primUV_zero_right, h00 i]
    ring
  · simp only [Uof, primUV_zero_left]
    ring
  · have e1 : z i (⟨u, hu⟩, ⟨v, hv⟩) = T z i (⟨u, hu⟩, ⟨v, hv⟩) := by rw [hz]
    have e2 : T z i (⟨u, hu⟩, ⟨v, hv⟩)
        = exp (-(lam * (u + v))) * Gof F φ ψ φ' ψ' (wz ha hb lam z) i (u, v) := rfl
    have e3 : wz ha hb lam z i u v = exp (lam * (u + v)) * z i (⟨u, hu⟩, ⟨v, hv⟩) := by
      simp only [wz, extR, projIcc_of_mem ha hu, projIcc_of_mem hb hv]
    rw [e3, e1, e2, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    rfl

end FieldEquations.Goursat
