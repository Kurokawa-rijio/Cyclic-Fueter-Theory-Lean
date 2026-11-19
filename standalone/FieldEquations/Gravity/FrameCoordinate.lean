import FieldEquations.Gravity.TorsionLorentz
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-
# Frame and coordinate Einstein tensors

Coordinate Riemann tensor Rc_{μνρσ} (all indices down), frame e^a_μ with Σ_μ e^a_μ E_b^μ = δ_ab,
signs η_a. g_{μν} = Σ η_a e^a_μ e^a_ν, g^{μν} = Σ η_a E_a^μ E_a^ν, frame components
RF_{abcd} = Σ E E E E Rc. Contractions in the 2nd and 4th slots.
* `ricci_frame`, `scalar_frame`, `metric_frame`, `einstein_frame`: the frame Ricci, scalar and
  Einstein tensors are the coordinate ones transported by the frame.
* `einstein_frame_iff`: frame G = 0 ⇔ coordinate G_{νσ} = 0 (`complete_of_heE` gives E e = 1).
* `metric_inverse`: with η_a² = 1, Σ_ν g_{μν} g^{νρ} = δ (one-sided).
* `einstein_lorentz_coord`: with η = diag(−1,1,1,1) and Rc having the two antisymmetries,
  Lorentzian Cartan–Palatini stationarity ⇔ G_{νσ} = 0.
That the Riemann tensor of the Levi-Civita connection of a metric has the two antisymmetries
is assumed, not proved here.
-/

open Finset

namespace FieldEquations.FrameCoordinate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum3 (f : ι → ι → ι → ℝ) :
    ∑ b, ∑ x, ∑ y, f b x y = ∑ x, ∑ y, ∑ b, f b x y := by
  calc ∑ b, ∑ x, ∑ y, f b x y = ∑ x, ∑ b, ∑ y, f b x y := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ b, f b x y := Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem sum4 (f : ι → ι → ι → ι → ℝ) :
    ∑ b, ∑ d, ∑ x, ∑ y, f b d x y = ∑ x, ∑ y, ∑ b, ∑ d, f b d x y := by
  calc ∑ b, ∑ d, ∑ x, ∑ y, f b d x y = ∑ b, ∑ x, ∑ d, ∑ y, f b d x y :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ x, ∑ y, ∑ d, f b d x y :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ b, ∑ y, ∑ d, f b d x y := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ b, ∑ d, f b d x y := Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem sum5 (f : ι → ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ x1, ∑ x2, ∑ x3, ∑ x4, f a x1 x2 x3 x4
      = ∑ x1, ∑ x3, ∑ x2, ∑ x4, ∑ a, f a x1 x2 x3 x4 := by
  calc ∑ a, ∑ x1, ∑ x2, ∑ x3, ∑ x4, f a x1 x2 x3 x4
        = ∑ x1, ∑ a, ∑ x2, ∑ x3, ∑ x4, f a x1 x2 x3 x4 := Finset.sum_comm
    _ = ∑ x1, ∑ x2, ∑ a, ∑ x3, ∑ x4, f a x1 x2 x3 x4 :=
        Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
    _ = ∑ x1, ∑ x2, ∑ x3, ∑ a, ∑ x4, f a x1 x2 x3 x4 :=
        Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ => Finset.sum_comm
    _ = ∑ x1, ∑ x2, ∑ x3, ∑ x4, ∑ a, f a x1 x2 x3 x4 :=
        Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ =>
          Finset.sum_congr rfl fun x3 _ => Finset.sum_comm
    _ = ∑ x1, ∑ x3, ∑ x2, ∑ x4, ∑ a, f a x1 x2 x3 x4 :=
        Finset.sum_congr rfl fun x1 _ => Finset.sum_comm

theorem sum_mul_sum' (f g : ι → ℝ) : (∑ i, f i) * (∑ j, g j) = ∑ i, ∑ j, f i * g j := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

def gco (e : ι → ι → ℝ) (η : ι → ℝ) (μ ν : ι) : ℝ := ∑ a, η a * e a μ * e a ν

def gin (E : ι → ι → ℝ) (η : ι → ℝ) (μ ν : ι) : ℝ := ∑ a, η a * E a μ * E a ν

def RicC (gi : ι → ι → ℝ) (Rc : ι → ι → ι → ι → ℝ) (ν σ : ι) : ℝ :=
  ∑ μ, ∑ ρ, gi μ ρ * Rc ν μ σ ρ

def RsC (gi : ι → ι → ℝ) (Ric : ι → ι → ℝ) : ℝ := ∑ ν, ∑ σ, gi ν σ * Ric ν σ

noncomputable def GC (g gi : ι → ι → ℝ) (Rc : ι → ι → ι → ι → ℝ) (ν σ : ι) : ℝ :=
  RicC gi Rc ν σ - (1/2 : ℝ) * g ν σ * RsC gi (RicC gi Rc)

def RF (E : ι → ι → ℝ) (Rc : ι → ι → ι → ι → ℝ) (a b c d : ι) : ℝ :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, E a μ * E b ν * E c ρ * E d σ * Rc μ ν ρ σ

def RicF (η : ι → ℝ) (R : ι → ι → ι → ι → ℝ) (b d : ι) : ℝ := ∑ a, η a * R b a d a

def RsF (η : ι → ℝ) (R : ι → ι → ι → ι → ℝ) : ℝ := ∑ b, η b * RicF η R b b

noncomputable def GF (η : ι → ℝ) (R : ι → ι → ι → ι → ℝ) (b d : ι) : ℝ :=
  RicF η R b d - (1/2 : ℝ) * (if b = d then η b else 0) * RsF η R

theorem complete_of_heE (e E : ι → ι → ℝ)
    (heE : ∀ a b, ∑ μ, e a μ * E b μ = if a = b then 1 else 0) :
    ∀ μ ν, ∑ a, E a μ * e a ν = if μ = ν then 1 else 0 := by
  let A : Matrix ι ι ℝ := Matrix.of fun a μ => e a μ
  let Bm : Matrix ι ι ℝ := Matrix.of fun μ b => E b μ
  have hAB : A * Bm = 1 := by
    ext a b
    simp [A, Bm, Matrix.mul_apply, Matrix.one_apply, heE]
  have hBA : Bm * A = 1 := Matrix.mul_eq_one_comm.mp hAB
  intro μ ν
  have h := congrArg (fun M : Matrix ι ι ℝ => M μ ν) hBA
  simpa [A, Bm, Matrix.mul_apply, Matrix.one_apply] using h

theorem metric_inverse (e E : ι → ι → ℝ) (η : ι → ℝ)
    (heE : ∀ a b, ∑ μ, e a μ * E b μ = if a = b then 1 else 0) (hη : ∀ a, η a * η a = 1)
    (μ ρ : ι) : ∑ ν, gco e η μ ν * gin E η ν ρ = if μ = ρ then 1 else 0 := by
  have hEe := complete_of_heE e E heE
  calc ∑ ν, gco e η μ ν * gin E η ν ρ
      = ∑ a, ∑ b, η a * η b * e a μ * E b ρ * (∑ ν, e a ν * E b ν) := by
        unfold gco gin
        simp only [sum_mul_sum']
        simp only [Finset.mul_sum]
        refine (sum3 _).trans ?_
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun ν _ => by ring
    _ = ∑ a, ∑ b, η a * η b * e a μ * E b ρ * (if a = b then 1 else 0) := by simp only [heE]
    _ = ∑ a, η a * η a * e a μ * E a ρ := Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_eq_single a (fun b _ h => by simp [Ne.symm h])
          (fun h => absurd (Finset.mem_univ a) h)]
        simp
    _ = ∑ a, E a ρ * e a μ := Finset.sum_congr rfl fun a _ => by rw [hη a]; ring
    _ = if μ = ρ then 1 else 0 := by
        rw [hEe ρ μ]
        by_cases h : μ = ρ
        · subst h; simp
        · simp [h, Ne.symm h]

theorem ricci_frame (E : ι → ι → ℝ) (η : ι → ℝ) (Rc : ι → ι → ι → ι → ℝ) (b d : ι) :
    RicF η (RF E Rc) b d = ∑ ν, ∑ σ, E b ν * E d σ * RicC (gin E η) Rc ν σ := by
  unfold RicF RF RicC gin
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine (sum5 _).trans ?_
  exact Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x3 _ =>
    Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun x4 _ =>
      Finset.sum_congr rfl fun a _ => by ring

theorem scalar_frame (E : ι → ι → ℝ) (η : ι → ℝ) (Rc : ι → ι → ι → ι → ℝ) :
    RsF η (RF E Rc) = RsC (gin E η) (RicC (gin E η) Rc) := by
  unfold RsF RsC
  simp only [ricci_frame]
  simp only [gin]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine (sum3 _).trans ?_
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun a _ => by ring

theorem metric_frame (e E : ι → ι → ℝ) (η : ι → ℝ)
    (heE : ∀ a b, ∑ μ, e a μ * E b μ = if a = b then 1 else 0) (b d : ι) :
    ∑ ν, ∑ σ, E b ν * E d σ * gco e η ν σ = if b = d then η b else 0 := by
  have key : ∀ a, ∑ ν, ∑ σ, E b ν * E d σ * (η a * e a ν * e a σ)
      = η a * ((∑ ν, e a ν * E b ν) * (∑ σ, e a σ * E d σ)) := by
    intro a
    rw [sum_mul_sum', Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  unfold gco
  simp only [Finset.mul_sum]
  refine (sum3 _).symm.trans ?_
  simp only [key, heE]
  rw [Finset.sum_eq_single b (fun a _ h => by simp [h]) (fun h => absurd (Finset.mem_univ b) h)]
  by_cases h : b = d
  · subst h; simp
  · simp [h]

theorem einstein_frame (e E : ι → ι → ℝ) (η : ι → ℝ) (Rc : ι → ι → ι → ι → ℝ)
    (heE : ∀ a b, ∑ μ, e a μ * E b μ = if a = b then 1 else 0) (b d : ι) :
    GF η (RF E Rc) b d = ∑ ν, ∑ σ, E b ν * E d σ * GC (gco e η) (gin E η) Rc ν σ := by
  have hsplit : ∑ ν, ∑ σ, E b ν * E d σ * GC (gco e η) (gin E η) Rc ν σ
      = ∑ ν, ∑ σ, E b ν * E d σ * RicC (gin E η) Rc ν σ
        - (1/2 : ℝ) * RsC (gin E η) (RicC (gin E η) Rc)
          * ∑ ν, ∑ σ, E b ν * E d σ * gco e η ν σ := by
    unfold GC
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hsplit, metric_frame e E η heE, ← ricci_frame, ← scalar_frame]
  unfold GF
  ring

theorem coord_of_frame (e E : ι → ι → ℝ)
    (hEe : ∀ μ ν, ∑ a, E a μ * e a ν = if μ = ν then 1 else 0) (X : ι → ι → ℝ) (ν σ : ι) :
    ∑ b, ∑ d, e b ν * e d σ * (∑ ν', ∑ σ', E b ν' * E d σ' * X ν' σ') = X ν σ := by
  have key : ∀ ν' σ', ∑ b, ∑ d, e b ν * e d σ * (E b ν' * E d σ' * X ν' σ')
      = ((if ν' = ν then 1 else 0) * (if σ' = σ then 1 else 0)) * X ν' σ' := by
    intro ν' σ'
    rw [← hEe ν' ν, ← hEe σ' σ, sum_mul_sum', Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [Finset.mul_sum]
  refine (sum4 _).trans ?_
  simp only [key]
  rw [Finset.sum_eq_single ν (fun ν' _ h => by simp [h]) (fun h => absurd (Finset.mem_univ ν) h)]
  rw [Finset.sum_eq_single σ (fun σ' _ h => by simp [h]) (fun h => absurd (Finset.mem_univ σ) h)]
  simp

/-- Frame Einstein equations ⇔ coordinate Einstein equations. -/
theorem einstein_frame_iff (e E : ι → ι → ℝ) (η : ι → ℝ) (Rc : ι → ι → ι → ι → ℝ)
    (heE : ∀ a b, ∑ μ, e a μ * E b μ = if a = b then 1 else 0) :
    (∀ b d, GF η (RF E Rc) b d = 0) ↔ ∀ ν σ, GC (gco e η) (gin E η) Rc ν σ = 0 := by
  have hEe := complete_of_heE e E heE
  constructor
  · intro h ν σ
    rw [← coord_of_frame e E hEe (GC (gco e η) (gin E η) Rc) ν σ]
    simp only [← einstein_frame e E η Rc heE, h, mul_zero, Finset.sum_const_zero]
  · intro h b d
    rw [einstein_frame e E η Rc heE]
    simp [h]

theorem RF_antisymm1 (E : ι → ι → ℝ) (Rc : ι → ι → ι → ι → ℝ)
    (h1 : ∀ μ ν ρ σ, Rc μ ν ρ σ = -Rc ν μ ρ σ) (a b c d : ι) :
    RF E Rc a b c d = -RF E Rc b a c d := by
  unfold RF
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => by rw [h1 μ ν ρ σ]; ring

theorem RF_antisymm2 (E : ι → ι → ℝ) (Rc : ι → ι → ι → ι → ℝ)
    (h2 : ∀ μ ν ρ σ, Rc μ ν ρ σ = -Rc μ ν σ ρ) (a b c d : ι) :
    RF E Rc a b c d = -RF E Rc a b d c := by
  unfold RF
  have hs : ∑ μ, ∑ ν, ∑ ρ, ∑ σ, E a μ * E b ν * E c ρ * E d σ * Rc μ ν ρ σ
      = ∑ μ, ∑ ν, ∑ σ, ∑ ρ, E a μ * E b ν * E c ρ * E d σ * Rc μ ν ρ σ :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => Finset.sum_comm
  rw [hs]
  simp only [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ρ _ => by rw [h2 μ ν ρ σ]; ring

open FieldEquations.CartanPalatini in
theorem GF_etaL (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (b d : Fin 4) :
    GF etaL R b d = GLor R b d := rfl

open FieldEquations.CartanPalatini in

/-- Lorentzian Cartan–Palatini stationarity ⇔ coordinate Einstein equations. -/
theorem einstein_lorentz_coord (e E : Fin 4 → Fin 4 → ℝ) (Rc : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (heE : ∀ a b, ∑ μ, e a μ * E b μ = if a = b then 1 else 0)
    (h1 : ∀ μ ν ρ σ, Rc μ ν ρ σ = -Rc ν μ ρ σ) (h2 : ∀ μ ν ρ σ, Rc μ ν ρ σ = -Rc μ ν σ ρ) :
    (∀ k, V (Rt (RF E Rc)) k = 0) ↔ ∀ ν σ, GC (gco e etaL) (gin E etaL) Rc ν σ = 0 := by
  rw [einstein_lorentz_iff (RF E Rc) (fun c d x y => RF_antisymm1 E Rc h1 c d x y)
    (fun c d x y => RF_antisymm2 E Rc h2 c d x y)]
  simp only [← GF_etaL]
  exact einstein_frame_iff e E etaL Rc heE

end FieldEquations.FrameCoordinate
