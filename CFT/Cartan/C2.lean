/-
  α-II.4 / II.6 の準備:C2 クラス(Ricci の固有値が三つとも異なり、Ric は Codazzi テンソル、
  σ₁ = tr Ric と σ₂ が一定)の 1 段目(Codazzi 方程式の一般解)

  仮定(構造体 C2):Ric(e_j,e_m) = λ_j δ_jm、e_k σ₁ = e_k σ₂ = 0、
    (∇_k Ric)_ij = (∇_i Ric)_kj(Codazzi。Cotton = 0 かつ R 一定と同値、II_iff_cotton)、
    λ_i − λ_j は単元(固有値が U 上で相異なる)。
  記号:a = Γ 0 2 2、b = Γ 1 2 2、c = Γ 1 2 1、h = Γ 0 1 2、inv01 = (λ₀ − λ₁)⁻¹ など。
  結論:e_k λ_i と残りの Γ はすべて (λ, a, b, c, h) で決まる(c2_lib.py の dd, Gs と同じ式)。
-/
import CFT.Cartan.Frame

namespace CFT.Cartan

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def inv01 (lam : Fin 3 → R) : R := Ring.inverse (lam 0 - lam 1)
noncomputable def inv02 (lam : Fin 3 → R) : R := Ring.inverse (lam 0 - lam 2)
noncomputable def inv12 (lam : Fin 3 → R) : R := Ring.inverse (lam 1 - lam 2)

/-- 対角な Ricci テンソル -/
def ricD (lam : Fin 3 → R) (i j : Fin 3) : R := if i = j then lam i else 0

/-- (∇_k Ric)(e_i, e_j) = e_k(Ric_ij) − Ric(∇_k e_i, e_j) − Ric(e_i, ∇_k e_j) -/
def Frame.nablaRic (F : Frame R) (lam : Fin 3 → R) (k i j : Fin 3) : R :=
  F.e k (ricD lam i j) - ∑ x, F.Γ x i k * ricD lam x j - ∑ x, F.Γ x j k * ricD lam i x

/-- 多項式の座標 α = a/(λ₀−λ₁)²、β = b/(λ₀−λ₁)²、γ = c/(λ₀−λ₂)²、η = h/((λ₀−λ₂)(λ₁−λ₂)) -/
noncomputable def alpha (F : Frame R) (lam : Fin 3 → R) : R := F.Γ 0 2 2 * (inv01 lam * inv01 lam)
noncomputable def beta (F : Frame R) (lam : Fin 3 → R) : R := F.Γ 1 2 2 * (inv01 lam * inv01 lam)
noncomputable def gamma (F : Frame R) (lam : Fin 3 → R) : R := F.Γ 1 2 1 * (inv02 lam * inv02 lam)
noncomputable def eta (F : Frame R) (lam : Fin 3 → R) : R := F.Γ 0 1 2 * (inv02 lam * inv12 lam)

/-- C2 クラスの仮定 -/
structure C2 (F : Frame R) (lam : Fin 3 → R) : Prop where
  ric_diag : ∀ j, F.Ric j j = lam j
  ric_off : ∀ j m, j ≠ m → F.Ric j m = 0
  sig1 : ∀ k, F.e k (lam 0 + lam 1 + lam 2) = 0
  sig2 : ∀ k, F.e k (lam 0 * lam 1 + lam 1 * lam 2 + lam 2 * lam 0) = 0
  codazzi : ∀ k i j, F.nablaRic lam k i j = F.nablaRic lam i k j
  u01 : IsUnit (lam 0 - lam 1)
  u02 : IsUnit (lam 0 - lam 2)
  u12 : IsUnit (lam 1 - lam 2)

namespace C2

variable {F : Frame R} {lam : Fin 3 → R} (H : C2 F lam)
include H

theorem h01 : (lam 0 - lam 1) * inv01 lam = 1 := Ring.mul_inverse_cancel _ H.u01
theorem h02 : (lam 0 - lam 2) * inv02 lam = 1 := Ring.mul_inverse_cancel _ H.u02
theorem h12 : (lam 1 - lam 2) * inv12 lam = 1 := Ring.mul_inverse_cancel _ H.u12

theorem hsum (k : Fin 3) : F.e k (lam 0) + F.e k (lam 1) + F.e k (lam 2) = 0 := by
  have h := H.sig1 k; simpa only [map_add] using h

theorem hsq (k : Fin 3) : lam 0 * F.e k (lam 0) + lam 1 * F.e k (lam 1) + lam 2 * F.e k (lam 2) = 0 := by
  have h2 := H.sig2 k; have h1 := H.hsum k
  simp only [map_add, Derivation.leibniz, smul_eq_mul] at h2
  linear_combination (lam 0 + lam 1 + lam 2) * h1 - h2

/-- Ricci の曲率テンソルは Kriem(3 次元、Ric = diag λ) -/
theorem riem (n j k m : Fin 3) : F.Riem n j k m = Kriem lam n j k m := by
  refine riem_of_diag_ricci lam F.Riem (fun n j k m => ?_) (fun n j k m => ?_) (fun j => ?_)
    (fun j m hjm => ?_) n j k m
  · rw [F.Riem_anti_left n j k m]; ring
  · rw [F.Riem_anti_right n j k m]; ring
  · have := H.ric_diag j; simp only [Frame.Ric, Fin.sum_univ_three] at this; exact this
  · have := H.ric_off j m hjm; simp only [Frame.Ric, Fin.sum_univ_three] at this; exact this

theorem cod010 : (((-1) * (F.e 1 (lam 0))) + ((F.Γ 0 1 0) * (lam 1)) + ((-1) * (F.Γ 0 1 0) * (lam 0))) = 0 := by
  have h := H.codazzi 0 1 0
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod011 : ((F.e 0 (lam 1)) + ((F.Γ 0 1 1) * (lam 0)) + ((-1) * (F.Γ 0 1 1) * (lam 1))) = 0 := by
  have h := H.codazzi 0 1 1
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod012 : (((F.Γ 0 2 1) * (lam 0)) + ((F.Γ 1 2 0) * (lam 2)) + ((-1) * (F.Γ 0 2 1) * (lam 2)) + ((-1) * (F.Γ 1 2 0) * (lam 1))) = 0 := by
  have h := H.codazzi 0 1 2
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod020 : (((-1) * (F.e 2 (lam 0))) + ((F.Γ 0 2 0) * (lam 2)) + ((-1) * (F.Γ 0 2 0) * (lam 0))) = 0 := by
  have h := H.codazzi 0 2 0
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod021 : (((F.Γ 0 1 2) * (lam 0)) + ((F.Γ 1 2 0) * (lam 2)) + ((-1) * (F.Γ 0 1 2) * (lam 1)) + ((-1) * (F.Γ 1 2 0) * (lam 1))) = 0 := by
  have h := H.codazzi 0 2 1
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod022 : ((F.e 0 (lam 2)) + ((F.Γ 0 2 2) * (lam 0)) + ((-1) * (F.Γ 0 2 2) * (lam 2))) = 0 := by
  have h := H.codazzi 0 2 2
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod120 : (((F.Γ 0 1 2) * (lam 0)) + ((F.Γ 0 2 1) * (lam 2)) + ((-1) * (F.Γ 0 1 2) * (lam 1)) + ((-1) * (F.Γ 0 2 1) * (lam 0))) = 0 := by
  have h := H.codazzi 1 2 0
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod121 : (((-1) * (F.e 2 (lam 1))) + ((F.Γ 1 2 1) * (lam 2)) + ((-1) * (F.Γ 1 2 1) * (lam 1))) = 0 := by
  have h := H.codazzi 1 2 1
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem cod122 : ((F.e 1 (lam 2)) + ((F.Γ 1 2 2) * (lam 1)) + ((-1) * (F.Γ 1 2 2) * (lam 2))) = 0 := by
  have h := H.codazzi 1 2 2
  simp only [Frame.nablaRic, ricD, Fin.sum_univ_three] at h
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag] at h
  first | linear_combination h | linear_combination -h

theorem D00 : F.e 0 (lam 0) = (((-1) * (F.Γ 0 2 2) * (inv01 lam) * ((lam 2) * (lam 2))) + ((F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 2)) + ((F.Γ 0 2 2) * (inv01 lam) * (lam 1) * (lam 2)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 1))) := by
  linear_combination (((-1) * (inv01 lam) * (lam 1))) * (H.hsum 0) + ((inv01 lam)) * (H.hsq 0) + ((((inv01 lam) * (lam 1)) + ((-1) * (inv01 lam) * (lam 2)))) * (H.cod022) + (((-1) * (F.e 0 (lam 0)))) * H.h01

theorem D01 : F.e 0 (lam 1) = (((F.Γ 0 2 2) * (inv01 lam) * ((lam 0) * (lam 0))) + ((F.Γ 0 2 2) * (inv01 lam) * ((lam 2) * (lam 2))) + ((-2) * (F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 2))) := by
  linear_combination (((inv01 lam) * (lam 0))) * (H.hsum 0) + (((-1) * (inv01 lam))) * (H.hsq 0) + ((((inv01 lam) * (lam 2)) + ((-1) * (inv01 lam) * (lam 0)))) * (H.cod022) + (((-1) * (F.e 0 (lam 1)))) * H.h01

theorem D02 : F.e 0 (lam 2) = (((F.Γ 0 2 2) * (lam 2)) + ((-1) * (F.Γ 0 2 2) * (lam 0))) := by
  linear_combination (1) * (H.cod022)

theorem D10 : F.e 1 (lam 0) = (((-1) * (F.Γ 1 2 2) * (inv01 lam) * ((lam 1) * (lam 1))) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * ((lam 2) * (lam 2))) + (2 * (F.Γ 1 2 2) * (inv01 lam) * (lam 1) * (lam 2))) := by
  linear_combination (((-1) * (inv01 lam) * (lam 1))) * (H.hsum 1) + ((inv01 lam)) * (H.hsq 1) + ((((inv01 lam) * (lam 1)) + ((-1) * (inv01 lam) * (lam 2)))) * (H.cod122) + (((-1) * (F.e 1 (lam 0)))) * H.h01

theorem D11 : F.e 1 (lam 1) = (((F.Γ 1 2 2) * (inv01 lam) * ((lam 2) * (lam 2))) + ((F.Γ 1 2 2) * (inv01 lam) * (lam 0) * (lam 1)) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * (lam 0) * (lam 2)) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * (lam 1) * (lam 2))) := by
  linear_combination (((inv01 lam) * (lam 0))) * (H.hsum 1) + (((-1) * (inv01 lam))) * (H.hsq 1) + ((((inv01 lam) * (lam 2)) + ((-1) * (inv01 lam) * (lam 0)))) * (H.cod122) + (((-1) * (F.e 1 (lam 1)))) * H.h01

theorem D12 : F.e 1 (lam 2) = (((F.Γ 1 2 2) * (lam 2)) + ((-1) * (F.Γ 1 2 2) * (lam 1))) := by
  linear_combination (1) * (H.cod122)

theorem D20 : F.e 2 (lam 0) = (((F.Γ 1 2 1) * (inv02 lam) * ((lam 1) * (lam 1))) + ((F.Γ 1 2 1) * (inv02 lam) * ((lam 2) * (lam 2))) + ((-2) * (F.Γ 1 2 1) * (inv02 lam) * (lam 1) * (lam 2))) := by
  linear_combination (((-1) * (inv02 lam) * (lam 2))) * (H.hsum 2) + ((inv02 lam)) * (H.hsq 2) + ((((inv02 lam) * (lam 1)) + ((-1) * (inv02 lam) * (lam 2)))) * (H.cod121) + (((-1) * (F.e 2 (lam 0)))) * H.h02

theorem D21 : F.e 2 (lam 1) = (((F.Γ 1 2 1) * (lam 2)) + ((-1) * (F.Γ 1 2 1) * (lam 1))) := by
  linear_combination ((-1)) * (H.cod121)

theorem D22 : F.e 2 (lam 2) = (((-1) * (F.Γ 1 2 1) * (inv02 lam) * ((lam 1) * (lam 1))) + ((F.Γ 1 2 1) * (inv02 lam) * (lam 0) * (lam 1)) + ((F.Γ 1 2 1) * (inv02 lam) * (lam 1) * (lam 2)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * (lam 0) * (lam 2))) := by
  linear_combination (((inv02 lam) * (lam 0))) * (H.hsum 2) + (((-1) * (inv02 lam))) * (H.hsq 2) + ((((inv02 lam) * (lam 0)) + ((-1) * (inv02 lam) * (lam 1)))) * (H.cod121) + (((-1) * (F.e 2 (lam 2)))) * H.h02

theorem G010 : F.Γ 0 1 0 = (((F.Γ 1 2 2) * ((inv01 lam) * (inv01 lam)) * ((lam 1) * (lam 1))) + ((F.Γ 1 2 2) * ((inv01 lam) * (inv01 lam)) * ((lam 2) * (lam 2))) + ((-2) * (F.Γ 1 2 2) * (lam 1) * (lam 2) * ((inv01 lam) * (inv01 lam)))) := by
  linear_combination (((lam 1) * ((inv01 lam)^2))) * (H.hsum 1) + (((-1) * ((inv01 lam)^2))) * (H.hsq 1) + (((-1) * (inv01 lam))) * (H.cod010) + ((((lam 2) * ((inv01 lam)^2)) + ((-1) * (lam 1) * ((inv01 lam)^2)))) * (H.cod122) + ((((-1) * (F.Γ 0 1 0)) + ((F.e 1 (lam 0)) * (inv01 lam)))) * H.h01

theorem G011 : F.Γ 0 1 1 = (((-1) * (F.Γ 0 2 2) * ((inv01 lam) * (inv01 lam)) * ((lam 0) * (lam 0))) + ((-1) * (F.Γ 0 2 2) * ((inv01 lam) * (inv01 lam)) * ((lam 2) * (lam 2))) + (2 * (F.Γ 0 2 2) * (lam 0) * (lam 2) * ((inv01 lam) * (inv01 lam)))) := by
  linear_combination (((-1) * (lam 0) * ((inv01 lam)^2))) * (H.hsum 0) + (((inv01 lam)^2)) * (H.hsq 0) + ((inv01 lam)) * (H.cod011) + ((((lam 0) * ((inv01 lam)^2)) + ((-1) * (lam 2) * ((inv01 lam)^2)))) * (H.cod022) + ((((-1) * (F.Γ 0 1 1)) + ((F.e 0 (lam 1)) * (inv01 lam)))) * H.h01

theorem G020 : F.Γ 0 2 0 = (((-1) * (F.Γ 1 2 1) * ((inv02 lam) * (inv02 lam)) * ((lam 1) * (lam 1))) + ((-1) * (F.Γ 1 2 1) * ((inv02 lam) * (inv02 lam)) * ((lam 2) * (lam 2))) + (2 * (F.Γ 1 2 1) * (lam 1) * (lam 2) * ((inv02 lam) * (inv02 lam)))) := by
  linear_combination (((lam 2) * ((inv02 lam)^2))) * (H.hsum 2) + (((-1) * ((inv02 lam)^2))) * (H.hsq 2) + (((-1) * (inv02 lam))) * (H.cod020) + ((((lam 2) * ((inv02 lam)^2)) + ((-1) * (lam 1) * ((inv02 lam)^2)))) * (H.cod121) + ((((-1) * (F.Γ 0 2 0)) + ((F.e 2 (lam 0)) * (inv02 lam)))) * H.h02

theorem G021 : F.Γ 0 2 1 = (((F.Γ 0 1 2) * (inv02 lam) * (lam 0)) + ((-1) * (F.Γ 0 1 2) * (inv02 lam) * (lam 1))) := by
  linear_combination ((inv02 lam)) * (H.cod012) + (((-1) * (inv02 lam))) * (H.cod021) + (((-1) * (F.Γ 0 2 1))) * H.h02

theorem G120 : F.Γ 1 2 0 = (((F.Γ 0 1 2) * (inv12 lam) * (lam 0)) + ((-1) * (F.Γ 0 1 2) * (inv12 lam) * (lam 1))) := by
  linear_combination (((-1) * (inv12 lam))) * (H.cod021) + (((-1) * (F.Γ 1 2 0))) * H.h12

/-! ### 多項式の座標

  a = (λ₀−λ₁)²α、b = (λ₀−λ₁)²β、c = (λ₀−λ₂)²γ、h = (λ₀−λ₂)(λ₁−λ₂)η と置き直すと、
  e_k λ_i と Γ はすべて (λ, α, β, γ, η) の多項式になる。以後の計算はこの座標で行う。 -/

theorem hhf : (2 : R) * half = 1 := two_mul_half

theorem e_ofNat (k : Fin 3) (n : ℕ) [n.AtLeastTwo] : F.e k (OfNat.ofNat n : R) = 0 := by
  rw [← Nat.cast_eq_ofNat]; exact Derivation.map_natCast _ n

theorem pD00 : F.e 0 (lam 0) = (((alpha F lam) * (lam 0) * ((lam 1) * (lam 1))) + ((alpha F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((alpha F lam) * (lam 2) * ((lam 0) * (lam 0))) + ((-1) * (alpha F lam) * (lam 0) * ((lam 2) * (lam 2))) + ((-1) * (alpha F lam) * (lam 1) * ((lam 0) * (lam 0))) + ((-1) * (alpha F lam) * (lam 2) * ((lam 1) * (lam 1)))) := by
  rw [H.D00]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 0 2 2) * (inv01 lam) * ((lam 2)^2)) + ((F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 1)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 2)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * (lam 1) * (lam 2)))) * H.h01

theorem pD01 : F.e 0 (lam 1) = (((alpha F lam) * ((lam 0) * (lam 0) * (lam 0))) + ((alpha F lam) * (lam 0) * ((lam 2) * (lam 2))) + ((-1) * (alpha F lam) * (lam 1) * ((lam 0) * (lam 0))) + ((-1) * (alpha F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((-2) * (alpha F lam) * (lam 2) * ((lam 0) * (lam 0))) + (2 * (alpha F lam) * (lam 0) * (lam 1) * (lam 2))) := by
  rw [H.D01]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((-1) * (F.Γ 0 2 2) * (inv01 lam) * ((lam 0)^2)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * ((lam 2)^2)) + (2 * (F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 2)))) * H.h01

theorem pD02 : F.e 0 (lam 2) = (((-1) * (alpha F lam) * ((lam 0) * (lam 0) * (lam 0))) + ((alpha F lam) * (lam 2) * ((lam 0) * (lam 0))) + ((alpha F lam) * (lam 2) * ((lam 1) * (lam 1))) + ((-1) * (alpha F lam) * (lam 0) * ((lam 1) * (lam 1))) + (2 * (alpha F lam) * (lam 1) * ((lam 0) * (lam 0))) + ((-2) * (alpha F lam) * (lam 0) * (lam 1) * (lam 2))) := by
  rw [H.D02]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 0 2 2) * (lam 0)) + ((-1) * (F.Γ 0 2 2) * (lam 2)) + ((F.Γ 0 2 2) * (inv01 lam) * ((lam 0)^2)) + ((F.Γ 0 2 2) * (inv01 lam) * (lam 1) * (lam 2)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 1)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * (lam 0) * (lam 2)))) * H.h01

theorem pD10 : F.e 1 (lam 0) = (((beta F lam) * ((lam 1) * (lam 1) * (lam 1))) + ((beta F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((-1) * (beta F lam) * (lam 0) * ((lam 1) * (lam 1))) + ((-1) * (beta F lam) * (lam 0) * ((lam 2) * (lam 2))) + ((-2) * (beta F lam) * (lam 2) * ((lam 1) * (lam 1))) + (2 * (beta F lam) * (lam 0) * (lam 1) * (lam 2))) := by
  rw [H.D10]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 1 2 2) * (inv01 lam) * ((lam 1)^2)) + ((F.Γ 1 2 2) * (inv01 lam) * ((lam 2)^2)) + ((-2) * (F.Γ 1 2 2) * (inv01 lam) * (lam 1) * (lam 2)))) * H.h01

theorem pD11 : F.e 1 (lam 1) = (((beta F lam) * (lam 0) * ((lam 2) * (lam 2))) + ((beta F lam) * (lam 1) * ((lam 0) * (lam 0))) + ((beta F lam) * (lam 2) * ((lam 1) * (lam 1))) + ((-1) * (beta F lam) * (lam 0) * ((lam 1) * (lam 1))) + ((-1) * (beta F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((-1) * (beta F lam) * (lam 2) * ((lam 0) * (lam 0)))) := by
  rw [H.D11]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((-1) * (F.Γ 1 2 2) * (inv01 lam) * ((lam 2)^2)) + ((F.Γ 1 2 2) * (inv01 lam) * (lam 0) * (lam 2)) + ((F.Γ 1 2 2) * (inv01 lam) * (lam 1) * (lam 2)) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * (lam 0) * (lam 1)))) * H.h01

theorem pD12 : F.e 1 (lam 2) = (((-1) * (beta F lam) * ((lam 1) * (lam 1) * (lam 1))) + ((beta F lam) * (lam 2) * ((lam 0) * (lam 0))) + ((beta F lam) * (lam 2) * ((lam 1) * (lam 1))) + ((-1) * (beta F lam) * (lam 1) * ((lam 0) * (lam 0))) + (2 * (beta F lam) * (lam 0) * ((lam 1) * (lam 1))) + ((-2) * (beta F lam) * (lam 0) * (lam 1) * (lam 2))) := by
  rw [H.D12]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 1 2 2) * (lam 1)) + ((-1) * (F.Γ 1 2 2) * (lam 2)) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * ((lam 1)^2)) + ((F.Γ 1 2 2) * (inv01 lam) * (lam 0) * (lam 1)) + ((F.Γ 1 2 2) * (inv01 lam) * (lam 1) * (lam 2)) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * (lam 0) * (lam 2)))) * H.h01

theorem pD20 : F.e 2 (lam 0) = (((-1) * (gamma F lam) * ((lam 2) * (lam 2) * (lam 2))) + ((gamma F lam) * (lam 0) * ((lam 1) * (lam 1))) + ((gamma F lam) * (lam 0) * ((lam 2) * (lam 2))) + ((-1) * (gamma F lam) * (lam 2) * ((lam 1) * (lam 1))) + (2 * (gamma F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((-2) * (gamma F lam) * (lam 0) * (lam 1) * (lam 2))) := by
  rw [H.D20]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((-1) * (F.Γ 1 2 1) * (inv02 lam) * ((lam 1)^2)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * ((lam 2)^2)) + (2 * (F.Γ 1 2 1) * (inv02 lam) * (lam 1) * (lam 2)))) * H.h02

theorem pD21 : F.e 2 (lam 1) = (((gamma F lam) * ((lam 2) * (lam 2) * (lam 2))) + ((gamma F lam) * (lam 2) * ((lam 0) * (lam 0))) + ((-1) * (gamma F lam) * (lam 1) * ((lam 0) * (lam 0))) + ((-1) * (gamma F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((-2) * (gamma F lam) * (lam 0) * ((lam 2) * (lam 2))) + (2 * (gamma F lam) * (lam 0) * (lam 1) * (lam 2))) := by
  rw [H.D21]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 1 2 1) * (lam 1)) + ((-1) * (F.Γ 1 2 1) * (lam 2)) + ((F.Γ 1 2 1) * (inv02 lam) * ((lam 2)^2)) + ((F.Γ 1 2 1) * (inv02 lam) * (lam 0) * (lam 1)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * (lam 0) * (lam 2)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * (lam 1) * (lam 2)))) * H.h02

theorem pD22 : F.e 2 (lam 2) = (((gamma F lam) * (lam 0) * ((lam 2) * (lam 2))) + ((gamma F lam) * (lam 1) * ((lam 0) * (lam 0))) + ((gamma F lam) * (lam 2) * ((lam 1) * (lam 1))) + ((-1) * (gamma F lam) * (lam 0) * ((lam 1) * (lam 1))) + ((-1) * (gamma F lam) * (lam 1) * ((lam 2) * (lam 2))) + ((-1) * (gamma F lam) * (lam 2) * ((lam 0) * (lam 0)))) := by
  rw [H.D22]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 1 2 1) * (inv02 lam) * ((lam 1)^2)) + ((F.Γ 1 2 1) * (inv02 lam) * (lam 0) * (lam 2)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * (lam 0) * (lam 1)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * (lam 1) * (lam 2)))) * H.h02

theorem pG010 : F.Γ 0 1 0 = (((beta F lam) * ((lam 1) * (lam 1))) + ((beta F lam) * ((lam 2) * (lam 2))) + ((-2) * (beta F lam) * (lam 1) * (lam 2))) := by
  rw [H.G010]; simp only [alpha, beta, gamma, eta]
  linear_combination 0

theorem pG020 : F.Γ 0 2 0 = (((-1) * (gamma F lam) * ((lam 1) * (lam 1))) + ((-1) * (gamma F lam) * ((lam 2) * (lam 2))) + (2 * (gamma F lam) * (lam 1) * (lam 2))) := by
  rw [H.G020]; simp only [alpha, beta, gamma, eta]
  linear_combination 0

theorem pG120 : F.Γ 1 2 0 = (((eta F lam) * ((lam 0) * (lam 0))) + ((eta F lam) * (lam 1) * (lam 2)) + ((-1) * (eta F lam) * (lam 0) * (lam 1)) + ((-1) * (eta F lam) * (lam 0) * (lam 2))) := by
  rw [H.G120]; simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 0 1 2) * (inv12 lam) * (lam 1)) + ((-1) * (F.Γ 0 1 2) * (inv12 lam) * (lam 0)))) * H.h02

theorem pG011 : F.Γ 0 1 1 = (((-1) * (alpha F lam) * ((lam 0) * (lam 0))) + ((-1) * (alpha F lam) * ((lam 2) * (lam 2))) + (2 * (alpha F lam) * (lam 0) * (lam 2))) := by
  rw [H.G011]; simp only [alpha, beta, gamma, eta]
  linear_combination 0

theorem pG021 : F.Γ 0 2 1 = (((-1) * (eta F lam) * ((lam 1) * (lam 1))) + ((eta F lam) * (lam 0) * (lam 1)) + ((eta F lam) * (lam 1) * (lam 2)) + ((-1) * (eta F lam) * (lam 0) * (lam 2))) := by
  rw [H.G021]; simp only [alpha, beta, gamma, eta]
  linear_combination (((F.Γ 0 1 2) + ((F.Γ 0 1 2) * (inv12 lam) * (lam 2)) + ((-1) * (F.Γ 0 1 2) * (inv12 lam) * (lam 1)))) * H.h02 + ((((-1) * (F.Γ 0 1 2)) + ((F.Γ 0 1 2) * (inv02 lam) * (lam 1)) + ((-1) * (F.Γ 0 1 2) * (inv02 lam) * (lam 2)))) * H.h12

theorem pG121 : F.Γ 1 2 1 = (((gamma F lam) * ((lam 0) * (lam 0))) + ((gamma F lam) * ((lam 2) * (lam 2))) + ((-2) * (gamma F lam) * (lam 0) * (lam 2))) := by
  simp only [alpha, beta, gamma, eta]
  linear_combination ((((-1) * (F.Γ 1 2 1)) + ((F.Γ 1 2 1) * (inv02 lam) * (lam 2)) + ((-1) * (F.Γ 1 2 1) * (inv02 lam) * (lam 0)))) * H.h02

theorem pG012 : F.Γ 0 1 2 = (((eta F lam) * ((lam 2) * (lam 2))) + ((eta F lam) * (lam 0) * (lam 1)) + ((-1) * (eta F lam) * (lam 0) * (lam 2)) + ((-1) * (eta F lam) * (lam 1) * (lam 2))) := by
  simp only [alpha, beta, gamma, eta]
  linear_combination ((((F.Γ 0 1 2) * (inv12 lam) * (lam 2)) + ((-1) * (F.Γ 0 1 2) * (inv12 lam) * (lam 1)))) * H.h02 + (((-1) * (F.Γ 0 1 2))) * H.h12

theorem pG022 : F.Γ 0 2 2 = (((alpha F lam) * ((lam 0) * (lam 0))) + ((alpha F lam) * ((lam 1) * (lam 1))) + ((-2) * (alpha F lam) * (lam 0) * (lam 1))) := by
  simp only [alpha, beta, gamma, eta]
  linear_combination ((((-1) * (F.Γ 0 2 2)) + ((F.Γ 0 2 2) * (inv01 lam) * (lam 1)) + ((-1) * (F.Γ 0 2 2) * (inv01 lam) * (lam 0)))) * H.h01

theorem pG122 : F.Γ 1 2 2 = (((beta F lam) * ((lam 0) * (lam 0))) + ((beta F lam) * ((lam 1) * (lam 1))) + ((-2) * (beta F lam) * (lam 0) * (lam 1))) := by
  simp only [alpha, beta, gamma, eta]
  linear_combination ((((-1) * (F.Γ 1 2 2)) + ((F.Γ 1 2 2) * (inv01 lam) * (lam 1)) + ((-1) * (F.Γ 1 2 2) * (inv01 lam) * (lam 0)))) * H.h01

theorem S0101 : (((-1) * (lam 0)) + ((-1) * (lam 1)) + ((half) * (lam 0)) + ((half) * (lam 1)) + ((half) * (lam 2)) + (((gamma F lam)^2) * ((lam 2)^4)) + ((-1) * (F.e 0 (alpha F lam)) * ((lam 0)^2)) + ((-1) * (F.e 0 (alpha F lam)) * ((lam 2)^2)) + ((-1) * (F.e 1 (beta F lam)) * ((lam 1)^2)) + ((-1) * (F.e 1 (beta F lam)) * ((lam 2)^2)) + ((-1) * ((alpha F lam)^2) * ((lam 2)^4)) + ((-1) * ((beta F lam)^2) * ((lam 2)^4)) + ((-3) * ((alpha F lam)^2) * ((lam 0)^4)) + ((-3) * ((beta F lam)^2) * ((lam 1)^4)) + (((gamma F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + (((gamma F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + (((gamma F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((alpha F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-4) * ((alpha F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((alpha F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((beta F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-4) * ((beta F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((beta F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((eta F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-2) * (lam 0) * ((gamma F lam)^2) * ((lam 2)^3)) + ((-2) * (lam 1) * ((gamma F lam)^2) * ((lam 2)^3)) + ((-2) * (lam 2) * ((eta F lam)^2) * ((lam 0)^3)) + ((-2) * (lam 2) * ((eta F lam)^2) * ((lam 1)^3)) + (2 * (F.e 0 (alpha F lam)) * (lam 0) * (lam 2)) + (2 * (F.e 1 (beta F lam)) * (lam 1) * (lam 2)) + (2 * (lam 0) * ((alpha F lam)^2) * ((lam 2)^3)) + (2 * (lam 0) * ((beta F lam)^2) * ((lam 2)^3)) + (2 * (lam 0) * ((eta F lam)^2) * ((lam 1)^3)) + (2 * (lam 1) * ((alpha F lam)^2) * ((lam 2)^3)) + (2 * (lam 1) * ((beta F lam)^2) * ((lam 2)^3)) + (2 * (lam 1) * ((eta F lam)^2) * ((lam 0)^3)) + (2 * ((eta F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + (2 * ((eta F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + (6 * (lam 0) * ((beta F lam)^2) * ((lam 1)^3)) + (6 * (lam 1) * ((alpha F lam)^2) * ((lam 0)^3)) + (6 * (lam 2) * ((alpha F lam)^2) * ((lam 0)^3)) + (6 * (lam 2) * ((beta F lam)^2) * ((lam 1)^3)) + ((-10) * (lam 0) * (lam 2) * ((beta F lam)^2) * ((lam 1)^2)) + ((-10) * (lam 1) * (lam 2) * ((alpha F lam)^2) * ((lam 0)^2)) + ((-4) * (lam 0) * (lam 1) * ((eta F lam)^2) * ((lam 2)^2)) + ((-2) * (lam 0) * (lam 2) * ((gamma F lam)^2) * ((lam 1)^2)) + ((-2) * (lam 1) * (lam 2) * ((gamma F lam)^2) * ((lam 0)^2)) + (2 * (lam 0) * (lam 1) * ((alpha F lam)^2) * ((lam 2)^2)) + (2 * (lam 0) * (lam 1) * ((beta F lam)^2) * ((lam 2)^2)) + (2 * (lam 0) * (lam 2) * ((eta F lam)^2) * ((lam 1)^2)) + (2 * (lam 1) * (lam 2) * ((eta F lam)^2) * ((lam 0)^2)) + (4 * (lam 0) * (lam 1) * ((gamma F lam)^2) * ((lam 2)^2)) + (8 * (lam 0) * (lam 2) * ((alpha F lam)^2) * ((lam 1)^2)) + (8 * (lam 1) * (lam 2) * ((beta F lam)^2) * ((lam 0)^2))) = 0 := by
  have h := H.riem 0 1 0 1
  rw [show Kriem lam 0 1 0 1 = ((lam 0) + (lam 1) + ((-1) * (half) * ((lam 0) + (lam 1) + (lam 2)))) by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S0102 : (((F.e 0 (eta F lam)) * ((lam 2)^2)) + ((-1) * (F.e 2 (beta F lam)) * ((lam 1)^2)) + ((-1) * (F.e 2 (beta F lam)) * ((lam 2)^2)) + ((F.e 0 (eta F lam)) * (lam 0) * (lam 1)) + ((alpha F lam) * (eta F lam) * ((lam 2)^4)) + ((-1) * (F.e 0 (eta F lam)) * (lam 0) * (lam 2)) + ((-1) * (F.e 0 (eta F lam)) * (lam 1) * (lam 2)) + (2 * (F.e 2 (beta F lam)) * (lam 1) * (lam 2)) + (2 * (beta F lam) * (gamma F lam) * ((lam 1)^4)) + (3 * (beta F lam) * (gamma F lam) * ((lam 2)^4)) + (4 * (alpha F lam) * (eta F lam) * ((lam 0)^4)) + ((-10) * (alpha F lam) * (eta F lam) * (lam 2) * ((lam 0)^3)) + ((-6) * (alpha F lam) * (eta F lam) * (lam 1) * ((lam 0)^3)) + ((-6) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^3)) + ((-6) * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^3)) + ((-4) * (alpha F lam) * (eta F lam) * (lam 0) * ((lam 2)^3)) + ((-4) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^3)) + ((-4) * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^3)) + (3 * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^2)) + (3 * (alpha F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^2)) + (5 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^2)) + (5 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^2)) + (5 * (beta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^2)) + (9 * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^2)) + ((-10) * (beta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + ((-6) * (alpha F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-6) * (alpha F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (2 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (8 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + (12 * (alpha F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^2))) = 0 := by
  have h := H.riem 0 1 0 2
  rw [show Kriem lam 0 1 0 2 = 0 by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S0112 : (((F.e 1 (eta F lam)) * ((lam 2)^2)) + ((F.e 2 (alpha F lam)) * ((lam 0)^2)) + ((F.e 2 (alpha F lam)) * ((lam 2)^2)) + ((F.e 1 (eta F lam)) * (lam 0) * (lam 1)) + ((beta F lam) * (eta F lam) * ((lam 2)^4)) + ((-1) * (F.e 1 (eta F lam)) * (lam 0) * (lam 2)) + ((-1) * (F.e 1 (eta F lam)) * (lam 1) * (lam 2)) + ((-2) * (F.e 2 (alpha F lam)) * (lam 0) * (lam 2)) + (2 * (alpha F lam) * (gamma F lam) * ((lam 0)^4)) + (3 * (alpha F lam) * (gamma F lam) * ((lam 2)^4)) + (4 * (beta F lam) * (eta F lam) * ((lam 1)^4)) + ((-10) * (beta F lam) * (eta F lam) * (lam 2) * ((lam 1)^3)) + ((-6) * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 2)^3)) + ((-6) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 2)^3)) + ((-6) * (beta F lam) * (eta F lam) * (lam 0) * ((lam 1)^3)) + ((-4) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^3)) + ((-4) * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^3)) + ((-4) * (beta F lam) * (eta F lam) * (lam 1) * ((lam 2)^3)) + (3 * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^2)) + (3 * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^2)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^2)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^2)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^2)) + (9 * (beta F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^2)) + ((-10) * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + ((-6) * (beta F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-6) * (beta F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (2 * (alpha F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (8 * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + (12 * (beta F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^2))) = 0 := by
  have h := H.riem 0 1 1 2
  rw [show Kriem lam 0 1 1 2 = 0 by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S0201 : (((F.e 1 (gamma F lam)) * ((lam 1)^2)) + ((F.e 1 (gamma F lam)) * ((lam 2)^2)) + ((-1) * (F.e 0 (eta F lam)) * ((lam 1)^2)) + ((F.e 0 (eta F lam)) * (lam 0) * (lam 1)) + ((F.e 0 (eta F lam)) * (lam 1) * (lam 2)) + ((alpha F lam) * (eta F lam) * ((lam 1)^4)) + ((-1) * (F.e 0 (eta F lam)) * (lam 0) * (lam 2)) + ((-2) * (F.e 1 (gamma F lam)) * (lam 1) * (lam 2)) + (2 * (beta F lam) * (gamma F lam) * ((lam 2)^4)) + (3 * (beta F lam) * (gamma F lam) * ((lam 1)^4)) + (4 * (alpha F lam) * (eta F lam) * ((lam 0)^4)) + ((-10) * (alpha F lam) * (eta F lam) * (lam 1) * ((lam 0)^3)) + ((-6) * (alpha F lam) * (eta F lam) * (lam 2) * ((lam 0)^3)) + ((-6) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^3)) + ((-6) * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^3)) + ((-4) * (alpha F lam) * (eta F lam) * (lam 0) * ((lam 1)^3)) + ((-4) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^3)) + ((-4) * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^3)) + (3 * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^2)) + (3 * (alpha F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^2)) + (5 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^2)) + (5 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^2)) + (5 * (beta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^2)) + (9 * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^2)) + ((-10) * (beta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + ((-6) * (alpha F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-6) * (alpha F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (2 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + (8 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (12 * (alpha F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^2))) = 0 := by
  have h := H.riem 0 2 0 1
  rw [show Kriem lam 0 2 0 1 = 0 by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S0202 : (((-1) * (lam 0)) + ((-1) * (lam 2)) + ((F.e 0 (alpha F lam)) * ((lam 0)^2)) + ((F.e 0 (alpha F lam)) * ((lam 1)^2)) + ((F.e 2 (gamma F lam)) * ((lam 1)^2)) + ((F.e 2 (gamma F lam)) * ((lam 2)^2)) + ((half) * (lam 0)) + ((half) * (lam 1)) + ((half) * (lam 2)) + (((beta F lam)^2) * ((lam 1)^4)) + ((-1) * ((alpha F lam)^2) * ((lam 1)^4)) + ((-1) * ((gamma F lam)^2) * ((lam 1)^4)) + ((-3) * ((alpha F lam)^2) * ((lam 0)^4)) + ((-3) * ((gamma F lam)^2) * ((lam 2)^4)) + (((beta F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + (((beta F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + (((beta F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((alpha F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-4) * ((alpha F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((alpha F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((eta F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((gamma F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-4) * ((gamma F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((gamma F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-2) * (F.e 0 (alpha F lam)) * (lam 0) * (lam 1)) + ((-2) * (F.e 2 (gamma F lam)) * (lam 1) * (lam 2)) + ((-2) * (lam 0) * ((beta F lam)^2) * ((lam 1)^3)) + ((-2) * (lam 1) * ((eta F lam)^2) * ((lam 0)^3)) + ((-2) * (lam 1) * ((eta F lam)^2) * ((lam 2)^3)) + ((-2) * (lam 2) * ((beta F lam)^2) * ((lam 1)^3)) + (2 * (lam 0) * ((alpha F lam)^2) * ((lam 1)^3)) + (2 * (lam 0) * ((eta F lam)^2) * ((lam 2)^3)) + (2 * (lam 0) * ((gamma F lam)^2) * ((lam 1)^3)) + (2 * (lam 2) * ((alpha F lam)^2) * ((lam 1)^3)) + (2 * (lam 2) * ((eta F lam)^2) * ((lam 0)^3)) + (2 * (lam 2) * ((gamma F lam)^2) * ((lam 1)^3)) + (2 * ((eta F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + (2 * ((eta F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + (6 * (lam 0) * ((gamma F lam)^2) * ((lam 2)^3)) + (6 * (lam 1) * ((alpha F lam)^2) * ((lam 0)^3)) + (6 * (lam 1) * ((gamma F lam)^2) * ((lam 2)^3)) + (6 * (lam 2) * ((alpha F lam)^2) * ((lam 0)^3)) + ((-10) * (lam 0) * (lam 1) * ((gamma F lam)^2) * ((lam 2)^2)) + ((-10) * (lam 1) * (lam 2) * ((alpha F lam)^2) * ((lam 0)^2)) + ((-4) * (lam 0) * (lam 2) * ((eta F lam)^2) * ((lam 1)^2)) + ((-2) * (lam 0) * (lam 1) * ((beta F lam)^2) * ((lam 2)^2)) + ((-2) * (lam 1) * (lam 2) * ((beta F lam)^2) * ((lam 0)^2)) + (2 * (lam 0) * (lam 1) * ((eta F lam)^2) * ((lam 2)^2)) + (2 * (lam 0) * (lam 2) * ((alpha F lam)^2) * ((lam 1)^2)) + (2 * (lam 0) * (lam 2) * ((gamma F lam)^2) * ((lam 1)^2)) + (2 * (lam 1) * (lam 2) * ((eta F lam)^2) * ((lam 0)^2)) + (4 * (lam 0) * (lam 2) * ((beta F lam)^2) * ((lam 1)^2)) + (8 * (lam 0) * (lam 1) * ((alpha F lam)^2) * ((lam 2)^2)) + (8 * (lam 1) * (lam 2) * ((gamma F lam)^2) * ((lam 0)^2))) = 0 := by
  have h := H.riem 0 2 0 2
  rw [show Kriem lam 0 2 0 2 = ((lam 0) + (lam 2) + ((-1) * (half) * ((lam 0) + (lam 1) + (lam 2)))) by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S0212 : (((F.e 1 (alpha F lam)) * ((lam 0)^2)) + ((F.e 1 (alpha F lam)) * ((lam 1)^2)) + ((F.e 2 (eta F lam)) * ((lam 1)^2)) + ((F.e 2 (eta F lam)) * (lam 0) * (lam 2)) + ((-1) * (F.e 2 (eta F lam)) * (lam 0) * (lam 1)) + ((-1) * (F.e 2 (eta F lam)) * (lam 1) * (lam 2)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 1)^4)) + ((-4) * (eta F lam) * (gamma F lam) * ((lam 2)^4)) + ((-3) * (alpha F lam) * (beta F lam) * ((lam 1)^4)) + ((-2) * (F.e 1 (alpha F lam)) * (lam 0) * (lam 1)) + ((-2) * (alpha F lam) * (beta F lam) * ((lam 0)^4)) + ((-9) * (eta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^2)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 1)^2)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 2)^2)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 1)^2) * ((lam 2)^2)) + ((-3) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^2)) + ((-3) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^2)) + (4 * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^3)) + (4 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^3)) + (4 * (eta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^3)) + (6 * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^3)) + (6 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 1)^3)) + (6 * (eta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^3)) + (10 * (eta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^3)) + ((-12) * (eta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-8) * (alpha F lam) * (beta F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + ((-2) * (alpha F lam) * (beta F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (6 * (eta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (6 * (eta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (10 * (alpha F lam) * (beta F lam) * (lam 0) * (lam 1) * ((lam 2)^2))) = 0 := by
  have h := H.riem 0 2 1 2
  rw [show Kriem lam 0 2 1 2 = 0 by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S1201 : (((F.e 0 (gamma F lam)) * ((lam 0)^2)) + ((F.e 0 (gamma F lam)) * ((lam 2)^2)) + ((-1) * (F.e 1 (eta F lam)) * ((lam 0)^2)) + ((F.e 1 (eta F lam)) * (lam 0) * (lam 1)) + ((F.e 1 (eta F lam)) * (lam 0) * (lam 2)) + ((beta F lam) * (eta F lam) * ((lam 0)^4)) + ((-1) * (F.e 1 (eta F lam)) * (lam 1) * (lam 2)) + ((-2) * (F.e 0 (gamma F lam)) * (lam 0) * (lam 2)) + (2 * (alpha F lam) * (gamma F lam) * ((lam 2)^4)) + (3 * (alpha F lam) * (gamma F lam) * ((lam 0)^4)) + (4 * (beta F lam) * (eta F lam) * ((lam 1)^4)) + ((-10) * (beta F lam) * (eta F lam) * (lam 0) * ((lam 1)^3)) + ((-6) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^3)) + ((-6) * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^3)) + ((-6) * (beta F lam) * (eta F lam) * (lam 2) * ((lam 1)^3)) + ((-4) * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 2)^3)) + ((-4) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 2)^3)) + ((-4) * (beta F lam) * (eta F lam) * (lam 1) * ((lam 0)^3)) + (3 * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^2)) + (3 * (beta F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^2)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^2)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^2)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^2)) + (9 * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^2)) + ((-10) * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + ((-6) * (beta F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-6) * (beta F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (2 * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + (8 * (alpha F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (12 * (beta F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^2))) = 0 := by
  have h := H.riem 1 2 0 1
  rw [show Kriem lam 1 2 0 1 = 0 by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S1202 : (((F.e 0 (beta F lam)) * ((lam 0)^2)) + ((F.e 0 (beta F lam)) * ((lam 1)^2)) + ((-1) * (F.e 2 (eta F lam)) * ((lam 0)^2)) + ((F.e 2 (eta F lam)) * (lam 0) * (lam 1)) + ((F.e 2 (eta F lam)) * (lam 0) * (lam 2)) + ((-1) * (F.e 2 (eta F lam)) * (lam 1) * (lam 2)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 0)^4)) + ((-4) * (eta F lam) * (gamma F lam) * ((lam 2)^4)) + ((-3) * (alpha F lam) * (beta F lam) * ((lam 0)^4)) + ((-2) * (F.e 0 (beta F lam)) * (lam 0) * (lam 1)) + ((-2) * (alpha F lam) * (beta F lam) * ((lam 1)^4)) + ((-9) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^2)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 1)^2)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 2)^2)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 1)^2) * ((lam 2)^2)) + ((-3) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^2)) + ((-3) * (eta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^2)) + (4 * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^3)) + (4 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 1)^3)) + (4 * (eta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^3)) + (6 * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^3)) + (6 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^3)) + (6 * (eta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^3)) + (10 * (eta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^3)) + ((-12) * (eta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-8) * (alpha F lam) * (beta F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + ((-2) * (alpha F lam) * (beta F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (6 * (eta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^2)) + (6 * (eta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^2)) + (10 * (alpha F lam) * (beta F lam) * (lam 0) * (lam 1) * ((lam 2)^2))) = 0 := by
  have h := H.riem 1 2 0 2
  rw [show Kriem lam 1 2 0 2 = 0 by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem S1212 : (((-1) * (lam 1)) + ((-1) * (lam 2)) + ((F.e 1 (beta F lam)) * ((lam 0)^2)) + ((F.e 1 (beta F lam)) * ((lam 1)^2)) + ((half) * (lam 0)) + ((half) * (lam 1)) + ((half) * (lam 2)) + (((alpha F lam)^2) * ((lam 0)^4)) + ((-1) * (F.e 2 (gamma F lam)) * ((lam 0)^2)) + ((-1) * (F.e 2 (gamma F lam)) * ((lam 2)^2)) + ((-1) * ((beta F lam)^2) * ((lam 0)^4)) + ((-1) * ((gamma F lam)^2) * ((lam 0)^4)) + ((-3) * ((beta F lam)^2) * ((lam 1)^4)) + ((-3) * ((gamma F lam)^2) * ((lam 2)^4)) + (((alpha F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + (((alpha F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + (((alpha F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((beta F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-4) * ((beta F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((beta F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((eta F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-4) * ((gamma F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + ((-4) * ((gamma F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + ((-4) * ((gamma F lam)^2) * ((lam 1)^2) * ((lam 2)^2)) + ((-2) * (F.e 1 (beta F lam)) * (lam 0) * (lam 1)) + ((-2) * (lam 0) * ((eta F lam)^2) * ((lam 1)^3)) + ((-2) * (lam 0) * ((eta F lam)^2) * ((lam 2)^3)) + ((-2) * (lam 1) * ((alpha F lam)^2) * ((lam 0)^3)) + ((-2) * (lam 2) * ((alpha F lam)^2) * ((lam 0)^3)) + (2 * (F.e 2 (gamma F lam)) * (lam 0) * (lam 2)) + (2 * (lam 1) * ((beta F lam)^2) * ((lam 0)^3)) + (2 * (lam 1) * ((eta F lam)^2) * ((lam 2)^3)) + (2 * (lam 1) * ((gamma F lam)^2) * ((lam 0)^3)) + (2 * (lam 2) * ((beta F lam)^2) * ((lam 0)^3)) + (2 * (lam 2) * ((eta F lam)^2) * ((lam 1)^3)) + (2 * (lam 2) * ((gamma F lam)^2) * ((lam 0)^3)) + (2 * ((eta F lam)^2) * ((lam 0)^2) * ((lam 1)^2)) + (2 * ((eta F lam)^2) * ((lam 0)^2) * ((lam 2)^2)) + (6 * (lam 0) * ((beta F lam)^2) * ((lam 1)^3)) + (6 * (lam 0) * ((gamma F lam)^2) * ((lam 2)^3)) + (6 * (lam 1) * ((gamma F lam)^2) * ((lam 2)^3)) + (6 * (lam 2) * ((beta F lam)^2) * ((lam 1)^3)) + ((-10) * (lam 0) * (lam 1) * ((gamma F lam)^2) * ((lam 2)^2)) + ((-10) * (lam 0) * (lam 2) * ((beta F lam)^2) * ((lam 1)^2)) + ((-4) * (lam 1) * (lam 2) * ((eta F lam)^2) * ((lam 0)^2)) + ((-2) * (lam 0) * (lam 1) * ((alpha F lam)^2) * ((lam 2)^2)) + ((-2) * (lam 0) * (lam 2) * ((alpha F lam)^2) * ((lam 1)^2)) + (2 * (lam 0) * (lam 1) * ((eta F lam)^2) * ((lam 2)^2)) + (2 * (lam 0) * (lam 2) * ((eta F lam)^2) * ((lam 1)^2)) + (2 * (lam 1) * (lam 2) * ((beta F lam)^2) * ((lam 0)^2)) + (2 * (lam 1) * (lam 2) * ((gamma F lam)^2) * ((lam 0)^2)) + (4 * (lam 1) * (lam 2) * ((alpha F lam)^2) * ((lam 0)^2)) + (8 * (lam 0) * (lam 1) * ((beta F lam)^2) * ((lam 2)^2)) + (8 * (lam 0) * (lam 2) * ((gamma F lam)^2) * ((lam 1)^2))) = 0 := by
  have h := H.riem 1 2 1 2
  rw [show Kriem lam 1 2 1 2 = ((lam 1) + (lam 2) + ((-1) * (half) * ((lam 0) + (lam 1) + (lam 2)))) by simp [Kriem, Kcurv]; try ring] at h
  simp only [Frame.Riem, Frame.br, Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T001 : (((F.e 0 (beta F lam)) * ((lam 1)^3)) + ((F.e 0 (beta F lam)) * (lam 1) * ((lam 2)^2)) + ((F.e 1 (alpha F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 1 (alpha F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 1 (alpha F lam)) * (lam 2) * ((lam 1)^2)) + ((-1) * (F.e 0 (beta F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 0 (beta F lam)) * (lam 0) * ((lam 2)^2)) + ((-1) * (F.e 1 (alpha F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 1 (alpha F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 1 (alpha F lam)) * (lam 2) * ((lam 0)^2)) + ((-2) * (F.e 0 (beta F lam)) * (lam 2) * ((lam 1)^2)) + ((-2) * (alpha F lam) * (beta F lam) * ((lam 1)^5)) + ((eta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^4)) + ((eta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((eta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-1) * (eta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^4)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-6) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-6) * (alpha F lam) * (beta F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-3) * (alpha F lam) * (beta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^4)) + ((-2) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + (2 * (F.e 0 (beta F lam)) * (lam 0) * (lam 1) * (lam 2)) + (2 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^4)) + (2 * (eta F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + (3 * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 2)^3)) + (3 * (alpha F lam) * (beta F lam) * ((lam 1)^2) * ((lam 2)^3)) + (5 * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^4)) + (5 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 1)^4)) + (5 * (alpha F lam) * (beta F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-8) * (alpha F lam) * (beta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + ((-6) * (alpha F lam) * (beta F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + ((-3) * (eta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (beta F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + ((-2) * (eta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (2 * (eta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (3 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + (3 * (eta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + (9 * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2))) = 0 := by
  have h := F.torsion 0 1 (lam 0)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T002 : (((-1) * (F.e 0 (gamma F lam)) * ((lam 2)^3)) + ((F.e 0 (gamma F lam)) * (lam 0) * ((lam 1)^2)) + ((F.e 0 (gamma F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 2 (alpha F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 2 (alpha F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 2 (alpha F lam)) * (lam 2) * ((lam 1)^2)) + ((-1) * (F.e 0 (gamma F lam)) * (lam 2) * ((lam 1)^2)) + ((-1) * (F.e 2 (alpha F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 2 (alpha F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 2 (alpha F lam)) * (lam 2) * ((lam 0)^2)) + ((-2) * (alpha F lam) * (gamma F lam) * ((lam 2)^5)) + (2 * (F.e 0 (gamma F lam)) * (lam 1) * ((lam 2)^2)) + ((beta F lam) * (eta F lam) * (lam 0) * ((lam 2)^4)) + ((beta F lam) * (eta F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((beta F lam) * (eta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-1) * (beta F lam) * (eta F lam) * (lam 1) * ((lam 2)^4)) + ((-1) * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-1) * (beta F lam) * (eta F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-6) * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-6) * (alpha F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-3) * (alpha F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-2) * (F.e 0 (gamma F lam)) * (lam 0) * (lam 1) * (lam 2)) + ((-2) * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^4)) + ((-2) * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^3)) + (2 * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^4)) + (2 * (beta F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^3)) + (3 * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + (3 * (alpha F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + (5 * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 2)^4)) + (5 * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 2)^4)) + (5 * (alpha F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-8) * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + ((-6) * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + ((-3) * (beta F lam) * (eta F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + ((-2) * (beta F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (2 * (beta F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (3 * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + (3 * (beta F lam) * (eta F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + (9 * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2))) = 0 := by
  have h := F.torsion 0 2 (lam 0)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T012 : (((-1) * (F.e 1 (gamma F lam)) * ((lam 2)^3)) + ((-1) * (F.e 2 (beta F lam)) * ((lam 1)^3)) + ((F.e 1 (gamma F lam)) * (lam 0) * ((lam 1)^2)) + ((F.e 1 (gamma F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 2 (beta F lam)) * (lam 0) * ((lam 1)^2)) + ((F.e 2 (beta F lam)) * (lam 0) * ((lam 2)^2)) + ((-1) * (F.e 1 (gamma F lam)) * (lam 2) * ((lam 1)^2)) + ((-1) * (F.e 2 (beta F lam)) * (lam 1) * ((lam 2)^2)) + ((-2) * (beta F lam) * (gamma F lam) * ((lam 2)^5)) + (2 * (F.e 1 (gamma F lam)) * (lam 1) * ((lam 2)^2)) + (2 * (F.e 2 (beta F lam)) * (lam 2) * ((lam 1)^2)) + (2 * (beta F lam) * (gamma F lam) * ((lam 1)^5)) + ((alpha F lam) * (eta F lam) * (lam 0) * ((lam 1)^4)) + ((alpha F lam) * (eta F lam) * (lam 1) * ((lam 2)^4)) + ((alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-1) * (alpha F lam) * (eta F lam) * (lam 0) * ((lam 2)^4)) + ((-1) * (alpha F lam) * (eta F lam) * (lam 2) * ((lam 1)^4)) + ((-1) * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-11) * (beta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-7) * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^4)) + ((-3) * (alpha F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-3) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^4)) + ((-3) * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-2) * (F.e 1 (gamma F lam)) * (lam 0) * (lam 1) * (lam 2)) + ((-2) * (F.e 2 (beta F lam)) * (lam 0) * (lam 1) * (lam 2)) + (3 * (alpha F lam) * (eta F lam) * ((lam 1)^3) * ((lam 2)^2)) + (3 * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^4)) + (3 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + (7 * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^4)) + (11 * (beta F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-9) * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + ((-6) * (beta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + ((-3) * (alpha F lam) * (eta F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (2 * (alpha F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (3 * (alpha F lam) * (eta F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + (6 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (9 * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2))) = 0 := by
  have h := F.torsion 1 2 (lam 0)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T101 : (((-1) * (F.e 1 (alpha F lam)) * ((lam 0)^3)) + ((F.e 0 (beta F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 0 (beta F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 0 (beta F lam)) * (lam 2) * ((lam 1)^2)) + ((F.e 1 (alpha F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 1 (alpha F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 0 (beta F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 0 (beta F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 0 (beta F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 1 (alpha F lam)) * (lam 0) * ((lam 2)^2)) + (2 * (F.e 1 (alpha F lam)) * (lam 2) * ((lam 0)^2)) + (2 * (alpha F lam) * (beta F lam) * ((lam 0)^5)) + ((eta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^4)) + ((eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((eta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-1) * (eta F lam) * (gamma F lam) * (lam 1) * ((lam 0)^4)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-5) * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^4)) + ((-5) * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^4)) + ((-5) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-3) * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-3) * (alpha F lam) * (beta F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-2) * (F.e 1 (alpha F lam)) * (lam 0) * (lam 1) * (lam 2)) + ((-2) * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 1)^4)) + ((-2) * (eta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + (2 * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^4)) + (2 * (eta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + (3 * (alpha F lam) * (beta F lam) * ((lam 1)^3) * ((lam 2)^2)) + (6 * (alpha F lam) * (beta F lam) * ((lam 0)^3) * ((lam 1)^2)) + (6 * (alpha F lam) * (beta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-9) * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + ((-3) * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + ((-3) * (eta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + ((-2) * (eta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (2 * (alpha F lam) * (beta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (2 * (eta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (3 * (eta F lam) * (gamma F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + (6 * (alpha F lam) * (beta F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (8 * (alpha F lam) * (beta F lam) * (lam 1) * (lam 2) * ((lam 0)^3))) = 0 := by
  have h := F.torsion 0 1 (lam 1)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T102 : (((F.e 0 (gamma F lam)) * ((lam 2)^3)) + ((-1) * (F.e 2 (alpha F lam)) * ((lam 0)^3)) + ((F.e 0 (gamma F lam)) * (lam 2) * ((lam 0)^2)) + ((F.e 2 (alpha F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 2 (alpha F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 0 (gamma F lam)) * (lam 1) * ((lam 0)^2)) + ((-1) * (F.e 0 (gamma F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 2 (alpha F lam)) * (lam 0) * ((lam 2)^2)) + ((-2) * (F.e 0 (gamma F lam)) * (lam 0) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (gamma F lam) * ((lam 0)^5)) + (2 * (F.e 2 (alpha F lam)) * (lam 2) * ((lam 0)^2)) + (2 * (alpha F lam) * (gamma F lam) * ((lam 2)^5)) + ((beta F lam) * (eta F lam) * (lam 1) * ((lam 2)^4)) + ((beta F lam) * (eta F lam) * (lam 2) * ((lam 0)^4)) + ((beta F lam) * (eta F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-1) * (beta F lam) * (eta F lam) * (lam 0) * ((lam 2)^4)) + ((-1) * (beta F lam) * (eta F lam) * (lam 1) * ((lam 0)^4)) + ((-1) * (beta F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-11) * (alpha F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-7) * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 2)^4)) + ((-3) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 2)^4)) + ((-3) * (alpha F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-3) * (beta F lam) * (eta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-2) * (F.e 2 (alpha F lam)) * (lam 0) * (lam 1) * (lam 2)) + (2 * (F.e 0 (gamma F lam)) * (lam 0) * (lam 1) * (lam 2)) + (3 * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^4)) + (3 * (alpha F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + (3 * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^3)) + (7 * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^4)) + (11 * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-9) * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + ((-6) * (alpha F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + ((-3) * (beta F lam) * (eta F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + ((-2) * (beta F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (2 * (beta F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (3 * (beta F lam) * (eta F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + (6 * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (9 * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2))) = 0 := by
  have h := F.torsion 0 2 (lam 1)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T112 : (((F.e 1 (gamma F lam)) * ((lam 2)^3)) + ((F.e 1 (gamma F lam)) * (lam 2) * ((lam 0)^2)) + ((F.e 2 (beta F lam)) * (lam 0) * ((lam 1)^2)) + ((F.e 2 (beta F lam)) * (lam 1) * ((lam 2)^2)) + ((F.e 2 (beta F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 1 (gamma F lam)) * (lam 1) * ((lam 0)^2)) + ((-1) * (F.e 1 (gamma F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 2 (beta F lam)) * (lam 0) * ((lam 2)^2)) + ((-1) * (F.e 2 (beta F lam)) * (lam 1) * ((lam 0)^2)) + ((-1) * (F.e 2 (beta F lam)) * (lam 2) * ((lam 1)^2)) + ((-2) * (F.e 1 (gamma F lam)) * (lam 0) * ((lam 2)^2)) + (2 * (beta F lam) * (gamma F lam) * ((lam 2)^5)) + ((alpha F lam) * (eta F lam) * (lam 0) * ((lam 2)^4)) + ((alpha F lam) * (eta F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((alpha F lam) * (eta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-1) * (alpha F lam) * (eta F lam) * (lam 1) * ((lam 2)^4)) + ((-1) * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-1) * (alpha F lam) * (eta F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-5) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^4)) + ((-5) * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^4)) + ((-5) * (beta F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-3) * (beta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-3) * (beta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-2) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^4)) + (2 * (F.e 1 (gamma F lam)) * (lam 0) * (lam 1) * (lam 2)) + (2 * (alpha F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^3)) + (2 * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^4)) + (3 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + (6 * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + (6 * (beta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-9) * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + ((-3) * (alpha F lam) * (eta F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + ((-3) * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (2 * (alpha F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (2 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (3 * (alpha F lam) * (eta F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + (6 * (beta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (8 * (beta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3))) = 0 := by
  have h := F.torsion 1 2 (lam 1)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T201 : (((F.e 1 (alpha F lam)) * ((lam 0)^3)) + ((-1) * (F.e 0 (beta F lam)) * ((lam 1)^3)) + ((F.e 0 (beta F lam)) * (lam 2) * ((lam 0)^2)) + ((F.e 0 (beta F lam)) * (lam 2) * ((lam 1)^2)) + ((F.e 1 (alpha F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 0 (beta F lam)) * (lam 1) * ((lam 0)^2)) + ((-1) * (F.e 1 (alpha F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 1 (alpha F lam)) * (lam 2) * ((lam 1)^2)) + ((-2) * (F.e 1 (alpha F lam)) * (lam 1) * ((lam 0)^2)) + ((-2) * (alpha F lam) * (beta F lam) * ((lam 0)^5)) + (2 * (F.e 0 (beta F lam)) * (lam 0) * ((lam 1)^2)) + (2 * (alpha F lam) * (beta F lam) * ((lam 1)^5)) + ((eta F lam) * (gamma F lam) * (lam 1) * ((lam 0)^4)) + ((eta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^4)) + ((eta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-1) * (eta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^4)) + ((-1) * (eta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^4)) + ((-1) * (eta F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-11) * (alpha F lam) * (beta F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-7) * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^4)) + ((-3) * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 1)^4)) + ((-3) * (alpha F lam) * (beta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-3) * (eta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-2) * (F.e 0 (beta F lam)) * (lam 0) * (lam 1) * (lam 2)) + (2 * (F.e 1 (alpha F lam)) * (lam 0) * (lam 1) * (lam 2)) + (3 * (alpha F lam) * (beta F lam) * (lam 2) * ((lam 0)^4)) + (3 * (alpha F lam) * (beta F lam) * ((lam 1)^3) * ((lam 2)^2)) + (3 * (eta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + (7 * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^4)) + (11 * (alpha F lam) * (beta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-9) * (alpha F lam) * (beta F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + ((-6) * (alpha F lam) * (beta F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + ((-3) * (eta F lam) * (gamma F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + ((-2) * (eta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (2 * (eta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (3 * (eta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + (6 * (alpha F lam) * (beta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (9 * (alpha F lam) * (beta F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2))) = 0 := by
  have h := F.torsion 0 1 (lam 2)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T202 : (((F.e 2 (alpha F lam)) * ((lam 0)^3)) + ((F.e 0 (gamma F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 0 (gamma F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 0 (gamma F lam)) * (lam 2) * ((lam 1)^2)) + ((F.e 2 (alpha F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 0 (gamma F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 0 (gamma F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 0 (gamma F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 2 (alpha F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 2 (alpha F lam)) * (lam 2) * ((lam 1)^2)) + ((-2) * (F.e 2 (alpha F lam)) * (lam 1) * ((lam 0)^2)) + (2 * (alpha F lam) * (gamma F lam) * ((lam 0)^5)) + ((beta F lam) * (eta F lam) * (lam 1) * ((lam 0)^4)) + ((beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((beta F lam) * (eta F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-1) * (beta F lam) * (eta F lam) * (lam 2) * ((lam 0)^4)) + ((-1) * (beta F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-1) * (beta F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-5) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^4)) + ((-5) * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^4)) + ((-5) * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-3) * (alpha F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-3) * (alpha F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-2) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 2)^4)) + ((-2) * (beta F lam) * (eta F lam) * ((lam 0)^3) * ((lam 1)^2)) + (2 * (F.e 2 (alpha F lam)) * (lam 0) * (lam 1) * (lam 2)) + (2 * (alpha F lam) * (gamma F lam) * (lam 0) * ((lam 2)^4)) + (2 * (beta F lam) * (eta F lam) * ((lam 0)^3) * ((lam 2)^2)) + (3 * (alpha F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + (6 * (alpha F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + (6 * (alpha F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-9) * (alpha F lam) * (gamma F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + ((-3) * (alpha F lam) * (gamma F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + ((-3) * (beta F lam) * (eta F lam) * (lam 1) * ((lam 0)^2) * ((lam 2)^2)) + ((-2) * (beta F lam) * (eta F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (2 * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (2 * (beta F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (3 * (beta F lam) * (eta F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + (6 * (alpha F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + (8 * (alpha F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3))) = 0 := by
  have h := F.torsion 0 2 (lam 2)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h

theorem T212 : (((F.e 2 (beta F lam)) * ((lam 1)^3)) + ((F.e 1 (gamma F lam)) * (lam 0) * ((lam 2)^2)) + ((F.e 1 (gamma F lam)) * (lam 1) * ((lam 0)^2)) + ((F.e 1 (gamma F lam)) * (lam 2) * ((lam 1)^2)) + ((F.e 2 (beta F lam)) * (lam 1) * ((lam 0)^2)) + ((-1) * (F.e 1 (gamma F lam)) * (lam 0) * ((lam 1)^2)) + ((-1) * (F.e 1 (gamma F lam)) * (lam 1) * ((lam 2)^2)) + ((-1) * (F.e 1 (gamma F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 2 (beta F lam)) * (lam 2) * ((lam 0)^2)) + ((-1) * (F.e 2 (beta F lam)) * (lam 2) * ((lam 1)^2)) + ((-2) * (F.e 2 (beta F lam)) * (lam 0) * ((lam 1)^2)) + ((-2) * (beta F lam) * (gamma F lam) * ((lam 1)^5)) + ((alpha F lam) * (eta F lam) * (lam 2) * ((lam 1)^4)) + ((alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((alpha F lam) * (eta F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-1) * (alpha F lam) * (eta F lam) * (lam 0) * ((lam 1)^4)) + ((-1) * (alpha F lam) * (eta F lam) * ((lam 0)^3) * ((lam 1)^2)) + ((-1) * (alpha F lam) * (eta F lam) * ((lam 0)^3) * ((lam 2)^2)) + ((-6) * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 1)^3)) + ((-6) * (beta F lam) * (gamma F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-3) * (beta F lam) * (gamma F lam) * ((lam 0)^2) * ((lam 2)^3)) + ((-2) * (alpha F lam) * (eta F lam) * ((lam 1)^3) * ((lam 2)^2)) + ((-2) * (beta F lam) * (gamma F lam) * (lam 1) * ((lam 2)^4)) + (2 * (F.e 2 (beta F lam)) * (lam 0) * (lam 1) * (lam 2)) + (2 * (alpha F lam) * (eta F lam) * ((lam 0)^2) * ((lam 1)^3)) + (2 * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 2)^4)) + (3 * (beta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 1)^2)) + (3 * (beta F lam) * (gamma F lam) * ((lam 0)^3) * ((lam 2)^2)) + (5 * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^4)) + (5 * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 1)^4)) + (5 * (beta F lam) * (gamma F lam) * ((lam 1)^2) * ((lam 2)^3)) + ((-8) * (beta F lam) * (gamma F lam) * (lam 0) * (lam 2) * ((lam 1)^3)) + ((-6) * (beta F lam) * (gamma F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + ((-3) * (alpha F lam) * (eta F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2)) + ((-2) * (alpha F lam) * (eta F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + ((-2) * (beta F lam) * (gamma F lam) * (lam 0) * (lam 1) * ((lam 2)^3)) + (2 * (alpha F lam) * (eta F lam) * (lam 1) * (lam 2) * ((lam 0)^3)) + (3 * (alpha F lam) * (eta F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + (3 * (beta F lam) * (gamma F lam) * (lam 0) * ((lam 1)^2) * ((lam 2)^2)) + (9 * (beta F lam) * (gamma F lam) * (lam 2) * ((lam 0)^2) * ((lam 1)^2))) = 0 := by
  have h := F.torsion 1 2 (lam 2)
  simp only [Fin.sum_univ_three] at h
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at h
  try simp only [map_add, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at h
  linear_combination h


/-- |∇Ric|² = Σ_{k,i,j} ((∇_k Ric)_ij)² -/
def _root_.CFT.Cartan.Frame.gradRic2 (F : Frame R) (lam : Fin 3 → R) : R :=
  ∑ k, ∑ i, ∑ j, F.nablaRic lam k i j * F.nablaRic lam k i j

/-- κ = Σ_{i<j} K_ij (λ_i − λ_j)²、K_ij = λ_i + λ_j − R/2(2 平面の断面曲率) -/
noncomputable def _root_.CFT.Cartan.kappaSum (lam : Fin 3 → R) : R :=
  Kcurv lam 0 1 * (lam 0 - lam 1)^2 + Kcurv lam 0 2 * (lam 0 - lam 2)^2
    + Kcurv lam 1 2 * (lam 1 - lam 2)^2

/-- α-II.4(Z4-1, Z4-2):1 段目の両立条件は Bochner 恒等式
  |∇Ric|² + Σ_{i<j} K_ij(λ_i − λ_j)² = 0。
  実際 |∇Ric|² + κ = −(λ₀−λ₁)²·S0101 − (λ₀−λ₂)²·S0202 − (λ₁−λ₂)²·S1212(曲率の構造式の一次結合) -/
theorem bochner : F.gradRic2 lam + kappaSum lam = 0 := by
  simp only [Frame.gradRic2, kappaSum, Kcurv, Frame.nablaRic, ricD, Fin.sum_univ_three]
  try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, map_zero, mul_zero, sub_zero, zero_add, add_zero]
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122]
  try simp only [H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22]
  linear_combination (-(lam 0 - lam 1)^2) * H.S0101 + (-(lam 0 - lam 2)^2) * H.S0202
    + (-(lam 1 - lam 2)^2) * H.S1212

end C2

end CFT.Cartan
