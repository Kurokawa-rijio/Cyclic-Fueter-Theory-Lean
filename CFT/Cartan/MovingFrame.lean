/-
  Cartan の動標構(3 次元、正規直交枠)の代数的な形式化

  R は開集合 U 上の滑らかな関数の環(可換、ℚ 代数)。正規直交枠 e₀, e₁, e₂ を R の導分として、
  Levi-Civita 接続の係数 Γ i j k = ⟨∇_{e_k} e_j, e_i⟩ を R の元として持つ。
    * 計量との両立:Γ i j k = −Γ j i k
    * 捩れゼロ:[e_k, e_m] = Σ_x (Γ x m k − Γ x k m) e_x(関数に作用させた形)
  曲率 Riem n j k m = ⟨R(e_k, e_m)e_j, e_n⟩ と Ricci Ric j m = Σ_n Riem n j n m は定義。
  多様体の上の幾何から Lean に入るのはこの二つの公理だけである。
  (U 上で消えない関数は R の単元である、という事実は各定理の仮定 IsUnit として入れる。)

  この節の定理:
    * Riem_anti_left, Riem_anti_right:曲率の反対称性(公理から導く)
    * riem_of_diag_ricci:3 次元では、両側反対称な 4 階テンソルは Ricci 縮約で決まる。
      Ric = diag(λ) なら Riem は断面曲率 K_km = λ_k + λ_m − R/2 で書ける(第一 Bianchi は不要)
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace CFT.Cartan

set_option maxHeartbeats 0

/-- 3 次元の正規直交動標構と Levi-Civita 接続係数 -/
structure Frame (R : Type*) [CommRing R] [Algebra ℚ R] where
  e : Fin 3 → Derivation ℚ R R
  Γ : Fin 3 → Fin 3 → Fin 3 → R
  metric : ∀ i j k, Γ i j k = -Γ j i k
  torsion : ∀ k m (f : R), e k (e m f) - e m (e k f) = ∑ x, (Γ x m k - Γ x k m) * e x f

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- ℚ 代数では 2 は単元 -/
theorem two_isUnit : IsUnit (2 : R) := by
  have : (2 : R) = algebraMap ℚ R 2 := (map_ofNat (algebraMap ℚ R) 2).symm
  rw [this]; exact (IsUnit.mk0 (2 : ℚ) (by norm_num)).map _

/-- ℚ 代数では 0 でない自然数は単元 -/
theorem natCast_isUnit (n : ℕ) (hn : n ≠ 0) : IsUnit (n : R) := by
  have : (n : R) = algebraMap ℚ R n := (map_natCast (algebraMap ℚ R) n).symm
  rw [this]; exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast hn)).map _

namespace Frame

variable (F : Frame R)

/-- 枠の交換子の係数 [e_k, e_m] = Σ_x br k m x · e_x -/
def br (k m x : Fin 3) : R := F.Γ x m k - F.Γ x k m

/-- 曲率 ⟨R(e_k,e_m)e_j, e_n⟩、R(X,Y) = ∇_X∇_Y − ∇_Y∇_X − ∇_{[X,Y]} -/
def Riem (n j k m : Fin 3) : R :=
  F.e k (F.Γ n j m) - F.e m (F.Γ n j k)
    + ∑ x, (F.Γ x j m * F.Γ n x k - F.Γ x j k * F.Γ n x m)
    - ∑ x, F.br k m x * F.Γ n j x

/-- Ricci テンソル Ric(e_j, e_m) = Σ_n ⟨R(e_n, e_m)e_j, e_n⟩ -/
def Ric (j m : Fin 3) : R := ∑ n, F.Riem n j n m

theorem Γ_diag (i k : Fin 3) : F.Γ i i k = 0 := by
  have h := F.metric i i k
  have h2 : (2 : R) * F.Γ i i k = 0 := by linear_combination h
  have hu : IsUnit (2 : R) := by
    have : (2 : R) = algebraMap ℚ R 2 := (map_ofNat (algebraMap ℚ R) 2).symm
    rw [this]; exact (IsUnit.mk0 (2 : ℚ) (by norm_num)).map _
  exact (hu.mul_right_eq_zero).mp h2

theorem Riem_anti_left (n j k m : Fin 3) : F.Riem n j k m = -F.Riem j n k m := by
  have hm : ∀ i j k, F.Γ i j k = -F.Γ j i k := F.metric
  simp only [Riem, br, Fin.sum_univ_three]
  rw [hm n j m, hm n j k, map_neg, map_neg]
  rw [hm 0 j m, hm 1 j m, hm 2 j m, hm 0 j k, hm 1 j k, hm 2 j k,
    hm n 0 k, hm n 1 k, hm n 2 k, hm n 0 m, hm n 1 m, hm n 2 m, hm n j 0, hm n j 1, hm n j 2]
  ring

theorem Riem_anti_right (n j k m : Fin 3) : F.Riem n j k m = -F.Riem n j m k := by
  simp only [Riem, br, Fin.sum_univ_three]; ring

end Frame


/-- 1/2 ∈ R(ℚ 代数) -/
noncomputable def half : R := algebraMap ℚ R (1 / 2)

theorem two_mul_half : (2 : R) * half = 1 := by
  rw [half, ← map_ofNat (algebraMap ℚ R) 2, ← map_mul]; norm_num

/-- 3 次元:Ric = diag(λ) の両側反対称テンソルの成分。K(k,m) = λ_k + λ_m − (λ₀+λ₁+λ₂)/2 -/
noncomputable def Kcurv (lam : Fin 3 → R) (k m : Fin 3) : R :=
  lam k + lam m - half * (lam 0 + lam 1 + lam 2)

noncomputable def Kriem (lam : Fin 3 → R) (n j k m : Fin 3) : R :=
  if k = m then 0 else if n = k ∧ j = m then Kcurv lam k m
  else if n = m ∧ j = k then -Kcurv lam k m else 0

/-- 3 次元では、両側反対称な 4 階テンソルは Ricci 縮約で決まる -/
theorem riem_of_diag_ricci (lam : Fin 3 → R) (T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R)
    (hL : ∀ n j k m, T n j k m + T j n k m = 0) (hR : ∀ n j k m, T n j k m + T n j m k = 0)
    (hD : ∀ j, T 0 j 0 j + T 1 j 1 j + T 2 j 2 j = lam j)
    (hO : ∀ j m, j ≠ m → T 0 j 0 m + T 1 j 1 m + T 2 j 2 m = 0) :
    ∀ n j k m, T n j k m = Kriem lam n j k m := by
  have hhalf : (2 : R) * half - 1 = 0 := by rw [two_mul_half]; ring
  have r00 : T 0 0 0 0 + T 1 0 1 0 + T 2 0 2 0 - lam 0 = 0 := by rw [hD 0]; ring
  have r01 : T 0 0 0 1 + T 1 0 1 1 + T 2 0 2 1 - 0 = 0 := by rw [hO 0 1 (by decide)]; ring
  have r02 : T 0 0 0 2 + T 1 0 1 2 + T 2 0 2 2 - 0 = 0 := by rw [hO 0 2 (by decide)]; ring
  have r10 : T 0 1 0 0 + T 1 1 1 0 + T 2 1 2 0 - 0 = 0 := by rw [hO 1 0 (by decide)]; ring
  have r11 : T 0 1 0 1 + T 1 1 1 1 + T 2 1 2 1 - lam 1 = 0 := by rw [hD 1]; ring
  have r12 : T 0 1 0 2 + T 1 1 1 2 + T 2 1 2 2 - 0 = 0 := by rw [hO 1 2 (by decide)]; ring
  have r20 : T 0 2 0 0 + T 1 2 1 0 + T 2 2 2 0 - 0 = 0 := by rw [hO 2 0 (by decide)]; ring
  have r21 : T 0 2 0 1 + T 1 2 1 1 + T 2 2 2 1 - 0 = 0 := by rw [hO 2 1 (by decide)]; ring
  have r22 : T 0 2 0 2 + T 1 2 1 2 + T 2 2 2 2 - lam 2 = 0 := by rw [hD 2]; ring
  have c0000 : T 0 0 0 0 = Kriem lam 0 0 0 0 := by
    rw [show Kriem lam 0 0 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 0) + (-T 0 0 0 0) * hhalf
  have c0001 : T 0 0 0 1 = Kriem lam 0 0 0 1 := by
    rw [show Kriem lam 0 0 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 1) + (-T 0 0 0 1) * hhalf
  have c0002 : T 0 0 0 2 = Kriem lam 0 0 0 2 := by
    rw [show Kriem lam 0 0 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 2) + (-T 0 0 0 2) * hhalf
  have c0010 : T 0 0 1 0 = Kriem lam 0 0 1 0 := by
    rw [show Kriem lam 0 0 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 0 1) + (1) * (hR 0 0 0 1) + (T 0 0 0 1) * hhalf
  have c0011 : T 0 0 1 1 = Kriem lam 0 0 1 1 := by
    rw [show Kriem lam 0 0 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 1 1) + (-T 0 0 1 1) * hhalf
  have c0012 : T 0 0 1 2 = Kriem lam 0 0 1 2 := by
    rw [show Kriem lam 0 0 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 1 2) + (-T 0 0 1 2) * hhalf
  have c0020 : T 0 0 2 0 = Kriem lam 0 0 2 0 := by
    rw [show Kriem lam 0 0 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 0 2) + (1) * (hR 0 0 0 2) + (T 0 0 0 2) * hhalf
  have c0021 : T 0 0 2 1 = Kriem lam 0 0 2 1 := by
    rw [show Kriem lam 0 0 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 1 2) + (1) * (hR 0 0 1 2) + (T 0 0 1 2) * hhalf
  have c0022 : T 0 0 2 2 = Kriem lam 0 0 2 2 := by
    rw [show Kriem lam 0 0 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 2 2) + (-T 0 0 2 2) * hhalf
  have c0100 : T 0 1 0 0 = Kriem lam 0 1 0 0 := by
    rw [show Kriem lam 0 1 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 1 0 0) + (-T 0 1 0 0) * hhalf
  have c0101 : T 0 1 0 1 = Kriem lam 0 1 0 1 := by
    rw [show Kriem lam 0 1 0 1 = lam 0 + lam 1 - half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half^2) * (hL 0 0 0 0) + (half) * (hR 0 1 0 1) + (-half) * (hL 0 1 1 0) + (half) * (hR 0 2 0 2) + (-half) * (hL 0 2 2 0) + (-half^2) * (hL 1 1 1 1) + (half) * (hR 1 2 1 2) + (-half) * (hL 1 2 2 1) + (half^2) * (hL 2 2 2 2) + (half) * r00 + (half) * r11 + (-half) * r22 + (lam 0 + lam 1 + T 0 0 0 0*half - T 0 1 0 1 + T 1 1 1 1*half - T 2 2 2 2*half) * hhalf
  have c0102 : T 0 1 0 2 = Kriem lam 0 1 0 2 := by
    rw [show Kriem lam 0 1 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 1 1 1 2) + (-1) * (hL 1 2 2 2) + (half) * (hR 1 2 2 2) + (1) * r12 + (T 1 1 1 2 - T 1 2 2 2) * hhalf
  have c0110 : T 0 1 1 0 = Kriem lam 0 1 1 0 := by
    rw [show Kriem lam 0 1 1 0 = -lam 0 - lam 1 + half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (half^2) * (hL 0 0 0 0) + (half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (-half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (half^2) * (hL 1 1 1 1) + (-half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (-half^2) * (hL 2 2 2 2) + (-half) * r00 + (-half) * r11 + (half) * r22 + (-lam 0 - lam 1 - T 0 0 0 0*half - T 0 1 1 0 - T 1 1 1 1*half + T 2 2 2 2*half) * hhalf
  have c0111 : T 0 1 1 1 = Kriem lam 0 1 1 1 := by
    rw [show Kriem lam 0 1 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 1 1 1) + (-T 0 1 1 1) * hhalf
  have c0112 : T 0 1 1 2 = Kriem lam 0 1 1 2 := by
    rw [show Kriem lam 0 1 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 2) + (1) * (hL 0 1 1 2) + (1) * (hL 0 2 2 2) + (-half) * (hR 0 2 2 2) + (-1) * r02 + (-T 0 0 0 2 + T 0 2 2 2) * hhalf
  have c0120 : T 0 1 2 0 = Kriem lam 0 1 2 0 := by
    rw [show Kriem lam 0 1 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hR 0 1 0 2) + (half) * (hL 1 1 1 2) + (1) * (hL 1 2 2 2) + (-half) * (hR 1 2 2 2) + (-1) * r12 + (-T 1 1 1 2 + T 1 2 2 2) * hhalf
  have c0121 : T 0 1 2 1 = Kriem lam 0 1 2 1 := by
    rw [show Kriem lam 0 1 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 0 2) + (-1) * (hL 0 1 1 2) + (1) * (hR 0 1 1 2) + (-1) * (hL 0 2 2 2) + (half) * (hR 0 2 2 2) + (1) * r02 + (T 0 0 0 2 - T 0 2 2 2) * hhalf
  have c0122 : T 0 1 2 2 = Kriem lam 0 1 2 2 := by
    rw [show Kriem lam 0 1 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 1 2 2) + (-T 0 1 2 2) * hhalf
  have c0200 : T 0 2 0 0 = Kriem lam 0 2 0 0 := by
    rw [show Kriem lam 0 2 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 2 0 0) + (-T 0 2 0 0) * hhalf
  have c0201 : T 0 2 0 1 = Kriem lam 0 2 0 1 := by
    rw [show Kriem lam 0 2 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hR 1 2 1 1) + (half) * (hL 2 2 1 2) + (-1) * (hR 2 2 1 2) + (1) * r21 + (T 1 2 1 1 - T 2 2 1 2) * hhalf
  have c0202 : T 0 2 0 2 = Kriem lam 0 2 0 2 := by
    rw [show Kriem lam 0 2 0 2 = lam 0 + lam 2 - half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half^2) * (hL 0 0 0 0) + (half) * (hR 0 1 0 1) + (-half) * (hL 0 1 1 0) + (half) * (hR 0 2 0 2) + (-half) * (hL 0 2 2 0) + (half^2) * (hL 1 1 1 1) + (-half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (-half^2) * (hL 2 2 2 2) + (half) * r00 + (-half) * r11 + (half) * r22 + (lam 0 + lam 2 + T 0 0 0 0*half - T 0 2 0 2 - T 1 1 1 1*half + T 2 2 2 2*half) * hhalf
  have c0210 : T 0 2 1 0 = Kriem lam 0 2 1 0 := by
    rw [show Kriem lam 0 2 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hR 0 2 0 1) + (half) * (hR 1 2 1 1) + (-half) * (hL 2 2 1 2) + (1) * (hR 2 2 1 2) + (-1) * r21 + (-T 1 2 1 1 + T 2 2 1 2) * hhalf
  have c0211 : T 0 2 1 1 = Kriem lam 0 2 1 1 := by
    rw [show Kriem lam 0 2 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 2 1 1) + (-T 0 2 1 1) * hhalf
  have c0212 : T 0 2 1 2 = Kriem lam 0 2 1 2 := by
    rw [show Kriem lam 0 2 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 0 1) + (-1) * (hL 0 1 1 1) + (half) * (hR 0 1 1 1) + (1) * (hR 0 2 1 2) + (-1) * (hL 0 2 2 1) + (1) * r01 + (T 0 0 0 1 - T 0 1 1 1) * hhalf
  have c0220 : T 0 2 2 0 = Kriem lam 0 2 2 0 := by
    rw [show Kriem lam 0 2 2 0 = -lam 0 - lam 2 + half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (half^2) * (hL 0 0 0 0) + (-half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (-half^2) * (hL 1 1 1 1) + (half) * (hR 1 2 1 2) + (-half) * (hL 1 2 2 1) + (half^2) * (hL 2 2 2 2) + (-half) * r00 + (half) * r11 + (-half) * r22 + (-lam 0 - lam 2 - T 0 0 0 0*half - T 0 2 2 0 + T 1 1 1 1*half - T 2 2 2 2*half) * hhalf
  have c0221 : T 0 2 2 1 = Kriem lam 0 2 2 1 := by
    rw [show Kriem lam 0 2 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 1) + (1) * (hL 0 1 1 1) + (-half) * (hR 0 1 1 1) + (1) * (hL 0 2 2 1) + (-1) * r01 + (-T 0 0 0 1 + T 0 1 1 1) * hhalf
  have c0222 : T 0 2 2 2 = Kriem lam 0 2 2 2 := by
    rw [show Kriem lam 0 2 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 2 2 2) + (-T 0 2 2 2) * hhalf
  have c1000 : T 1 0 0 0 = Kriem lam 1 0 0 0 := by
    rw [show Kriem lam 1 0 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 1 0 0) + (-half) * (hR 0 1 0 0) + (T 0 1 0 0) * hhalf
  have c1001 : T 1 0 0 1 = Kriem lam 1 0 0 1 := by
    rw [show Kriem lam 1 0 0 1 = -lam 0 - lam 1 + half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (half^2) * (hL 0 0 0 0) + (1) * (hL 0 1 0 1) + (-half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (-half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (half^2) * (hL 1 1 1 1) + (-half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (-half^2) * (hL 2 2 2 2) + (-half) * r00 + (-half) * r11 + (half) * r22 + (-lam 0 - lam 1 - T 0 0 0 0*half + T 0 1 0 1 - T 1 1 1 1*half + T 2 2 2 2*half) * hhalf
  have c1002 : T 1 0 0 2 = Kriem lam 1 0 0 2 := by
    rw [show Kriem lam 1 0 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 1 0 2) + (half) * (hL 1 1 1 2) + (1) * (hL 1 2 2 2) + (-half) * (hR 1 2 2 2) + (-1) * r12 + (-T 1 1 1 2 + T 1 2 2 2) * hhalf
  have c1010 : T 1 0 1 0 = Kriem lam 1 0 1 0 := by
    rw [show Kriem lam 1 0 1 0 = lam 0 + lam 1 - half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half^2) * (hL 0 0 0 0) + (-half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (half) * (hR 0 2 0 2) + (-half) * (hL 0 2 2 0) + (-half^2) * (hL 1 1 1 1) + (half) * (hR 1 2 1 2) + (-half) * (hL 1 2 2 1) + (half^2) * (hL 2 2 2 2) + (half) * r00 + (half) * r11 + (-half) * r22 + (lam 0 + lam 1 + T 0 0 0 0*half - T 1 0 1 0 + T 1 1 1 1*half - T 2 2 2 2*half) * hhalf
  have c1011 : T 1 0 1 1 = Kriem lam 1 0 1 1 := by
    rw [show Kriem lam 1 0 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 1 1 1) + (-half) * (hR 0 1 1 1) + (T 0 1 1 1) * hhalf
  have c1012 : T 1 0 1 2 = Kriem lam 1 0 1 2 := by
    rw [show Kriem lam 1 0 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 0 2) + (-1) * (hL 0 2 2 2) + (half) * (hR 0 2 2 2) + (1) * r02 + (T 0 0 0 2 - T 0 2 2 2) * hhalf
  have c1020 : T 1 0 2 0 = Kriem lam 1 0 2 0 := by
    rw [show Kriem lam 1 0 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-1) * (hR 0 1 0 2) + (1) * (hL 0 1 2 0) + (-half) * (hL 1 1 1 2) + (-1) * (hL 1 2 2 2) + (half) * (hR 1 2 2 2) + (1) * r12 + (T 1 1 1 2 - T 1 2 2 2) * hhalf
  have c1021 : T 1 0 2 1 = Kriem lam 1 0 2 1 := by
    rw [show Kriem lam 1 0 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 2) + (1) * (hL 0 1 1 2) + (-1) * (hR 0 1 1 2) + (1) * (hL 0 1 2 1) + (1) * (hL 0 2 2 2) + (-half) * (hR 0 2 2 2) + (-1) * r02 + (-T 0 0 0 2 + T 0 2 2 2) * hhalf
  have c1022 : T 1 0 2 2 = Kriem lam 1 0 2 2 := by
    rw [show Kriem lam 1 0 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 1 2 2) + (-half) * (hR 0 1 2 2) + (T 0 1 2 2) * hhalf
  have c1100 : T 1 1 0 0 = Kriem lam 1 1 0 0 := by
    rw [show Kriem lam 1 1 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 1 1 0 0) + (-T 1 1 0 0) * hhalf
  have c1101 : T 1 1 0 1 = Kriem lam 1 1 0 1 := by
    rw [show Kriem lam 1 1 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 1 1 0 1) + (-T 1 1 0 1) * hhalf
  have c1102 : T 1 1 0 2 = Kriem lam 1 1 0 2 := by
    rw [show Kriem lam 1 1 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 1 1 0 2) + (-T 1 1 0 2) * hhalf
  have c1110 : T 1 1 1 0 = Kriem lam 1 1 1 0 := by
    rw [show Kriem lam 1 1 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 1 1 0 1) + (1) * (hR 1 1 0 1) + (T 1 1 0 1) * hhalf
  have c1111 : T 1 1 1 1 = Kriem lam 1 1 1 1 := by
    rw [show Kriem lam 1 1 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 1 1 1 1) + (-T 1 1 1 1) * hhalf
  have c1112 : T 1 1 1 2 = Kriem lam 1 1 1 2 := by
    rw [show Kriem lam 1 1 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 1 1 1 2) + (-T 1 1 1 2) * hhalf
  have c1120 : T 1 1 2 0 = Kriem lam 1 1 2 0 := by
    rw [show Kriem lam 1 1 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 1 1 0 2) + (1) * (hR 1 1 0 2) + (T 1 1 0 2) * hhalf
  have c1121 : T 1 1 2 1 = Kriem lam 1 1 2 1 := by
    rw [show Kriem lam 1 1 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 1 1 1 2) + (1) * (hR 1 1 1 2) + (T 1 1 1 2) * hhalf
  have c1122 : T 1 1 2 2 = Kriem lam 1 1 2 2 := by
    rw [show Kriem lam 1 1 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 1 1 2 2) + (-T 1 1 2 2) * hhalf
  have c1200 : T 1 2 0 0 = Kriem lam 1 2 0 0 := by
    rw [show Kriem lam 1 2 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 1 2 0 0) + (-T 1 2 0 0) * hhalf
  have c1201 : T 1 2 0 1 = Kriem lam 1 2 0 1 := by
    rw [show Kriem lam 1 2 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 2 0 0) + (1) * (hR 1 2 0 1) + (-half) * (hL 2 2 0 2) + (1) * (hR 2 2 0 2) + (-1) * r20 + (-T 0 2 0 0 + T 2 2 0 2) * hhalf
  have c1202 : T 1 2 0 2 = Kriem lam 1 2 0 2 := by
    rw [show Kriem lam 1 2 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hR 0 1 0 0) + (half) * (hL 1 1 0 1) + (-1) * (hR 1 1 0 1) + (1) * (hR 1 2 0 2) + (-1) * (hL 1 2 2 0) + (1) * r10 + (T 0 1 0 0 - T 1 1 0 1) * hhalf
  have c1210 : T 1 2 1 0 = Kriem lam 1 2 1 0 := by
    rw [show Kriem lam 1 2 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hR 0 2 0 0) + (half) * (hL 2 2 0 2) + (-1) * (hR 2 2 0 2) + (1) * r20 + (T 0 2 0 0 - T 2 2 0 2) * hhalf
  have c1211 : T 1 2 1 1 = Kriem lam 1 2 1 1 := by
    rw [show Kriem lam 1 2 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 1 2 1 1) + (-T 1 2 1 1) * hhalf
  have c1212 : T 1 2 1 2 = Kriem lam 1 2 1 2 := by
    rw [show Kriem lam 1 2 1 2 = lam 1 + lam 2 - half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (half^2) * (hL 0 0 0 0) + (-half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (-half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (-half^2) * (hL 1 1 1 1) + (half) * (hR 1 2 1 2) + (-half) * (hL 1 2 2 1) + (-half^2) * (hL 2 2 2 2) + (-half) * r00 + (half) * r11 + (half) * r22 + (lam 1 + lam 2 - T 0 0 0 0*half + T 1 1 1 1*half - T 1 2 1 2 + T 2 2 2 2*half) * hhalf
  have c1220 : T 1 2 2 0 = Kriem lam 1 2 2 0 := by
    rw [show Kriem lam 1 2 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 1 0 0) + (-half) * (hL 1 1 0 1) + (1) * (hR 1 1 0 1) + (1) * (hL 1 2 2 0) + (-1) * r10 + (-T 0 1 0 0 + T 1 1 0 1) * hhalf
  have c1221 : T 1 2 2 1 = Kriem lam 1 2 2 1 := by
    rw [show Kriem lam 1 2 2 1 = -lam 1 - lam 2 + half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half^2) * (hL 0 0 0 0) + (half) * (hR 0 1 0 1) + (-half) * (hL 0 1 1 0) + (half) * (hR 0 2 0 2) + (-half) * (hL 0 2 2 0) + (half^2) * (hL 1 1 1 1) + (half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (half^2) * (hL 2 2 2 2) + (half) * r00 + (-half) * r11 + (-half) * r22 + (-lam 1 - lam 2 + T 0 0 0 0*half - T 1 1 1 1*half - T 1 2 2 1 - T 2 2 2 2*half) * hhalf
  have c1222 : T 1 2 2 2 = Kriem lam 1 2 2 2 := by
    rw [show Kriem lam 1 2 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 1 2 2 2) + (-T 1 2 2 2) * hhalf
  have c2000 : T 2 0 0 0 = Kriem lam 2 0 0 0 := by
    rw [show Kriem lam 2 0 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 2 0 0) + (-half) * (hR 0 2 0 0) + (T 0 2 0 0) * hhalf
  have c2001 : T 2 0 0 1 = Kriem lam 2 0 0 1 := by
    rw [show Kriem lam 2 0 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 2 0 1) + (half) * (hR 1 2 1 1) + (-half) * (hL 2 2 1 2) + (1) * (hR 2 2 1 2) + (-1) * r21 + (-T 1 2 1 1 + T 2 2 1 2) * hhalf
  have c2002 : T 2 0 0 2 = Kriem lam 2 0 0 2 := by
    rw [show Kriem lam 2 0 0 2 = -lam 0 - lam 2 + half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (half^2) * (hL 0 0 0 0) + (-half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (1) * (hL 0 2 0 2) + (-half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (-half^2) * (hL 1 1 1 1) + (half) * (hR 1 2 1 2) + (-half) * (hL 1 2 2 1) + (half^2) * (hL 2 2 2 2) + (-half) * r00 + (half) * r11 + (-half) * r22 + (-lam 0 - lam 2 - T 0 0 0 0*half + T 0 2 0 2 + T 1 1 1 1*half - T 2 2 2 2*half) * hhalf
  have c2010 : T 2 0 1 0 = Kriem lam 2 0 1 0 := by
    rw [show Kriem lam 2 0 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-1) * (hR 0 2 0 1) + (1) * (hL 0 2 1 0) + (-half) * (hR 1 2 1 1) + (half) * (hL 2 2 1 2) + (-1) * (hR 2 2 1 2) + (1) * r21 + (T 1 2 1 1 - T 2 2 1 2) * hhalf
  have c2011 : T 2 0 1 1 = Kriem lam 2 0 1 1 := by
    rw [show Kriem lam 2 0 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 2 1 1) + (-half) * (hR 0 2 1 1) + (T 0 2 1 1) * hhalf
  have c2012 : T 2 0 1 2 = Kriem lam 2 0 1 2 := by
    rw [show Kriem lam 2 0 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 0 0 0 1) + (1) * (hL 0 1 1 1) + (-half) * (hR 0 1 1 1) + (1) * (hL 0 2 1 2) + (-1) * (hR 0 2 1 2) + (1) * (hL 0 2 2 1) + (-1) * r01 + (-T 0 0 0 1 + T 0 1 1 1) * hhalf
  have c2020 : T 2 0 2 0 = Kriem lam 2 0 2 0 := by
    rw [show Kriem lam 2 0 2 0 = lam 0 + lam 2 - half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half^2) * (hL 0 0 0 0) + (half) * (hR 0 1 0 1) + (-half) * (hL 0 1 1 0) + (-half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (half^2) * (hL 1 1 1 1) + (-half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (-half^2) * (hL 2 2 2 2) + (half) * r00 + (-half) * r11 + (half) * r22 + (lam 0 + lam 2 + T 0 0 0 0*half - T 1 1 1 1*half - T 2 0 2 0 + T 2 2 2 2*half) * hhalf
  have c2021 : T 2 0 2 1 = Kriem lam 2 0 2 1 := by
    rw [show Kriem lam 2 0 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 0 0 0 1) + (-1) * (hL 0 1 1 1) + (half) * (hR 0 1 1 1) + (1) * r01 + (T 0 0 0 1 - T 0 1 1 1) * hhalf
  have c2022 : T 2 0 2 2 = Kriem lam 2 0 2 2 := by
    rw [show Kriem lam 2 0 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 0 2 2 2) + (-half) * (hR 0 2 2 2) + (T 0 2 2 2) * hhalf
  have c2100 : T 2 1 0 0 = Kriem lam 2 1 0 0 := by
    rw [show Kriem lam 2 1 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 1 2 0 0) + (-half) * (hR 1 2 0 0) + (T 1 2 0 0) * hhalf
  have c2101 : T 2 1 0 1 = Kriem lam 2 1 0 1 := by
    rw [show Kriem lam 2 1 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hR 0 2 0 0) + (1) * (hL 1 2 0 1) + (-1) * (hR 1 2 0 1) + (half) * (hL 2 2 0 2) + (-1) * (hR 2 2 0 2) + (1) * r20 + (T 0 2 0 0 - T 2 2 0 2) * hhalf
  have c2102 : T 2 1 0 2 = Kriem lam 2 1 0 2 := by
    rw [show Kriem lam 2 1 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 1 0 0) + (-half) * (hL 1 1 0 1) + (1) * (hR 1 1 0 1) + (1) * (hL 1 2 0 2) + (-1) * (hR 1 2 0 2) + (1) * (hL 1 2 2 0) + (-1) * r10 + (-T 0 1 0 0 + T 1 1 0 1) * hhalf
  have c2110 : T 2 1 1 0 = Kriem lam 2 1 1 0 := by
    rw [show Kriem lam 2 1 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hR 0 2 0 0) + (1) * (hL 1 2 1 0) + (-half) * (hL 2 2 0 2) + (1) * (hR 2 2 0 2) + (-1) * r20 + (-T 0 2 0 0 + T 2 2 0 2) * hhalf
  have c2111 : T 2 1 1 1 = Kriem lam 2 1 1 1 := by
    rw [show Kriem lam 2 1 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 1 2 1 1) + (-half) * (hR 1 2 1 1) + (T 1 2 1 1) * hhalf
  have c2112 : T 2 1 1 2 = Kriem lam 2 1 1 2 := by
    rw [show Kriem lam 2 1 1 2 = -lam 1 - lam 2 + half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half^2) * (hL 0 0 0 0) + (half) * (hR 0 1 0 1) + (-half) * (hL 0 1 1 0) + (half) * (hR 0 2 0 2) + (-half) * (hL 0 2 2 0) + (half^2) * (hL 1 1 1 1) + (1) * (hL 1 2 1 2) + (-half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (half^2) * (hL 2 2 2 2) + (half) * r00 + (-half) * r11 + (-half) * r22 + (-lam 1 - lam 2 + T 0 0 0 0*half - T 1 1 1 1*half + T 1 2 1 2 - T 2 2 2 2*half) * hhalf
  have c2120 : T 2 1 2 0 = Kriem lam 2 1 2 0 := by
    rw [show Kriem lam 2 1 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hR 0 1 0 0) + (half) * (hL 1 1 0 1) + (-1) * (hR 1 1 0 1) + (1) * r10 + (T 0 1 0 0 - T 1 1 0 1) * hhalf
  have c2121 : T 2 1 2 1 = Kriem lam 2 1 2 1 := by
    rw [show Kriem lam 2 1 2 1 = lam 1 + lam 2 - half*(lam 0 + lam 1 + lam 2) by simp [Kriem, Kcurv]; try ring]
    linear_combination (half^2) * (hL 0 0 0 0) + (-half) * (hR 0 1 0 1) + (half) * (hL 0 1 1 0) + (-half) * (hR 0 2 0 2) + (half) * (hL 0 2 2 0) + (-half^2) * (hL 1 1 1 1) + (-half) * (hR 1 2 1 2) + (half) * (hL 1 2 2 1) + (-half^2) * (hL 2 2 2 2) + (-half) * r00 + (half) * r11 + (half) * r22 + (lam 1 + lam 2 - T 0 0 0 0*half + T 1 1 1 1*half - T 2 1 2 1 + T 2 2 2 2*half) * hhalf
  have c2122 : T 2 1 2 2 = Kriem lam 2 1 2 2 := by
    rw [show Kriem lam 2 1 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (1) * (hL 1 2 2 2) + (-half) * (hR 1 2 2 2) + (T 1 2 2 2) * hhalf
  have c2200 : T 2 2 0 0 = Kriem lam 2 2 0 0 := by
    rw [show Kriem lam 2 2 0 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 2 2 0 0) + (-T 2 2 0 0) * hhalf
  have c2201 : T 2 2 0 1 = Kriem lam 2 2 0 1 := by
    rw [show Kriem lam 2 2 0 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 2 2 0 1) + (-T 2 2 0 1) * hhalf
  have c2202 : T 2 2 0 2 = Kriem lam 2 2 0 2 := by
    rw [show Kriem lam 2 2 0 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 2 2 0 2) + (-T 2 2 0 2) * hhalf
  have c2210 : T 2 2 1 0 = Kriem lam 2 2 1 0 := by
    rw [show Kriem lam 2 2 1 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 2 2 0 1) + (1) * (hR 2 2 0 1) + (T 2 2 0 1) * hhalf
  have c2211 : T 2 2 1 1 = Kriem lam 2 2 1 1 := by
    rw [show Kriem lam 2 2 1 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 2 2 1 1) + (-T 2 2 1 1) * hhalf
  have c2212 : T 2 2 1 2 = Kriem lam 2 2 1 2 := by
    rw [show Kriem lam 2 2 1 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 2 2 1 2) + (-T 2 2 1 2) * hhalf
  have c2220 : T 2 2 2 0 = Kriem lam 2 2 2 0 := by
    rw [show Kriem lam 2 2 2 0 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 2 2 0 2) + (1) * (hR 2 2 0 2) + (T 2 2 0 2) * hhalf
  have c2221 : T 2 2 2 1 = Kriem lam 2 2 2 1 := by
    rw [show Kriem lam 2 2 2 1 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (-half) * (hL 2 2 1 2) + (1) * (hR 2 2 1 2) + (T 2 2 1 2) * hhalf
  have c2222 : T 2 2 2 2 = Kriem lam 2 2 2 2 := by
    rw [show Kriem lam 2 2 2 2 = 0 by simp [Kriem, Kcurv]; try ring]
    linear_combination (half) * (hL 2 2 2 2) + (-T 2 2 2 2) * hhalf
  intro n j k m
  fin_cases n <;> fin_cases j <;> fin_cases k <;> fin_cases m <;> assumption

end CFT.Cartan
