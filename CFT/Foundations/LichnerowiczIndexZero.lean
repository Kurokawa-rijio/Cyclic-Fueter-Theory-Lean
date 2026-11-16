/-
  α-VII.6(Z28-f)の作り直し:奇数次元の指数が 0 であること、丸い S⁹ に零モードがないことを、
  Atiyah–Singer の指数定理なしに示す

  A. 指数 0(index_zero):内積空間 E の対称な線形写像 D(⟪Dx, y⟫ = ⟪x, Dy⟫)では、
     像の直交補空間(余核)は核と一致する:y ⊥ range D ⇔ D y = 0。
     奇数次元の閉多様体の Dirac 作用素はカイラリティで分かれず、D: Γ(S) → Γ(S) は対称なので、
     指数 dim ker D − dim coker D は 0。
  B. Clifford 代数の恒等式(Lichnerowicz の公式の代数の核心、一般の次元 n):
     γ_aγ_b + γ_bγ_a = −2δ_ab、R_abcd は (ab)、(cd) で反対称、(ab)↔(cd) で対称、第一 Bianchi を満たすとき
       * clifford_three:Σ_bcd R_abcd γ_bγ_cγ_d = 2 Σ_c Ric_ac γ_c(Ric_ac = Σ_b R_abcb)
       * clifford_four:Σ_abcd R_abcd γ_aγ_bγ_cγ_d = −2 (Σ_a Ric_aa)·1
     これにスピノルの曲率 [∇_a, ∇_b] = ¼ Σ R_abcd γ_cγ_d(標準の公式)を合わせると D² = ∇*∇ + scal/4。
  C. 零モードの不在(no_zero_mode):‖Dψ‖² = ‖∇ψ‖² + c‖ψ‖²、c > 0 なら Dψ = 0 ⇒ ψ = 0。
     丸い S⁹ では scal = n(n − 1) = 72 > 0(s9_scalar)、c = scal/4 = 18。
  外部に残るもの:スピノルの曲率の公式と、閉多様体上での部分積分(⟨D²ψ, ψ⟩ = ‖Dψ‖² 等)。
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing

open Finset

namespace CFT.Lichnerowicz

/-! ### A. 対称な作用素の指数は 0 -/

theorem index_zero {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (D : E →ₗ[𝕜] E) (hD : ∀ x y, inner (D x) y = (inner x (D y) : 𝕜)) (y : E) :
    y ∈ (LinearMap.range D)ᗮ ↔ D y = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    have h1 := h (D (D y)) ⟨D y, rfl⟩
    rw [hD] at h1
    exact inner_self_eq_zero.mp h1
  · rintro h _ ⟨x, rfl⟩
    rw [hD, h, inner_zero_right]

/-! ### B. Clifford 代数の恒等式 -/

section clifford

variable {B : Type*} [Ring B] [Algebra ℝ B] {n : ℕ} (γ : Fin n → B)
  (hcl : ∀ i j, γ i * γ j + γ j * γ i = (-2 * if i = j then (1 : ℝ) else 0) • (1 : B))

include hcl

theorem swap (i j : Fin n) :
    γ i * γ j = (-2 * if i = j then (1 : ℝ) else 0) • (1 : B) - γ j * γ i := by
  rw [← hcl i j]; abel

theorem reorder1 (b c d : Fin n) :
    γ d * γ b * γ c = γ b * γ c * γ d + (2 * if c = d then (1 : ℝ) else 0) • γ b
      - (2 * if b = d then (1 : ℝ) else 0) • γ c := by
  have h1 := swap γ hcl d b
  have h2 := swap γ hcl d c
  have e : γ d * γ b * γ c = (-2 * if d = b then (1 : ℝ) else 0) • γ c - γ b * (γ d * γ c) := by
    rw [h1, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
  rw [e, h2, mul_sub, mul_smul_comm, mul_one, ← mul_assoc]
  have hdb : (if d = b then (1:ℝ) else 0) = if b = d then 1 else 0 := by
    by_cases h : b = d <;> simp [h, eq_comm]
  have hdc : (if d = c then (1:ℝ) else 0) = if c = d then 1 else 0 := by
    by_cases h : c = d <;> simp [h, eq_comm]
  rw [hdb, hdc]
  rw [show (-2 * if b = d then (1 : ℝ) else 0) = -(2 * if b = d then (1 : ℝ) else 0) by ring,
    show (-2 * if c = d then (1 : ℝ) else 0) = -(2 * if c = d then (1 : ℝ) else 0) by ring,
    neg_smul, neg_smul]
  abel

theorem reorder2 (b c d : Fin n) :
    γ c * γ d * γ b = γ b * γ c * γ d + (2 * if b = c then (1 : ℝ) else 0) • γ d
      - (2 * if b = d then (1 : ℝ) else 0) • γ c := by
  have h1 := swap γ hcl d b
  have h3 := swap γ hcl c b
  have e : γ c * γ d * γ b = (-2 * if d = b then (1 : ℝ) else 0) • γ c - γ c * γ b * γ d := by
    rw [mul_assoc, h1, mul_sub, mul_smul_comm, mul_one, ← mul_assoc]
  rw [e, h3, sub_mul, smul_mul_assoc, one_mul]
  have hdb : (if d = b then (1:ℝ) else 0) = if b = d then 1 else 0 := by
    by_cases h : b = d <;> simp [h, eq_comm]
  have hcb : (if c = b then (1:ℝ) else 0) = if b = c then 1 else 0 := by
    by_cases h : b = c <;> simp [h, eq_comm]
  rw [hdb, hcb]
  rw [show (-2 * if b = d then (1 : ℝ) else 0) = -(2 * if b = d then (1 : ℝ) else 0) by ring,
    show (-2 * if b = c then (1 : ℝ) else 0) = -(2 * if b = c then (1 : ℝ) else 0) by ring,
    neg_smul, neg_smul]
  abel

omit hcl in
/-- 三重和の添字の付け替え(巡回) -/
theorem relabel1 (f : Fin n → Fin n → Fin n → B) :
    (∑ b, ∑ c, ∑ d, f c d b) = ∑ b, ∑ c, ∑ d, f b c d := by
  calc (∑ b, ∑ c, ∑ d, f c d b) = ∑ c, ∑ b, ∑ d, f c d b := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, f c d b := Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

omit hcl in
theorem relabel2 (g : Fin n → Fin n → Fin n → B) :
    (∑ b, ∑ c, ∑ d, g d b c) = ∑ b, ∑ c, ∑ d, g b c d := by
  calc (∑ b, ∑ c, ∑ d, g d b c) = ∑ b, ∑ d, ∑ c, g d b c :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    _ = ∑ d, ∑ b, ∑ c, g d b c := Finset.sum_comm

omit hcl in
theorem delta_sum (F : Fin n → B) (b : Fin n) :
    (∑ d, (if b = d then (1 : ℝ) else 0) • F d) = F b := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro d _ hd; simp [Ne.symm hd]
  · simp

theorem clifford_three (Rm : Fin n → Fin n → Fin n → Fin n → ℝ) (a : Fin n)
    (hB : ∀ b c d, Rm a b c d + Rm a c d b + Rm a d b c = 0)
    (h2 : ∀ b c d, Rm a b c d = -Rm a b d c) :
    (∑ b, ∑ c, ∑ d, Rm a b c d • (γ b * γ c * γ d)) = (2 : ℝ) • ∑ c, (∑ b, Rm a b c b) • γ c := by
  set U := ∑ b, ∑ c, ∑ d, Rm a b c d • (γ b * γ c * γ d) with hU
  -- Bianchi
  have e1 : U = -(∑ b, ∑ c, ∑ d, Rm a c d b • (γ b * γ c * γ d))
      - ∑ b, ∑ c, ∑ d, Rm a d b c • (γ b * γ c * γ d) := by
    rw [hU, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show Rm a b c d = -Rm a c d b - Rm a d b c by linarith [hB b c d], sub_smul, neg_smul]
  -- 添字の付け替え
  have e2 := relabel1 (fun x y z => Rm a x y z • (γ z * γ x * γ y))
  have e3 := relabel2 (fun x y z => Rm a x y z • (γ y * γ z * γ x))
  simp only at e2 e3
  rw [e2, e3] at e1
  -- 並べ替え
  have r1 : (∑ b, ∑ c, ∑ d, Rm a b c d • (γ d * γ b * γ c))
      = U + (2 : ℝ) • (∑ b, ∑ c, ∑ d, Rm a b c d • ((if c = d then (1 : ℝ) else 0) • γ b))
        - (2 : ℝ) • (∑ b, ∑ c, ∑ d, Rm a b c d • ((if b = d then (1 : ℝ) else 0) • γ c)) := by
    rw [hU]; simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun d _ => ?_)))
    rw [reorder1 γ hcl b c d, smul_sub, smul_add, mul_smul, mul_smul, smul_comm (2 : ℝ) (Rm a b c d),
      smul_comm (2 : ℝ) (Rm a b c d)]
  have r2 : (∑ b, ∑ c, ∑ d, Rm a b c d • (γ c * γ d * γ b))
      = U + (2 : ℝ) • (∑ b, ∑ c, ∑ d, Rm a b c d • ((if b = c then (1 : ℝ) else 0) • γ d))
        - (2 : ℝ) • (∑ b, ∑ c, ∑ d, Rm a b c d • ((if b = d then (1 : ℝ) else 0) • γ c)) := by
    rw [hU]; simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun d _ => ?_)))
    rw [reorder2 γ hcl b c d, smul_sub, smul_add, mul_smul, mul_smul, smul_comm (2 : ℝ) (Rm a b c d),
      smul_comm (2 : ℝ) (Rm a b c d)]
  -- δ の和
  have sCD : (∑ b, ∑ c, ∑ d, Rm a b c d • ((if c = d then (1 : ℝ) else 0) • γ b)) = 0 := by
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun c _ => ?_))
    have := delta_sum (fun d => Rm a b c d • γ b) c
    simp only [smul_smul] at this ⊢
    simp only [mul_comm (Rm a b c _)] at this ⊢
    rw [this]
    have h0 : Rm a b c c = 0 := by linarith [h2 b c c]
    rw [h0, zero_smul]
  have sBD : (∑ b, ∑ c, ∑ d, Rm a b c d • ((if b = d then (1 : ℝ) else 0) • γ c))
      = ∑ b, ∑ c, Rm a b c b • γ c := by
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
    have := delta_sum (fun d => Rm a b c d • γ c) b
    simp only [smul_smul] at this ⊢
    simp only [mul_comm (Rm a b c _)] at this ⊢
    exact this
  have sBC : (∑ b, ∑ c, ∑ d, Rm a b c d • ((if b = c then (1 : ℝ) else 0) • γ d))
      = -∑ b, ∑ c, Rm a b c b • γ c := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    have : ∀ d, (∑ c, Rm a b c d • ((if b = c then (1 : ℝ) else 0) • γ d)) = Rm a b b d • γ d := by
      intro d
      have := delta_sum (fun c => Rm a b c d • γ d) b
      simp only [smul_smul] at this ⊢
      simp only [mul_comm (Rm a b _ d)] at this ⊢
      exact this
    simp only [this]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [h2 b b d, neg_smul]
  rw [r1, r2, sCD, sBD, sBC] at e1
  have e4 : (3 : ℝ) • U = (6 : ℝ) • ∑ b, ∑ c, Rm a b c b • γ c := by
    have : U + U + U = (6 : ℝ) • ∑ b, ∑ c, Rm a b c b • γ c := by
      nth_rewrite 1 [e1]
      simp only [smul_zero, add_zero, smul_neg]
      module
    rw [show (3 : ℝ) • U = U + U + U by module, this]
  have e5 : U = (2 : ℝ) • ∑ b, ∑ c, Rm a b c b • γ c := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    calc U = (3 : ℝ)⁻¹ • ((3 : ℝ) • U) := by rw [smul_smul, inv_mul_cancel₀ h3, one_smul]
      _ = (2 : ℝ) • ∑ b, ∑ c, Rm a b c b • γ c := by
        rw [e4, smul_smul]; norm_num
  rw [e5, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_smul]

theorem clifford_four (Rm : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hB : ∀ a b c d, Rm a b c d + Rm a c d b + Rm a d b c = 0)
    (h2 : ∀ a b c d, Rm a b c d = -Rm a b d c)
    (hP : ∀ a b c d, Rm a b c d = Rm c d a b) :
    (∑ a, γ a * ∑ b, ∑ c, ∑ d, Rm a b c d • (γ b * γ c * γ d))
      = (-2 * ∑ a, ∑ b, Rm a b a b) • (1 : B) := by
  have hU : ∀ a, (∑ b, ∑ c, ∑ d, Rm a b c d • (γ b * γ c * γ d))
      = (2 : ℝ) • ∑ c, (∑ b, Rm a b c b) • γ c :=
    fun a => clifford_three γ hcl Rm a (hB a) (h2 a)
  simp only [hU]
  set Ric : Fin n → Fin n → ℝ := fun a c => ∑ b, Rm a b c b with hRic
  have hsym : ∀ a c, Ric a c = Ric c a := by
    intro a c; simp only [hRic]; exact Finset.sum_congr rfl (fun b _ => hP a b c b)
  have e1 : (∑ a, γ a * ((2 : ℝ) • ∑ c, Ric a c • γ c))
      = (2 : ℝ) • ∑ a, ∑ c, Ric a c • (γ a * γ c) := by
    rw [Finset.smul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mul_smul_comm, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [mul_smul_comm]
  have e2 : (∑ a, ∑ c, Ric a c • (γ a * γ c)) = ∑ a, ∑ c, Ric a c • (γ c * γ a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
    rw [hsym]
  have e3 : (2 : ℝ) • (∑ a, ∑ c, Ric a c • (γ a * γ c))
      = ∑ a, ∑ c, Ric a c • (γ a * γ c + γ c * γ a) := by
    rw [two_smul]; nth_rewrite 2 [e2]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [smul_add]
  rw [e1, e3]
  simp only [hcl, smul_smul]
  have e4 : ∀ a, (∑ c, (Ric a c * (-2 * if a = c then (1 : ℝ) else 0)) • (1 : B))
      = (-2 * Ric a a) • (1 : B) := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp; ring_nf
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  simp only [e4, ← Finset.sum_smul]
  congr 1
  rw [Finset.mul_sum]

end clifford

/-! ### C. 零モードの不在 -/

/-- ‖Dψ‖² = ‖∇ψ‖² + c‖ψ‖²、c > 0 なら Dψ = 0 ⇒ ψ = 0 -/
theorem no_zero_mode (Dpsi2 Npsi2 psi2 c : ℝ) (hN : 0 ≤ Npsi2) (hp : 0 ≤ psi2) (hc : 0 < c)
    (hL : Dpsi2 = Npsi2 + c * psi2) (hD : Dpsi2 = 0) : psi2 = 0 := by
  have : c * psi2 ≤ 0 := by linarith
  have : psi2 ≤ 0 := by
    by_contra h; push_neg at h; have := mul_pos hc h; linarith
  linarith

/-- 丸い Sⁿ のスカラー曲率 n(n − 1)(半径 1)、S⁹ で 72、Lichnerowicz の定数 scal/4 = 18 -/
theorem s9_scalar : (9 : ℝ) * (9 - 1) = 72 ∧ (72 : ℝ) / 4 = 18 ∧ (0 : ℝ) < 18 := by norm_num

end CFT.Lichnerowicz
