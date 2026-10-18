/-
  α-VII.4(Z28-d):非縮退準位の二次の摂動公式(一般の有限次元、多準位)

  H₀ の固有基底で H₀ = diag(E₀, E₁′, …, E_n′)(添字 0 が注目する準位、他の準位と縮退なし)、
  H(ε) = H₀ + εV + ε²W、E(ε) = E₀ + εe₁ + ε²e₂、ψ(ε) = e₀ + εψ₁ + ε²ψ₂(中間規格化 (ψ_k)₀ = 0)。
  ε¹ と ε² の係数の式から
    * rs_first:e₁ = V₀₀、(ψ₁)_m = V_{m0}/(E₀ − E_m)(m ≠ 0)
    * rs_second:e₂ = W₀₀ + Σ_{m≠0} V_{0m}V_{m0}/(E₀ − E_m)
  (エルミートなら V_{0m}V_{m0} = |V_{m0}|²)。AlphaVII_Perturb の rs_single_level は、励起が一準位に
  集まる場合のこの式。体 K の上で成り立つ代数的な主張で、作用素論(収束、定義域)は扱わない。
  未形式化:Z28-d の作用素族 H(ε) そのもの(V, W の係数の出所)。
-/
import CFT.Basic
import Mathlib.Algebra.BigOperators.Fin

open Finset

namespace CFT.RS

variable {K : Type*} [Field K] {n : ℕ}

/-- 一次の式:成分 0 から e₁ = V₀₀、成分 m から (ψ₁)_m -/
theorem rs_first (Ev : Fin (n + 1) → K) (V : Fin (n + 1) → Fin (n + 1) → K)
    (ψ1 : Fin (n + 1) → K) (e1 : K) (hnorm : ψ1 0 = 0)
    (h1 : ∀ i, Ev i * ψ1 i + V i 0 = Ev 0 * ψ1 i + e1 * (if i = 0 then 1 else 0))
    (hgap : ∀ m : Fin n, Ev 0 ≠ Ev m.succ) :
    e1 = V 0 0 ∧ ∀ m : Fin n, ψ1 m.succ = V m.succ 0 / (Ev 0 - Ev m.succ) := by
  constructor
  · have := h1 0; simp [hnorm] at this; exact this.symm
  · intro m
    have := h1 m.succ
    simp [Fin.succ_ne_zero] at this
    have hg : Ev 0 - Ev m.succ ≠ 0 := sub_ne_zero.mpr (hgap m)
    rw [eq_div_iff hg]; linear_combination -this

/-- 二次の式:e₂ = W₀₀ + Σ_{m≠0} V_{0m}V_{m0}/(E₀ − E_m) -/
theorem rs_second (Ev : Fin (n + 1) → K) (V W : Fin (n + 1) → Fin (n + 1) → K)
    (ψ1 ψ2 : Fin (n + 1) → K) (e1 e2 : K) (hn1 : ψ1 0 = 0)
    (h1 : ∀ i, Ev i * ψ1 i + V i 0 = Ev 0 * ψ1 i + e1 * (if i = 0 then 1 else 0))
    (h2 : ∀ i, Ev i * ψ2 i + (∑ j, V i j * ψ1 j) + W i 0
      = Ev 0 * ψ2 i + e1 * ψ1 i + e2 * (if i = 0 then 1 else 0))
    (hgap : ∀ m : Fin n, Ev 0 ≠ Ev m.succ) :
    e2 = W 0 0 + ∑ m : Fin n, V 0 m.succ * V m.succ 0 / (Ev 0 - Ev m.succ) := by
  obtain ⟨-, hψ⟩ := rs_first Ev V ψ1 e1 hn1 h1 hgap
  have := h2 0
  simp only [if_pos rfl, mul_one, hn1, mul_zero, add_zero, Fin.sum_univ_succ] at this
  simp only [if_true, mul_one, zero_add] at this
  have e : ∑ m : Fin n, V 0 m.succ * ψ1 m.succ = ∑ m : Fin n, V 0 m.succ * V m.succ 0 / (Ev 0 - Ev m.succ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ m]; ring
  rw [← e]; linear_combination -this

/-- エルミートな V(V_{0m} = conj V_{m0})では e₂ = W₀₀ + Σ |V_{m0}|²/(E₀ − E_m) -/
theorem rs_second_hermitian (Ev : Fin (n + 1) → ℂ) (V W : Fin (n + 1) → Fin (n + 1) → ℂ)
    (ψ1 ψ2 : Fin (n + 1) → ℂ) (e1 e2 : ℂ) (hn1 : ψ1 0 = 0)
    (h1 : ∀ i, Ev i * ψ1 i + V i 0 = Ev 0 * ψ1 i + e1 * (if i = 0 then 1 else 0))
    (h2 : ∀ i, Ev i * ψ2 i + (∑ j, V i j * ψ1 j) + W i 0
      = Ev 0 * ψ2 i + e1 * ψ1 i + e2 * (if i = 0 then 1 else 0))
    (hgap : ∀ m : Fin n, Ev 0 ≠ Ev m.succ)
    (herm : ∀ m : Fin n, V 0 m.succ = (starRingEnd ℂ) (V m.succ 0)) :
    e2 = W 0 0 + ∑ m : Fin n, (Complex.normSq (V m.succ 0) : ℂ) / (Ev 0 - Ev m.succ) := by
  rw [rs_second Ev V W ψ1 ψ2 e1 e2 hn1 h1 h2 hgap]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [herm m, mul_comm, Complex.mul_conj]

end CFT.RS
