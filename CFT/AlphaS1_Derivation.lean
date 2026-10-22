/-
  段階 1:作用原理の導出(幾何の公理から作用が一意に決まること)

  作用 S = ∫√−g[R/(16πG) − (1/4g²)F^aF^a] + (1/8πG)∮K√h を、選ぶのではなく次の段で導く。
  A. ゲージ群(gauge_group):右 ℍ 加群としての構造とノルムを保つ ℝ 線形写像 T : ℍ → ℍ は
     左からの単位四元数の積 x ↦ ux(|u| = 1)に限る。巡回 Fueter 系の右核 γ(−k)ℍ(α-I.2)は右 ℍ 直線なので、
     その各点の対称性は Q = Sp(1) ≅ SU(2)(α-I.3 の rho_SU2)。構造定数は四元数の交換子(su_two_bracket)
  B. ゲージ場の作用:
     * maxwell_symbol:Lorentz 不変な二階の二次形式の記号 a(k·k)(ξ·ξ) + b(k·ξ)² がゲージ変換 ξ → ξ + tk で
       不変 ⇔ a + b = 0。そのとき記号は (a/2)F_{μν}F^{μν}(F = kξ − ξk)。Maxwell の作用は定数倍を除いて一意
     * ym_covariance:非可換な場合、δA^a = ∂ε^a + ε^{abc}A^bε^c のもとで δF^a = ε^{abc}F^bε^c
       (Jacobi の恒等式を使う)。ym_invariance:Σ_a F^aF^a は不変
     * theta_total_derivative:ε^{μνρσ}F_{μν}F_{ρσ} = 4∂_μ(ε^{μνρσ}A_ν∂_ρA_σ)。θ 項は全微分で方程式に効かない
  C. 重力の作用:
     * fierz_pauli:対称テンソル h の Lorentz 不変な二階の二次形式
         Q = c₁(k·k)(h·h) + c₂|kh|² + c₃ tr h·(khk) + c₄(k·k)(tr h)²
       が線形化した微分同相 h → h + kξ + ξk で不変 ⇔ (c₁, c₂, c₃, c₄) = c₁(1, −2, 2, −1)。
       これは線形化した Einstein–Hilbert(Fierz–Pauli)。非線形への一意な延長は Lovelock の定理(外部、1971)
  D. 境界項:
     * ghy_frw:閉じた FRW の帽子で √−g R ∝ 6(a²ä + aȧ² + a) = 6[(a²ȧ)˙ − aȧ² + a]。
       二階の微分は全微分 (a²ȧ)˙ にだけ入り、GHY 項(∝ a²ȧ の境界値)がちょうどそれを打ち消すので、
       端で a を固定する変分問題が立つ。GHY 項は Dirichlet 条件の要請から決まる
  E. 定数:Λ = 0(lambda_zero、貼り合わせ)と ℓ² = 4πG/g²(ell_cap、ell_neck、二つの相の整合)は既存の定理
  外部に残るもの:Lovelock の定理(二階の方程式を与える微分同相不変な作用の一意性)、
  非可換なゲージ不変性の一意な延長(Utiyama 1956)、Lorentz 不変なテンソルが η と k だけで書けること(標準)。
-/
import CFT.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination

open Quaternion

namespace CFT.S1

set_option maxHeartbeats 4000000

/-! ### A. ゲージ群 -/

/-- 右 ℍ 線形な写像は左からの積:T x = T 1 · x -/
theorem right_linear_is_left_mul (T : ℍ[ℝ] → ℍ[ℝ]) (hT : ∀ x q, T (x * q) = T x * q) (x : ℍ[ℝ]) :
    T x = T 1 * x := by
  have := hT 1 x; rwa [one_mul] at this

/-- さらにノルムを保てば、係数は単位四元数 -/
theorem gauge_group (T : ℍ[ℝ] → ℍ[ℝ]) (hT : ∀ x q, T (x * q) = T x * q)
    (hn : ∀ x, normSq (T x) = normSq x) :
    normSq (T 1) = 1 ∧ ∀ x, T x = T 1 * x :=
  ⟨by rw [hn 1, map_one], right_linear_is_left_mul T hT⟩

/-- 逆に、単位四元数 u の左積は右 ℍ 線形でノルムを保つ -/
theorem unit_left_mul (u : ℍ[ℝ]) (hu : normSq u = 1) :
    (∀ x q, u * (x * q) = (u * x) * q) ∧ ∀ x, normSq (u * x) = normSq x := by
  refine ⟨fun x q => (mul_assoc u x q).symm, fun x => ?_⟩
  rw [map_mul, hu, one_mul]

/-- su(2) = Im ℍ の構造定数:[i/2, j/2] = k/2 など(ε_{abc}) -/
theorem su_two_bracket :
    let i : ℍ[ℝ] := ⟨0, 1/2, 0, 0⟩
    let j : ℍ[ℝ] := ⟨0, 0, 1/2, 0⟩
    let k : ℍ[ℝ] := ⟨0, 0, 0, 1/2⟩
    i * j - j * i = k ∧ j * k - k * j = i ∧ k * i - i * k = j := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp <;> norm_num

/-! ### B. ゲージ場の作用 -/

/-- Minkowski 計量 -/
def eta : Fin 4 → ℝ := ![-1, 1, 1, 1]
def dot (u v : Fin 4 → ℝ) : ℝ := ∑ i, eta i * u i * v i

/-- 二次形式の記号 a(k·k)(ξ·ξ) + b(k·ξ)² -/
def vecQ (a b : ℝ) (k ξ : Fin 4 → ℝ) : ℝ := a * dot k k * dot ξ ξ + b * dot k ξ ^ 2

/-- ゲージ不変性(純ゲージ ξ → ξ + t k)⇔ a + b = 0 -/
theorem maxwell_symbol (a b : ℝ) :
    (∀ k ξ (t : ℝ), vecQ a b k (fun i => ξ i + t * k i) = vecQ a b k ξ) ↔ a + b = 0 := by
  constructor
  · intro h
    have := h ![-1, 0, 0, 0] ![0, 0, 0, 0] 1
    simp [vecQ, dot, eta, Fin.sum_univ_four] at this
    linarith
  · intro hab k ξ t
    have hb : b = -a := by linarith
    subst hb
    simp only [vecQ, dot, Fin.sum_univ_four]
    ring

/-- a + b = 0 のとき記号は (a/2)F_{μν}F^{μν}、F_{μν} = k_μξ_ν − k_νξ_μ -/
theorem maxwell_is_F2 (a : ℝ) (k ξ : Fin 4 → ℝ) :
    vecQ a (-a) k ξ = (a / 2) * ∑ μ, ∑ ν, eta μ * eta ν * (k μ * ξ ν - k ν * ξ μ) ^ 2 := by
  simp only [vecQ, dot, eta, Fin.sum_univ_four]
  simp
  ring

section YM
variable {S : Type*} [CommRing S]

/-- su(2) の構造定数 ε_{abc} -/
def f3 (a b c : Fin 3) : S :=
  if (a, b, c) = (0, 1, 2) ∨ (a, b, c) = (1, 2, 0) ∨ (a, b, c) = (2, 0, 1) then 1
  else if (a, b, c) = (0, 2, 1) ∨ (a, b, c) = (2, 1, 0) ∨ (a, b, c) = (1, 0, 2) then -1 else 0

variable (D : Fin 4 → Derivation ℤ S S) (A : Fin 3 → Fin 4 → S) (ε : Fin 3 → S)

/-- F^a_{μν} = ∂_μA^a_ν − ∂_νA^a_μ + ε^{abc}A^b_μA^c_ν -/
def F (a : Fin 3) (μ ν : Fin 4) : S :=
  D μ (A a ν) - D ν (A a μ) + ∑ b, ∑ c, f3 a b c * A b μ * A c ν

/-- δA^a_μ = ∂_με^a + ε^{abc}A^b_με^c -/
def dA (a : Fin 3) (μ : Fin 4) : S := D μ (ε a) + ∑ b, ∑ c, f3 a b c * A b μ * ε c

/-- δF の Leibniz 展開 -/
def dF (a : Fin 3) (μ ν : Fin 4) : S :=
  D μ (dA D A ε a ν) - D ν (dA D A ε a μ)
    + ∑ b, ∑ c, f3 a b c * (dA D A ε b μ * A c ν + A b μ * dA D A ε c ν)

theorem ym_covariance (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (a : Fin 3) (μ ν : Fin 4) :
    dF D A ε a μ ν = ∑ b, ∑ c, f3 a b c * F D A b μ ν * ε c := by
  have h := hc μ ν
  fin_cases a <;>
  simp [dF, dA, F, f3, Fin.sum_univ_three, map_add, map_sub, map_neg, Derivation.leibniz,
    smul_eq_mul, h] <;> ring

theorem ym_invariance (μ ν : Fin 4) :
    ∑ a, F D A a μ ν * (∑ b, ∑ c, f3 a b c * F D A b μ ν * ε c) = 0 := by
  simp [f3, Fin.sum_univ_three]; ring

/-- 4 次元の Levi-Civita 記号 -/
def eps4 (a b c d : Fin 4) : ℤ :=
  ((b : ℤ) - a) * ((c : ℤ) - a) * ((d : ℤ) - a) * ((c : ℤ) - b) * ((d : ℤ) - b) * ((d : ℤ) - c) / 12

/-- 可換な場合の F_{μν} -/
def Fab (B : Fin 4 → S) (μ ν : Fin 4) : S := D μ (B ν) - D ν (B μ)

/-- θ 項は全微分:ε^{μνρσ}F_{μν}F_{ρσ} = 4∂_μ(ε^{μνρσ}A_ν∂_ρA_σ) -/
theorem theta_total_derivative (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (B : Fin 4 → S) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ σ, (eps4 μ ν ρ σ : S) * Fab D B μ ν * Fab D B ρ σ
      = 4 * ∑ μ, D μ (∑ ν, ∑ ρ, ∑ σ, (eps4 μ ν ρ σ : S) * B ν * D ρ (B σ)) := by
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fab, map_sum, Fin.sum_univ_four, eps4, v0, v1, v2, v3]
  norm_num
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, smul_eq_mul,
    hc 1 0, hc 2 0, hc 3 0, hc 2 1, hc 3 1, hc 3 2]
  ring

end YM

/-! ### C. 重力の作用(Fierz–Pauli の一意性) -/

def kh (k : Fin 4 → ℝ) (h : Fin 4 → Fin 4 → ℝ) (n : Fin 4) : ℝ := ∑ m, eta m * k m * h m n
def khk (k : Fin 4 → ℝ) (h : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ m, ∑ n, eta m * eta n * k m * k n * h m n
def trh (h : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ m, eta m * h m m
def hh (h : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ m, ∑ n, eta m * eta n * h m n ^ 2

def tenQ (c : Fin 4 → ℝ) (k : Fin 4 → ℝ) (h : Fin 4 → Fin 4 → ℝ) : ℝ :=
  c 0 * dot k k * hh h + c 1 * dot (kh k h) (kh k h) + c 2 * trh h * khk k h + c 3 * dot k k * trh h ^ 2

/-- 線形化した微分同相 δh = kξ + ξk -/
def gauge (k ξ : Fin 4 → ℝ) (h : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => h i j + (k i * ξ j + k j * ξ i)

def unitM (i j : Fin 4) : Fin 4 → Fin 4 → ℝ := fun a b => if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0

theorem fierz_pauli (c : Fin 4 → ℝ) :
    (∀ k ξ (h : Fin 4 → Fin 4 → ℝ), (∀ i j, h i j = h j i) → tenQ c k (gauge k ξ h) = tenQ c k h) ↔
      (c 1 = -2 * c 0 ∧ c 2 = 2 * c 0 ∧ c 3 = -c 0) := by
  constructor
  · intro H
    have sym : ∀ i j : Fin 4, ∀ a b, unitM i j a b = unitM i j b a := by
      intro i j a b; simp only [unitM]; by_cases h1 : a = i <;> by_cases h2 : b = j <;>
        by_cases h3 : a = j <;> by_cases h4 : b = i <;> simp_all
    have e1 := H ![1, 0, 0, 0] ![0, 1, 0, 0] (unitM 0 0) (sym 0 0)
    have e2 := H ![1, 0, 0, 0] ![1, 0, 0, 0] (unitM 1 1) (sym 1 1)
    have e3 := H ![1, 0, 0, 0] ![1, 0, 0, 0] (unitM 0 0) (sym 0 0)
    simp [tenQ, gauge, unitM, kh, khk, trh, hh, dot, eta, Fin.sum_univ_four] at e1 e2 e3
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩ k ξ h hs
    simp only [tenQ, gauge, kh, khk, trh, hh, dot, eta, Fin.sum_univ_four, h1, h2, h3]
    rw [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]
    simp
    ring

/-! ### D. 境界項(閉じた FRW の帽子) -/

theorem ghy_frw (a a' a'' : ℝ → ℝ) (t : ℝ) (h1 : HasDerivAt a (a' t) t) (h2 : HasDerivAt a' (a'' t) t) :
    HasDerivAt (fun t => a t ^ 2 * a' t) (2 * a t * a' t ^ 2 + a t ^ 2 * a'' t) t ∧
    a t ^ 2 * a'' t + a t * a' t ^ 2 + a t
      = (2 * a t * a' t ^ 2 + a t ^ 2 * a'' t) - a t * a' t ^ 2 + a t := by
  refine ⟨?_, by ring⟩
  have := (h1.pow 2).mul h2
  convert this using 1; push_cast; ring

end CFT.S1
