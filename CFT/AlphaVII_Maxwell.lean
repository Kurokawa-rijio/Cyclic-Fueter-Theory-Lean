/-
  α-VII.1 (Z25):Maxwell 方程式の幾何学的導出(Bianchi 恒等式と運動方程式を区別)

  関数は可換環 S の元、∂_0..∂_3 は可換な導分(体ではなく環なので、点で 0 になる関数も扱える)。
  計量は η = diag(−1, 1, 1, 1)。接続 A_μ、曲率 F_μν = ∂_μA_ν − ∂_νA_μ。
  * Bianchi 恒等式 ∂_λF_μν + ∂_μF_νλ + ∂_νF_λμ = 0 は、A についての仮定なしに定義から従う
    (`bianchi`)。運動方程式ではない。
  * 作用 L = −¼F_μνF^μν − J^νA_ν(ここでは 4L を扱う)の第 1 変分:
      4L(A + εB) = 4L(A) + 4ε(E^ν B_ν − ∂_μ(F^μν B_ν)) − ε² F_μν(B)F^μν(B)   (`first_variation`)
    E^ν = ∂_μF^μν − J^ν。全微分を除いた 1 次の項が消えることが運動方程式 ∂_μF^μν = J^ν
    (変分法の基本補題は標準的な事実)。
  * 運動方程式と両立するには電流が保存:∂_ν∂_μF^μν = 0 は恒等式(`div_div_F`)。
  * 磁束の量子化(c₁ = N ∈ ℤ)は束の遷移関数の一価性から出る(AlphaVII_Bundle の `dirac_quantization`)。
    運動方程式は使わない。トポロジーの帰結と場の方程式の帰結は別のもの。
-/
import Mathlib

namespace CFT.Maxwell

variable {S : Type*} [CommRing S] (d : Fin 4 → Derivation ℤ S S)

/-- η = diag(−1, 1, 1, 1) -/
def eta : Fin 4 → S := ![-1, 1, 1, 1]

/-- 曲率 F_μν = ∂_μA_ν − ∂_νA_μ -/
def Fd (A : Fin 4 → S) (m n : Fin 4) : S := d m (A n) - d n (A m)

/-- 4L = −F_μνF^μν − 4J^νA_ν(F^μν = η^μη^ν F_μν) -/
def L4 (A J : Fin 4 → S) : S :=
  -(∑ m, ∑ n, eta m * eta n * Fd d A m n * Fd d A m n) - 4 * ∑ n, eta n * J n * A n

/-- 運動方程式の左辺 E^ν = ∂_μF^μν − J^ν(η の成分は定数なので導分の外に出す) -/
def Eom (A J : Fin 4 → S) (n : Fin 4) : S :=
  eta n * ∑ m, eta m * d m (Fd d A m n) - J n

/-- 【Z25】Bianchi 恒等式(定義から。運動方程式は使わない) -/
theorem bianchi (A : Fin 4 → S) (comm : ∀ i j f, d i (d j f) = d j (d i f)) (l m n : Fin 4) :
    d l (Fd d A m n) + d m (Fd d A n l) + d n (Fd d A l m) = 0 := by
  simp only [Fd, map_sub]
  linear_combination comm l m (A n) + comm m n (A l) + comm n l (A m)

set_option maxHeartbeats 4000000 in
/-- 【Z25】作用の第 1 変分。ε は定数(∂ε = 0)。 -/
theorem first_variation (A B J : Fin 4 → S) (ε : S) (hε : ∀ i, d i ε = 0) :
    L4 d (fun n => A n + ε * B n) J
      = L4 d A J + 4 * ε * (∑ n, eta n * Eom d A J n * B n
          - ∑ m, eta m * ∑ n, eta n * d m (Fd d A m n * B n))
        - ε ^ 2 * ∑ m, ∑ n, eta m * eta n * Fd d B m n * Fd d B m n := by
  simp only [L4, Eom, Fd, map_add, Derivation.leibniz, hε, smul_eq_mul, mul_zero, add_zero,
    Fin.sum_univ_four, eta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_sub]
  ring

/-- 電流の保存との両立:∂_ν∂_μF^μν = 0(交換する導分と F の反対称性から) -/
theorem div_div_F (A : Fin 4 → S) (comm : ∀ i j f, d i (d j f) = d j (d i f)) :
    ∑ n, eta n * ∑ m, eta m * d n (d m (Fd d A m n)) = 0 := by
  have anti : ∀ m n, Fd d A n m = -Fd d A m n := by intro m n; simp only [Fd]; ring
  have diag : ∀ m, Fd d A m m = 0 := by intro m; simp only [Fd, sub_self]
  simp only [Fin.sum_univ_four, diag, map_zero, mul_zero, add_zero, zero_add,
    anti 0 1, anti 0 2, anti 0 3, anti 1 2, anti 1 3, anti 2 3, map_neg]
  linear_combination (eta 0 * eta 1) * comm 1 0 (Fd d A 0 1) + (eta 0 * eta 2) * comm 2 0 (Fd d A 0 2)
    + (eta 0 * eta 3) * comm 3 0 (Fd d A 0 3) + (eta 1 * eta 2) * comm 2 1 (Fd d A 1 2)
    + (eta 1 * eta 3) * comm 3 1 (Fd d A 1 3) + (eta 2 * eta 3) * comm 3 2 (Fd d A 2 3)

/-- 運動方程式 E = 0 が成り立つなら電流は保存:∂_νJ^ν = 0(J^ν は上付き) -/
theorem current_conserved (A J : Fin 4 → S) (comm : ∀ i j f, d i (d j f) = d j (d i f))
    (heom : ∀ n, Eom d A J n = 0) :
    ∑ n, d n (J n) = 0 := by
  have hJ : ∀ n, J n = eta n * ∑ m, eta m * d m (Fd d A m n) := fun n => by
    have := heom n
    simp only [Eom] at this
    exact (sub_eq_zero.mp this).symm
  have h := div_div_F d A comm
  simp only [Fin.sum_univ_four] at h ⊢
  rw [hJ 0, hJ 1, hJ 2, hJ 3]
  simp only [eta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.sum_univ_four, map_add, map_neg,
    neg_one_mul, one_mul, neg_neg] at h ⊢
  linear_combination h

end CFT.Maxwell
