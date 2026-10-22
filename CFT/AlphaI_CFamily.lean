/-
  α-I.2(Y2):係数行列 C を作用素の族から導き、二つの核を作用素の言葉で読む

  監査の指摘「C の成分は台帳にない(再構成)」への対応。統合版 v6 の定義 8.1(Vol. I, Conv. 4.1)の
  巡回族 D_m = Σ_a e_{m+a} ∂_a(e = (1, i, j, k)、添字は 4 を法)から出発する。
  座標関数 x_b(∂_a x_b = δ_ab)を持つ関数の環 R の上で:
    * coefficient_extraction:D_m を座標関数 x_a に作用させると e_{m+a}。つまり族の係数行列は
      C_{ma} = e_{m+a} に一意に決まる(coefficient_unique:二つの係数の組が同じ作用素を与えれば等しい)
    * null_solution:右核の元 γ(−k)q = (1, −k, −1, k)q から作った一次関数 f = Σ_a x_a γ_a q は
      四つの作用素すべての解(D_m f = 0、m = 0, …, 3)
    * operator_relation:左核の元 γ(i) = (1, i, −1, −i) は四つの作用素の間の関係を与える:
      Σ_m γ(i)_m D_m = 0(すべての f で)
  AlphaI_C の right_kernel、left_kernel(核はちょうどこれらの直線)、rank_three と合わせて、
  台帳 Y2 の rank_ℍ C = 3、ker_R C = γ(−k)ℍ と、統合版 v6 第 9 章の ker_L C = ℍγ(i) が、
  作用素の族そのものから従う。
-/
import CFT.AlphaI_Operators

open Quaternion

namespace CFT.CFamily

open CFT.Operators

set_option maxHeartbeats 2000000

variable {R : Type*} [CommRing R] (d : Fin 4 → Derivation ℤ R R)

/-- 巡回族 D_m = Σ_a e_{m+a} ∂_a -/
def Dm (m : Fin 4) (f : ℍ[R]) : ℍ[R] := ∑ a, e (m + a) * dq (d a) f

/-- 一般の係数 c_a の一階の作用素 -/
def Op (c : Fin 4 → ℍ[R]) (f : ℍ[R]) : ℍ[R] := ∑ a, c a * dq (d a) f

/-- 実の関数 x を四元数の値の関数 x·1 とみなす -/
def ofR (x : R) : ℍ[R] := ⟨x, 0, 0, 0⟩

section
variable (x : Fin 4 → R) (hx : ∀ a b, d a (x b) = if a = b then 1 else 0)
include hx

theorem dq_coord (a b : Fin 4) : dq (d a) (ofR (x b)) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp [dq, ofR, hx]; rfl
  · simp [dq, ofR, hx, h]; rfl

/-- 係数の取り出し:Op c (x_b) = c_b -/
theorem op_coord (c : Fin 4 → ℍ[R]) (b : Fin 4) : Op d c (ofR (x b)) = c b := by
  simp only [Op, dq_coord d x hx]
  rw [Finset.sum_eq_single b (fun a _ hab => by simp [hab]) (by simp)]
  simp

/-- 族の係数行列は C_{ma} = e_{m+a} -/
theorem coefficient_extraction (m a : Fin 4) : Dm d m (ofR (x a)) = e (m + a) :=
  op_coord d x hx (fun a => e (m + a)) a

/-- 係数は作用素から一意に決まる -/
theorem coefficient_unique (c c' : Fin 4 → ℍ[R]) (h : ∀ f, Op d c f = Op d c' f) : c = c' := by
  funext b
  rw [← op_coord d x hx c b, ← op_coord d x hx c' b, h]

end

/-- 定数の四元数(すべての ∂ で 0) -/
def IsConst (q : ℍ[R]) : Prop := ∀ a, dq (d a) q = 0

theorem dq_add (a : Fin 4) (f g : ℍ[R]) : dq (d a) (f + g) = dq (d a) f + dq (d a) g := by
  ext <;> simp [dq]

theorem dq_mul_const (a : Fin 4) (f q : ℍ[R]) (hq : IsConst d q) :
    dq (d a) (f * q) = dq (d a) f * q := by
  have h := hq a
  simp only [dq, Quaternion.ext_iff] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK] at h0 h1 h2 h3
  ext <;> simp [dq, Derivation.leibniz, h0, h1, h2, h3] <;> ring

/-- 右核 γ(−k) = (1, −k, −1, k) -/
def gamK : Fin 4 → ℍ[R] := ![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨-1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩]
/-- 左核 γ(i) = (1, i, −1, −i) -/
def gamI : Fin 4 → ℍ[R] := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩]

theorem right_kernel_rows (m : Fin 4) : ∑ a, e (m + a) * (gamK a : ℍ[R]) = 0 := by
  fin_cases m <;> ext <;> simp [e, gamK, Fin.sum_univ_four]

theorem left_kernel_cols (a : Fin 4) : ∑ m, (gamI m : ℍ[R]) * e (m + a) = 0 := by
  fin_cases a <;> ext <;> simp [e, gamI, Fin.sum_univ_four]

section
variable (x : Fin 4 → R) (hx : ∀ a b, d a (x b) = if a = b then 1 else 0)
include hx

/-- 右核から作る一次関数 f = Σ_a x_a γ_a q はすべての D_m の解 -/
theorem null_solution (q : ℍ[R]) (hq : IsConst d q) (m : Fin 4) :
    Dm d m (∑ b, ofR (x b) * gamK b * q) = 0 := by
  have hg : ∀ b, IsConst d (gamK b * q : ℍ[R]) := by
    intro b a
    have h := hq a
    simp only [dq, Quaternion.ext_iff] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp only [Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ, Quaternion.zero_imK] at h0 h1 h2 h3
    fin_cases b <;> ext <;> simp [dq, gamK, Derivation.leibniz, h0, h1, h2, h3]
  have hsum : ∀ a, dq (d a) (∑ b, ofR (x b) * gamK b * q) = gamK a * q := by
    intro a
    have : ∀ (s : Finset (Fin 4)), dq (d a) (∑ b in s, ofR (x b) * (gamK b * q))
        = ∑ b in s, dq (d a) (ofR (x b)) * (gamK b * q) := by
      intro s
      induction s using Finset.induction_on with
      | empty => ext <;> simp [dq]
      | insert hn ih =>
        rw [Finset.sum_insert hn, Finset.sum_insert hn, dq_add, ih, dq_mul_const d _ _ _ (hg _)]
    simp only [mul_assoc]
    rw [this, Finset.sum_eq_single a (fun b _ hab => by rw [dq_coord d x hx, if_neg (Ne.symm hab)]; simp)
      (by simp)]
    rw [dq_coord d x hx, if_pos rfl, one_mul]
  simp only [Dm, hsum, ← mul_assoc]
  rw [← Finset.sum_mul, right_kernel_rows, zero_mul]

end

/-- 左核は作用素の関係を与える:Σ_m γ(i)_m D_m f = 0 -/
theorem operator_relation (f : ℍ[R]) : ∑ m, (gamI m : ℍ[R]) * Dm d m f = 0 := by
  simp only [Dm, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  have : ∀ a, ∑ m, (gamI m : ℍ[R]) * e (m + a) * dq (d a) f = 0 := by
    intro a; rw [← Finset.sum_mul, left_kernel_cols, zero_mul]
  simp [this]

end CFT.CFamily
