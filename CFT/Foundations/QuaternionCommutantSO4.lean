/-
  α-VII.3:障害 N1 の正確な形(so(4) の中の su(2)_L の可換子)

  四元数 ℍ ≅ ℝ⁴ に左の掛け算 L(q) で作用する SU(2)_L(単位四元数)を考える。
  電弱混合に必要な超電荷 Y は、SU(2)_L の生成子すべてと可換な、ℝ⁴ の回転の生成子
  (反対称な 4×4 実行列)でなければならない。
  * L(i)、L(j) と可換な反対称行列は、ちょうど R(b)(b は純虚四元数、右の掛け算)である
    (`commutant_so4`)。解の空間は 3 次元で、so(4) = L(Im ℍ) ⊕ R(Im ℍ) の右側の因子に一致する。
  * したがって、左の作用 L(Im ℍ) の中には Y になれる元は 0 しかない(`no_hypercharge_left`)。
    左の作用だけの理論では Y = 0、Q = T₃ で sin²θ_W = 1(混合がない)。これが N1。
  * Y は右の作用 SU(2)_R からしか来ない。これが N1-break(α-VII.8)の出発点になる。

  N1 の定義(台帳への記載用):「単位四元数の片側の作用 SU(2)_L だけを対称性とする理論では、
  SU(2)_L と可換な U(1)_Y の生成子は so(4) の中で R(Im ℍ) に限られ、L(Im ℍ) の中には存在しない」。
-/
import Mathlib

namespace CFT.VIIComm

open Matrix

/-- 左の掛け算 L(a) の行列(基底 1, i, j, k) -/
def Lm (a0 a1 a2 a3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a0, -a1, -a2, -a3; a1, a0, -a3, a2; a2, a3, a0, -a1; a3, -a2, a1, a0]

/-- 右の掛け算 R(b) の行列(基底 1, i, j, k) -/
def Rm (b0 b1 b2 b3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![b0, -b1, -b2, -b3; b1, b0, b3, -b2; b2, -b3, b0, b1; b3, b2, -b1, b0]

/-- R(b) は反対称(b が純虚のとき)で、L(i)、L(j) と可換 -/
theorem Rm_mem (b1 b2 b3 : ℝ) :
    (Rm 0 b1 b2 b3)ᵀ = -Rm 0 b1 b2 b3 ∧
    Rm 0 b1 b2 b3 * Lm 0 1 0 0 = Lm 0 1 0 0 * Rm 0 b1 b2 b3 ∧
    Rm 0 b1 b2 b3 * Lm 0 0 1 0 = Lm 0 0 1 0 * Rm 0 b1 b2 b3 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [Rm, Lm, Matrix.mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 4000000 in
/-- 【α-VII.3】L(i)、L(j) と可換な反対称 4×4 実行列は R(b)(b は純虚)に限る。
計算:可換の条件 32 本と反対称の条件 16 本(すべて線形)。解の空間は 3 次元。 -/
theorem commutant_so4 (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ = -M)
    (hi : M * Lm 0 1 0 0 = Lm 0 1 0 0 * M) (hj : M * Lm 0 0 1 0 = Lm 0 0 1 0 * M) :
    M = Rm 0 (M 1 0) (M 2 0) (M 3 0) := by
  have hi' : ∀ r c, (M * Lm 0 1 0 0) r c = (Lm 0 1 0 0 * M) r c := fun r c => by rw [hi]
  have hj' : ∀ r c, (M * Lm 0 0 1 0) r c = (Lm 0 0 1 0 * M) r c := fun r c => by rw [hj]
  have hM' : ∀ r c, Mᵀ r c = (-M) r c := fun r c => by rw [hM]
  have i00 := hi' 0 0
  have i01 := hi' 0 1
  have i02 := hi' 0 2
  have i03 := hi' 0 3
  have i10 := hi' 1 0
  have i11 := hi' 1 1
  have i12 := hi' 1 2
  have i13 := hi' 1 3
  have i20 := hi' 2 0
  have i21 := hi' 2 1
  have i22 := hi' 2 2
  have i23 := hi' 2 3
  have i30 := hi' 3 0
  have i31 := hi' 3 1
  have i32 := hi' 3 2
  have i33 := hi' 3 3
  have j00 := hj' 0 0
  have j01 := hj' 0 1
  have j02 := hj' 0 2
  have j03 := hj' 0 3
  have j10 := hj' 1 0
  have j11 := hj' 1 1
  have j12 := hj' 1 2
  have j13 := hj' 1 3
  have j20 := hj' 2 0
  have j21 := hj' 2 1
  have j22 := hj' 2 2
  have j23 := hj' 2 3
  have j30 := hj' 3 0
  have j31 := hj' 3 1
  have j32 := hj' 3 2
  have j33 := hj' 3 3
  have a00 := hM' 0 0
  have a01 := hM' 0 1
  have a02 := hM' 0 2
  have a03 := hM' 0 3
  have a10 := hM' 1 0
  have a11 := hM' 1 1
  have a12 := hM' 1 2
  have a13 := hM' 1 3
  have a20 := hM' 2 0
  have a21 := hM' 2 1
  have a22 := hM' 2 2
  have a23 := hM' 2 3
  have a30 := hM' 3 0
  have a31 := hM' 3 1
  have a32 := hM' 3 2
  have a33 := hM' 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, Lm, Matrix.transpose_apply] at i00 i01 i02 i03 i10 i11 i12 i13 i20 i21 i22 i23 i30 i31 i32 i33 j00 j01 j02 j03 j10 j11 j12 j13 j20 j21 j22 j23 j30 j31 j32 j33 a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Rm] <;> linarith

/-- 【α-VII.3】左の作用 L(Im ℍ) の中に、L(i)、L(j) と可換な元は 0 しかない(N1)。 -/
theorem no_hypercharge_left (a1 a2 a3 : ℝ)
    (hi : Lm 0 a1 a2 a3 * Lm 0 1 0 0 = Lm 0 1 0 0 * Lm 0 a1 a2 a3)
    (hj : Lm 0 a1 a2 a3 * Lm 0 0 1 0 = Lm 0 0 1 0 * Lm 0 a1 a2 a3) :
    a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  have e1 := congrFun (congrFun hi 2) 0
  have e2 := congrFun (congrFun hi 3) 0
  have e3 := congrFun (congrFun hj 3) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, Lm] at e1 e2 e3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- 【α-VII.3】Y = 0 なら Q = T₃ で、Weinberg 角 sin²θ_W = tr T₃²/tr Q² は 1(混合なし)。
ここで tr は ℝ⁴ への表現 L の上の跡、T₃ = L(i)/2 とする。 -/
theorem weinberg_left_only :
    (Lm 0 (1 / 2) 0 0 * Lm 0 (1 / 2) 0 0).trace
      / ((Lm 0 (1 / 2) 0 0 + 0) * (Lm 0 (1 / 2) 0 0 + 0)).trace = 1 := by
  norm_num [Lm, Matrix.trace, Fin.sum_univ_four, Matrix.mul_apply]

end CFT.VIIComm
