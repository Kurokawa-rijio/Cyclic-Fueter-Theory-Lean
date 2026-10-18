/-
  α-VII.3(Z28)⊘ と α-VII.8(Z28-f)◎:表現論の障害 N1 とその解消(N1-break)

  N1(障害)の正確な形:電弱混合には SU(2)_L × U(1)_Y、つまり SU(2)_L の生成子すべてと可換な
  超電荷 Y が必要。Q-球面の SU(2)(単位四元数の片側の作用)一つの Lie 代数 Im ℍ の中には、
  そのような Y は 0 しかない(SU(2) に U(1) 部分群(最大トーラス)はあるが、それは SU(2) と可換ではない)。
    * center_pure_trivial:純虚四元数 x が i と j と可換なら x = 0(su(2) の中心は 0)
    * no_mixing:Y = 0 なら Q = T₃ で、sin²θ_W = Tr T₃²/Tr Q² = 1(混合なし)
  N1-break(解消の代数的な部分、n1_break.py):
    * U(p) = (m − iσ·p)/E は SU(2) の元(U_unitary, U_det)で、U(−p) = U(p)⁻¹(U_parity)
    * 反転 X ↦ X⁻¹ は左右の作用を交換する(inversion_swaps)
    * 左乗法と右乗法は可換(left_right_commute)→ SU(2)_L × SU(2)_R
    * 電荷 Q = T₃L + T₃R + X、Y = T₃R + X、X = (B−L)/2(X の値は入力:
      レプトン −1/2、クォーク 1/6。Spin(10) の 16 の複素構造からの導出は n1h.py の数値計算のみ)
    * 一世代の電荷は標準模型と一致(charges_*)
    * sin²θ_W = Tr T₃L² / Tr Q² = 3/8(一世代全体)、1/4(レプトンだけ)
    * 標準模型の一世代(左手 Weyl)でゲージ anomaly が相殺(anomaly_*)、SU(2) 二重項は 4 個(偶数)
  未形式化:B−L の割当を幾何から導くこと(Spin(10) の 16 の構成)、Higgs と Yukawa の物理作用(Z28-f)。
-/
import CFT.Basic

open Quaternion Matrix Complex

namespace CFT.N1

/-! ### N1:単一の SU(2) の障害 -/

/-- 純虚四元数が i, j と可換なら 0(su(2) の中心は自明) -/
theorem center_pure_trivial (x : ℍ[ℝ]) (hre : x.re = 0)
    (hi : x * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * x) (hj : x * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * x) :
    x = 0 := by
  have a1 := congrArg QuaternionAlgebra.imJ hi; have a2 := congrArg QuaternionAlgebra.imK hi
  have b1 := congrArg QuaternionAlgebra.imI hj; have b2 := congrArg QuaternionAlgebra.imK hj
  simp at a1 a2 b1 b2
  ext <;> simp [hre] <;> linarith

/-- Y = 0(独立な超電荷がない)なら Q = T₃ となり sin²θ_W = 1:混合角は生じない -/
theorem no_mixing (trT3 : ℚ) (h : trT3 ≠ 0) : trT3 / (trT3 + 0) = 1 := by
  rw [add_zero, div_self h]

/-! ### N1-break:左右の作用 -/

/-- 4 E² U を作る行列 M(p) = m − iσ·p -/
noncomputable def Mmat (m p1 p2 p3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(m : ℂ) - I * p3, -(I * p1) - p2; -(I * p1) + p2, (m : ℂ) + I * p3]

noncomputable def Umat (m p1 p2 p3 E : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / (E : ℂ)) • Mmat m p1 p2 p3

theorem M_parity (m p1 p2 p3 : ℝ) :
    Mmat m (-p1) (-p2) (-p3) * Mmat m p1 p2 p3 = ((m : ℂ) ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Mmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [I_sq] <;> ring

/-- U(−p)U(p) = 1(E² = m² + |p|²) -/
theorem U_parity (m p1 p2 p3 E : ℝ) (hE : E ^ 2 = m ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) (hE0 : E ≠ 0) :
    Umat m (-p1) (-p2) (-p3) E * Umat m p1 p2 p3 E = 1 := by
  have hE' : (m : ℂ) ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2 = (E : ℂ) ^ 2 := by exact_mod_cast hE.symm
  have hE0' : (E : ℂ) ≠ 0 := by exact_mod_cast hE0
  rw [Umat, Umat, smul_mul_smul_comm, M_parity, hE', smul_smul]
  have : 1 / (E : ℂ) * (1 / (E : ℂ)) * (E : ℂ) ^ 2 = 1 := by field_simp; ring
  rw [this, one_smul]

/-- det U = 1 -/
theorem U_det (m p1 p2 p3 E : ℝ) (hE : E ^ 2 = m ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) (hE0 : E ≠ 0) :
    (Umat m p1 p2 p3 E).det = 1 := by
  have hE' : (m : ℂ) ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2 = (E : ℂ) ^ 2 := by exact_mod_cast hE.symm
  have hE0' : (E : ℂ) ≠ 0 := by exact_mod_cast hE0
  have hdet : (Mmat m p1 p2 p3).det = (m : ℂ) ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2 := by
    rw [Mmat, Matrix.det_fin_two_of]; ring_nf; simp [I_sq]; ring
  rw [Umat, Matrix.det_smul, hdet, hE']
  simp only [Fintype.card_fin]
  field_simp

/-- 反転は左右の作用を交換する:(g_L X g_R⁻¹)⁻¹ = g_R X⁻¹ g_L⁻¹ -/
theorem inversion_swaps {G : Type*} [Group G] (gL gR X : G) :
    (gL * X * gR⁻¹)⁻¹ = gR * X⁻¹ * gL⁻¹ := by
  simp [_root_.mul_inv_rev, mul_assoc]

/-- 左乗法と右乗法は可換:L(a)R(b) = R(b)L(a) -/
theorem left_right_commute (a b x : ℍ[ℝ]) : a * (x * b) = (a * x) * b := (mul_assoc a x b).symm

/-! ### 電荷と Weinberg 角(X = (B−L)/2 の割当は入力) -/

/-- 状態 (T₃L, T₃R, X, 多重度) -/
def leptons : List (ℚ × ℚ × ℚ × ℚ) :=
  [(1/2, 0, -1/2, 1), (-1/2, 0, -1/2, 1), (0, 1/2, -1/2, 1), (0, -1/2, -1/2, 1)]
def quarks : List (ℚ × ℚ × ℚ × ℚ) :=
  [(1/2, 0, 1/6, 3), (-1/2, 0, 1/6, 3), (0, 1/2, 1/6, 3), (0, -1/2, 1/6, 3)]

def Qem (s : ℚ × ℚ × ℚ × ℚ) : ℚ := s.1 + s.2.1 + s.2.2.1
def Ychg (s : ℚ × ℚ × ℚ × ℚ) : ℚ := s.2.1 + s.2.2.1

theorem charges_leptons : leptons.map Qem = [0, -1, 0, -1] := by norm_num [leptons, Qem]
theorem charges_quarks : quarks.map Qem = [2/3, -1/3, 2/3, -1/3] := by norm_num [quarks, Qem]
/-- 右手の超電荷 ν_R : 0、e_R : −1、u_R : 2/3、d_R : −1/3、左手二重項 −1/2, 1/6 -/
theorem hypercharges : (leptons ++ quarks).map Ychg = [-1/2, -1/2, 0, -1, 1/6, 1/6, 2/3, -1/3] := by
  norm_num [leptons, quarks, Ychg]

def trT3L (L : List (ℚ × ℚ × ℚ × ℚ)) : ℚ := (L.map fun s => s.2.2.2 * s.1 ^ 2).sum
def trQ2 (L : List (ℚ × ℚ × ℚ × ℚ)) : ℚ := (L.map fun s => s.2.2.2 * Qem s ^ 2).sum

/-- sin²θ_W = Tr T₃L² / Tr Q² = 3/8(一世代全体) -/
theorem weinberg_full : trT3L (leptons ++ quarks) / trQ2 (leptons ++ quarks) = 3 / 8 := by
  norm_num [trT3L, trQ2, leptons, quarks, Qem]

/-- レプトンだけでは 1/4 -/
theorem weinberg_leptons : trT3L leptons / trQ2 leptons = 1 / 4 := by
  norm_num [trT3L, trQ2, leptons, Qem]

/-! ### 比較:標準模型の一世代(左手 Weyl)のゲージ anomaly -/

/-- (SU(3) 次元, SU(2) 次元, Y) -/
def smWeyl : List (ℚ × ℚ × ℚ) :=
  [(3, 2, 1/6), (3, 1, -2/3), (3, 1, 1/3), (1, 2, -1/2), (1, 1, 1)]

theorem anomaly_Y3 : (smWeyl.map fun f => f.1 * f.2.1 * f.2.2 ^ 3).sum = 0 := by norm_num [smWeyl]
theorem anomaly_grav : (smWeyl.map fun f => f.1 * f.2.1 * f.2.2).sum = 0 := by norm_num [smWeyl]
/-- SU(2)²U(1):二重項だけ(色の多重度つき) -/
theorem anomaly_SU2sqY : 3 * (1 / 6 : ℚ) + 1 * (-1 / 2) = 0 := by norm_num
/-- SU(3)²U(1):三重項だけ(SU(2) の多重度つき) -/
theorem anomaly_SU3sqY : 2 * (1 / 6 : ℚ) + (-2 / 3) + 1 / 3 = 0 := by norm_num
/-- Witten の SU(2) 大域 anomaly:二重項の数 3 + 1 = 4 は偶数 -/
theorem witten_even : Even (3 + 1 : ℕ) := ⟨2, rfl⟩

end CFT.N1
