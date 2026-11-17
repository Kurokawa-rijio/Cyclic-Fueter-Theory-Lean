/-
  3-2 積計量でのスピノル曲率の恒等式（S² × ℝ 版：首で使う積計量）

  3-1（S³）・S³ × ℝ 版の続き。S² のスピン接続は左不変枠を持たないため、
  S³ の定数接続とは違い θ に依存する。正規直交枠 e^θ = dθ, e^φ = sin θ dφ で
    A_θ = 0, A_φ = −(i/2) cos θ · σ_z。
  したがって曲率は交換子ではなく外微分 dA から来る：
    F_{θφ} = ∂_θ A_φ = (i/2) sin θ · σ_z（座標成分）、枠成分は (i/2)σ_z。
  一方、定曲率 +1 の Riemann テンソル R_abcd = δ_adδ_bc − δ_acδ_bd（S³ と同じ式）の
  クリフォード縮約は (1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_ab σ_z（S³ と同じ符号）で、
  枠成分の曲率はその負になる。符号の違いは R(X,Y)Z = ⟨Y,Z⟩X − ⟨X,Z⟩Y の規約による。

  証明する恒等式（すべて sympy による明示行列計算でも照合済み）：
  * `s2SpinConn_eq`：A_θ = 0、A_φ = −(i/2) cos θ · σ_z。
  * `s2SpinConn_commutator`：[A_a, A_b] = 0（A_θ = 0 で A_φ は自分自身と可換）。
  * `s2Riemann_clifford`：(1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_ab σ_z。
  * `s2SpinConn_deriv`：∂_θ A_φ = (i/2) sin θ · σ_z（HasDerivAt）。
  * `s2Curvature`：座標成分の曲率 F_{θφ} = (i/2) sin θ · σ_z は、
    sin θ ×（Riemann 縮約の負）に等しい。すなわち枠成分の曲率 = −(1/4)Σ R σσ。
  * `s2_dirac_shift`：Σ_a σ_a A_a = (cos θ / 2)·σ_x。
  積計量 S² × ℝ（添字 Fin 3、0,1 が球面方向、2 が平坦な ℝ 方向）では、
  球面ブロックは上の恒等式そのものに帰着し、平坦方向を含む場合は両辺とも 0 になる。
  （`prodS2_*` の各定理。S³ × ℝ 版 `SpinCurvatureProduct.lean` と同じ構成。）

  範囲の注記：ここで扱うのは 2×2 Pauli 行列による球面ブロックの成分表示であり、
  3 次元スピノル全体の 4×4 ガンマ行列表示ではない。S² の枠は極で特異だが、
  恒等式は θ の関数として大域的に成り立つ。
-/
import CFT.Quantum.SpinCurvatureS3
import Mathlib.Analysis.Matrix

namespace CFT.SpinCurvatureS2

open Matrix Complex CFT.AlphaV CFT.S3Dirac CFT.SpinCurvature

/- 行列の sup ノルムによるノルム構造をこのファイル内でのみ instance 化する。
   Mathlib は行列のノルムを意図的に global instance にしていない
   （`Matrix.normedAddCommGroup`・`Matrix.normedSpace` は `protected def`）ため、
   行列値関数の `HasDerivAt` を使うにはこの局所導入が必要。 -/
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- S² のガンマ行列（枠方向の Pauli 行列 σ_x, σ_y） -/
noncomputable def s2Gamma : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![σx, σy]

/-- 丸い S² のスピン接続の成分（正規直交枠）。A_θ = 0、A_φ = −(i/2) cos θ · σ_z -/
noncomputable def s2SpinConn (θ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![0, (-(Complex.I / 2) * Real.cos θ) • σ 2]

/-- S² の 2 次元 Levi-Civita 記号 -/
def s2Eps (a b : Fin 2) : ℝ := ![![0, 1], ![-1, 0]] a b

/-- 定曲率 +1 の S² の Riemann テンソル R_abcd = δ_adδ_bc − δ_acδ_bd（S³ と同じ式） -/
noncomputable def s2Riemann (a b c d : Fin 2) : ℝ :=
  (if a = d then 1 else 0) * (if b = c then 1 else 0)
    - (if a = c then 1 else 0) * (if b = d then 1 else 0)

/-- 【3-2】S² のガンマ行列は 3 次元の Pauli 行列の最初の 2 つ -/
theorem s2Gamma_castSucc (a : Fin 2) : σ (Fin.castSucc a) = s2Gamma a := by
  fin_cases a <;> rfl

/-- 【3-2】スピン接続の θ 成分は 0 -/
theorem s2SpinConn_theta (θ : ℝ) : s2SpinConn θ 0 = 0 := by
  simp [s2SpinConn]

/-- 【3-2】スピン接続の φ 成分は −(i/2) cos θ · σ_z -/
theorem s2SpinConn_phi (θ : ℝ) :
    s2SpinConn θ 1 = (-(Complex.I / 2) * Real.cos θ) • σ 2 := by
  simp [s2SpinConn]

/-- 【3-2】スピン接続の交換子は 0 -/
theorem s2SpinConn_commutator (θ : ℝ) (a b : Fin 2) :
    s2SpinConn θ a * s2SpinConn θ b - s2SpinConn θ b * s2SpinConn θ a = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [s2SpinConn_theta, s2SpinConn_phi]

/-- 【3-2】2 次元 Levi-Civita 記号：ε_01 = 1 -/
theorem s2Eps_zero_one : s2Eps 0 1 = 1 := by
  simp [s2Eps]

/-- 【3-2】2 次元 Levi-Civita 記号：ε_10 = −1 -/
theorem s2Eps_one_zero : s2Eps 1 0 = -1 := by
  simp [s2Eps]

set_option maxHeartbeats 800000 in
/-- 【3-2】Riemann テンソルとクリフォード積の縮約：(1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_ab σ_z -/
theorem s2Riemann_clifford (a b : Fin 2) :
    (1 / 4 : ℂ) • ∑ c, ∑ d, ((s2Riemann a b c d : ℝ) : ℂ) • (s2Gamma c * s2Gamma d)
      = (-Complex.I / 2) • (((s2Eps a b : ℝ) : ℂ) • σ 2) := by
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s2Riemann, s2Eps, s2Gamma, σ, σx, σy, σz, Fin.sum_univ_two, Matrix.mul_apply] <;>
    (try ring_nf)

/-- 【3-2】スピン接続の φ 成分の θ 微分：∂_θ A_φ = (i/2) sin θ · σ_z -/
theorem s2SpinConn_deriv (θ : ℝ) :
    HasDerivAt (fun θ => s2SpinConn θ 1) ((Complex.I / 2 * Real.sin θ) • σ 2) θ := by
  have h2 : (fun θ => s2SpinConn θ 1)
      = fun θ => (-(Complex.I / 2) * (Real.cos θ : ℂ)) • σ 2 :=
    funext fun θ => by simp [s2SpinConn]
  rw [h2]
  have hcos : HasDerivAt (fun θ : ℝ => (Real.cos θ : ℂ))
      (((-Real.sin θ : ℝ)) : ℂ) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hder : (-(Complex.I / 2) * (((-Real.sin θ : ℝ)) : ℂ))
      = Complex.I / 2 * Real.sin θ := by
    rw [Complex.ofReal_neg, neg_mul_neg]
  have hsmul := (hcos.const_mul (-(Complex.I / 2))).smul_const (σ 2)
  rw [hder] at hsmul
  exact hsmul

/-- 【3-2】S² の曲率 2-form の座標成分：F_{θφ} = (i/2) sin θ · σ_z。
    枠成分の曲率 (i/2)σ_z は Riemann 縮約の負で、座標成分は sin θ 倍。 -/
theorem s2Curvature (θ : ℝ) :
    (Complex.I / 2 * Real.sin θ) • σ 2
      = -((Real.sin θ : ℂ)) • ((1 / 4 : ℂ) • ∑ c, ∑ d,
          ((s2Riemann 0 1 c d : ℝ) : ℂ) • (s2Gamma c * s2Gamma d)) := by
  rw [s2Riemann_clifford, s2Eps_zero_one]
  simp only [Complex.ofReal_one, one_smul, smul_smul, smul_neg, neg_smul, neg_neg]
  congr 1
  ring

/-- 【3-2】Dirac シフト：Σ_a σ_a A_a = (cos θ / 2)·σ_x -/
theorem s2_dirac_shift (θ : ℝ) :
    ∑ a, s2Gamma a * s2SpinConn θ a = (Real.cos θ / 2 : ℂ) • σ 0 := by
  rw [Fin.sum_univ_two]
  simp only [s2Gamma, s2SpinConn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.mul_zero, add_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ, σx, σy, σz, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf)

/-- 積計量 S² × ℝ のスピン接続の成分。球面方向は S² のもの、平坦方向は 0 -/
noncomputable def prodS2SpinConn (θ : ℝ) (A : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if h : A.val < 2 then s2SpinConn θ ⟨A.val, h⟩ else 0

/-- 積計量の Riemann テンソル。添字に平坦方向が含まれれば 0 -/
noncomputable def prodS2Riemann (A B C D : Fin 3) : ℝ :=
  if h : A.val < 2 ∧ B.val < 2 ∧ C.val < 2 ∧ D.val < 2 then
    s2Riemann ⟨A.val, h.1⟩ ⟨B.val, h.2.1⟩ ⟨C.val, h.2.2.1⟩ ⟨D.val, h.2.2.2⟩
  else 0

/-- 積計量の Levi-Civita 記号の拡張。添字に平坦方向が含まれれば 0 -/
noncomputable def prodS2Eps (A B : Fin 3) : ℝ :=
  if h : A.val < 2 ∧ B.val < 2 then
    s2Eps ⟨A.val, h.1⟩ ⟨B.val, h.2⟩
  else 0

/-- 【3-2】球面方向のスピン接続は S² のもの -/
theorem prodS2SpinConn_sphere (θ : ℝ) (a : Fin 2) :
    prodS2SpinConn θ (Fin.castSucc a) = s2SpinConn θ a := by
  have h : (Fin.castSucc a).val < 2 := a.isLt
  unfold prodS2SpinConn
  rw [dif_pos h]
  congr 1

/-- 【3-2】平坦方向のスピン接続は 0 -/
theorem prodS2SpinConn_flat (θ : ℝ) : prodS2SpinConn θ 2 = 0 := by
  unfold prodS2SpinConn
  rw [dif_neg (by decide : ¬ (2 : Fin 3).val < 2)]

/-- 【3-2】球面ブロックの Riemann テンソルは S² のもの -/
theorem prodS2Riemann_sphere (a b c d : Fin 2) :
    prodS2Riemann (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc c) (Fin.castSucc d)
      = s2Riemann a b c d := by
  have h : (Fin.castSucc a).val < 2 ∧ (Fin.castSucc b).val < 2 ∧
      (Fin.castSucc c).val < 2 ∧ (Fin.castSucc d).val < 2 :=
    ⟨a.isLt, b.isLt, c.isLt, d.isLt⟩
  unfold prodS2Riemann
  rw [dif_pos h]
  congr 1

/-- 【3-2】球面ブロックの Levi-Civita 記号は S² のもの -/
theorem prodS2Eps_sphere (a b : Fin 2) :
    prodS2Eps (Fin.castSucc a) (Fin.castSucc b) = s2Eps a b := by
  have h : (Fin.castSucc a).val < 2 ∧ (Fin.castSucc b).val < 2 :=
    ⟨a.isLt, b.isLt⟩
  unfold prodS2Eps
  rw [dif_pos h]
  congr 1

/-- 【3-2】第 1 添字が平坦方向なら Riemann テンソルは 0 -/
theorem prodS2Riemann_flat_left (B C D : Fin 3) :
    prodS2Riemann 2 B C D = 0 := by
  unfold prodS2Riemann
  rw [dif_neg (fun h => absurd h.1 (by decide : ¬ (2 : Fin 3).val < 2))]

/-- 【3-2】第 1 添字が平坦方向なら Levi-Civita 記号は 0 -/
theorem prodS2Eps_flat_left (B : Fin 3) :
    prodS2Eps 2 B = 0 := by
  unfold prodS2Eps
  rw [dif_neg (fun h => absurd h.1 (by decide : ¬ (2 : Fin 3).val < 2))]

/-- 【3-2】球面ブロックの交換子は 0 -/
theorem prodS2_commutator_sphere (θ : ℝ) (a b : Fin 2) :
    prodS2SpinConn θ (Fin.castSucc a) * prodS2SpinConn θ (Fin.castSucc b)
      - prodS2SpinConn θ (Fin.castSucc b) * prodS2SpinConn θ (Fin.castSucc a)
      = 0 := by
  simp only [prodS2SpinConn_sphere]
  exact s2SpinConn_commutator θ a b

/-- 【3-2】平坦方向との交換子は 0 -/
theorem prodS2_commutator_flat_left (θ : ℝ) (B : Fin 3) :
    prodS2SpinConn θ 2 * prodS2SpinConn θ B - prodS2SpinConn θ B * prodS2SpinConn θ 2
      = 0 := by
  rw [prodS2SpinConn_flat, zero_mul, mul_zero, sub_self]

/-- 【3-2】球面ブロックの Riemann 縮約：(1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_ab σ_z -/
theorem prodS2_riemann_clifford_sphere (a b : Fin 2) :
    (1 / 4 : ℂ) • ∑ c, ∑ d, ((prodS2Riemann (Fin.castSucc a) (Fin.castSucc b)
          (Fin.castSucc c) (Fin.castSucc d) : ℝ) : ℂ) •
          (σ (Fin.castSucc c) * σ (Fin.castSucc d))
      = (-Complex.I / 2) • (((prodS2Eps (Fin.castSucc a) (Fin.castSucc b) : ℝ) : ℂ)
          • σ 2) := by
  simp only [prodS2Riemann_sphere, prodS2Eps_sphere, s2Gamma_castSucc]
  exact s2Riemann_clifford a b

/-- 【3-2】第 1 添字が平坦方向なら Riemann 縮約は両辺とも 0 -/
theorem prodS2_riemann_clifford_flat (B : Fin 3) :
    (1 / 4 : ℂ) • ∑ c, ∑ d, ((prodS2Riemann 2 B
          (Fin.castSucc c) (Fin.castSucc d) : ℝ) : ℂ) •
          (σ (Fin.castSucc c) * σ (Fin.castSucc d))
      = (-Complex.I / 2) • (((prodS2Eps 2 B : ℝ) : ℂ) • σ 2) := by
  have hR : ∀ c d : Fin 2, prodS2Riemann 2 B (Fin.castSucc c) (Fin.castSucc d) = 0 :=
    fun c d => prodS2Riemann_flat_left B _ _
  have hE : prodS2Eps 2 B = 0 := prodS2Eps_flat_left B
  simp [hR, hE]

/-- 【3-2】球面ブロックの Dirac シフト Σ_a σ_a A_a = (cos θ / 2)·σ_x -/
theorem prodS2_dirac_shift (θ : ℝ) :
    ∑ a, σ (Fin.castSucc a) * prodS2SpinConn θ (Fin.castSucc a)
      = (Real.cos θ / 2 : ℂ) • σ 0 := by
  simp only [prodS2SpinConn_sphere, s2Gamma_castSucc]
  exact s2_dirac_shift θ

/-- 【3-2】平坦方向は Dirac シフトに寄与しない（A_2 = 0 なので） -/
theorem prodS2_dirac_shift_flat (θ : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * prodS2SpinConn θ 2 = 0 := by
  rw [prodS2SpinConn_flat, mul_zero]

/-- 【3-2】球面ブロックのスピン接続の φ 成分の θ 微分 -/
theorem prodS2SpinConn_deriv (θ : ℝ) :
    HasDerivAt (fun θ => prodS2SpinConn θ (Fin.castSucc 1))
      ((Complex.I / 2 * Real.sin θ) • σ 2) θ := by
  have h : (fun θ => prodS2SpinConn θ (Fin.castSucc 1))
      = fun θ => s2SpinConn θ 1 :=
    funext fun θ => prodS2SpinConn_sphere θ 1
  rw [h]
  exact s2SpinConn_deriv θ

/-- 【3-2】球面ブロックの曲率 2-form の座標成分：F_{θφ} = (i/2) sin θ · σ_z -/
theorem prodS2_curvature_sphere (θ : ℝ) :
    (Complex.I / 2 * Real.sin θ) • σ 2
      = -((Real.sin θ : ℂ)) • ((1 / 4 : ℂ) • ∑ c, ∑ d,
          ((prodS2Riemann (Fin.castSucc 0) (Fin.castSucc 1)
            (Fin.castSucc c) (Fin.castSucc d) : ℝ) : ℂ) •
            (σ (Fin.castSucc c) * σ (Fin.castSucc d))) := by
  simp only [prodS2Riemann_sphere, s2Gamma_castSucc]
  exact s2Curvature θ

end CFT.SpinCurvatureS2
