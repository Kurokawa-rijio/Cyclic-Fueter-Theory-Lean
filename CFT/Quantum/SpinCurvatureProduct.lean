/-
  3-2 積計量でのスピノル曲率の恒等式（モデルケース S³ × ℝ）

  3-1 で示した S³ の成分恒等式を、積計量 S³ × ℝ に広げる。積計量の
  Levi-Civita 接続は直和なので、積の正規直交枠（添字 Fin 4、0,1,2 が球面方向、
  3 が平坦な ℝ 方向）では接続係数は平坦方向を含むものがすべて 0 になる。
  スピン接続も同じブロック構造を継承する：球面方向は 3-1 の `spinConn` そのもの、
  平坦方向は 0。Riemann テンソルも Levi-Civita 記号も、添字に平坦方向が
  1 つでも含まれれば 0 になる。したがって曲率の恒等式は次の 2 通りに分かれる：

  * 球面ブロック（両添字とも Fin 3）：3-1 の恒等式そのものに帰着する。
  * 平坦方向を含む場合：両辺とも 0 になる（恒等式は 0 = 0 として成り立つ）。

  証明する恒等式（すべて 3-1 の定理の組み立て）：
  * `prod_commutator_sphere` / `prod_commutator_flat_left`：交換子 [A_A, A_B]。
  * `prod_riemann_clifford_sphere` / `prod_riemann_clifford_flat`：
    (1/4)Σ_CD R_ABCD σ_C σ_D = −(i/2)ε̃_ABC σ_C。
  * `prod_spin_curvature_sphere` / `prod_spin_curvature_flat`：完全な曲率
    F_AB = [A_A, A_B] − Σ_C 2ε̃_ABC A_C。
  * `prod_dirac_shift`：球面ブロックの Σ_a σ_a A_a = (3i/2)·1。
    平坦方向の寄与は A_3 = 0 なので 0（`prod_dirac_shift_flat`）。

  範囲の注記：ここで扱うのは 2×2 Pauli 行列による球面ブロックの成分表示で
  あり、4 次元スピノル全体の 4×4 ガンマ行列表示ではない。首で使う
  S² × ℝ 版は S² のスピン接続の成分計算が別途必要で、本モジュールの残り
  （3-2 の次の段）とする。
-/
import CFT.Quantum.SpinCurvatureS3

namespace CFT.SpinCurvatureProduct

open Matrix Complex CFT.AlphaV CFT.S3Dirac CFT.SpinCurvature

/-- 積計量 S³ × ℝ のスピン接続の成分。球面方向は 3-1 のもの、平坦方向は 0 -/
noncomputable def prodSpinConn (A : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if h : A.val < 3 then spinConn ⟨A.val, h⟩ else 0

/-- 積計量の Riemann テンソル。添字に平坦方向が含まれれば 0 -/
noncomputable def prodRiemann (A B C D : Fin 4) : ℝ :=
  if h : A.val < 3 ∧ B.val < 3 ∧ C.val < 3 ∧ D.val < 3 then
    riemannS3 ⟨A.val, h.1⟩ ⟨B.val, h.2.1⟩ ⟨C.val, h.2.2.1⟩ ⟨D.val, h.2.2.2⟩
  else 0

/-- 積計量の Levi-Civita 記号の拡張。添字に平坦方向が含まれれば 0 -/
noncomputable def prodEps (A B C : Fin 4) : ℝ :=
  if h : A.val < 3 ∧ B.val < 3 ∧ C.val < 3 then
    eps ⟨A.val, h.1⟩ ⟨B.val, h.2.1⟩ ⟨C.val, h.2.2⟩
  else 0

/-- 【3-2】球面方向のスピン接続は 3-1 のもの -/
theorem prodSpinConn_sphere (a : Fin 3) :
    prodSpinConn (Fin.castSucc a) = spinConn a := by
  have h : (Fin.castSucc a).val < 3 := a.isLt
  unfold prodSpinConn
  rw [dif_pos h]
  congr 1

/-- 【3-2】平坦方向のスピン接続は 0 -/
theorem prodSpinConn_flat : prodSpinConn 3 = 0 := by
  unfold prodSpinConn
  rw [dif_neg (by decide : ¬ (3 : Fin 4).val < 3)]

/-- 【3-2】球面ブロックの Riemann テンソルは 3-1 のもの -/
theorem prodRiemann_sphere (a b c d : Fin 3) :
    prodRiemann (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc c) (Fin.castSucc d)
      = riemannS3 a b c d := by
  have h : (Fin.castSucc a).val < 3 ∧ (Fin.castSucc b).val < 3 ∧
      (Fin.castSucc c).val < 3 ∧ (Fin.castSucc d).val < 3 :=
    ⟨a.isLt, b.isLt, c.isLt, d.isLt⟩
  unfold prodRiemann
  rw [dif_pos h]
  congr 1

/-- 【3-2】球面ブロックの Levi-Civita 記号は 3-1 のもの -/
theorem prodEps_sphere (a b c : Fin 3) :
    prodEps (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc c) = eps a b c := by
  have h : (Fin.castSucc a).val < 3 ∧ (Fin.castSucc b).val < 3 ∧
      (Fin.castSucc c).val < 3 :=
    ⟨a.isLt, b.isLt, c.isLt⟩
  unfold prodEps
  rw [dif_pos h]
  congr 1

/-- 【3-2】第 1 添字が平坦方向なら Riemann テンソルは 0 -/
theorem prodRiemann_flat_left (B C D : Fin 4) :
    prodRiemann 3 B C D = 0 := by
  unfold prodRiemann
  rw [dif_neg (fun h => absurd h.1 (by decide : ¬ (3 : Fin 4).val < 3))]

/-- 【3-2】第 1 添字が平坦方向なら Levi-Civita 記号は 0 -/
theorem prodEps_flat_left (B C : Fin 4) :
    prodEps 3 B C = 0 := by
  unfold prodEps
  rw [dif_neg (fun h => absurd h.1 (by decide : ¬ (3 : Fin 4).val < 3))]

/-- 【3-2】球面ブロックの交換子 [A_a, A_b] = −(i/2)ε_abc σ_c -/
theorem prod_commutator_sphere (a b : Fin 3) :
    prodSpinConn (Fin.castSucc a) * prodSpinConn (Fin.castSucc b)
      - prodSpinConn (Fin.castSucc b) * prodSpinConn (Fin.castSucc a)
      = (-Complex.I / 2) • ∑ c, ((prodEps (Fin.castSucc a) (Fin.castSucc b)
          (Fin.castSucc c) : ℝ) : ℂ) • σ c := by
  simp only [prodSpinConn_sphere, prodEps_sphere]
  exact spin_conn_commutator a b

/-- 【3-2】平坦方向との交換子は 0 -/
theorem prod_commutator_flat_left (B : Fin 4) :
    prodSpinConn 3 * prodSpinConn B - prodSpinConn B * prodSpinConn 3 = 0 := by
  rw [prodSpinConn_flat, zero_mul, mul_zero, sub_self]

/-- 【3-2】球面ブロックの Riemann 縮約：(1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_abc σ_c -/
theorem prod_riemann_clifford_sphere (a b : Fin 3) :
    (1 / 4 : ℂ) • ∑ c, ∑ d, ((prodRiemann (Fin.castSucc a) (Fin.castSucc b)
          (Fin.castSucc c) (Fin.castSucc d) : ℝ) : ℂ) • (σ c * σ d)
      = (-Complex.I / 2) • ∑ c, ((prodEps (Fin.castSucc a) (Fin.castSucc b)
          (Fin.castSucc c) : ℝ) : ℂ) • σ c := by
  simp only [prodRiemann_sphere, prodEps_sphere]
  exact riemann_clifford a b

/-- 【3-2】第 1 添字が平坦方向なら Riemann 縮約は両辺とも 0 -/
theorem prod_riemann_clifford_flat (B : Fin 4) :
    (1 / 4 : ℂ) • ∑ c, ∑ d, ((prodRiemann 3 B
          (Fin.castSucc c) (Fin.castSucc d) : ℝ) : ℂ) • (σ c * σ d)
      = (-Complex.I / 2) • ∑ c, ((prodEps 3 B
          (Fin.castSucc c) : ℝ) : ℂ) • σ c := by
  have hR : ∀ c d : Fin 3, prodRiemann 3 B (Fin.castSucc c) (Fin.castSucc d) = 0 :=
    fun c d => prodRiemann_flat_left B _ _
  have hE : ∀ c : Fin 3, prodEps 3 B (Fin.castSucc c) = 0 :=
    fun c => prodEps_flat_left B _
  simp [hR, hE]

/-- 【3-2】球面ブロックの完全なスピノル曲率 F_ab = −(3i/2)ε_abc σ_c -/
theorem prod_spin_curvature_sphere (a b : Fin 3) :
    prodSpinConn (Fin.castSucc a) * prodSpinConn (Fin.castSucc b)
      - prodSpinConn (Fin.castSucc b) * prodSpinConn (Fin.castSucc a)
      - ∑ c, ((2 * prodEps (Fin.castSucc a) (Fin.castSucc b)
          (Fin.castSucc c) : ℝ) : ℂ) • prodSpinConn (Fin.castSucc c)
      = (-3 / 2 * Complex.I) • ∑ c, ((prodEps (Fin.castSucc a) (Fin.castSucc b)
          (Fin.castSucc c) : ℝ) : ℂ) • σ c := by
  simp only [prodSpinConn_sphere, prodEps_sphere]
  exact spin_curvature a b

/-- 【3-2】第 1 添字が平坦方向なら完全な曲率は 0 -/
theorem prod_spin_curvature_flat (B : Fin 4) :
    prodSpinConn 3 * prodSpinConn B - prodSpinConn B * prodSpinConn 3
      - ∑ c, ((2 * prodEps 3 B (Fin.castSucc c) : ℝ) : ℂ) •
          prodSpinConn (Fin.castSucc c) = 0 := by
  have hE : ∀ c : Fin 3, prodEps 3 B (Fin.castSucc c) = 0 :=
    fun c => prodEps_flat_left B _
  simp [prodSpinConn_flat, hE]

/-- 【3-2】球面ブロックの Dirac シフト Σ_a σ_a A_a = (3i/2)·1 -/
theorem prod_dirac_shift :
    ∑ a, σ a * prodSpinConn (Fin.castSucc a)
      = (3 / 2 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [prodSpinConn_sphere]
  exact dirac_shift

/-- 【3-2】平坦方向は Dirac シフトに寄与しない（A_3 = 0 なので） -/
theorem prod_dirac_shift_flat (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * prodSpinConn 3 = 0 := by
  rw [prodSpinConn_flat, mul_zero]

end CFT.SpinCurvatureProduct
