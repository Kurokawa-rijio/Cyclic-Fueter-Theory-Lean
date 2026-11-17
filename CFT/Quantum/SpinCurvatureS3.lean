/-
  3-1 定曲率でのスピノル曲率の恒等式（S³、丸い球面）

  `CFT/Quantum/S3DiracReduction.lean`（α-V.2）が既に示している部品：
  左不変枠の括弧 [X_a, X_b] = 2ε_abc X_c（`lie_bracket`）、Koszul 係数
  ω_abc = ε_abc（`koszul`）、スピン項の和 (1/4)Σ_abc ε_abc σ_aσ_bσ_c = (3i/2)·1
  （`spin_term`）。ここでは成分ごとの恒等式に分解し、交換子 [∇, ∇] が
  曲率とクリフォード積で書けることを示す。

  規約は `S3DiracReduction` と同じ：Pauli 行列 σ_a（σ_aσ_b + σ_bσ_a = 2δ_ab）、
  Dirac 作用素 D = −iΣ_a σ_a∇_a、∇_a = X_a + A_a、スピン接続の成分
    A_a = (1/4)Σ_bc ω_abc σ_bσ_c = (1/4)Σ_bc ε_abc σ_bσ_c。
  証明する恒等式（すべて sympy による明示行列計算でも照合済み）：
  * `spinConn_eq`：A_a = (i/2)σ_a。
  * `spin_conn_commutator`：[A_a, A_b] = −(i/2)ε_abc σ_c。
  * `riemann_clifford`：定曲率 +1 の Riemann テンソル
    R_abcd = δ_adδ_bc − δ_acδ_bd（R(X,Y)Z = ⟨Y,Z⟩X − ⟨X,Z⟩Y の符号）に対し
    (1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_abc σ_c。すなわち裸の交換子
    [A_a, A_b] は Riemann テンソルとクリフォード積の縮約そのもの。
  * `spin_curvature`：Lie 括弧の分を差し引いた完全な曲率
    F_ab = [A_a, A_b] − Σ_c 2ε_abc A_c = −(3i/2)ε_abc σ_c。
    （[∇_a, ∇_b] − ∇_[X_a,X_b] の行列部分。Σ_c 2ε_abc A_c が ∇_[X_a,X_b] の
    接続部分で、`lie_bracket` の [X_a, X_b] = 2ε_abc X_c から来る。）
  * `spin_curvature_riemann`：F_ab = 3·(1/4)Σ_cd R_abcd σ_cσ_d。
  * `dirac_shift`：Σ_a σ_a A_a = (3i/2)·1（`spin_term` の成分版。
    左不変スピノル上の D = 3/2 の源）。
-/
import CFT.Quantum.S3DiracReduction

namespace CFT.SpinCurvature

open Matrix Complex CFT.AlphaV CFT.S3Dirac

/-- スピン接続の成分 A_a = (1/4)Σ_bc ε_abc σ_b σ_c -/
noncomputable def spinConn (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℂ) • ∑ b, ∑ c, ((eps a b c : ℝ) : ℂ) • (σ b * σ c)

/-- 定曲率 +1 の Riemann テンソル R_abcd = δ_adδ_bc − δ_acδ_bd -/
noncomputable def riemannS3 (a b c d : Fin 3) : ℝ :=
  (if a = d then 1 else 0) * (if b = c then 1 else 0)
    - (if a = c then 1 else 0) * (if b = d then 1 else 0)

/-- 【3-1】スピン接続の成分は (i/2)σ_a -/
theorem spinConn_eq (a : Fin 3) : spinConn a = (Complex.I / 2) • σ a := by
  show (1 / 4 : ℂ) • ∑ b, ∑ c, ((eps a b c : ℝ) : ℂ) • (σ b * σ c)
    = (Complex.I / 2) • σ a
  fin_cases a <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ, σx, σy, σz, eps, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring) <;>
    (try simp only [pow_three, Complex.I_mul_I]) <;> (try ring_nf) <;> (try ring)

set_option maxHeartbeats 800000 in
/-- 【3-1】スピン接続の交換子 [A_a, A_b] = −(i/2)ε_abc σ_c -/
theorem spin_conn_commutator (a b : Fin 3) :
    spinConn a * spinConn b - spinConn b * spinConn a
      = (-Complex.I / 2) • ∑ c, ((eps a b c : ℝ) : ℂ) • σ c := by
  simp only [spinConn_eq]
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ, σx, σy, σz, eps, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring) <;>
    (try simp only [pow_three, Complex.I_mul_I]) <;> (try ring_nf) <;> (try ring)

set_option maxHeartbeats 800000 in
/-- 【3-1】Riemann テンソルとクリフォード積の縮約：(1/4)Σ_cd R_abcd σ_cσ_d = −(i/2)ε_abc σ_c -/
theorem riemann_clifford (a b : Fin 3) :
    (1 / 4 : ℂ) • ∑ c, ∑ d, ((riemannS3 a b c d : ℝ) : ℂ) • (σ c * σ d)
      = (-Complex.I / 2) • ∑ c, ((eps a b c : ℝ) : ℂ) • σ c := by
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [riemannS3, σ, σx, σy, σz, eps, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring) <;>
    (try simp only [pow_three, Complex.I_mul_I]) <;> (try ring_nf) <;> (try ring)

set_option maxHeartbeats 800000 in
/-- 【3-1】完全なスピノル曲率 F_ab = [A_a, A_b] − Σ_c 2ε_abc A_c = −(3i/2)ε_abc σ_c -/
theorem spin_curvature (a b : Fin 3) :
    spinConn a * spinConn b - spinConn b * spinConn a
      - ∑ c, ((2 * eps a b c : ℝ) : ℂ) • spinConn c
      = (-3 / 2 * Complex.I) • ∑ c, ((eps a b c : ℝ) : ℂ) • σ c := by
  simp only [spinConn_eq]
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ, σx, σy, σz, eps, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring) <;>
    (try simp only [pow_three, Complex.I_mul_I]) <;> (try ring_nf) <;> (try ring)

/-- 【3-1】完全なスピノル曲率は Riemann 縮約の 3 倍：F_ab = 3·(1/4)Σ_cd R_abcd σ_cσ_d -/
theorem spin_curvature_riemann (a b : Fin 3) :
    spinConn a * spinConn b - spinConn b * spinConn a
      - ∑ c, ((2 * eps a b c : ℝ) : ℂ) • spinConn c
      = (3 : ℂ) • ((1 / 4 : ℂ) • ∑ c, ∑ d, ((riemannS3 a b c d : ℝ) : ℂ) • (σ c * σ d)) := by
  rw [spin_curvature, riemann_clifford, smul_smul]
  congr 1
  ring

/-- 【3-1】Σ_a σ_a A_a = (3i/2)·1（`spin_term` の成分版） -/
theorem dirac_shift :
    ∑ a, σ a * spinConn a
      = (3 / 2 * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [spinConn_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ, σx, σy, σz, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring) <;>
    (try simp only [pow_three, Complex.I_mul_I]) <;> (try ring_nf) <;> (try ring)

end CFT.SpinCurvature
