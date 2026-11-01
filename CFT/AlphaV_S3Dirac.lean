/-
  α-V.2 (Z18-a):S³ の Dirac 作用素から準位 3/2 − 3λ、3/2 + λ への還元

  単位 S³ = 単位四元数 = SU(2)。左不変な正規直交枠 X_a(q) = q e_a(e = (i, j, k))をとる。
  * 括弧:[X_a, X_b] は Lie 代数の括弧 e_a e_b − e_b e_a = 2 ε_abc e_c(`lie_bracket`)
    (左不変なベクトル場の括弧が Lie 代数の括弧であることは標準的な事実)
  * Levi-Civita 接続の係数 ω_abc = ½(c_abc − c_bca + c_cab)(Koszul、c_abc = 2ε_abc)は ω_abc = ε_abc(`koszul`)
  * スピン接続の定数項:¼ Σ ω_abc σ_a σ_b σ_c = (3i/2)·1(`spin_term`)
  * 左不変な SU(2) 接続 A(X_a) = iλ τ_a(λ = 0 と 1 が真空、λ = 1/2 がメロン)
  Dirac 作用素 D = −i Σ_a σ_a (X_a + ¼ ω_abc σ_b σ_c + A(X_a)) は、左不変な断面(枠の上で一定な
  スピノル ⊗ アイソスピン、4 次元)を保ち、そこで
    D = 3/2 + λ Σ_a σ_a ⊗ τ_a                       (`reduced_dirac`)
  に還元される。固有値は一重項で 3/2 − 3λ、三重項で 3/2 + λ(`level_singlet`、`level_triplet`)。
  左不変な断面はなめらかな大域的断面なので、D の定義域(H¹)と L²(S³) の状態空間に属する。
-/
import CFT.AlphaV

namespace CFT.S3Dirac

open Matrix Complex CFT.AlphaV Quaternion

/-- Levi-Civita 記号 -/
def eps (a b c : Fin 3) : ℝ :=
  (![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
     ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
     ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] : Fin 3 → Fin 3 → Fin 3 → ℝ) a b c

/-- 虚数単位 e = (i, j, k) -/
noncomputable def e : Fin 3 → ℍ[ℝ] := ![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- 左不変なベクトル場の括弧 = Lie 代数の括弧:e_a e_b − e_b e_a = Σ_c 2ε_abc e_c -/
theorem lie_bracket (a b : Fin 3) :
    e a * e b - e b * e a = ∑ c, (2 * eps a b c) • e c := by
  fin_cases a <;> fin_cases b <;> ext <;>
    simp [e, eps, Fin.sum_univ_three] <;> norm_num

/-- Koszul:c_abc = 2ε_abc のとき ω_abc = ½(c_abc − c_bca + c_cab) = ε_abc -/
theorem koszul (a b c : Fin 3) :
    (2 * eps a b c - 2 * eps b c a + 2 * eps c a b) / 2 = eps a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps] <;> norm_num

/-- Pauli 行列 σ = (σ_x, σ_y, σ_z) -/
def σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![σx, σy, σz]

/-- スピン接続の定数項:¼ Σ ε_abc σ_a σ_b σ_c = (3i/2)·1 -/
theorem spin_term :
    (1 / 4 : ℂ) • ∑ a, ∑ b, ∑ c, ((eps a b c : ℝ) : ℂ) • (σ a * σ b * σ c)
      = (3 / 2 * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ, σx, σy, σz, eps, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring)

/-- ゲージ項 Σ_a σ_a ⊗ A(X_a)、A(X_a) = iλ σ_a(アイソスピン) -/
noncomputable def gaugeTerm (lam : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ a, Matrix.kroneckerMap (· * ·) (σ a) ((I * lam) • σ a)

/-- 【α-V.2】一様な断面の上で D = −i(スピン項 ⊗ 1 + ゲージ項) = 3/2 + λ Σσ⊗σ -/
theorem reduced_dirac (lam : ℂ) :
    (-I) • (Matrix.kroneckerMap (· * ·) ((3 / 2 * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) + gaugeTerm lam)
      = (3 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + lam • SS := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [gaugeTerm, SS, σ, σx, σy, σz, Fin.sum_univ_three, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.add_apply, Prod.ext_iff] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq, pow_succ, Prod.ext_iff]) <;> (try ring_nf) <;>
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring)

/-- 【α-V.2】一重項の準位 3/2 − 3λ -/
theorem level_singlet (lam : ℂ) :
    ((-I) • (Matrix.kroneckerMap (· * ·) ((3 / 2 * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) + gaugeTerm lam)).mulVec singlet
      = (3 / 2 - 3 * lam) • singlet := by
  rw [reduced_dirac]; exact level_shift lam

/-- 【α-V.2】三重項の準位 3/2 + λ -/
theorem level_triplet' (lam : ℂ) :
    ((-I) • (Matrix.kroneckerMap (· * ·) ((3 / 2 * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) + gaugeTerm lam)).mulVec upup
      = (3 / 2 + lam) • upup := by
  rw [reduced_dirac]; exact level_triplet lam

end CFT.S3Dirac
