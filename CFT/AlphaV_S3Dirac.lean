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
import Mathlib.Analysis.Quaternion

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
    (try simp [Complex.I_sq, pow_succ]) <;> (try ring) <;>
    linear_combination (I * lam) * Complex.I_sq

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

/-! ### 幾何の側:S³ の左不変な枠(V.2 を実際の S³ に結ぶ) -/

/-- 枠 X_a(q) = q e_a は S³ に接する:Re(q̄ · q e_a) = 0(q に直交) -/
theorem frame_tangent (q : ℍ[ℝ]) (a : Fin 3) : (star q * (q * e a)).re = 0 := by
  fin_cases a <;> simp [e] <;> ring

/-- 枠は正規直交:Re(conj(q e_a) · q e_b) = |q|² δ_ab(|q| = 1 なら正規直交) -/
theorem frame_orthonormal (q : ℍ[ℝ]) (a b : Fin 3) :
    (star (q * e a) * (q * e b)).re
      = (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) * (if a = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> simp [e] <;> ring

/-- X_b は線形な場 q ↦ q e_b なので、方向 v の微分は v e_b(Lie 括弧の計算に使う) -/
theorem frame_deriv (q v : ℍ[ℝ]) (b : Fin 3) :
    HasDerivAt (fun t : ℝ => (q + t • v) * e b) (v * e b) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (v * e b)).const_add (q * e b)
  have hf : (fun t : ℝ => (q + t • v) * e b) = fun t => q * e b + id t • (v * e b) := by
    funext t
    simp [add_mul, smul_mul_assoc]
  rw [hf]
  simpa using h

/-- 【α-V.2】ベクトル場の Lie 括弧:[X_a, X_b](q) = DX_b(q)[X_a(q)] − DX_a(q)[X_b(q)]
= (q e_a) e_b − (q e_b) e_a = Σ_c 2ε_abc X_c(q)(`frame_deriv` で DX_b(q)[v] = v e_b) -/
theorem frame_bracket (q : ℍ[ℝ]) (a b : Fin 3) :
    (q * e a) * e b - (q * e b) * e a = ∑ c, (2 * eps a b c) • (q * e c) := by
  rw [mul_assoc, mul_assoc, ← mul_sub, lie_bracket, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => Algebra.mul_smul_comm _ _ _)

/-! ### 4 次元の不変な断面の上の固有空間の全体 -/

/-- |↓↓⟩ -/
def dndn : Fin 2 × Fin 2 → ℂ := fun ij => if ij = (1, 1) then 1 else 0

/-- (|↑↓⟩ + |↓↑⟩) -/
def tsym : Fin 2 × Fin 2 → ℂ := fun ij => if ij = (0, 1) then 1 else if ij = (1, 0) then 1 else 0

theorem SS_dndn : SS.mulVec dndn = (1 : ℂ) • dndn := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [SS, σx, σy, σz, dndn, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring) <;> (try simp [Prod.ext_iff])

theorem SS_tsym : SS.mulVec tsym = (1 : ℂ) • tsym := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [SS, σx, σy, σz, tsym, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring) <;> (try simp [Prod.ext_iff])

/-- SS v = μ v なら (3/2 + λSS) v = (3/2 + λμ) v -/
theorem level_of (lam μ : ℂ) (v : Fin 2 × Fin 2 → ℂ) (h : SS.mulVec v = μ • v) :
    ((3 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + lam • SS).mulVec v
      = (3 / 2 + lam * μ) • v := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    h, smul_smul, ← add_smul]

/-- 4 次元の空間は三重項(upup, tsym, dndn)と一重項に分かれる:任意の v の分解 -/
theorem decomp (v : Fin 2 × Fin 2 → ℂ) :
    v = v (0, 0) • upup + v (1, 1) • dndn + ((v (0, 1) + v (1, 0)) / 2) • tsym
      + ((v (0, 1) - v (1, 0)) / 2) • singlet := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [upup, dndn, tsym, singlet, Prod.ext_iff] <;> ring

/-- 【α-V.2】還元した Dirac 作用素のスペクトルの全体:任意の v について
D v = (3/2 + λ)(v − c·singlet) + (3/2 − 3λ) c·singlet、c = (v₀₁ − v₁₀)/2。
三重項(3 次元)の固有値は 3/2 + λ、一重項(1 次元)は 3/2 − 3λ で、これで尽きる。 -/
theorem reduced_dirac_spectrum (lam : ℂ) (v : Fin 2 × Fin 2 → ℂ) :
    ((-I) • (Matrix.kroneckerMap (· * ·) ((3 / 2 * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (1 : Matrix (Fin 2) (Fin 2) ℂ) + gaugeTerm lam)).mulVec v
      = (3 / 2 + lam) • (v - ((v (0, 1) - v (1, 0)) / 2) • singlet)
        + (3 / 2 - 3 * lam) • (((v (0, 1) - v (1, 0)) / 2) • singlet) := by
  rw [reduced_dirac]
  have hu := level_of lam 1 upup SS_upup
  have hd := level_of lam 1 dndn SS_dndn
  have ht := level_of lam 1 tsym SS_tsym
  have hs := level_of lam (-3) singlet SS_singlet
  conv_lhs => rw [decomp v]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hu, hd, ht, hs]
  ext x
  have hx := congrFun (decomp v) x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hx ⊢
  linear_combination (-(3 / 2 + lam)) * hx

end CFT.S3Dirac
