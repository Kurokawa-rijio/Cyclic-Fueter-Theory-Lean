/-
  α-V 量子論(Z14〜Z19, Z29, Z31)

  形式化した内容
  * α-V.1 (Z14)  量子半球と H³ の共形対応:χ = gd ρ とすると
                  cos χ = sech ρ、sin χ = tanh ρ、tan χ = sinh ρ、dχ/dρ = sech ρ(= cos χ)
         (Z15)  Foldy–Wouthuysen 生成子:(β α·p̂)² = −1(Clifford 関係から)
         (Z16)  U = (m − iσ·p)/E は単位四元数(α-I.5 の qD_unit と同じ)
  * α-V.2 (Z18-a) isospin 1/2 に結合した S³ 上の Dirac 作用素の j = 0 部分
                  D = 3/2 + λ Σσₐ⊗σₐ:一重項の固有値は 3/2 − 3λ、三重項は 3/2 + λ
  * α-V.4 (Z19)  Gauss 写像:cos χ = √(1 − 2m/r) なら sin²χ = 2m/r。
                  一様密度の内部で 2σ₂ = 16πρ、真空の外部で k_r/k_⊥ = −1/2
  * α-V.7 (Z31)  熱核係数 a₄ = 4√π λ²(1−λ)²、対数係数 2λ²(1−λ)² は meron(λ = 1/2)で 1/8

  形式化していない内容
  * α-V.5 (Z29) limit-point 判定:Weyl の limit-point/limit-circle 判定(外部定理)と
    Lebesgue 積分の評価が必要(README)
-/
import CFT.AlphaIV
import Mathlib.Data.Matrix.Kronecker

open Real

namespace CFT.AlphaV

open CFT.AlphaIV (gd)

/-! ### α-V.1 共形対応(Z14) -/

theorem cos_gd (ρ : ℝ) : cos (gd ρ) = 1 / cosh ρ := by
  rw [gd, cos_arctan, ← cosh_sq', Real.sqrt_sq (cosh_pos ρ).le]

theorem sin_gd (ρ : ℝ) : sin (gd ρ) = sinh ρ / cosh ρ := by
  rw [gd, sin_arctan, ← cosh_sq', Real.sqrt_sq (cosh_pos ρ).le]

/-- tan χ = sinh ρ、sin²χ + cos²χ = 1 の整合 -/
theorem conformal_consistent (ρ : ℝ) :
    (sinh ρ / cosh ρ) ^ 2 + (1 / cosh ρ) ^ 2 = 1 ∧ (sinh ρ / cosh ρ) / (1 / cosh ρ) = sinh ρ := by
  have hc : cosh ρ ≠ 0 := (cosh_pos ρ).ne'
  constructor
  · field_simp; rw [cosh_sq]
  · field_simp

/-- モードの一致 u₁ = sin χ cos χ = tanh ρ sech ρ = ψ₁ -/
theorem mode_identity (ρ : ℝ) :
    sin (gd ρ) * cos (gd ρ) = (sinh ρ / cosh ρ) * (1 / cosh ρ) := by
  rw [sin_gd, cos_gd]

/-! ### Z15 Foldy–Wouthuysen 生成子 -/

theorem fw_generator {A : Type*} [Ring A] (β n : A)
    (hb : β * β = 1) (hn : n * n = 1) (hbn : n * β = -(β * n)) :
    (β * n) * (β * n) = -1 := by
  calc (β * n) * (β * n) = β * (n * β) * n := by simp only [mul_assoc]
    _ = β * (-(β * n)) * n := by rw [hbn]
    _ = -((β * β) * (n * n)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [hb, hn, one_mul]

/-! ### α-V.2 準位の移動 3/2 − 3λ(Z18-a) -/

/-- Pauli 行列 -/
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Σₐ σₐ ⊗ σₐ -/
def SS : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) σx σx + Matrix.kroneckerMap (· * ·) σy σy
    + Matrix.kroneckerMap (· * ·) σz σz

/-- 一重項 (|↑↓⟩ − |↓↑⟩) -/
def singlet : Fin 2 × Fin 2 → ℂ := fun ij =>
  if ij = (0, 1) then 1 else if ij = (1, 0) then -1 else 0

/-- 三重項の代表 |↑↑⟩ -/
def upup : Fin 2 × Fin 2 → ℂ := fun ij => if ij = (0, 0) then 1 else 0

theorem SS_singlet : SS.mulVec singlet = (-3 : ℂ) • singlet := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [SS, σx, σy, σz, singlet, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply] <;>
    (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring) <;> (try simp [Prod.ext_iff])

theorem SS_upup : SS.mulVec upup = (1 : ℂ) • upup := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [SS, σx, σy, σz, upup, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply]

/-- D = 3/2 + λ·SS の一重項での値は 3/2 − 3λ -/
theorem level_shift (lam : ℂ) :
    ((3 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + lam • SS).mulVec singlet
      = (3 / 2 - 3 * lam) • singlet := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    SS_singlet, smul_smul, ← add_smul]
  congr 1
  ring

theorem level_triplet (lam : ℂ) :
    ((3 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + lam • SS).mulVec upup
      = (3 / 2 + lam) • upup := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    SS_upup, smul_smul, ← add_smul]
  congr 1
  ring

/-! ### α-V.4 Gauss 写像(Z19) -/

theorem gauss_compactness (m r : ℝ) (h : 2 * m / r ≤ 1) :
    1 - (√(1 - 2 * m / r)) ^ 2 = 2 * m / r := by
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- 一様密度の星の内部:k_r = k_⊥ = c、c² = 2M/R³ なら 2σ₂ = 2(2k_r k_⊥ + k_⊥²) = 16πρ、
    ρ = 3M/(4πR³) -/
theorem gauss_interior (M R c : ℝ) (hR : R ≠ 0) (hc : c ^ 2 = 2 * M / R ^ 3) :
    2 * (2 * c * c + c ^ 2) = 16 * π * (3 * M / (4 * π * R ^ 3)) := by
  have hπ : π ≠ 0 := pi_ne_zero
  have : 2 * (2 * c * c + c ^ 2) = 6 * c ^ 2 := by ring
  rw [this, hc]
  field_simp
  ring

/-- 真空の外部:σ₂ = 2k_r k_⊥ + k_⊥² = 0、k_⊥ ≠ 0 なら k_r/k_⊥ = −1/2 -/
theorem gauss_vacuum (kr kp : ℝ) (hp : kp ≠ 0) (h : 2 * kr * kp + kp ^ 2 = 0) :
    kr / kp = -1 / 2 := by
  field_simp
  have : kp * (2 * kr + kp) = 0 := by linarith [h]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hp
  · linarith

/-! ### α-V.7 熱核係数(Z31) -/

noncomputable def a4 (lam : ℝ) : ℝ := 4 * √π * lam ^ 2 * (1 - lam) ^ 2

theorem log_coeff_meron : 2 * (1 / 2 : ℝ) ^ 2 * (1 - 1 / 2) ^ 2 = 1 / 8 := by norm_num

theorem a4_meron : a4 (1 / 2) = √π / 4 := by
  rw [a4]; ring

/-- 真空(λ = 0)とゲージ同値な真空(λ = 1)では a₄ = 0 -/
theorem a4_vacua : a4 0 = 0 ∧ a4 1 = 0 := by
  constructor <;> simp [a4]

end CFT.AlphaV
