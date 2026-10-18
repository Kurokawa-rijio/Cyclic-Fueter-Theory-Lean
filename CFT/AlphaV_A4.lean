/-
  α-V.7(Z31):a₄ の閉じた導出(Gilkey の公式 + 有限次元の代数)

  演算子:単位 S³ 上、スピノル C² ⊗ ゲージ C²(SU(2) 二重項)に働く
    D_λ = Σ_a 2σ_a ⊗ (L_a + λ s_a) + 3/2   (z31_heat.py の spectrum と同じ)
  左不変正規直交枠 X_a = 2iL_a は [X_a, X_b] = −2ε_abc X_c を満たす。
  ゲージ接続(枠成分、定数)A_a = 2iλ s_a、s_a = σ_a/2。
  左不変な A に対して曲率は F_ab = [A_a, A_b] − A([X_a, X_b]) = [A_a, A_b] + 2ε_abc A_c。
  D² = −∇² − E、E = ½ γ^aγ^b F_ab + (λ によらない曲率項)、γ^a = σ_a。

  Gilkey(1975)の a₄(閉多様体、E_{;kk} の項は積分で消える):
    a₄ = (4π)^{−n/2}(1/360) ∫ tr(60RE + 180E² + 30Ω_ijΩ_ij + λ によらない項)
  λ に依存するのは 180 tr E_F² + 30 tr Ω_F² だけ(tr F_ab = 0 なので交差項と RE の項は消える)。

  この節で Lean が確かめること:
    * F_ab = 4iλ(1−λ) ε_abc s_c                         : curvature_formula
    * tr F_ab = 0                                          : curvature_traceless
    * E_F = ½Σ σ_aσ_b ⊗ F_ab = i·4iλ(1−λ) Σ σ_c ⊗ s_c       : EF_eq
    * tr E_F² = 48λ²(1−λ)²、Σ tr (1⊗F_ab)² = −96λ²(1−λ)²  : trace_EF_sq, trace_Omega_sq
    * (4π)^{−3/2}(1/360)·Vol(S³)·(180·48 − 30·96) = 4√π      : a4_value
  よって a₄(λ) − a₄(0) = 4√π λ²(1−λ)²(数値フィットで認識した値の閉じた導出)。
  D_λ は S³ 上の真のねじれ Dirac 演算子である(定数 3/2 は左不変枠でのスピン接続の寄与。
  λ = 0 で固有値 ±(n + 3/2) を再現する)。
  外部定理:Gilkey の熱核係数の公式と Lichnerowicz の公式 D² = ∇*∇ + R/4 + ½γ^aγ^bF_ab。
  独立な確認:z31_heat.py の熱核の数値フィット(a₄(λ) − a₄(0) ≈ 4√π λ²(1−λ)²)と一致。
-/
import CFT.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix Complex
open scoped Kronecker

namespace CFT.A4

set_option maxHeartbeats 0

theorem I_cubed : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring

/-- パウリ行列 -/
def σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -I; I, 0], !![1, 0; 0, -1]]

/-- ゲージの生成子 s_a = σ_a/2 -/
noncomputable def s (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • σ a

/-- Levi-Civita 記号 -/
def eps : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- 接続の枠成分 A_a = 2iλ s_a -/
noncomputable def Ag (lam : ℝ) (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (2 * I * lam) • s a

/-- 曲率 F_ab = [A_a, A_b] + 2ε_abc A_c([X_a, X_b] = −2ε_abc X_c、A は左不変) -/
noncomputable def F (lam : ℝ) (a b : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  Ag lam a * Ag lam b - Ag lam b * Ag lam a + (2 : ℂ) • ∑ c, eps a b c • Ag lam c

theorem curvature_formula (lam : ℝ) (a b : Fin 3) :
    F lam a b = (4 * I * lam * (1 - lam)) • ∑ c, eps a b c • s c := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [F, Ag, s, σ, eps, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [I_sq, I_cubed]) <;> (try ring_nf) <;> (try simp [I_sq, I_cubed]) <;> (try ring)

theorem curvature_traceless (lam : ℝ) (a b : Fin 3) : trace (F lam a b) = 0 := by
  rw [curvature_formula, trace_smul, trace_sum]
  simp only [trace_smul, s, smul_eq_mul]
  have h : ∀ c, trace (σ c) = 0 := by
    intro c; fin_cases c <;> simp [σ, trace, Fin.sum_univ_two]
  simp [h]

/-- E の λ 依存部分 E_F = ½ Σ_ab σ_aσ_b ⊗ F_ab -/
noncomputable def EF (lam : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • ∑ a, ∑ b, (σ a * σ b) ⊗ₖ F lam a b

noncomputable def Msum : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := ∑ c, σ c ⊗ₖ s c

theorem EF_eq (lam : ℝ) : EF lam = (I * (4 * I * lam * (1 - lam))) • Msum := by
  simp only [EF, curvature_formula]
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [Msum, s, σ, eps, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.sum_apply, kroneckerMap_apply] <;>
    ring_nf <;> simp [I_sq] <;> ring

theorem trace_Msum_sq : trace (Msum * Msum) = 3 := by
  rw [Msum, Finset.sum_mul_sum]
  simp only [← mul_kronecker_mul, trace_sum, trace_kronecker]
  simp [s, σ, trace, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.mul_apply]
  norm_num

theorem trace_EF_sq (lam : ℝ) :
    trace (EF lam * EF lam) = 48 * (lam : ℂ)^2 * (1 - lam)^2 := by
  rw [EF_eq, smul_mul_smul_comm, trace_smul, trace_Msum_sq, smul_eq_mul]
  have e : I * (4 * I * (lam:ℂ) * (1 - lam)) * (I * (4 * I * lam * (1 - lam))) * 3
      = 48 * (I ^ 2) ^ 2 * (lam:ℂ) ^ 2 * (1 - lam) ^ 2 := by ring
  rw [e, I_sq]; ring

/-- Ω のゲージ部分 1 ⊗ F_ab の二乗の跡の和 -/
theorem trace_Omega_sq (lam : ℝ) :
    ∑ a, ∑ b, trace (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F lam a b) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F lam a b)) = -96 * (lam : ℂ)^2 * (1 - lam)^2 := by
  simp only [← mul_kronecker_mul, trace_kronecker, curvature_formula, mul_one]
  simp [s, σ, eps, trace, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.mul_apply]
  ring_nf; simp [I_sq]; ring

/-- 180·48 − 30·96 = 5760 -/
theorem integrand (lam : ℝ) :
    180 * trace (EF lam * EF lam) + 30 * (∑ a, ∑ b, trace (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
      F lam a b) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ F lam a b)))
      = 5760 * (lam : ℂ)^2 * (1 - lam)^2 := by
  rw [trace_EF_sq, trace_Omega_sq]; ring

/-- (4π)^{−3/2} = 1/(8π√π)、Vol(S³) = 2π²:(1/360)(4π)^{−3/2}·2π²·5760 = 4√π -/
theorem a4_value : (1 / 360 : ℝ) * (1 / (8 * Real.pi * Real.sqrt Real.pi)) * (2 * Real.pi ^ 2) * 5760
    = 4 * Real.sqrt Real.pi := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hp
  have hss : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hp.le
  field_simp
  nlinarith [hss]

/-- (4π)^{3/2} = 8π√π -/
theorem four_pi_three_halves : (4 * Real.pi) ^ ((3 : ℝ) / 2) = 8 * Real.pi * Real.sqrt Real.pi := by
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  ring

end CFT.A4
