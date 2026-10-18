/-
  α-I 代数的な起点(Y1〜Y6)

  形式化した内容
  * α-I.1 (Y1)  四元数の規約 i² = j² = k² = ijk = −1、ノルムの乗法性
  * α-I.3 (Y1, Y2) 二つの実形
        Euclid 実形   ρ(q) ∈ M₂(ℂ)、det ρ(q) = |q|²、ρ は積を保つ
        Lorentz 実形  X = tI + x·σ、det X = t² − |x|²
  * α-I.4 (Y3)  Clifford 関係から H² = E²、正エネルギー射影 P = ½(1 + H/E) は冪等
  * α-I.5 (Y4)  q_D = m/E + p/E は単位四元数、m > 0 なら開いた上半球。
                 動径方向の計量 ½|dq|² = ½ χ′²、χ = arctan(|p|/m)、χ′ = m/E²
  * α-I.7 (Y6)  Hopf 写像 q ↦ q x q̄ はノルムを |q|²|x| に写し、純虚を保つ。
                 sech, tanh のプロファイルが k′ = −f k, f′ = k² を満たす

  形式化していない内容(理由は README)
  * α-I.2 (Y2)  行列 C の成分が手元の資料にないため
  * α-I.6 (Y5)  Berry 接続と Wigner 接続の曲率比の式が手元にないため
-/
import CFT.Basic

open Quaternion Real

namespace CFT.AlphaI

/-! ### α-I.1 四元数の規約 -/

/-- i² = −1 -/
theorem i_sq : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 1, 0, 0⟩ = -1 := by
  ext <;> simp

/-- j² = −1 -/
theorem j_sq : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ = -1 := by
  ext <;> simp

/-- k² = −1 -/
theorem k_sq : (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) * ⟨0, 0, 0, 1⟩ = -1 := by
  ext <;> simp

/-- ijk = −1 -/
theorem ijk : (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * ⟨0, 0, 1, 0⟩ * ⟨0, 0, 0, 1⟩ = -1 := by
  ext <;> simp

/-- ノルムの乗法性 |pq|² = |p|²|q|² -/
theorem normSq_mul' (p q : ℍ[ℝ]) : normSq (p * q) = normSq p * normSq q :=
  map_mul normSq p q

/-! ### α-I.3 二つの実形 -/

/-- Euclid 実形 ρ : ℍ → M₂(ℂ) -/
noncomputable def rho (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
     -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I]

/-- det ρ(q) = |q|² -/
theorem det_rho (q : ℍ[ℝ]) : (rho q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [rho, Matrix.det_fin_two_of, Quaternion.normSq_def']
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- ρ は積を保つ(代数準同型であることの核心部分) -/
theorem rho_mul (p q : ℍ[ℝ]) : rho (p * q) = rho p * rho q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [rho, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Lorentz 実形:X = tI + x·σ の行列式は t² − |x|² -/
theorem det_lorentz (t x y z : ℝ) :
    (!![(t : ℂ) + z, (x : ℂ) - y * Complex.I; (x : ℂ) + y * Complex.I, (t : ℂ) - z] :
      Matrix (Fin 2) (Fin 2) ℂ).det = ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two_of]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### α-I.4 Clifford 関係と正エネルギー射影 -/

section Clifford

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- β² = α_i² = 1、相異なるものは反可換なら、H = mβ + Σ pᵢαᵢ は H² = (m² + |p|²)·1 -/
theorem dirac_sq (β a1 a2 a3 : A) (m p1 p2 p3 : ℝ)
    (hb : β * β = 1) (h1 : a1 * a1 = 1) (h2 : a2 * a2 = 1) (h3 : a3 * a3 = 1)
    (hb1 : a1 * β = -(β * a1)) (hb2 : a2 * β = -(β * a2)) (hb3 : a3 * β = -(β * a3))
    (h12 : a2 * a1 = -(a1 * a2)) (h13 : a3 * a1 = -(a1 * a3)) (h23 : a3 * a2 = -(a2 * a3)) :
    (m • β + p1 • a1 + p2 • a2 + p3 • a3) * (m • β + p1 • a1 + p2 • a2 + p3 • a3)
      = (m ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, hb, h1, h2, h3, hb1, hb2, hb3, h12, h13,
    h23, smul_neg]
  simp only [add_smul, pow_two]
  rw [mul_comm p1 m, mul_comm p2 m, mul_comm p3 m, mul_comm p2 p1, mul_comm p3 p1,
    mul_comm p3 p2]
  abel

/-- H² = E²·1、E ≠ 0 なら P = ½(1 + H/E) は冪等(P² = P) -/
theorem proj_idem (H : A) (E : ℝ) (hE : E ≠ 0) (hH : H * H = (E ^ 2) • (1 : A)) :
    ((1 / 2 : ℝ) • (1 + E⁻¹ • H)) * ((1 / 2 : ℝ) • (1 + E⁻¹ • H))
      = (1 / 2 : ℝ) • (1 + E⁻¹ • H) := by
  have key : (E⁻¹ • H) * (E⁻¹ • H) = (1 : A) := by
    rw [smul_mul_smul_comm, hH, smul_smul]
    rw [show E⁻¹ * E⁻¹ * E ^ 2 = (1 : ℝ) by field_simp; ring, one_smul]
  simp only [smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, key]
  rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
  have : (1 : A) + E⁻¹ • H + (E⁻¹ • H + 1) = (2 : ℝ) • (1 + E⁻¹ • H) := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

end Clifford

/-! ### α-I.5 量子半球 -/

/-- q_D = (m + p)/E は単位四元数 -/
theorem qD_unit (m p1 p2 p3 E : ℝ) (hE0 : E ≠ 0)
    (hE : E ^ 2 = m ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) :
    normSq (⟨m / E, p1 / E, p2 / E, p3 / E⟩ : ℍ[ℝ]) = 1 := by
  rw [normSq_def']
  simp only
  field_simp
  linarith [hE]

/-- m > 0、E > 0 なら q_D の実部は正(開いた上半球) -/
theorem qD_upper (m E : ℝ) (hm : 0 < m) (hE : 0 < E) : 0 < m / E := div_pos hm hE

/-- 速度表示 Q_m = √(1 − |β|²) + β も単位四元数 -/
theorem Qm_unit (b1 b2 b3 : ℝ) (hb : b1 ^ 2 + b2 ^ 2 + b3 ^ 2 ≤ 1) :
    normSq (⟨√(1 - (b1 ^ 2 + b2 ^ 2 + b3 ^ 2)), b1, b2, b3⟩ : ℍ[ℝ]) = 1 := by
  rw [normSq_def']
  simp only
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- 静止極限(β = 0)は北極 1 -/
theorem Qm_rest : (⟨√(1 - (0 ^ 2 + 0 ^ 2 + 0 ^ 2 : ℝ)), 0, 0, 0⟩ : ℍ[ℝ]) = 1 := by
  ext <;> simp

/-- 動径方向:d(m/E)/dp = −mp/E³、d(p/E)/dp = m²/E³ の二乗和は (m/E²)² -/
theorem radial_metric (m p E : ℝ) (hE0 : E ≠ 0) (hE : E ^ 2 = m ^ 2 + p ^ 2) :
    (-(m * p) / E ^ 3) ^ 2 + (m ^ 2 / E ^ 3) ^ 2 = (m / E ^ 2) ^ 2 := by
  field_simp
  have h3 : (E ^ 3) ^ 2 = (E ^ 2) ^ 2 * E ^ 2 := by ring
  rw [h3, hE]
  ring

/-- χ(p) = arctan(p/m) の導関数は m/(m² + p²) = m/E² -/
theorem chi_deriv (m p : ℝ) (hm : m ≠ 0) :
    HasDerivAt (fun p => arctan (p / m)) (m / (m ^ 2 + p ^ 2)) p := by
  have h := (hasDerivAt_arctan (p / m)).comp p ((hasDerivAt_id p).div_const m)
  convert h using 1
  have : m ^ 2 + p ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### α-I.7 Hopf 写像と BPS プロファイル -/

/-- |q x q̄|² = |q|⁴ |x|² -/
theorem hopf_norm (q x : ℍ[ℝ]) : normSq (q * x * star q) = normSq q ^ 2 * normSq x := by
  rw [map_mul, map_mul, normSq_star]
  ring

/-- Re(q x q̄) = |q|² Re x。とくに x が純虚なら q x q̄ も純虚(S² に値をとる) -/
theorem hopf_re (q x : ℍ[ℝ]) : (q * x * star q).re = normSq q * x.re := by
  rw [normSq_def']
  simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]
  ring

/-- k = sech η、f = tanh η は k′ = −f k を満たす -/
theorem bps_k (η : ℝ) :
    HasDerivAt (fun η => (cosh η)⁻¹) (-(sinh η / cosh η) * (cosh η)⁻¹) η := by
  have hc : cosh η ≠ 0 := (cosh_pos η).ne'
  have h := (hasDerivAt_cosh η).inv hc
  convert h using 1
  ring

/-- f = tanh η = sinh/cosh は f′ = k² = sech² η を満たす -/
theorem bps_f (η : ℝ) :
    HasDerivAt (fun η => sinh η / cosh η) (((cosh η)⁻¹) ^ 2) η := by
  have hc : cosh η ≠ 0 := (cosh_pos η).ne'
  have h := (hasDerivAt_sinh η).div (hasDerivAt_cosh η) hc
  convert h using 1
  field_simp
  linear_combination (-1 : ℝ) * cosh_sq η

end CFT.AlphaI
