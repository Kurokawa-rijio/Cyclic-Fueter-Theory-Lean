/-
  完全化(その2):α-I.3、α-II.1、α-V.1(Z16)、α-I.4、α-I.5

  * α-I.3  Euclid 実形 ρ は単射で ρ(q̄) = ρ(q)†、単位四元数は SU(2) に写る。
           Lorentz 実形:det A = 1 の A ∈ SL(2,ℂ) は X ↦ AXA† でエルミート性と det X = t² − |x|² を保つ
  * α-II.1 (II) ⇔ {∇R = 0, Cotton = 0}(直交枠の成分で、縮約 Bianchi のもとで)
  * α-V.1 (Z16) e = U⁻¹dU(U = (m − iσ·p)/E)は e_i = i[σ·(p×e_i) − mσ_i]/E²、
           Maurer–Cartan(捩れゼロ)de + e∧e = 0 が成り立ち、e は su(2) 値、
           計量 −½tr(e_i e_j) = δ_ij/E² − p_i p_j/E⁴ は |dQ|² の引き戻しに一致。
           よって A_F = ½e は計量 |dQ|²(したがって ½|dQ|² = g^Q)の Levi-Civita スピン接続
  * α-I.4 (Y3) 正エネルギー射影 P = ½(1 + H/E) の量子計量 ½tr(∂_iP ∂_jP) = ½(δ_ij/E² − p_i p_j/E⁴)
  * α-I.5 (Y4) Q = (m, p)/E の引き戻し計量 Σ_μ ∂_iQ_μ ∂_jQ_μ = δ_ij/E² − p_i p_j/E⁴。
           したがって g^Q = ½ × (単位 S³ の計量) で、量子球面の半径は 1/√2
  1/E は変数 iE と関係式 (m² + |p|²) iE² = 1 で扱う(E² = m² + |p|²、E > 0 と同値)。
  各成分の等式は sympy(aux/gen_B.py)で求めた係数で Lean が検算する。
-/
import CFT.AlphaI
import CFT.AlphaI_AW
import CFT.AlphaV_FW
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Matrix Quaternion

namespace CFT.AlphaCompleteB

/-! ### α-I.3 二つの実形(完全化) -/

open CFT.AlphaI in
/-- ρ は単射 -/
theorem rho_injective (q : ℍ[ℝ]) (h : rho q = 0) : q = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [rho, Complex.ext_iff] at h00 h01
  ext <;> simp [h00, h01]

open CFT.AlphaI in
/-- ρ(q̄) = ρ(q)†(共役転置) -/
theorem rho_star (q : ℍ[ℝ]) : rho (star q) = (rho q).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, Matrix.conjTranspose_apply, Complex.ext_iff] <;> ring_nf <;> simp

open CFT.AlphaI in
theorem rho_one : rho 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho]

open CFT.AlphaI in
/-- 単位四元数は SU(2) に写る:ρ(q)ρ(q)† = 1、det ρ(q) = 1 -/
theorem rho_SU2 (q : ℍ[ℝ]) (hq : Quaternion.normSq q = 1) :
    rho q * (rho q).conjTranspose = 1 ∧ (rho q).det = 1 := by
  constructor
  · rw [← rho_star, ← rho_mul, Quaternion.self_mul_star, hq]
    simpa using rho_one
  · rw [det_rho, hq]; simp

/-- Lorentz 実形:A ∈ SL(2,ℂ) は X ↦ AXA† でエルミート性と行列式を保つ -/
theorem lorentz_action (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (hX : X.conjTranspose = X) :
    (A * X * A.conjTranspose).conjTranspose = A * X * A.conjTranspose ∧
      (A * X * A.conjTranspose).det = X.det := by
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX,
      Matrix.mul_assoc]
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hA]
    simp

/-! ### α-II.1 (II) ⇔ {∇R = 0, Cotton = 0} -/

/-- N c b d = ∇_c Ric_bd(直交枠、b, d について対称)、∇_d R = Σ_b N d b b、
    縮約 Bianchi Σ_c N c c d = ½∇_d R。
    (II):T c b d = N c b d − N b c d = 0。
    Cotton:C c b d = (N c b d − ¼∇_c R δ_bd) − (N b c d − ¼∇_b R δ_cd) -/
theorem II_iff_cotton (N : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hsym : ∀ c b d, N c b d = N c d b)
    (hBianchi : ∀ d, ∑ c, N c c d = (∑ b, N d b b) / 2) :
    let gradR : Fin 3 → ℝ := fun d => ∑ b, N d b b
    let δ : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0
    let C : Fin 3 → Fin 3 → Fin 3 → ℝ := fun c b d =>
      (N c b d - gradR c * δ b d / 4) - (N b c d - gradR b * δ c d / 4)
    (∀ c b d, N c b d - N b c d = 0) ↔ ((∀ d, gradR d = 0) ∧ ∀ c b d, C c b d = 0) := by
  intro gradR δ C
  constructor
  · intro hT
    have hgrad : ∀ d, gradR d = 0 := by
      intro d
      have h1 : ∑ c, (N c d c - N d c c) = 0 := by
        apply Finset.sum_eq_zero; intro c _; exact hT c d c
      have h2 : ∑ c, N c d c = ∑ c, N c c d := by
        apply Finset.sum_congr rfl; intro c _; exact hsym c d c
      rw [Finset.sum_sub_distrib, h2, hBianchi d] at h1
      simp only [gradR]
      linarith
    refine ⟨hgrad, ?_⟩
    intro c b d
    simp only [C, hgrad]
    have := hT c b d
    linarith
  · rintro ⟨hgrad, hC⟩ c b d
    have := hC c b d
    simp only [C, hgrad] at this
    linarith

/-! ### α-V.1 (Z16) A_F = Levi-Civita スピン接続 -/

section Z16

open CFT.AlphaI_AW

/-- U⁻¹ = (m + iσ·p)/E -/
noncomputable def Uinv (m iE : ℂ) (p : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  iE • ((m • (1 : Matrix (Fin 2) (Fin 2) ℂ)) + Complex.I • sd p)

/-- ∂_iU(連鎖律:∂_i(1/E) = −p_i/E³) -/
noncomputable def dU (m iE : ℂ) (p : Fin 3 → ℂ) (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I * iE) • σ i + (-(p i) * iE ^ 3) • ((m • (1 : Matrix (Fin 2) (Fin 2) ℂ)) - Complex.I • sd p)

set_option maxHeartbeats 0 in
/-- e_i = U⁻¹∂_iU = i[σ·(p×e_i) − mσ_i]/E²(= A p (1/E²) (−m/E²) i) -/
theorem frame_eq (m iE : ℂ) (p : Fin 3 → ℂ)
    (hiE : (m ^ 2 + p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * iE ^ 2 = 1) (i : Fin 3) :
    Uinv m iE p * dU m iE p i = A p (iE ^ 2) (-m * iE ^ 2) i := by
  have hJ : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Uinv, dU, Fin.sum_univ_three, CFT.AlphaI_AW.sd, CFT.AlphaI_AW.A, CFT.AlphaI_AW.crossv, CFT.AlphaI_AW.ev, CFT.AlphaI_AW.σ, CFT.AlphaI_AW.σ1, CFT.AlphaI_AW.σ2, CFT.AlphaI_AW.σ3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.single_apply, Matrix.trace_fin_two] <;>
    all_goals (first | ring1 | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 + Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 + Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 + Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 + Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 + Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 + Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 - Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 - Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 - Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 - Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 - Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 1^2 - Complex.I*iE^2*p 1 + iE^4*p 0^3 + iE^4*p 0*p 1^2 + iE^4*p 0*p 2^2 - iE^2*p 0) * hJ + (-iE^2*p 0) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 - Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 - Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 - Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 - Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 - Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 - Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (1:ℂ) * ((Complex.I*iE^2*p 2) * hJ + (0) * hiE)) | (linear_combination (-1:ℂ) * ((Complex.I*iE^2*p 2) * hJ + (0) * hiE)) | (linear_combination (2:ℂ) * ((Complex.I*iE^2*p 2) * hJ + (0) * hiE)) | (linear_combination (-2:ℂ) * ((Complex.I*iE^2*p 2) * hJ + (0) * hiE)) | (linear_combination (1/2:ℂ) * ((Complex.I*iE^2*p 2) * hJ + (0) * hiE)) | (linear_combination (-1/2:ℂ) * ((Complex.I*iE^2*p 2) * hJ + (0) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 + Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 + Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 + Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 + Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 + Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*p 1^3 + Complex.I^2*iE^2*p 1 + Complex.I*iE^2*p 0 + iE^4*p 0^2*p 1 + iE^4*p 1^3 + iE^4*p 1*p 2^2 - iE^2*p 1) * hJ + (-iE^2*p 1) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*p 1^2*p 2 + iE^4*p 0^2*p 2 + iE^4*p 1^2*p 2 + iE^4*p 2^3 - iE^2*p 2) * hJ + (-iE^2*p 2) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*p 1^2*p 2 + iE^4*p 0^2*p 2 + iE^4*p 1^2*p 2 + iE^4*p 2^3 - iE^2*p 2) * hJ + (-iE^2*p 2) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*p 1^2*p 2 + iE^4*p 0^2*p 2 + iE^4*p 1^2*p 2 + iE^4*p 2^3 - iE^2*p 2) * hJ + (-iE^2*p 2) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*p 1^2*p 2 + iE^4*p 0^2*p 2 + iE^4*p 1^2*p 2 + iE^4*p 2^3 - iE^2*p 2) * hJ + (-iE^2*p 2) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*p 1^2*p 2 + iE^4*p 0^2*p 2 + iE^4*p 1^2*p 2 + iE^4*p 2^3 - iE^2*p 2) * hJ + (-iE^2*p 2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*p 1^2*p 2 + iE^4*p 0^2*p 2 + iE^4*p 1^2*p 2 + iE^4*p 2^3 - iE^2*p 2) * hJ + (-iE^2*p 2) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I*iE^2*p 1) * hJ + (0) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I*iE^2*p 1) * hJ + (0) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I*iE^2*p 1) * hJ + (0) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I*iE^2*p 1) * hJ + (0) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I*iE^2*p 1) * hJ + (0) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I*iE^2*p 1) * hJ + (0) * hiE)))

/-- 捩れゼロ(Maurer–Cartan):e = A(a = 1/E², b = −m/E²)の曲率は 0。
    a′ = d(1/(m²+s))/ds = −1/E⁴、b′ = m/E⁴ -/
theorem maurer_cartan (m iE : ℂ) (p : Fin 3 → ℂ)
    (hiE : (m ^ 2 + p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * iE ^ 2 = 1) :
    F p (iE ^ 2) (-(iE ^ 4)) (-m * iE ^ 2) (m * iE ^ 4) 1 2 = 0 ∧
    F p (iE ^ 2) (-(iE ^ 4)) (-m * iE ^ 2) (m * iE ^ 4) 2 0 = 0 ∧
    F p (iE ^ 2) (-(iE ^ 4)) (-m * iE ^ 2) (m * iE ^ 4) 0 1 = 0 := by
  obtain ⟨h1, h2, h3⟩ := curv_formula p (iE ^ 2) (-(iE ^ 4)) (-m * iE ^ 2) (m * iE ^ 4)
  have hα : 2 * (iE ^ 2 + -(iE ^ 4) * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) - (-m * iE ^ 2) ^ 2) = 0 := by
    linear_combination (-2 * iE ^ 2) * hiE
  have hβ : -2 * ((iE ^ 2) ^ 2 + -(iE ^ 4)) = 0 := by ring
  have hγ : 2 * (iE ^ 2 * (-m * iE ^ 2) + m * iE ^ 4) = 0 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; simp only [hα, hβ, hγ]; simp
  · rw [h2]; simp only [hα, hβ, hγ]; simp
  · rw [h3]; simp only [hα, hβ, hγ]; simp

/-- 1/(m² + s) の s 微分は −1/(m² + s)²(a′ = −1/E⁴ の根拠) -/
theorem inv_deriv (m s : ℝ) (h : m ^ 2 + s ≠ 0) :
    HasDerivAt (fun s => 1 / (m ^ 2 + s)) (-(1 / (m ^ 2 + s)) ^ 2) s := by
  have h1 := ((hasDerivAt_id s).const_add (m ^ 2)).inv h
  have hf : (fun s => 1 / (m ^ 2 + s)) = fun s => (m ^ 2 + id s)⁻¹ := by funext s; simp
  rw [hf]
  convert h1 using 1
  field_simp

set_option maxHeartbeats 0 in
/-- 枠の計量:−½tr(e_i e_j) = δ_ij/E² − p_i p_j/E⁴ -/
theorem frame_metric (m iE : ℂ) (p : Fin 3 → ℂ)
    (hiE : (m ^ 2 + p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * iE ^ 2 = 1) (i j : Fin 3) :
    -(1 / 2) * trace (A p (iE ^ 2) (-m * iE ^ 2) i * A p (iE ^ 2) (-m * iE ^ 2) j)
      = (if i = j then iE ^ 2 else 0) - p i * p j * iE ^ 4 := by
  have hJ : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, CFT.AlphaI_AW.sd, CFT.AlphaI_AW.A, CFT.AlphaI_AW.crossv, CFT.AlphaI_AW.ev, CFT.AlphaI_AW.σ, CFT.AlphaI_AW.σ1, CFT.AlphaI_AW.σ2, CFT.AlphaI_AW.σ3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.single_apply, Matrix.trace_fin_two] <;>
    all_goals (first | ring1 | (linear_combination (1:ℂ) * ((Complex.I^2*iE^4*p 2^2 - iE^4*m^2 - iE^4*p 1^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (-1:ℂ) * ((Complex.I^2*iE^4*p 2^2 - iE^4*m^2 - iE^4*p 1^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (2:ℂ) * ((Complex.I^2*iE^4*p 2^2 - iE^4*m^2 - iE^4*p 1^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (-2:ℂ) * ((Complex.I^2*iE^4*p 2^2 - iE^4*m^2 - iE^4*p 1^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (1/2:ℂ) * ((Complex.I^2*iE^4*p 2^2 - iE^4*m^2 - iE^4*p 1^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (-1/2:ℂ) * ((Complex.I^2*iE^4*p 2^2 - iE^4*m^2 - iE^4*p 1^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*m*p 2 + iE^4*p 0*p 1) * hJ + (0) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*m*p 2 + iE^4*p 0*p 1) * hJ + (0) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*m*p 2 + iE^4*p 0*p 1) * hJ + (0) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*m*p 2 + iE^4*p 0*p 1) * hJ + (0) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*m*p 2 + iE^4*p 0*p 1) * hJ + (0) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*m*p 2 + iE^4*p 0*p 1) * hJ + (0) * hiE)) | (linear_combination (1:ℂ) * ((-Complex.I^2*iE^4*p 0*p 2 + iE^4*p 0*p 2) * hJ + (0) * hiE)) | (linear_combination (-1:ℂ) * ((-Complex.I^2*iE^4*p 0*p 2 + iE^4*p 0*p 2) * hJ + (0) * hiE)) | (linear_combination (2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 2 + iE^4*p 0*p 2) * hJ + (0) * hiE)) | (linear_combination (-2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 2 + iE^4*p 0*p 2) * hJ + (0) * hiE)) | (linear_combination (1/2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 2 + iE^4*p 0*p 2) * hJ + (0) * hiE)) | (linear_combination (-1/2:ℂ) * ((-Complex.I^2*iE^4*p 0*p 2 + iE^4*p 0*p 2) * hJ + (0) * hiE)) | (linear_combination (1:ℂ) * ((Complex.I^2*iE^4*m^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (-1:ℂ) * ((Complex.I^2*iE^4*m^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (2:ℂ) * ((Complex.I^2*iE^4*m^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (-2:ℂ) * ((Complex.I^2*iE^4*m^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (1/2:ℂ) * ((Complex.I^2*iE^4*m^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (-1/2:ℂ) * ((Complex.I^2*iE^4*m^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 2^2) * hJ + (iE^2) * hiE)) | (linear_combination (1:ℂ) * ((Complex.I^2*iE^4*m*p 0 + iE^4*p 1*p 2) * hJ + (0) * hiE)) | (linear_combination (-1:ℂ) * ((Complex.I^2*iE^4*m*p 0 + iE^4*p 1*p 2) * hJ + (0) * hiE)) | (linear_combination (2:ℂ) * ((Complex.I^2*iE^4*m*p 0 + iE^4*p 1*p 2) * hJ + (0) * hiE)) | (linear_combination (-2:ℂ) * ((Complex.I^2*iE^4*m*p 0 + iE^4*p 1*p 2) * hJ + (0) * hiE)) | (linear_combination (1/2:ℂ) * ((Complex.I^2*iE^4*m*p 0 + iE^4*p 1*p 2) * hJ + (0) * hiE)) | (linear_combination (-1/2:ℂ) * ((Complex.I^2*iE^4*m*p 0 + iE^4*p 1*p 2) * hJ + (0) * hiE)) | (linear_combination (1:ℂ) * ((Complex.I^2*iE^4*p 0^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 1^2) * hJ + (iE^2) * hiE)) | (linear_combination (-1:ℂ) * ((Complex.I^2*iE^4*p 0^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 1^2) * hJ + (iE^2) * hiE)) | (linear_combination (2:ℂ) * ((Complex.I^2*iE^4*p 0^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 1^2) * hJ + (iE^2) * hiE)) | (linear_combination (-2:ℂ) * ((Complex.I^2*iE^4*p 0^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 1^2) * hJ + (iE^2) * hiE)) | (linear_combination (1/2:ℂ) * ((Complex.I^2*iE^4*p 0^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 1^2) * hJ + (iE^2) * hiE)) | (linear_combination (-1/2:ℂ) * ((Complex.I^2*iE^4*p 0^2 - iE^4*m^2 - iE^4*p 0^2 - iE^4*p 1^2) * hJ + (iE^2) * hiE)))

end Z16

/-! ### α-I.4 / α-I.5 量子計量と半径 1/√2 -/

section QMetric

open CFT.AlphaV

noncomputable def αv : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ := ![αx, αy, αz]

noncomputable def Hm (m : ℂ) (p : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  m • β + p 0 • αx + p 1 • αy + p 2 • αz

/-- ∂_iP = ½(α_i/E − H p_i/E³)(P = ½(1 + H/E)、連鎖律) -/
noncomputable def dP (m iE : ℂ) (p : Fin 3 → ℂ) (i : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • (iE • αv i - (p i * iE ^ 3) • Hm m p)

set_option maxHeartbeats 0 in
/-- 量子計量 ½tr(∂_iP ∂_jP) = ½(δ_ij/E² − p_i p_j/E⁴) -/
theorem quantum_metric (m iE : ℂ) (p : Fin 3 → ℂ)
    (hiE : (m ^ 2 + p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * iE ^ 2 = 1) (i j : Fin 3) :
    (1 / 2) * trace (dP m iE p i * dP m iE p j)
      = (1 / 2) * ((if i = j then iE ^ 2 else 0) - p i * p j * iE ^ 4) := by
  have hJ : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [dP, Hm, αv, Fin.sum_univ_four, Fin.sum_univ_three, CFT.AlphaV.β, CFT.AlphaV.αx, CFT.AlphaV.αy, CFT.AlphaV.αz, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.trace, Matrix.diag] <;>
    all_goals (first | ring1 | (linear_combination (1:ℂ) * ((-iE^6*p 0^2*p 1^2/2) * hJ + (iE^4*p 0^2/2) * hiE)) | (linear_combination (-1:ℂ) * ((-iE^6*p 0^2*p 1^2/2) * hJ + (iE^4*p 0^2/2) * hiE)) | (linear_combination (2:ℂ) * ((-iE^6*p 0^2*p 1^2/2) * hJ + (iE^4*p 0^2/2) * hiE)) | (linear_combination (-2:ℂ) * ((-iE^6*p 0^2*p 1^2/2) * hJ + (iE^4*p 0^2/2) * hiE)) | (linear_combination (1/2:ℂ) * ((-iE^6*p 0^2*p 1^2/2) * hJ + (iE^4*p 0^2/2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-iE^6*p 0^2*p 1^2/2) * hJ + (iE^4*p 0^2/2) * hiE)) | (linear_combination (1:ℂ) * ((-iE^6*p 0*p 1^3/2 + iE^4*p 0*p 1/2) * hJ + (iE^4*p 0*p 1/2) * hiE)) | (linear_combination (-1:ℂ) * ((-iE^6*p 0*p 1^3/2 + iE^4*p 0*p 1/2) * hJ + (iE^4*p 0*p 1/2) * hiE)) | (linear_combination (2:ℂ) * ((-iE^6*p 0*p 1^3/2 + iE^4*p 0*p 1/2) * hJ + (iE^4*p 0*p 1/2) * hiE)) | (linear_combination (-2:ℂ) * ((-iE^6*p 0*p 1^3/2 + iE^4*p 0*p 1/2) * hJ + (iE^4*p 0*p 1/2) * hiE)) | (linear_combination (1/2:ℂ) * ((-iE^6*p 0*p 1^3/2 + iE^4*p 0*p 1/2) * hJ + (iE^4*p 0*p 1/2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-iE^6*p 0*p 1^3/2 + iE^4*p 0*p 1/2) * hJ + (iE^4*p 0*p 1/2) * hiE)) | (linear_combination (1:ℂ) * ((-iE^6*p 0*p 1^2*p 2/2) * hJ + (iE^4*p 0*p 2/2) * hiE)) | (linear_combination (-1:ℂ) * ((-iE^6*p 0*p 1^2*p 2/2) * hJ + (iE^4*p 0*p 2/2) * hiE)) | (linear_combination (2:ℂ) * ((-iE^6*p 0*p 1^2*p 2/2) * hJ + (iE^4*p 0*p 2/2) * hiE)) | (linear_combination (-2:ℂ) * ((-iE^6*p 0*p 1^2*p 2/2) * hJ + (iE^4*p 0*p 2/2) * hiE)) | (linear_combination (1/2:ℂ) * ((-iE^6*p 0*p 1^2*p 2/2) * hJ + (iE^4*p 0*p 2/2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-iE^6*p 0*p 1^2*p 2/2) * hJ + (iE^4*p 0*p 2/2) * hiE)) | (linear_combination (1:ℂ) * ((-iE^6*p 1^4/2 + iE^4*p 1^2 - iE^2/2) * hJ + (iE^4*p 1^2/2) * hiE)) | (linear_combination (-1:ℂ) * ((-iE^6*p 1^4/2 + iE^4*p 1^2 - iE^2/2) * hJ + (iE^4*p 1^2/2) * hiE)) | (linear_combination (2:ℂ) * ((-iE^6*p 1^4/2 + iE^4*p 1^2 - iE^2/2) * hJ + (iE^4*p 1^2/2) * hiE)) | (linear_combination (-2:ℂ) * ((-iE^6*p 1^4/2 + iE^4*p 1^2 - iE^2/2) * hJ + (iE^4*p 1^2/2) * hiE)) | (linear_combination (1/2:ℂ) * ((-iE^6*p 1^4/2 + iE^4*p 1^2 - iE^2/2) * hJ + (iE^4*p 1^2/2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-iE^6*p 1^4/2 + iE^4*p 1^2 - iE^2/2) * hJ + (iE^4*p 1^2/2) * hiE)) | (linear_combination (1:ℂ) * ((-iE^6*p 1^3*p 2/2 + iE^4*p 1*p 2/2) * hJ + (iE^4*p 1*p 2/2) * hiE)) | (linear_combination (-1:ℂ) * ((-iE^6*p 1^3*p 2/2 + iE^4*p 1*p 2/2) * hJ + (iE^4*p 1*p 2/2) * hiE)) | (linear_combination (2:ℂ) * ((-iE^6*p 1^3*p 2/2 + iE^4*p 1*p 2/2) * hJ + (iE^4*p 1*p 2/2) * hiE)) | (linear_combination (-2:ℂ) * ((-iE^6*p 1^3*p 2/2 + iE^4*p 1*p 2/2) * hJ + (iE^4*p 1*p 2/2) * hiE)) | (linear_combination (1/2:ℂ) * ((-iE^6*p 1^3*p 2/2 + iE^4*p 1*p 2/2) * hJ + (iE^4*p 1*p 2/2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-iE^6*p 1^3*p 2/2 + iE^4*p 1*p 2/2) * hJ + (iE^4*p 1*p 2/2) * hiE)) | (linear_combination (1:ℂ) * ((-iE^6*p 1^2*p 2^2/2) * hJ + (iE^4*p 2^2/2) * hiE)) | (linear_combination (-1:ℂ) * ((-iE^6*p 1^2*p 2^2/2) * hJ + (iE^4*p 2^2/2) * hiE)) | (linear_combination (2:ℂ) * ((-iE^6*p 1^2*p 2^2/2) * hJ + (iE^4*p 2^2/2) * hiE)) | (linear_combination (-2:ℂ) * ((-iE^6*p 1^2*p 2^2/2) * hJ + (iE^4*p 2^2/2) * hiE)) | (linear_combination (1/2:ℂ) * ((-iE^6*p 1^2*p 2^2/2) * hJ + (iE^4*p 2^2/2) * hiE)) | (linear_combination (-1/2:ℂ) * ((-iE^6*p 1^2*p 2^2/2) * hJ + (iE^4*p 2^2/2) * hiE)))

/-- Q = (m, p)/E の偏微分(連鎖律の結果) -/
noncomputable def dQ (m iE : ℂ) (p : Fin 3 → ℂ) (i : Fin 3) : Fin 4 → ℂ :=
  ![-m * p i * iE ^ 3, (if i = 0 then iE else 0) - p 0 * p i * iE ^ 3,
    (if i = 1 then iE else 0) - p 1 * p i * iE ^ 3, (if i = 2 then iE else 0) - p 2 * p i * iE ^ 3]

set_option maxHeartbeats 0 in
/-- 引き戻し計量 Σ_μ ∂_iQ_μ ∂_jQ_μ = δ_ij/E² − p_i p_j/E⁴ -/
theorem pullback_metric (m iE : ℂ) (p : Fin 3 → ℂ)
    (hiE : (m ^ 2 + p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * iE ^ 2 = 1) (i j : Fin 3) :
    ∑ μ, dQ m iE p i μ * dQ m iE p j μ = (if i = j then iE ^ 2 else 0) - p i * p j * iE ^ 4 := by
  have hJ : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [dQ, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] <;>
    all_goals (first | ring1 | (linear_combination (1:ℂ) * ((0) * hJ + (iE^4*p 0^2) * hiE)) | (linear_combination (-1:ℂ) * ((0) * hJ + (iE^4*p 0^2) * hiE)) | (linear_combination (2:ℂ) * ((0) * hJ + (iE^4*p 0^2) * hiE)) | (linear_combination (-2:ℂ) * ((0) * hJ + (iE^4*p 0^2) * hiE)) | (linear_combination (1/2:ℂ) * ((0) * hJ + (iE^4*p 0^2) * hiE)) | (linear_combination (-1/2:ℂ) * ((0) * hJ + (iE^4*p 0^2) * hiE)) | (linear_combination (1:ℂ) * ((0) * hJ + (iE^4*p 0*p 1) * hiE)) | (linear_combination (-1:ℂ) * ((0) * hJ + (iE^4*p 0*p 1) * hiE)) | (linear_combination (2:ℂ) * ((0) * hJ + (iE^4*p 0*p 1) * hiE)) | (linear_combination (-2:ℂ) * ((0) * hJ + (iE^4*p 0*p 1) * hiE)) | (linear_combination (1/2:ℂ) * ((0) * hJ + (iE^4*p 0*p 1) * hiE)) | (linear_combination (-1/2:ℂ) * ((0) * hJ + (iE^4*p 0*p 1) * hiE)) | (linear_combination (1:ℂ) * ((0) * hJ + (iE^4*p 0*p 2) * hiE)) | (linear_combination (-1:ℂ) * ((0) * hJ + (iE^4*p 0*p 2) * hiE)) | (linear_combination (2:ℂ) * ((0) * hJ + (iE^4*p 0*p 2) * hiE)) | (linear_combination (-2:ℂ) * ((0) * hJ + (iE^4*p 0*p 2) * hiE)) | (linear_combination (1/2:ℂ) * ((0) * hJ + (iE^4*p 0*p 2) * hiE)) | (linear_combination (-1/2:ℂ) * ((0) * hJ + (iE^4*p 0*p 2) * hiE)) | (linear_combination (1:ℂ) * ((0) * hJ + (iE^4*p 1^2) * hiE)) | (linear_combination (-1:ℂ) * ((0) * hJ + (iE^4*p 1^2) * hiE)) | (linear_combination (2:ℂ) * ((0) * hJ + (iE^4*p 1^2) * hiE)) | (linear_combination (-2:ℂ) * ((0) * hJ + (iE^4*p 1^2) * hiE)) | (linear_combination (1/2:ℂ) * ((0) * hJ + (iE^4*p 1^2) * hiE)) | (linear_combination (-1/2:ℂ) * ((0) * hJ + (iE^4*p 1^2) * hiE)) | (linear_combination (1:ℂ) * ((0) * hJ + (iE^4*p 1*p 2) * hiE)) | (linear_combination (-1:ℂ) * ((0) * hJ + (iE^4*p 1*p 2) * hiE)) | (linear_combination (2:ℂ) * ((0) * hJ + (iE^4*p 1*p 2) * hiE)) | (linear_combination (-2:ℂ) * ((0) * hJ + (iE^4*p 1*p 2) * hiE)) | (linear_combination (1/2:ℂ) * ((0) * hJ + (iE^4*p 1*p 2) * hiE)) | (linear_combination (-1/2:ℂ) * ((0) * hJ + (iE^4*p 1*p 2) * hiE)) | (linear_combination (1:ℂ) * ((0) * hJ + (iE^4*p 2^2) * hiE)) | (linear_combination (-1:ℂ) * ((0) * hJ + (iE^4*p 2^2) * hiE)) | (linear_combination (2:ℂ) * ((0) * hJ + (iE^4*p 2^2) * hiE)) | (linear_combination (-2:ℂ) * ((0) * hJ + (iE^4*p 2^2) * hiE)) | (linear_combination (1/2:ℂ) * ((0) * hJ + (iE^4*p 2^2) * hiE)) | (linear_combination (-1/2:ℂ) * ((0) * hJ + (iE^4*p 2^2) * hiE)))

end QMetric

/-- 連鎖律の確認:∂/∂p₁ (m/√(m² + p₁² + c)) = −m p₁/E³ -/
theorem dQ0_deriv (m c x : ℝ) (h : 0 < m ^ 2 + x ^ 2 + c) :
    HasDerivAt (fun x => m / Real.sqrt (m ^ 2 + x ^ 2 + c))
      (-(m * x) / Real.sqrt (m ^ 2 + x ^ 2 + c) ^ 3) x := by
  have hs0 : Real.sqrt (m ^ 2 + x ^ 2 + c) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  have hin : HasDerivAt (fun x => m ^ 2 + x ^ 2 + c) (2 * x) x := by
    simpa using (((hasDerivAt_id x).pow 2).const_add (m ^ 2)).add_const c
  have hs := (Real.hasDerivAt_sqrt h.ne').comp x hin
  have hq := (hasDerivAt_const x m).div hs hs0
  convert hq using 1
  simp only [Function.comp_def]
  have h2 : Real.sqrt (m ^ 2 + x ^ 2 + c) ^ 2 = m ^ 2 + x ^ 2 + c := Real.sq_sqrt h.le
  field_simp
  rw [show Real.sqrt (m ^ 2 + x ^ 2 + c) ^ 3 = Real.sqrt (m ^ 2 + x ^ 2 + c) ^ 2 * Real.sqrt (m ^ 2 + x ^ 2 + c) by ring, h2]
  ring

end CFT.AlphaCompleteB
