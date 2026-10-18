/-
  α-VIII.5(Z38、Z42)の幾何の部分:S³ = SU(2)(= 量子球面 Q)の平行化の捩れと流束の量子化

  A. 構造定数は四元数の交換子(quat_bracket):[i, j] = 2k、[j, k] = 2i、[k, i] = 2j。
     半径 R の S³ = SU(2) の左不変な正規直交枠では [e_a, e_b] = (2/R) ε_abc e_c。
     平坦な(Cartan–Schouten の)接続の捩れは H_abc = (2/R) ε_abc。
  B. 1 ループの共形不変性の条件 Ric_ab = ¼ Σ H_acd H_bcd が、恒等式として成り立つ:
     * eps_contract:Σ_cd ε_acd ε_bcd = 2δ_ab
     * s3_ricci:S³(R) の断面曲率はすべて 1/R²(AlphaI_H3 の sectional を f = R sin(s/R) で)、Ric = 2/R²
     * parallelizing_torsion:¼ Σ_cd H_acd H_bcd = (2/R²)δ_ab = Ric_ab
  C. 流束:
     * s3_volume:Vol(S³(R)) = ∫₀^{πR} 4π(R sin(s/R))² ds = 2π²R³
     * flux:∫_{S³} H = (2/R)·2π²R³ = 4π²R²
     * level:Wess–Zumino 項が定まる条件 ∫H/(4π²α′) = k ∈ ℤ(外部:規格化は弦の世界面の作用、Witten 1984)
       から R² = kα′。R = ℓ*、α′ = 4ℓ*² なら k = 1/4(AlphaVIII_Z38 の one_quarter_not_integer)
  外部に残るもの:H の規格化に α′ が入ること(世界面の作用)と G_N = c α_GUT α′(次元縮約)。
-/
import CFT.AlphaI_H3
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Algebra.Quaternion

open Real

namespace CFT.WZW

/-! ### A. 四元数の交換子 -/

theorem quat_bracket :
    let i : Quaternion ℝ := ⟨0, 1, 0, 0⟩
    let j : Quaternion ℝ := ⟨0, 0, 1, 0⟩
    let k : Quaternion ℝ := ⟨0, 0, 0, 1⟩
    i * j - j * i = (2 : ℝ) • k ∧ j * k - k * j = (2 : ℝ) • i ∧ k * i - i * k = (2 : ℝ) • j := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Quaternion.ext <;> simp <;> norm_num

/-! ### B. 平行化の捩れ -/

noncomputable def eps (a b c : Fin 3) : ℝ :=
  ((b.val : ℝ) - a.val) * ((c.val : ℝ) - a.val) * ((c.val : ℝ) - b.val) / 2

theorem eps_contract (a b : Fin 3) :
    ∑ c, ∑ d, eps a c d * eps b c d = 2 * (if a = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> simp [eps, Fin.sum_univ_three] <;> norm_num

/-- S³(R):f = R sin(s/R) の断面曲率はすべて 1/R² -/
theorem s3_ricci (R x : ℝ) (hR : R ≠ 0) (hx : sin x ≠ 0) :
    -((-(sin x) / R) / (R * sin x)) = 1 / R ^ 2 ∧ (1 - cos x ^ 2) / (R * sin x) ^ 2 = 1 / R ^ 2 ∧
    1 / R ^ 2 + 1 / R ^ 2 = 2 / R ^ 2 :=
  ⟨(CFT.H3.cap_curvature R x hR hx).1, (CFT.H3.cap_curvature R x hR hx).2, by ring⟩

theorem parallelizing_torsion (R : ℝ) (hR : R ≠ 0) (a b : Fin 3) :
    (1 / 4) * ∑ c, ∑ d, (2 / R * eps a c d) * (2 / R * eps b c d)
      = 2 / R ^ 2 * (if a = b then 1 else 0) := by
  have h : ∑ c, ∑ d, (2 / R * eps a c d) * (2 / R * eps b c d)
      = (4 / R ^ 2) * ∑ c, ∑ d, eps a c d * eps b c d := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun d _ => ?_)
    field_simp; ring
  rw [h, eps_contract]; field_simp; ring

/-! ### C. 流束と準位 -/

theorem s3_volume (R : ℝ) (hR : 0 < R) :
    ∫ s in (0 : ℝ)..(π * R), 4 * π * (R * sin (s / R)) ^ 2 = 2 * π ^ 2 * R ^ 3 := by
  have hR' := hR.ne'
  have h : ∀ s ∈ Set.uIcc (0 : ℝ) (π * R), HasDerivAt
      (fun t => 4 * π * R ^ 2 * (t / 2 - R * sin (2 * (t / R)) / 4)) (4 * π * (R * sin (s / R)) ^ 2) s := by
    intro s _
    have := ((((hasDerivAt_id s).div_const R).const_mul 2).sin.const_mul R |>.div_const 4
      |> (((hasDerivAt_id s).div_const 2).sub ·)).const_mul (4 * π * R ^ 2)
    convert this using 1
    simp only [id]
    rw [show cos (2 * (s / R)) = 1 - 2 * sin (s / R) ^ 2 by rw [cos_two_mul, cos_sq']; ring]
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
    apply Continuous.intervalIntegrable; fun_prop)]
  rw [show 2 * (π * R / R) = 2 * π by field_simp]
  simp [sin_two_pi]; ring

theorem flux (R : ℝ) (hR : R ≠ 0) : 2 / R * (2 * π ^ 2 * R ^ 3) = 4 * π ^ 2 * R ^ 2 := by
  field_simp; ring

/-- ∫H/(4π²α′) = k ⇔ R² = kα′ -/
theorem level (R α' k : ℝ) (hα : α' ≠ 0) :
    4 * π ^ 2 * R ^ 2 / (4 * π ^ 2 * α') = k ↔ R ^ 2 = k * α' := by
  have hπ : π ^ 2 ≠ 0 := pow_ne_zero 2 pi_ne_zero
  have h4 : 4 * π ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have : 4 * π ^ 2 * (R ^ 2 - k * α') = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h4
    · linarith
  · intro h; rw [h]; ring

end CFT.WZW
