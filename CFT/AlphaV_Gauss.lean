/-
  α-V.4(Z19)の作り直し:Gauss 写像から sin²χ = 2Gm/r を導く(監査:旧版は cos χ = √(1 − 2m/r) を前提にしていた)

  設定(台帳の閉鎖条件どおり、条件を明示する):
    * 時間対称(K_ij = 0)で球対称な空間の切り口 ds² + r(s)² dΩ²、|r′| ≤ 1(R⁴ に埋め込める)
    * 埋め込み:R⁴ = R³ × R の回転面 (r(s) n̂, z(s))、r′² + z′² = 1(s は弧長)
    * Gauss 写像:各点にその単位法線 N ∈ S³ を対応させる。経線の面で N = (−z′ n̂, r′)
    * χ:N の z 軸(北極)からの角、cos χ = N の z 成分
  結果:
    * gauss_normal:N は単位で、接ベクトル (r′, z′) と直交
    * gauss_angle:cos χ = r′、sin²χ = 1 − r′²
    * gauss_mass:時間対称な切り口の Misner–Sharp 質量 2Gm = r(1 − r′²)(AlphaIII の M₂)を使うと
      sin²χ = 2Gm/r(台帳 U17 の式)
    * gauss_schwarzschild:Schwarzschild の切り口 r′ = √(1 − 2m/r) では sin²χ = 2m/r
    * gauss_marginal:sin²χ = 1(χ = π/2、S³ の赤道)⇔ r′ = 0 ⇔ 2Gm = r(周縁的捕捉面、地平面)
  ダンベルでは:
    * gauss_cap:帽子 r = ℓ sin(s/ℓ) では cos χ = cos(s/ℓ):Gauss 写像は χ = s/ℓ(半球の恒等写像)
    * gauss_neck:首(r′ = 0)全体が赤道 χ = π/2 に写る、接合の球面も赤道
  量子球面 Q との対応(Q の極角は cos χ_Q = m/E、赤道は質量ゼロ)は、同じ S³ の極角という形の対応で、
  物理として同じであることは主張しない。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

namespace CFT.Gauss

theorem gauss_normal (r1 z1 : ℝ) (h : r1 ^ 2 + z1 ^ 2 = 1) :
    (-z1) ^ 2 + r1 ^ 2 = 1 ∧ r1 * (-z1) + z1 * r1 = 0 := by
  constructor <;> nlinarith [h]

/-- cos χ = N_z = r′、sin²χ = 1 − cos²χ = 1 − r′² -/
theorem gauss_angle (r1 z1 : ℝ) (h : r1 ^ 2 + z1 ^ 2 = 1) :
    (-z1) ^ 2 = 1 - r1 ^ 2 := by nlinarith [h]

/-- sin²χ = 2Gm/r(2Gm = r(1 − r′²)) -/
theorem gauss_mass (r r1 : ℝ) (hr : r ≠ 0) : 1 - r1 ^ 2 = (r * (1 - r1 ^ 2)) / r := by
  field_simp

theorem gauss_schwarzschild (m r : ℝ) (h : 2 * m / r ≤ 1) :
    1 - (√(1 - 2 * m / r)) ^ 2 = 2 * m / r := by
  rw [Real.sq_sqrt (by linarith)]; ring

/-- 赤道 ⇔ r′ = 0 ⇔ 2Gm = r -/
theorem gauss_marginal (r r1 : ℝ) (hr : r ≠ 0) :
    (1 - r1 ^ 2 = 1 ↔ r1 = 0) ∧ (r * (1 - r1 ^ 2) = r ↔ r1 = 0) := by
  constructor
  · constructor <;> intro h
    · nlinarith [sq_nonneg r1]
    · rw [h]; ring
  · constructor <;> intro h
    · have : r * r1 ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hr
      · exact pow_eq_zero_iff (by norm_num) |>.mp h'
    · rw [h]; ring

/-- 帽子:cos χ = r′ = cos(s/ℓ) なので χ = s/ℓ(0 ≤ s/ℓ ≤ π/2 で) -/
theorem gauss_cap (l s : ℝ) (hl : 0 < l) (h0 : 0 ≤ s / l) (h1 : s / l ≤ π / 2) :
    arccos (cos (s / l)) = s / l ∧ 1 - cos (s / l) ^ 2 = sin (s / l) ^ 2 := by
  refine ⟨arccos_cos h0 (by linarith [pi_pos]), ?_⟩
  rw [← sin_sq_add_cos_sq (s / l)]; ring

/-- 首:r′ = 0 で χ = π/2(赤道)、接合 s = πℓ/2 でも赤道 -/
theorem gauss_neck (l : ℝ) (hl : l ≠ 0) :
    arccos 0 = π / 2 ∧ cos ((π * l / 2) / l) = 0 := by
  refine ⟨arccos_zero, ?_⟩
  rw [show π * l / 2 / l = π / 2 by field_simp; ring]; exact cos_pi_div_two

end CFT.Gauss
