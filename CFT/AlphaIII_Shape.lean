/-
  B(ダンベルの基礎):時空の切り口のダンベルの形(傾き・面積・体積・接合部の法線の意味)と、
  Penrose 型定理の仮定 hD(質量の恒等式)を拘束方程式から導くこと

  切り口 ds² + r(s)² dΩ²、帽子 r = ℓ sin(s/ℓ)(0 ≤ s ≤ πℓ/2)、首 r = ℓ。
  傾き:
    * cap_slope:r′ = cos(s/ℓ)。頂点 s = 0 で r′ = 1(円錐の特異点がない)、接合 s = πℓ/2 で r′ = 0
  面積・体積(2 次元の断面 (s, θ) と 3 次元の切り口):
    * band_cap:帽子の帯 [s₁, s₂] の面積 ∫ 2π ℓ sin(s/ℓ) ds = 2πℓ²(cos(s₁/ℓ) − cos(s₂/ℓ))
    * band_neck:首の帯の面積 2πℓ(s₂ − s₁)
    * cap_volume:3 次元の帽子(S³ の半球)の体積 ∫₀^{πℓ/2} 4π ℓ² sin²(s/ℓ) ds = π²ℓ³
    * gauss_bonnet_dumbbell:二つの帽子(各 2π)+ 首(曲率 0)= 4π = 2π χ(S²)、
      接合の円は測地線(測地曲率 r′/r = 0)
  接合部の意味(時間対称な切り口 K_ij = 0):
    * junction_mots:null 膨張 θ± = (2/r)(±r′ + r K_T) は接合で 0:接合の球面は周縁的捕捉面
    * junction_schwarzschild:2Gm_MS = r(1 − r′²) = r:接合の球面はちょうど自分の Schwarzschild 半径にある
    * junction_entropy:接合の球面の面積 4πℓ²、A/(4G) = πℓ²/G
    * normal_stress:法線方向の応力(動径の圧力)は、帽子側が放射の圧力 ρ_cap/3 = +1/(8πGℓ²)、
      首側が磁場の張力 −ρ_neck = −1/(8πGℓ²)、跳びは −1/(4πGℓ²)(israel_impossible の値と一致):
      接合部は「外へ押す圧力」が「引っぱる張力」に入れ替わる面
  拘束から質量の恒等式(AlphaIII.penrose_spherical の仮定 hD を外す):
    * ms_from_constraints:ハミルトン拘束 ³R + 4ab + 2b² = 2ρ(³R = 2(1 − r′² − 2rr″)/r²)と
      運動量拘束 2(r′/r)(a − b) − 2b′ = J(AlphaIII_Codazzi の codazzi_s)のもとで
      M = r(1 − r′² + r²b²) の微分は r²(ρ r′ − J r b)(ρ, J は 8πG をかけた密度)
    * penrose_from_constraints:hD を拘束方程式に置き換えた Penrose 型定理
-/
import CFT.AlphaIII
import Mathlib.Analysis.SpecialFunctions.Integrals

open Real Set

namespace CFT.Shape

theorem cap_slope (l s : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun t => l * sin (t / l)) (cos (s / l)) s := by
  have h := ((hasDerivAt_id s).div_const l).sin.const_mul l
  convert h using 1; field_simp

theorem cap_slope_ends (l : ℝ) (hl : l ≠ 0) : cos (0 / l) = 1 ∧ cos ((π * l / 2) / l) = 0 := by
  refine ⟨by simp, ?_⟩
  rw [show π * l / 2 / l = π / 2 by field_simp; ring]; exact cos_pi_div_two

theorem band_cap (l s1 s2 : ℝ) (hl : l ≠ 0) :
    ∫ s in s1..s2, 2 * π * (l * sin (s / l)) = 2 * π * l ^ 2 * (cos (s1 / l) - cos (s2 / l)) := by
  have h : ∀ s ∈ uIcc s1 s2, HasDerivAt (fun t => -(2 * π * l ^ 2) * cos (t / l)) (2 * π * (l * sin (s / l))) s := by
    intro s _
    have := (((hasDerivAt_id s).div_const l).cos).const_mul (-(2 * π * l ^ 2))
    convert this using 1; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
    apply Continuous.intervalIntegrable; fun_prop)]
  ring

theorem band_neck (l s1 s2 : ℝ) : ∫ _s in s1..s2, 2 * π * l = 2 * π * l * (s2 - s1) := by
  simp; ring

theorem cap_volume (l : ℝ) (hl : 0 < l) :
    ∫ s in (0 : ℝ)..(π * l / 2), 4 * π * (l * sin (s / l)) ^ 2 = π ^ 2 * l ^ 3 := by
  have hl' := hl.ne'
  have h : ∀ s ∈ uIcc (0 : ℝ) (π * l / 2), HasDerivAt
      (fun t => 4 * π * l ^ 2 * (t / 2 - l * sin (2 * (t / l)) / 4)) (4 * π * (l * sin (s / l)) ^ 2) s := by
    intro s _
    have := ((((hasDerivAt_id s).div_const l).const_mul 2).sin.const_mul l |>.div_const 4
      |> (((hasDerivAt_id s).div_const 2).sub ·)).const_mul (4 * π * l ^ 2)
    convert this using 1
    simp only [id]
    rw [show cos (2 * (s / l)) = 1 - 2 * sin (s / l) ^ 2 by rw [cos_two_mul, cos_sq']; ring]
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
    apply Continuous.intervalIntegrable; fun_prop)]
  rw [show 2 * (π * l / 2 / l) = π by field_simp; ring]
  simp; ring

theorem gauss_bonnet_dumbbell (l : ℝ) (hl : 0 < l) :
    2 * (∫ s in (0 : ℝ)..(π * l / 2), (1 / l ^ 2) * (2 * π * (l * sin (s / l)))) + 0 = 4 * π ∧
    cos ((π * l / 2) / l) / sin ((π * l / 2) / l) = 0 := by
  have hl' := hl.ne'
  have e : π * l / 2 / l = π / 2 := by field_simp; ring
  constructor
  · rw [intervalIntegral.integral_const_mul, band_cap l 0 _ hl', e]; simp; field_simp; ring
  · rw [e]; simp

/-! ### 接合部の意味 -/

theorem junction_mots (r : ℝ) : (2 / r) * (0 + r * 0) = 0 ∧ (2 / r) * (-0 + r * 0) = 0 := by simp

theorem junction_schwarzschild (l : ℝ) : l * (1 - 0 ^ 2) = l := by ring

theorem junction_entropy (G l : ℝ) (hG : G ≠ 0) : 4 * π * l ^ 2 / (4 * G) = π * l ^ 2 / G := by
  field_simp; ring

/-- 動径の応力:帽子 +ρ_cap/3、首 −ρ_neck、跳び −1/(4πGℓ²) -/
theorem normal_stress (G l : ℝ) (hG : G ≠ 0) (hl : l ≠ 0) :
    (3 / (8 * π * G * l ^ 2)) / 3 = 1 / (8 * π * G * l ^ 2) ∧
    -(1 / (8 * π * G * l ^ 2)) - (3 / (8 * π * G * l ^ 2)) / 3 = -(1 / (4 * π * G * l ^ 2)) := by
  have hπ := pi_ne_zero
  constructor <;> field_simp <;> ring

/-! ### 拘束から質量の恒等式 -/

/-- 一点での代数:拘束のもとで M′ = r²(ρ r′ − J r b) -/
theorem ms_from_constraints (r rp rpp a b bp ρ J : ℝ) (hr : r ≠ 0)
    (hH : 2 * (1 - rp ^ 2 - 2 * r * rpp) / r ^ 2 + 4 * a * b + 2 * b ^ 2 = 2 * ρ)
    (hM : 2 * (rp / r) * (a - b) - 2 * bp = J) :
    rp * (1 - rp ^ 2 + r ^ 2 * b ^ 2) + r * (-(2 * rp * rpp) + (2 * r * rp * b ^ 2 + r ^ 2 * (2 * b * bp)))
      = r ^ 2 * (ρ * rp - J * (r * b)) := by
  have hrpp : rpp = (1 - rp ^ 2 + r ^ 2 * (2 * a * b + b ^ 2 - ρ)) / (2 * r) := by
    field_simp; field_simp at hH; linarith
  have hbp : bp = (rp / r) * (a - b) - J / 2 := by linarith
  rw [hrpp, hbp]; field_simp; ring

/-- Penrose 型定理(AlphaIII.penrose_spherical)の仮定 hD を拘束方程式に置き換えたもの -/
theorem penrose_from_constraints (r rp rpp a KT KTp ρ J M : ℝ → ℝ) (s0 s1 : ℝ)
    (hM : ∀ s, M s = r s * (1 - rp s ^ 2 + r s ^ 2 * KT s ^ 2))
    (hr0 : ∀ s ∈ Icc s0 s1, r s ≠ 0)
    (d1 : ∀ s ∈ Icc s0 s1, HasDerivAt r (rp s) s)
    (d2 : ∀ s ∈ Icc s0 s1, HasDerivAt rp (rpp s) s)
    (d3 : ∀ s ∈ Icc s0 s1, HasDerivAt KT (KTp s) s)
    (hH : ∀ s ∈ Icc s0 s1, 2 * (1 - rp s ^ 2 - 2 * r s * rpp s) / r s ^ 2
      + 4 * a s * KT s + 2 * KT s ^ 2 = 2 * ρ s)
    (hMom : ∀ s ∈ Icc s0 s1, 2 * (rp s / r s) * (a s - KT s) - 2 * KTp s = J s)
    (hunt : ∀ s ∈ Icc s0 s1, |r s * KT s| ≤ rp s)
    (hdec : ∀ s ∈ Icc s0 s1, |J s| ≤ ρ s)
    (hmarg : rp s0 ^ 2 = r s0 ^ 2 * KT s0 ^ 2) :
    ∀ s ∈ Icc s0 s1, r s0 ≤ M s := by
  have hMf : M = fun s => r s * (1 - rp s ^ 2 + r s ^ 2 * KT s ^ 2) := funext hM
  apply CFT.AlphaIII.penrose_spherical r rp KT ρ J M s0 s1 hM _ hunt hdec hmarg
  intro s hs
  have h := (d1 s hs).mul ((((d2 s hs).pow 2).const_sub 1).add (((d1 s hs).pow 2).mul ((d3 s hs).pow 2)))
  rw [hMf]
  convert h using 1
  rw [← ms_from_constraints (r s) (rp s) (rpp s) (a s) (KT s) (KTp s) (ρ s) (J s) (hr0 s hs)
    (hH s hs) (hMom s hs)]
  simp only [Nat.cast_ofNat]; ring

end CFT.Shape
