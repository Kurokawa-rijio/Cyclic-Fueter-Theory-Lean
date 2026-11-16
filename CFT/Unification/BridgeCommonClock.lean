/-
  橋 C:共通の時計(X.9、2026-11-05)

  仮説「帽子と首は共形時間 η = t/ℓ でそろう」は否定された(η は帽子の共形時間、t は首の固有時間で、
  種類の違う時間。cos の一致は座標の偶然)。正しい共通の時計は、初期の断面 Σ からのガウス正規時間。

  * 運動学:首は AdS₂ × S²。AdS₂ を埋め込み −X₀² − X₁² + X₂² = −ℓ² で表す。
      同期の座標 (t, z):X₀ = ℓ cos(t/ℓ)cosh(z/ℓ)、X₁ = ℓ sin(t/ℓ)、X₂ = ℓ cos(t/ℓ)sinh(z/ℓ)。
      静的な座標 (τ, x):X₀ = ℓ cosh(x/ℓ)cos τ、X₁ = ℓ cosh(x/ℓ)sin τ、X₂ = ℓ sinh(x/ℓ)。
      帽子は閉じた輻射 FRW、a = ℓ cos η。
  * 力学(作用は EYM、帽子と首の解は既に得たもの):
    (1) 首の同期の座標はガウス正規:g_tt = −1、g_tz = 0、g_zz = cos²(t/ℓ)(`neck_gaussian`)。
        帽子の共動の時間 τ_c = ℓ sin η もガウス正規(dτ_c = a dη、`cap_gaussian`)。
        したがって共通の時計は帽子の τ_c と首の t。
    (2) この時計で帽子の崩壊は ℓ、首の z = 一定の測地線の焦点は πℓ/2(cos(t/ℓ) = 0)。ℓ < πℓ/2 で、
        二つは別の出来事(`two_events`)。ℓ と πℓ/2 は時計の食い違いではない。
    (3) 同じ点の座標の関係:sin τ cosh(x/ℓ) = sin(t/ℓ)、sinh(x/ℓ) = cos(t/ℓ)sinh(z/ℓ)(`same_point`)、
        静的な位置 u(cosh(x/ℓ) sin u = 1)では sin τ = sin(t/ℓ) sin u(`static_clock`)。
    (4) 首の中心(z = 0)では x = 0 で、静的な時計 ℓτ はガウス時間 t そのもの(`neck_centre_clock`)。
        XI.1 (iv) の「時計をそろえる」は、首の中心の時計 = 共通のガウス時間として定理になる。
  * XI.1 への影響(数値、X.7):不安定なモードは接合のそば u ∼ e^{−L/ℓ} にいて、そこで測った倍率は
    L によらず約 0.4 回の e 倍(探索の数値)。XI.1 (iv) は「首の中心の時計で」と範囲を限る。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Pi.Bounds

namespace CFT.BridgeClock

open Real

/-- AdS₂ の同期の座標は双曲面の上 -/
theorem on_hyperboloid (l t z : ℝ) :
    -(l * cos (t / l) * cosh (z / l)) ^ 2 - (l * sin (t / l)) ^ 2 + (l * cos (t / l) * sinh (z / l)) ^ 2
      = -l ^ 2 := by
  have h1 := sin_sq_add_cos_sq (t / l)
  have h2 := cosh_sq_sub_sinh_sq (z / l)
  linear_combination (-(l ^ 2) * cos (t / l) ^ 2) * h2 + (-(l ^ 2)) * h1

/-- 同期の座標の t 微分(ℓ cos(t/ℓ)cosh(z/ℓ) → −sin(t/ℓ)cosh(z/ℓ) など) -/
theorem dt_embedding (l t z : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun s => l * cos (s / l) * cosh (z / l)) (-sin (t / l) * cosh (z / l)) t ∧
    HasDerivAt (fun s => l * sin (s / l)) (cos (t / l)) t ∧
    HasDerivAt (fun s => l * cos (s / l) * sinh (z / l)) (-sin (t / l) * sinh (z / l)) t := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) t := (hasDerivAt_id' t).div_const l
  refine ⟨?_, ?_, ?_⟩
  · have h := (((hasDerivAt_cos (t / l)).comp t hu).const_mul l).mul_const (cosh (z / l))
    convert h using 1; field_simp <;> ring
  · have h := ((hasDerivAt_sin (t / l)).comp t hu).const_mul l
    convert h using 1; field_simp <;> ring
  · have h := (((hasDerivAt_cos (t / l)).comp t hu).const_mul l).mul_const (sinh (z / l))
    convert h using 1; field_simp <;> ring

/-- 同期の座標の z 微分 -/
theorem dz_embedding (l t z : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun s => l * cos (t / l) * cosh (s / l)) (cos (t / l) * sinh (z / l)) z ∧
    HasDerivAt (fun s => l * cos (t / l) * sinh (s / l)) (cos (t / l) * cosh (z / l)) z := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) z := (hasDerivAt_id' z).div_const l
  refine ⟨?_, ?_⟩
  · have h := ((Real.hasDerivAt_cosh (z / l)).comp z hu).const_mul (l * cos (t / l))
    convert h using 1; field_simp <;> ring
  · have h := ((Real.hasDerivAt_sinh (z / l)).comp z hu).const_mul (l * cos (t / l))
    convert h using 1; field_simp <;> ring

/-- 【α-X.9】首の同期の座標はガウス正規:g_tt = −1、g_tz = 0、g_zz = cos²(t/ℓ)
(誘導計量 −dX₀² − dX₁² + dX₂² に上の微分を入れる) -/
theorem neck_gaussian (t z l : ℝ) :
    -(-sin (t / l) * cosh (z / l)) ^ 2 - cos (t / l) ^ 2 + (-sin (t / l) * sinh (z / l)) ^ 2 = -1 ∧
    -((-sin (t / l) * cosh (z / l)) * (cos (t / l) * sinh (z / l))) - cos (t / l) * 0
      + (-sin (t / l) * sinh (z / l)) * (cos (t / l) * cosh (z / l)) = 0 ∧
    -(cos (t / l) * sinh (z / l)) ^ 2 - 0 ^ 2 + (cos (t / l) * cosh (z / l)) ^ 2 = cos (t / l) ^ 2 := by
  have h1 := sin_sq_add_cos_sq (t / l)
  have h2 := cosh_sq_sub_sinh_sq (z / l)
  refine ⟨?_, by ring, ?_⟩
  · linear_combination (-(sin (t / l) ^ 2)) * h2 + (-1) * h1
  · linear_combination (cos (t / l) ^ 2) * h2

/-- 【α-X.9】帽子の共動の時間 τ_c = ℓ sin η:dτ_c/dη = a = ℓ cos η(ガウス正規)、崩壊 η = π/2 で τ_c = ℓ -/
theorem cap_gaussian (l η : ℝ) :
    HasDerivAt (fun e => l * sin e) (l * cos η) η ∧ l * sin (π / 2) = l := by
  exact ⟨(hasDerivAt_sin η).const_mul l, by rw [sin_pi_div_two, mul_one]⟩

/-- 【α-X.9】共通の時計で、帽子の崩壊 ℓ は首の焦点 πℓ/2(cos(t/ℓ) = 0)より前の、別の出来事 -/
theorem two_events (l : ℝ) (hl : 0 < l) : l < π * l / 2 ∧ cos (π * l / 2 / l) = 0 := by
  have hl' := hl.ne'
  constructor
  · have := pi_gt_three
    nlinarith
  · rw [show π * l / 2 / l = π / 2 by field_simp <;> ring]
    exact cos_pi_div_two

/-- 【α-X.9】同じ点の座標の関係(同期の座標と静的な座標) -/
theorem same_point (l t z τ x : ℝ) (hl : l ≠ 0)
    (h1 : l * sin (t / l) = l * cosh (x / l) * sin τ)
    (h2 : l * cos (t / l) * sinh (z / l) = l * sinh (x / l)) :
    sin τ * cosh (x / l) = sin (t / l) ∧ sinh (x / l) = cos (t / l) * sinh (z / l) := by
  constructor
  · have := mul_left_cancel₀ hl (h1.trans (by ring : l * cosh (x / l) * sin τ = l * (cosh (x / l) * sin τ)))
    linarith
  · have := mul_left_cancel₀ hl ((by ring : l * (cos (t / l) * sinh (z / l)) = l * cos (t / l) * sinh (z / l)).trans h2)
    linarith

/-- 【α-X.9】静的な位置 u(cosh(x/ℓ) sin u = 1)では sin τ = sin(t/ℓ) sin u -/
theorem static_clock (t l τ x u : ℝ) (h : sin τ * cosh (x / l) = sin (t / l)) (hu : cosh (x / l) * sin u = 1) :
    sin τ = sin (t / l) * sin u := by
  rw [← h]
  linear_combination (-(sin τ)) * hu

/-- 【α-X.9】首の中心 z = 0 では x = 0、sin τ = sin(t/ℓ)、cos τ = cos(t/ℓ):静的な時計はガウス時間そのもの -/
theorem neck_centre_clock (l t τ x : ℝ) (hl : l ≠ 0)
    (h0 : l * cos (t / l) * cosh (0 / l) = l * cosh (x / l) * cos τ)
    (h1 : l * sin (t / l) = l * cosh (x / l) * sin τ)
    (h2 : l * cos (t / l) * sinh (0 / l) = l * sinh (x / l)) :
    x = 0 ∧ sin τ = sin (t / l) ∧ cos τ = cos (t / l) := by
  have hx : sinh (x / l) = 0 := by
    have := mul_left_cancel₀ hl ((by simp : l * 0 = l * cos (t / l) * sinh (0 / l)).trans h2)
    exact this.symm
  have hx' : x / l = 0 := Real.sinh_injective (by rw [hx, sinh_zero])
  have hx0 : x = 0 := by
    rcases div_eq_zero_iff.1 hx' with h | h
    · exact h
    · exact absurd h hl
  simp only [hx0, zero_div, cosh_zero, mul_one] at h0 h1
  exact ⟨hx0, (mul_left_cancel₀ hl h1).symm, (mul_left_cancel₀ hl h0).symm⟩

end CFT.BridgeClock
