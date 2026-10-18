/-
  α-VIII.3(Z41):アトラクター機構とダンベルの首(台帳の式からの導出)

  作用 L = R/(16πG) − F_{μν}F^{μν}/(4g²)、近地平線 AdS₂ × S²:
    ds² = v₁(−r²dt² + dr²/r²) + v₂ dΩ²、F_{θφ} = p sinθ(磁荷 p)。
  R = −2/v₁ + 2/v₂、F² = 2p²/v₂²、√−g を S² で積分すると 4π v₁ v₂。
    * entropy_from_action:Sen のエントロピー関数 ℰ = 2π(q e − f)(電荷 0)は台帳の式
        ℰ(v₁, v₂) = (π/G)(v₂ − v₁) + (4π²p²/g²)(v₁/v₂)
      に一致する(作用からの導出)
    * z41_deriv_v1, z41_deriv_v2:偏導関数
    * z41_critical:v₁, v₂ > 0 での臨界点は v₁ = v₂ = p²ℓ*²(ℓ*² = 4πG/g²)だけ
    * z41_entropy:臨界値 ℰ = 4π²p²/g² = (地平線の面積 4πv₂)/(4G)(Bekenstein–Hawking)
    * z41_neck:p = 1 なら近地平線の半径 √v₂ = ℓ*(Z27 の首の半径 r₀ = ℓ* と一致)
-/
import CFT.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

open Real

namespace CFT.Z41

/-- 角度方向に積分したラグランジアン f = 4π v₁ v₂ (R/(16πG) − F²/(4g²)) -/
noncomputable def fLag (G g p v1 v2 : ℝ) : ℝ :=
  4 * π * v1 * v2 * ((-2 / v1 + 2 / v2) / (16 * π * G) - (2 * p ^ 2 / v2 ^ 2) / (4 * g ^ 2))

/-- 台帳のエントロピー関数 -/
noncomputable def E (G g p v1 v2 : ℝ) : ℝ := π / G * (v2 - v1) + 4 * π ^ 2 * p ^ 2 / g ^ 2 * (v1 / v2)

/-- 作用からの導出:ℰ = 2π(0·e − f) が台帳の式 -/
theorem entropy_from_action (G g p v1 v2 : ℝ) (hG : G ≠ 0) (hg : g ≠ 0) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) :
    2 * π * (0 - fLag G g p v1 v2) = E G g p v1 v2 := by
  have hπ : π ≠ 0 := pi_ne_zero
  unfold fLag E; field_simp; ring

theorem z41_deriv_v1 (G g p v1 v2 : ℝ) :
    HasDerivAt (fun x => E G g p x v2) (-(π / G) + 4 * π ^ 2 * p ^ 2 / g ^ 2 / v2) v1 := by
  have h := (((hasDerivAt_id v1).const_mul (-(π / G))).add_const (π / G * v2)).add
    ((hasDerivAt_id v1).const_mul (4 * π ^ 2 * p ^ 2 / g ^ 2 / v2))
  convert h using 1
  · funext x; simp only [E, id]; ring
  · ring

theorem z41_deriv_v2 (G g p v1 v2 : ℝ) (h2 : v2 ≠ 0) :
    HasDerivAt (fun x => E G g p v1 x) (π / G - 4 * π ^ 2 * p ^ 2 / g ^ 2 * v1 / v2 ^ 2) v2 := by
  have h := (((hasDerivAt_id v2).const_mul (π / G)).add_const (-(π / G * v1))).add
    ((hasDerivAt_inv h2).const_mul (4 * π ^ 2 * p ^ 2 / g ^ 2 * v1))
  convert h using 1
  · funext x; simp only [E, id]; ring
  · field_simp; ring

/-- 臨界点は v₁ = v₂ = p²ℓ*² だけ(ℓ*² = 4πG/g²) -/
theorem z41_critical (G g p v1 v2 : ℝ) (hG : 0 < G) (hg : g ≠ 0) (h1 : 0 < v1) (h2 : 0 < v2)
    (d1 : -(π / G) + 4 * π ^ 2 * p ^ 2 / g ^ 2 / v2 = 0)
    (d2 : π / G - 4 * π ^ 2 * p ^ 2 / g ^ 2 * v1 / v2 ^ 2 = 0) :
    v2 = p ^ 2 * (4 * π * G / g ^ 2) ∧ v1 = p ^ 2 * (4 * π * G / g ^ 2) := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hG' := hG.ne'; have h2' := h2.ne'; have h1' := h1.ne'
  have e2 : v2 = p ^ 2 * (4 * π * G / g ^ 2) := by
    field_simp at d1
    have h3 : π * (v2 * g ^ 2 - 4 * π * G * p ^ 2) = 0 := by linear_combination -d1
    have h4 := (mul_eq_zero.mp h3).resolve_left hπ
    field_simp; linear_combination h4
  refine ⟨e2, ?_⟩
  -- d1 + d2·(v₂/v₁)… から v₁ = v₂
  have hsum : 4 * π ^ 2 * p ^ 2 / g ^ 2 / v2 * (1 - v1 / v2) = 0 := by linear_combination d1 + d2
  have hp : 4 * π ^ 2 * p ^ 2 / g ^ 2 / v2 ≠ 0 := by
    have : 4 * π ^ 2 * p ^ 2 / g ^ 2 / v2 = π / G := by linarith
    rw [this]; exact div_ne_zero hπ hG'
  have : 1 - v1 / v2 = 0 := (mul_eq_zero.mp hsum).resolve_left hp
  have hv : v1 = v2 := by field_simp at this; linarith
  rw [hv, e2]

/-- 臨界値:ℰ = 4π²p²/g² = 面積/(4G) -/
theorem z41_entropy (G g p : ℝ) (hG : G ≠ 0) (hg : g ≠ 0) (hp : p ≠ 0) :
    E G g p (p ^ 2 * (4 * π * G / g ^ 2)) (p ^ 2 * (4 * π * G / g ^ 2)) = 4 * π ^ 2 * p ^ 2 / g ^ 2
    ∧ 4 * π ^ 2 * p ^ 2 / g ^ 2 = 4 * π * (p ^ 2 * (4 * π * G / g ^ 2)) / (4 * G) := by
  have hπ : π ≠ 0 := pi_ne_zero
  constructor
  · unfold E; field_simp
  · field_simp; ring

/-- p = 1:近地平線の半径² = ℓ*²(首の半径 r₀ = ℓ*) -/
theorem z41_neck (G g : ℝ) : (1 : ℝ) ^ 2 * (4 * π * G / g ^ 2) = 4 * π * G / g ^ 2 := by ring

end CFT.Z41
