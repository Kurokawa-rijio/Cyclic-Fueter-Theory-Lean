/-
  α-VIII.3(Z41):非線形アトラクター(Sen のエントロピー関数の方法)の比較模型

  Einstein–Maxwell(G = 1、L = (R − F_{μν}F^{μν})/(16π))の極限的な近地平線幾何
    ds² = v₁(−r²dt² + dr²/r²) + v₂ dΩ²、F_{rt} = e、F_{θφ} = p sinθ
  で、f(v₁, v₂, e) = ∫_{S²} √−g L = (1/4)(2v₁ − 2v₂ + 2e²v₂/v₁ − 2p²v₁/v₂)、
  エントロピー関数 ℰ = 2π(q e − f)。
    * f_deriv_e, f_deriv_v1, f_deriv_v2:f の偏導関数(HasDerivAt)
    * attractor_unique:v₁, v₂ > 0 で ∂ℰ = 0 ⇔ v₁ = v₂ = q² + p²、e = q(臨界点は一つ:
      近地平線の値は電荷だけで決まる。アトラクター機構)
    * attractor_entropy:臨界値 ℰ = π(q² + p²) = (面積 4πv₂)/4(Bekenstein–Hawking)
  これは Sen の方法を標準の作用に当てはめた比較で、Z41 の作用(元の有効作用)のアトラクターではない。
  Z41 のアトラクター関数は元の作用が手元にないため未形式化(線形の BF 境界は AlphaVIII_BF)。
-/
import CFT.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace CFT.Attractor

noncomputable def f (p v1 v2 e : ℝ) : ℝ :=
  (1 / 4) * (2 * v1 - 2 * v2 + 2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2)

noncomputable def entropyFn (p q v1 v2 e : ℝ) : ℝ := 2 * Real.pi * (q * e - f p v1 v2 e)

theorem f_deriv_e (p v1 v2 e : ℝ) (h1 : v1 ≠ 0) :
    HasDerivAt (fun x => f p v1 v2 x) (e * v2 / v1) e := by
  have h := (((hasDerivAt_pow 2 e).const_mul (2 * v2 / v1)).const_add (2 * v1 - 2 * v2 - 2 * p ^ 2 * v1 / v2)).const_mul (1 / 4 : ℝ)
  convert h using 1
  · funext x; simp only [f]; field_simp; ring
  · field_simp; ring

theorem f_deriv_v1 (p v1 v2 e : ℝ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) :
    HasDerivAt (fun x => f p x v2 e) ((1 / 4) * (2 - 2 * e ^ 2 * v2 / v1 ^ 2 - 2 * p ^ 2 / v2)) v1 := by
  have h := ((((hasDerivAt_id v1).const_mul (2 - 2 * p ^ 2 / v2)).add
    ((hasDerivAt_inv h1).const_mul (2 * e ^ 2 * v2))).const_add (-2 * v2)).const_mul (1 / 4 : ℝ)
  convert h using 1
  · funext x; simp only [f, id]; field_simp; ring
  · field_simp; ring

theorem f_deriv_v2 (p v1 v2 e : ℝ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) :
    HasDerivAt (fun x => f p v1 x e) ((1 / 4) * (-2 + 2 * e ^ 2 / v1 + 2 * p ^ 2 * v1 / v2 ^ 2)) v2 := by
  have h := ((((hasDerivAt_id v2).const_mul (-2 + 2 * e ^ 2 / v1)).add
    ((hasDerivAt_inv h2).const_mul (-2 * p ^ 2 * v1))).const_add (2 * v1)).const_mul (1 / 4 : ℝ)
  convert h using 1
  · funext x; simp only [f, id]; field_simp; ring
  · field_simp

/-- 臨界点の方程式(∂ℰ/∂e = ∂ℰ/∂v₁ = ∂ℰ/∂v₂ = 0)の解は一つ:v₁ = v₂ = q² + p²、e = q -/
theorem attractor_unique (p q v1 v2 e : ℝ) (h1 : 0 < v1) (h2 : 0 < v2)
    (de : q - e * v2 / v1 = 0)
    (dv1 : (1 / 4) * (2 - 2 * e ^ 2 * v2 / v1 ^ 2 - 2 * p ^ 2 / v2) = 0)
    (dv2 : (1 / 4) * (-2 + 2 * e ^ 2 / v1 + 2 * p ^ 2 * v1 / v2 ^ 2) = 0) :
    v1 = q ^ 2 + p ^ 2 ∧ v2 = q ^ 2 + p ^ 2 ∧ e = q := by
  have a1 := h1.ne'; have a2 := h2.ne'
  field_simp at de dv1 dv2
  -- B + C から v₁v₂(v₁ − v₂) = 0
  have hB : v1 ^ 2 * v2 - e ^ 2 * v2 ^ 2 - p ^ 2 * v1 ^ 2 = 0 := by nlinarith [dv1]
  have hC : -(v1 * v2 ^ 2) + e ^ 2 * v2 ^ 2 + p ^ 2 * v1 ^ 2 = 0 := by nlinarith [dv2]
  have hs : v1 * v2 * (v1 - v2) = 0 := by linear_combination hB + hC
  have heq : v1 = v2 := by
    rcases mul_eq_zero.mp hs with h | h
    · exact absurd h (mul_ne_zero a1 a2)
    · linarith
  subst heq
  have he : e = q := by
    have : v1 * (q - e) = 0 := by linear_combination de
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h a1
    · linarith
  subst he
  have : v1 ^ 2 * (v1 - e ^ 2 - p ^ 2) = 0 := by linear_combination hB
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.mp h) a1
  · exact ⟨by linarith, by linarith, rfl⟩

/-- 臨界値:ℰ = π(q² + p²) = 面積/4 -/
theorem attractor_entropy (p q : ℝ) (hv : 0 < q ^ 2 + p ^ 2) :
    entropyFn p q (q ^ 2 + p ^ 2) (q ^ 2 + p ^ 2) q = Real.pi * (q ^ 2 + p ^ 2)
    ∧ Real.pi * (q ^ 2 + p ^ 2) = (4 * Real.pi * (q ^ 2 + p ^ 2)) / 4 := by
  refine ⟨?_, by ring⟩
  simp only [entropyFn, f]
  field_simp; ring

end CFT.Attractor
