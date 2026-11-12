/-
  アイデアの検証(2026-11-12):証明できる部分だけ

  * 案 7(単極子 = 球面の上の向きの統計力学):Z = sinh x / x は分配関数 ½∫_{−1}^{1} e^{xu} du(`id_Z_integral`)。
    W = 1/Z、h = Z′/Z とすると W′ = −W h は恒等式(`id_bog1`)。もう一本 h′ = (1 − W²)/x² は
    Z Z″ − Z′² = (Z² − 1)/x² と同値(`id_bog2`)で、Z = sinh x / x はこれをみたす(`id_Z_sinh`)。
  * 案 5(重力波とゲージ場の混合の選択則):TT テンソルの個数 2(n + 2)(n − 2) = 2(n² − 4)(`id_tt_count`)。
    パリティは λ → 1 − λ、f = 2λ − 1 → −f(`id_parity`)で、ポテンシャル (1 − f²)² は偶(`id_even`)。
    帽子 f = 0 はパリティで不変。
  * 案 2(反転 r → ℓ²/r):KS の運動項は −(ℓ³/r³) 倍(`id_inv_kinetic`)、ポテンシャルは −(r³/ℓ³) 倍(`id_inv_potential`)。
    ラプスを取り直すと作用は符号だけ変わる(解は解に写る)。
  * 案 8(形の揺らぎ = 内部の Ω):第二変分の係数 (k − 1)(k + n) は k = 0 で −n(`id_yamabe_k0`)。
-/
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace CFT.ID

theorem id_bog1 {Z : ℝ → ℝ} {Z' x : ℝ} (hZ : HasDerivAt Z Z' x) (h0 : Z x ≠ 0) :
    HasDerivAt (fun y => (Z y)⁻¹) (-((Z x)⁻¹ * (Z' * (Z x)⁻¹))) x := by
  have h := hZ.inv h0
  convert h using 1
  field_simp

theorem id_bog2 (Z Z' Z'' Zi xi : ℝ) (hZi : Z * Zi = 1)
    (hZ : Z * Z'' - Z' ^ 2 = (Z ^ 2 - 1) * xi ^ 2) :
    Z'' * Zi - Z' ^ 2 * Zi ^ 2 = (1 - Zi ^ 2) * xi ^ 2 := by
  linear_combination Zi ^ 2 * hZ + (-Z'' * Zi + xi ^ 2 * (Z * Zi + 1)) * hZi

theorem id_Z_sinh (s c xi : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    (s * xi) * (s * xi - 2 * c * xi ^ 2 + 2 * s * xi ^ 3) - (c * xi - s * xi ^ 2) ^ 2
      = ((s * xi) ^ 2 - 1) * xi ^ 2 := by
  linear_combination (-xi ^ 2) * hcs

theorem id_tt_count (n : ℝ) : 2 * ((n + 2) * (n - 2)) = 2 * (n ^ 2 - 4) := by ring

theorem id_parity (lam : ℝ) : 2 * (1 - lam) - 1 = -(2 * lam - 1) := by ring

theorem id_even (f : ℝ) : (1 - (-f) ^ 2) ^ 2 = (1 - f ^ 2) ^ 2 := by ring

theorem id_inv_kinetic (a r ad rd l : ℝ) (hr : r ≠ 0) (hl : l ≠ 0) :
    -(a * r / l) * (-(l ^ 2 * rd / r ^ 2)) ^ 2
      - 2 * (l ^ 2 / r) * ((ad * r + a * rd) / l) * (-(l ^ 2 * rd / r ^ 2))
      = -(l ^ 3 / r ^ 3) * (-a * rd ^ 2 - 2 * r * ad * rd) := by
  field_simp
  ring

theorem id_inv_potential (a r l : ℝ) (hr : r ≠ 0) (hl : l ≠ 0) :
    (a * r / l) * (1 - l ^ 2 / (l ^ 2 / r) ^ 2) = -(r ^ 3 / l ^ 3) * (a * (1 - l ^ 2 / r ^ 2)) := by
  field_simp
  ring

theorem id_yamabe_k0 (n : ℝ) : 0 * (0 + n - 1) - n = -n := by ring

theorem id_Z_integral (x : ℝ) (hx : x ≠ 0) :
    (1 / 2) * ∫ u in (-1 : ℝ)..1, Real.exp (x * u) = Real.sinh x / x := by
  have hd : ∀ u ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun u => Real.exp (x * u) / x) (Real.exp (x * u)) u := by
    intro u _
    have h := (((hasDerivAt_id' u).const_mul x).exp).div_const x
    convert h using 1
    field_simp
  have hc : IntervalIntegrable (fun u => Real.exp (x * u)) MeasureTheory.volume (-1) 1 :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc
  rw [e, Real.sinh_eq]
  simp only [mul_one, mul_neg_one]
  ring

end CFT.ID
