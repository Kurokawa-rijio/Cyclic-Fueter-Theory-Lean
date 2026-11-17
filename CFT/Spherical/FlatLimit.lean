/-
  命題集 `LEAN_GAP_TREES.md` 9-2（平坦極限）：
  質量パラメータ M = 0 のシュワルツシルト場は平坦時空（二重ヌル座標での
  ミンコフスキー）になることを示す。

  証明は 9-1 と同じ導分代数の流儀（場を体 S の元、∂_u, ∂_v を導分として扱う）。
  M = 0 ではトータス関係は 2Ω = 1、すなわち Ω = 1/2（定数）、r_u = −1/2、
  r_v = +1/2 になり、真空の発展方程式は平坦な波動方程式 r_uv = 0、Ω_uv = 0
  に帰着し、ミスナー–シャープ質量は 0 になる。2 次元部分の計量
  −2Ω du dv = −du dv は定数係数で、これが平坦極限の内容である。

  恒等式（r_uv の右辺 = 0、質量 = 0、2Ω = 1）は sympy による有理関数計算でも
  照合済み。

  残り：解析的な `deriv` 版（`Du`/`Dv`）への移行、地平線の扱い（M = 0 では
  地平線は無い）。9-1 と同じく本モジュールの範囲外。
-/
import CFT.Spherical.SchwarzschildVacuumSolution

namespace CFT.FlatLimit

open CFT.Schwarzschild

variable {S : Type*} [Field S] [CharZero S]

variable (du dv : Derivation ℤ S S) (r Om : S)

/-- M = 0 のシュワルツシルト場の値：Ω = 1/2、r_u = −1/2、r_v = +1/2。 -/
theorem flat_field_values (h : SchwarzschildField du dv r Om 0) :
    Om = 1 / 2 ∧ du r = -(1 / 2 : S) ∧ dv r = 1 / 2 := by
  have h1 := h.1
  simp only [mul_zero, zero_div, sub_zero] at h1
  have hOm : Om = 1 / 2 := by linear_combination h1 / 2
  have hru := h.2.1
  have hrv := h.2.2.1
  rw [hOm] at hru hrv
  exact ⟨hOm, hru, hrv⟩

/-- 逆向き：Ω = 1/2、r_u = −1/2、r_v = +1/2 なら M = 0 のシュワルツシルト場。 -/
theorem schwarzschild_zero_of_flat (hOm : Om = 1 / 2) (hru : du r = -(1 / 2 : S))
    (hrv : dv r = 1 / 2) :
    SchwarzschildField du dv r Om 0 := by
  subst hOm
  refine ⟨by norm_num, hru, hrv, map_zero du, map_zero dv⟩

/-- M = 0 のシュワルツシルト場 ⟺ 平坦な場の値。 -/
theorem flat_field_iff (hOm : Om = 1 / 2) :
    SchwarzschildField du dv r Om 0 ↔ du r = -(1 / 2 : S) ∧ dv r = 1 / 2 := by
  constructor
  · intro h
    exact (flat_field_values du dv r Om h).2
  · intro h
    exact schwarzschild_zero_of_flat du dv r Om hOm h.1 h.2

/-- Ω は u 方向に定数。 -/
theorem flat_du_Om (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    du Om = 0 := by
  have hdu := schwarzschild_du_Om du dv r Om 0 h hr
  simpa using hdu

/-- Ω は v 方向に定数。 -/
theorem flat_dv_Om (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    dv Om = 0 := by
  have hdv := schwarzschild_dv_Om du dv r Om 0 h hr
  simpa using hdv

set_option linter.unusedSectionVars false in
/-- 計量係数：2Ω = 1、すなわち 2 次元部分 −2Ω du dv = −du dv は定数係数
    （ミンコフスキーの二重ヌル表示）。 -/
theorem flat_metric_coeff (h : SchwarzschildField du dv r Om 0) :
    2 * Om = 1 := by
  have h1 := h.1
  simpa only [mul_zero, zero_div, sub_zero] using h1

/-- r の平坦な波動方程式：r_uv = 0。 -/
theorem flat_r_uv (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    du (dv r) = 0 := by
  have hrv := h.2.2.1
  have hdu := schwarzschild_du_Om du dv r Om 0 h hr
  rw [hrv]
  simpa using hdu

/-- Ω の平坦な波動方程式：Ω_uv = 0。 -/
theorem flat_Om_uv (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    du (dv Om) = 0 := by
  have hdv := schwarzschild_dv_Om du dv r Om 0 h hr
  rw [show dv Om = 0 by simpa using hdv]
  exact map_zero du

/-- r_u は u 方向に定数（r_uu = 0）。 -/
theorem flat_r_uu (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    du (du r) = 0 := by
  have hru := h.2.1
  have hdu := schwarzschild_du_Om du dv r Om 0 h hr
  rw [hru, map_neg]
  simpa using hdu

/-- r_v は v 方向に定数（r_vv = 0）。 -/
theorem flat_r_vv (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    dv (dv r) = 0 := by
  have hrv := h.2.2.1
  have hdv := schwarzschild_dv_Om du dv r Om 0 h hr
  rw [hrv]
  simpa using hdv

/-- まとめ：真空の発展方程式は平坦な波動方程式に帰着する。 -/
theorem flat_vacuum (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    du (dv r) = 0 ∧ du (dv Om) = 0 :=
  ⟨flat_r_uv du dv r Om h hr, flat_Om_uv du dv r Om h hr⟩

/-- ミスナー–シャープ質量は 0（平坦極限では質量が消える）。 -/
theorem flat_mass (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    CFT.WedgeMass.misnerSharpMass du dv r Om = 0 := by
  have hOm : Om = 1 / 2 := (flat_field_values du dv r Om h).1
  have hOm0 : Om ≠ 0 := by rw [hOm]; norm_num
  have hm := schwarzschild_mass du dv r Om 0 h hr hOm0
  simpa using hm

/-- まとめ：平坦極限。 -/
theorem flat_limit (h : SchwarzschildField du dv r Om 0) (hr : r ≠ 0) :
    Om = 1 / 2 ∧ du r = -(1 / 2 : S) ∧ dv r = 1 / 2 ∧ du (dv r) = 0 ∧
      du (dv Om) = 0 ∧ CFT.WedgeMass.misnerSharpMass du dv r Om = 0 := by
  obtain ⟨hOm, hru, hrv⟩ := flat_field_values du dv r Om h
  exact ⟨hOm, hru, hrv, flat_r_uv du dv r Om h hr, flat_Om_uv du dv r Om h hr,
    flat_mass du dv r Om h hr⟩

end CFT.FlatLimit
