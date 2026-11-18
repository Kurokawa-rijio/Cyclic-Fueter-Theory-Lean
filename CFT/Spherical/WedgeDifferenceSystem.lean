import CFT.Spherical.WedgeEnergyIdentity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-
  命題集 `LEAN_GAP_TREES.md` 4-7（一意性）の第1歩：差の線形系の導出。
  滑らかな解が2つあれば一致することを、差の線形系へのエネルギー評価と
  特性方向のグロンウォールで示すのが 4-7 の本体だが、その出発点は
  「2つの解の差は、係数が2つの解で決まる線形系を満たす」という純粋な
  代数恒等式である。本モジュールはその恒等式を、4-2・4-5 と同じ導分代数の
  流儀（`Derivation ℤ S S`、体 S 上の抽象場）で証明する。
  3本の発展方程式の右辺の差を、δr・δW・δΩ とその1階微分（Ω 方程式では
  δruv = du (dv δr) も）に線形な形に因数分解し、2つの解が方程式を満たせば
  その差がこの線形系を満たすことを示す。残り：差の線形系へのエネルギー評価
  と特性方向のグロンウォール（4-7 の本体）、解析的な `deriv` 版への移行、
  拘束の差の線形系。
  恒等式は sympy による展開計算（`~/workspace/tmp_scratch/check47.py`・
  `check47b.py`）でも照合済み。
-/

namespace CFT.WedgeDifference

set_option maxHeartbeats 0

variable {S : Type*} [Field S]

open CFT.WedgeEnergy

/-- W(1-W²) の差の因数分解。 -/
theorem w_cubic_factor (W W' : S) :
    W * (1 - W ^ 2) - W' * (1 - W' ^ 2)
      = (W - W') * (1 - W ^ 2 - W * W' - W' ^ 2) := by ring

/-- (1-W²)² の差の因数分解。 -/
theorem w_quartic_factor (W W' : S) :
    (1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2
      = -(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2) := by ring

/-- Ω² の差の因数分解。 -/
theorem om_sq_factor (Om Om' : S) :
    Om ^ 2 - Om' ^ 2 = (Om - Om') * (Om + Om') := by ring

/-- 逆元の差。 -/
theorem inv_diff (r r' : S) (hr : r ≠ 0) (hr' : r' ≠ 0) :
    r⁻¹ - r'⁻¹ = -(r - r') * r⁻¹ * r'⁻¹ := by
  field_simp

/-- 逆元二乗の差。 -/
theorem inv_sq_diff (r r' : S) (hr : r ≠ 0) (hr' : r' ≠ 0) :
    (r⁻¹) ^ 2 - (r'⁻¹) ^ 2
      = -(r - r') * (r + r') * (r⁻¹) ^ 2 * (r'⁻¹) ^ 2 := by
  field_simp
  ring

/-- 逆元三乗の差。 -/
theorem inv_cube_diff (r r' : S) (hr : r ≠ 0) (hr' : r' ≠ 0) :
    (r⁻¹) ^ 3 - (r'⁻¹) ^ 3
      = -(r - r') * (r ^ 2 + r * r' + r' ^ 2) * (r⁻¹) ^ 3 * (r'⁻¹) ^ 3 := by
  field_simp
  ring

/-- 逆元四乗の差。 -/
theorem inv_pow4_diff (r r' : S) (hr : r ≠ 0) (hr' : r' ≠ 0) :
    (r⁻¹) ^ 4 - (r'⁻¹) ^ 4
      = -(r - r') * (r ^ 3 + r ^ 2 * r' + r * r' ^ 2 + r' ^ 3)
          * (r⁻¹) ^ 4 * (r'⁻¹) ^ 4 := by
  field_simp
  ring

/-- Ω の逆元の差。 -/
theorem inv_diff_Om (Om Om' : S) (hOm : Om ≠ 0) (hOm' : Om' ≠ 0) :
    Om⁻¹ - Om'⁻¹ = -(Om - Om') * Om⁻¹ * Om'⁻¹ := by
  field_simp

/-- r 方程式の右辺（`WedgeEYMSystem.rhsR` と同じ式を ⁻¹ 形で書いたもの）。 -/
noncomputable def wedgeRuv (Om W ru rv r : S) : S :=
  2⁻¹ * Om * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹ - ru * rv * r⁻¹

/-- Ω 方程式の右辺（`WedgeEYMSystem.rhsOm` と同じ式を ⁻¹ 形で書いたもの）。 -/
noncomputable def wedgeOmuv (Om Ou Ov ruv r W : S) : S :=
  Ou * Ov * Om⁻¹ - 2 * Om * ruv * r⁻¹ - Om ^ 2 * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4

/-- W 方程式の右辺の差（テレスコープ形）。 -/
theorem wedgeWuv_diff_grouped (Om W r Om' W' r' : S) :
    wedgeWuv Om W r - wedgeWuv Om' W' r'
      = 2⁻¹ * (Om - Om') * W * (1 - W ^ 2) * (r⁻¹) ^ 2
        + 2⁻¹ * Om' * (W * (1 - W ^ 2) - W' * (1 - W' ^ 2)) * (r⁻¹) ^ 2
        + 2⁻¹ * Om' * W' * (1 - W' ^ 2) * ((r⁻¹) ^ 2 - (r'⁻¹) ^ 2) := by
  simp only [wedgeWuv]
  ring

/-- W 方程式の右辺の差：δOm・δW・δr に線形な形。 -/
theorem wedgeWuv_diff_linear (Om W r Om' W' r' : S) (hr : r ≠ 0) (hr' : r' ≠ 0) :
    wedgeWuv Om W r - wedgeWuv Om' W' r'
      = 2⁻¹ * W * (1 - W ^ 2) * (r⁻¹) ^ 2 * (Om - Om')
        + 2⁻¹ * Om' * (1 - W ^ 2 - W * W' - W' ^ 2) * (r⁻¹) ^ 2 * (W - W')
        - 2⁻¹ * Om' * W' * (1 - W' ^ 2) * (r + r') * (r⁻¹) ^ 2 * (r'⁻¹) ^ 2
            * (r - r') := by
  have h := wedgeWuv_diff_grouped Om W r Om' W' r'
  rw [w_cubic_factor, inv_sq_diff r r' hr hr'] at h
  linear_combination h

/-- r 方程式の右辺の差（テレスコープ形）。 -/
theorem wedgeRuv_diff_grouped (Om W ru rv r Om' W' ru' rv' r' : S) :
    wedgeRuv Om W ru rv r - wedgeRuv Om' W' ru' rv' r'
      = 2⁻¹ * (Om - Om') * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹
        + 2⁻¹ * Om' * (((1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2) * (r⁻¹) ^ 3
            + (1 - W' ^ 2) ^ 2 * ((r⁻¹) ^ 3 - (r'⁻¹) ^ 3)
            - (r⁻¹ - r'⁻¹))
        - ((ru - ru') * rv * r⁻¹ + ru' * (rv - rv') * r⁻¹
            + ru' * rv' * (r⁻¹ - r'⁻¹)) := by
  simp only [wedgeRuv]
  ring

/-- r 方程式の右辺の差：δOm・δW・δr・δru・δrv に線形な形。 -/
theorem wedgeRuv_diff_linear (Om W ru rv r Om' W' ru' rv' r' : S)
    (hr : r ≠ 0) (hr' : r' ≠ 0) :
    wedgeRuv Om W ru rv r - wedgeRuv Om' W' ru' rv' r'
      = 2⁻¹ * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹ * (Om - Om')
        + 2⁻¹ * Om' * (-(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2) * (r⁻¹) ^ 3
            + (1 - W' ^ 2) ^ 2
                * (-(r - r') * (r ^ 2 + r * r' + r' ^ 2) * (r⁻¹) ^ 3 * (r'⁻¹) ^ 3)
            + (r - r') * r⁻¹ * r'⁻¹)
        - ((ru - ru') * rv * r⁻¹ + ru' * (rv - rv') * r⁻¹
            - ru' * rv' * (r - r') * r⁻¹ * r'⁻¹) := by
  have h := wedgeRuv_diff_grouped Om W ru rv r Om' W' ru' rv' r'
  rw [w_quartic_factor, inv_cube_diff r r' hr hr', inv_diff r r' hr hr'] at h
  linear_combination h

/-- Ω 方程式の右辺の差（テレスコープ形）。 -/
theorem wedgeOmuv_diff_grouped (Om Ou Ov ruv r W Om' Ou' Ov' ruv' r' W' : S) :
    wedgeOmuv Om Ou Ov ruv r W - wedgeOmuv Om' Ou' Ov' ruv' r' W'
      = (Ou - Ou') * Ov * Om⁻¹ + Ou' * (Ov - Ov') * Om⁻¹
          + Ou' * Ov' * (Om⁻¹ - Om'⁻¹)
        - 2 * ((Om - Om') * ruv * r⁻¹ + Om' * (ruv - ruv') * r⁻¹
            + Om' * ruv' * (r⁻¹ - r'⁻¹))
        - ((Om ^ 2 - Om' ^ 2) * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4
            + Om' ^ 2 * ((1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2) * (r⁻¹) ^ 4
            + Om' ^ 2 * (1 - W' ^ 2) ^ 2 * ((r⁻¹) ^ 4 - (r'⁻¹) ^ 4)) := by
  simp only [wedgeOmuv]
  ring

/-- Ω 方程式の右辺の差：δOm・δW・δr・δOu・δOv・δruv に線形な形。 -/
theorem wedgeOmuv_diff_linear (Om Ou Ov ruv r W Om' Ou' Ov' ruv' r' W' : S)
    (hr : r ≠ 0) (hr' : r' ≠ 0) (hOm : Om ≠ 0) (hOm' : Om' ≠ 0) :
    wedgeOmuv Om Ou Ov ruv r W - wedgeOmuv Om' Ou' Ov' ruv' r' W'
      = (Ov * Om⁻¹ * (Ou - Ou') + Ou' * Om⁻¹ * (Ov - Ov')
          - Ou' * Ov' * Om⁻¹ * Om'⁻¹ * (Om - Om'))
        - 2 * (ruv * r⁻¹ * (Om - Om') + Om' * r⁻¹ * (ruv - ruv')
            - Om' * ruv' * (r - r') * r⁻¹ * r'⁻¹)
        - ((Om - Om') * (Om + Om') * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4
            + Om' ^ 2 * (-(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2)) * (r⁻¹) ^ 4
            + Om' ^ 2 * (1 - W' ^ 2) ^ 2
                * (-(r - r') * (r ^ 3 + r ^ 2 * r' + r * r' ^ 2 + r' ^ 3)
                    * (r⁻¹) ^ 4 * (r'⁻¹) ^ 4)) := by
  have h := wedgeOmuv_diff_grouped Om Ou Ov ruv r W Om' Ou' Ov' ruv' r' W'
  rw [inv_diff_Om Om Om' hOm hOm', inv_diff r r' hr hr', om_sq_factor,
    w_quartic_factor, inv_pow4_diff r r' hr hr'] at h
  linear_combination h


section

variable (du dv : Derivation ℤ S S) (r Om W r' Om' W' : S)

/-- 2つの解の W の差は線形系を満たす。 -/
theorem diff_W_eq (hr : r ≠ 0) (hr' : r' ≠ 0)
    (eW : du (dv W) = wedgeWuv Om W r)
    (eW' : du (dv W') = wedgeWuv Om' W' r') :
    du (dv (W - W'))
      = 2⁻¹ * W * (1 - W ^ 2) * (r⁻¹) ^ 2 * (Om - Om')
        + 2⁻¹ * Om' * (1 - W ^ 2 - W * W' - W' ^ 2) * (r⁻¹) ^ 2 * (W - W')
        - 2⁻¹ * Om' * W' * (1 - W' ^ 2) * (r + r') * (r⁻¹) ^ 2 * (r'⁻¹) ^ 2
            * (r - r') := by
  have h : du (dv (W - W')) = du (dv W) - du (dv W') := by simp only [map_sub]
  rw [h, eW, eW']
  exact wedgeWuv_diff_linear Om W r Om' W' r' hr hr'

/-- 2つの解の r の差は線形系を満たす。 -/
theorem diff_r_eq (hr : r ≠ 0) (hr' : r' ≠ 0)
    (eR : du (dv r) = wedgeRuv Om W (du r) (dv r) r)
    (eR' : du (dv r') = wedgeRuv Om' W' (du r') (dv r') r') :
    du (dv (r - r'))
      = 2⁻¹ * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹ * (Om - Om')
        + 2⁻¹ * Om' * (-(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2) * (r⁻¹) ^ 3
            + (1 - W' ^ 2) ^ 2
                * (-(r - r') * (r ^ 2 + r * r' + r' ^ 2) * (r⁻¹) ^ 3 * (r'⁻¹) ^ 3)
            + (r - r') * r⁻¹ * r'⁻¹)
        - ((du r - du r') * dv r * r⁻¹ + du r' * (dv r - dv r') * r⁻¹
            - du r' * dv r' * (r - r') * r⁻¹ * r'⁻¹) := by
  have h : du (dv (r - r')) = du (dv r) - du (dv r') := by simp only [map_sub]
  rw [h, eR, eR']
  exact wedgeRuv_diff_linear Om W (du r) (dv r) r Om' W' (du r') (dv r') r' hr hr'

/-- 2つの解の Ω の差は線形系を満たす。 -/
theorem diff_Om_eq (hr : r ≠ 0) (hr' : r' ≠ 0) (hOm : Om ≠ 0) (hOm' : Om' ≠ 0)
    (eOm : du (dv Om) = wedgeOmuv Om (du Om) (dv Om) (du (dv r)) r W)
    (eOm' : du (dv Om') = wedgeOmuv Om' (du Om') (dv Om') (du (dv r')) r' W') :
    du (dv (Om - Om'))
      = (dv Om * Om⁻¹ * (du Om - du Om') + du Om' * Om⁻¹ * (dv Om - dv Om')
          - du Om' * dv Om' * Om⁻¹ * Om'⁻¹ * (Om - Om'))
        - 2 * (du (dv r) * r⁻¹ * (Om - Om') + Om' * r⁻¹ * (du (dv r) - du (dv r'))
            - Om' * du (dv r') * (r - r') * r⁻¹ * r'⁻¹)
        - ((Om - Om') * (Om + Om') * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4
            + Om' ^ 2 * (-(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2)) * (r⁻¹) ^ 4
            + Om' ^ 2 * (1 - W' ^ 2) ^ 2
                * (-(r - r') * (r ^ 3 + r ^ 2 * r' + r * r' ^ 2 + r' ^ 3)
                    * (r⁻¹) ^ 4 * (r'⁻¹) ^ 4)) := by
  have h : du (dv (Om - Om')) = du (dv Om) - du (dv Om') := by simp only [map_sub]
  rw [h, eOm, eOm']
  exact wedgeOmuv_diff_linear Om (du Om) (dv Om) (du (dv r)) r W
    Om' (du Om') (dv Om') (du (dv r')) r' W' hr hr' hOm hOm'

/-- まとめ：2つの解の差は、係数が2つの解で決まる線形系を満たす。 -/
theorem difference_system (hr : r ≠ 0) (hr' : r' ≠ 0) (hOm : Om ≠ 0) (hOm' : Om' ≠ 0)
    (eR : du (dv r) = wedgeRuv Om W (du r) (dv r) r)
    (eR' : du (dv r') = wedgeRuv Om' W' (du r') (dv r') r')
    (eOm : du (dv Om) = wedgeOmuv Om (du Om) (dv Om) (du (dv r)) r W)
    (eOm' : du (dv Om') = wedgeOmuv Om' (du Om') (dv Om') (du (dv r')) r' W')
    (eW : du (dv W) = wedgeWuv Om W r)
    (eW' : du (dv W') = wedgeWuv Om' W' r') :
    du (dv (r - r'))
      = 2⁻¹ * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹ * (Om - Om')
        + 2⁻¹ * Om' * (-(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2) * (r⁻¹) ^ 3
            + (1 - W' ^ 2) ^ 2
                * (-(r - r') * (r ^ 2 + r * r' + r' ^ 2) * (r⁻¹) ^ 3 * (r'⁻¹) ^ 3)
            + (r - r') * r⁻¹ * r'⁻¹)
        - ((du r - du r') * dv r * r⁻¹ + du r' * (dv r - dv r') * r⁻¹
            - du r' * dv r' * (r - r') * r⁻¹ * r'⁻¹)
    ∧ du (dv (Om - Om'))
      = (dv Om * Om⁻¹ * (du Om - du Om') + du Om' * Om⁻¹ * (dv Om - dv Om')
          - du Om' * dv Om' * Om⁻¹ * Om'⁻¹ * (Om - Om'))
        - 2 * (du (dv r) * r⁻¹ * (Om - Om') + Om' * r⁻¹ * (du (dv r) - du (dv r'))
            - Om' * du (dv r') * (r - r') * r⁻¹ * r'⁻¹)
        - ((Om - Om') * (Om + Om') * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4
            + Om' ^ 2 * (-(W - W') * (W + W') * (2 - W ^ 2 - W' ^ 2)) * (r⁻¹) ^ 4
            + Om' ^ 2 * (1 - W' ^ 2) ^ 2
                * (-(r - r') * (r ^ 3 + r ^ 2 * r' + r * r' ^ 2 + r' ^ 3)
                    * (r⁻¹) ^ 4 * (r'⁻¹) ^ 4))
    ∧ du (dv (W - W'))
      = 2⁻¹ * W * (1 - W ^ 2) * (r⁻¹) ^ 2 * (Om - Om')
        + 2⁻¹ * Om' * (1 - W ^ 2 - W * W' - W' ^ 2) * (r⁻¹) ^ 2 * (W - W')
        - 2⁻¹ * Om' * W' * (1 - W' ^ 2) * (r + r') * (r⁻¹) ^ 2 * (r'⁻¹) ^ 2
            * (r - r') := by
  exact ⟨diff_r_eq du dv r Om W r' Om' W' hr hr' eR eR',
    diff_Om_eq du dv r Om W r' Om' W' hr hr' hOm hOm' eOm eOm',
    diff_W_eq du dv r Om W r' Om' W' hr hr' eW eW'⟩

end

end CFT.WedgeDifference
