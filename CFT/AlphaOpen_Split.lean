/-
  未着手の三項目(X.11-C、XV.9、X.10-B)を小分けにして、証明できる核を閉じる(2026-11-12)

  * X.11-C(反作用を含む球対称な摂動の方程式の構造、ℓ は結合の長さ):
    `os_area_linear`:面積 R = r² は R_uv = (Ω/r²)(ℓ²(1 − W²)² − R) をみたす(Q = ln(Ω/r²) と W を与えると R について線形)。
    `os_Q_eq`:Weyl の変換で不変な量 Q = ln(Ω/r²) は Q_uv = 6 r_u r_v/r² − 3Ωℓ²(1 − W²)²/r⁴ + 2Ω/r² をみたす。
    `os_backreaction`、`os_backreaction_ne`:Q の源の W についての微分は 12Ωℓ²W(1 − W²)/r⁴ で、
    W ≠ 0、W² ≠ 1 なら 0 でない(W の摂動は一次で共形平坦からのずれを作る)。
  * XV.9(線形の重力波):`os_graviton` 帽子(a″ = −a)の上で、非等方な応力の摂動がないとき、
    テンソルの摂動 h″ + 2(a′/a)h′ + (n² − 1)h = 0 は μ = a h で μ″ = −n² μ(整数の振動数 n の振動子)。
    `os_graviton_count`:偏極を含む縮退度 2(n² − 4) は n = 3 で 10。
  * X.10-B(形の揺らぎの二次の項):`os_yamabe_factor` 球面 Sⁿ の共形の方向の第二変分の係数
    λ_k − n = (k − 1)(k + n)(λ_k = k(k + n − 1))。`os_yamabe_l1` k = 1 は 0(共形変換)、
    `os_yamabe_l2` k = 2 は n + 2、`os_shape_S9` S⁹ では 11 で、k = 2 の調和関数は 54 個。
  ここで証明するのは代数と微分の部分だけ。第二変分の式、テンソルの調和関数の固有値は外部の結果。
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace CFT.OS

/-- 面積 R = r² の式:R_uv = 2 r r_uv + 2 r_u r_v = (Ω/r²)(ℓ²(1 − W²)² − r²) -/
theorem os_area_linear (r ru rv ruv Om W l : ℝ) (hr : r ≠ 0)
    (h : ruv = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r) :
    2 * r * ruv + 2 * ru * rv = Om / r ^ 2 * (l ^ 2 * (1 - W ^ 2) ^ 2 - r ^ 2) := by
  rw [h]
  field_simp
  ring

/-- Q = ln(Ω/r²) の式:Q_uv = (ln Ω)_uv − 2(ln r)_uv = 6 r_u r_v/r² − 3Ωℓ²(1 − W²)²/r⁴ + 2Ω/r² -/
theorem os_Q_eq (r ru rv ruv Om Omu Omv Omuv W l : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (h1 : ruv = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r)
    (h2 : Omuv = Omu * Omv / Om - 2 * Om * ruv / r - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4) :
    (Omuv / Om - Omu * Omv / Om ^ 2) - 2 * (ruv / r - ru * rv / r ^ 2)
      = 6 * ru * rv / r ^ 2 - 3 * Om * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4 + 2 * Om / r ^ 2 := by
  rw [h2, h1]
  field_simp
  ring

/-- Q の源の W についての微分 -/
theorem os_backreaction (Om l r W : ℝ) :
    HasDerivAt (fun W : ℝ => -3 * Om * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4)
      (12 * Om * l ^ 2 * W * (1 - W ^ 2) / r ^ 4) W := by
  have hg : HasDerivAt (fun y : ℝ => 1 - y * y) (-(1 * W + W * 1)) W :=
    ((hasDerivAt_id' W).mul (hasDerivAt_id' W)).const_sub 1
  have h : HasDerivAt (fun y : ℝ => (-3 * Om * l ^ 2 / r ^ 4) * ((1 - y * y) * (1 - y * y)))
      ((-3 * Om * l ^ 2 / r ^ 4) * ((-(1 * W + W * 1)) * (1 - W * W) + (1 - W * W) * (-(1 * W + W * 1)))) W :=
    (hg.mul hg).const_mul _
  have e : (fun W : ℝ => -3 * Om * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4)
      = fun y : ℝ => (-3 * Om * l ^ 2 / r ^ 4) * ((1 - y * y) * (1 - y * y)) := by
    funext y
    ring
  rw [e]
  exact h.congr_deriv (by ring)

/-- 反作用は一次で避けられない:W ≠ 0、W² ≠ 1 なら源の微分は 0 でない -/
theorem os_backreaction_ne (Om l r W : ℝ) (hO : Om ≠ 0) (hl : l ≠ 0) (hr : r ≠ 0) (hW : W ≠ 0)
    (h1 : 1 - W ^ 2 ≠ 0) : 12 * Om * l ^ 2 * W * (1 - W ^ 2) / r ^ 4 ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hO) (pow_ne_zero 2 hl)) hW) h1)
    (pow_ne_zero 4 hr)

/-- 帽子の上の重力波:a″ = −a、h″ = −2(a′/a)h′ − (n² − 1)h なら (a h)″ = −n²(a h) -/
theorem os_graviton (a a' a'' h h' h'' n : ℝ) (ha : a ≠ 0) (hb : a'' = -a)
    (hh : h'' = -(2 * (a' / a) * h') - (n ^ 2 - 1) * h) :
    a'' * h + 2 * a' * h' + a * h'' = -n ^ 2 * (a * h) := by
  rw [hb, hh]
  field_simp
  ring

/-- 縮退度 2(n² − 4) は最低の n = 3 で 10 -/
theorem os_graviton_count : 2 * (3 ^ 2 - 4) = (10 : ℕ) := by norm_num

/-- 共形の方向の第二変分の係数:k(k + n − 1) − n = (k − 1)(k + n) -/
theorem os_yamabe_factor (k n : ℝ) : k * (k + n - 1) - n = (k - 1) * (k + n) := by ring

theorem os_yamabe_l1 (n : ℝ) : 1 * (1 + n - 1) - n = 0 := by ring

theorem os_yamabe_l2 (n : ℝ) : 2 * (2 + n - 1) - n = n + 2 := by ring

/-- S⁹:k = 2 の係数は 11、k = 2 の調和関数の個数は 10·11/2 − 1 = 54 -/
theorem os_shape_S9 : (2 : ℝ) * (2 + 9 - 1) - 9 = 11 ∧ (10 * 11 / 2 - 1 : ℕ) = 54 := by
  constructor <;> norm_num

end CFT.OS
