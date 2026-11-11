/-
  段階 20(2026-11-11):残りの 5 項目を小分けにして、証明できる核を閉じる

  * α-X.11-B(一様な YM の方向 = スファレロンの方向):一様等方な部分は Ω(η) と f(η) の 2 自由度。
    `ol_ym_energy` f″ = 2f(1 − f²) なら f′² + (1 − f²)² は保存、`ol_sphaleron_rate` 障壁の頂上 f = 0 のまわりで
    δf″ = 2δf、解 e^{√2η}(不安定、成長率 √2)。`ol_geometry_rigid` 一方トレースの式 Ω″ = −Ω は f によらず、
    Ω = a cos(η − η₀) の振幅は a² = Ω′² + Ω²(保存)。場は不安定でも、幾何は Tolman 宇宙のまま変わらない。
  * α-XI.6(Hawking–Page 型):`ol_hp_sign` 自由エネルギーの差 F = (r/4G)(1 − r²/L²) は r > L で負、
    `ol_hp_temperature` 転移の温度 T(r = L) = 1/(πL)(F と T の式は外部:Hawking–Page 1983)。
  * α-XI.7-B(Higgs の一様でない帽子 = 単極子の芯):平坦な極限の厳密解(Prasad–Sommerfield)
    W = x/sinh x、h = coth x − 1/x が Bogomolny の方程式 W′ = −Wh、h′ = (1 − W²)/x² をみたす
    (`ol_ps_W`、`ol_ps_h`)。中心で W = 1、h = 0(帽子の極と対称な相)、遠方で W = 0、h = 1(首の値)。
  * α-XV.8(すべてのモードの量子化):`ol_reduced_action` 球対称に縮約した重力の作用は
    sin²χ·√ĝ R の密度 = 6r(r_ηη − r_χχ)(r の自由な波動、符号は負)。`ol_gauge_k2` ゲージの摂動
    cos χ cos 2η·sin χ = ½ sin 2χ cos 2η は k = 2 のモード。`ol_gauge_count` 3 つの生成子が位相空間の 6 次元を除き、
    それは Ω の k = 1、k = 2 と W の n = 0 の 3 つの振動子に一致する。
  * α-X.10(随伴 Higgs の出どころ):`ol_rep_count` 楕円体の変形 = SO(10) の対称トレースレス 54 =
    (1,1) + (3,3) + (1,20′) + (4,6)(1 + 9 + 20 + 24)、(3,3) = 1 + 3 + 5 は対角の SU(2) の随伴 3 を含む(表現論は外部)。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

namespace CFT.OL

/-! ### α-X.11-B:一様な YM の方向 -/

/-- 一様な YM 場 f(η) の方程式 f″ = 2f(1 − f²) のもとで、エネルギー f′² + (1 − f²)² は保存する -/
theorem ol_ym_energy {f f1 : ℝ → ℝ} (η : ℝ) (hf : HasDerivAt f (f1 η) η)
    (hf1 : HasDerivAt f1 (2 * f η * (1 - f η * f η)) η) :
    HasDerivAt (fun η => f1 η * f1 η + (1 - f η * f η) * (1 - f η * f η)) 0 η := by
  have hg := (hf.mul hf).const_sub 1
  have h := (hf1.mul hf1).add (hg.mul hg)
  convert h using 1
  ring

/-- 障壁の頂上 f = 0 のまわりの線形化 δf″ = 2δf:e^{√2η} の 2 階微分の係数は (√2)² = 2(成長率 √2) -/
theorem ol_sphaleron_rate (e : ℝ) : Real.sqrt 2 * (Real.sqrt 2 * e) = 2 * e := by
  rw [← mul_assoc, Real.mul_self_sqrt (by norm_num)]

/-- 幾何は変わらない:Ω = a cos(η − η₀)(Ω″ = −Ω の解)では Ω′² + Ω² = a²(η によらない) -/
theorem ol_geometry_rigid (a η η0 : ℝ) :
    (-(a * sin (η - η0))) ^ 2 + (a * cos (η - η0)) ^ 2 = a ^ 2 := by
  linear_combination a ^ 2 * sin_sq_add_cos_sq (η - η0)

/-! ### α-XI.6:Hawking–Page 型の比較 -/

/-- 自由エネルギーの差 F = (r/4G)(1 − r²/L²) が負になるのは、地平線の半径が r > L のとき -/
theorem ol_hp_sign (r L G : ℝ) (hr : 0 < r) (hL : 0 < L) (hG : 0 < G) :
    r / (4 * G) * (1 - r ^ 2 / L ^ 2) < 0 ↔ L < r := by
  have hL2 : 0 < L ^ 2 := by positivity
  have hc : 0 < r / (4 * G) := by positivity
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have h1 : r ^ 2 ≤ L ^ 2 := by nlinarith
    have h2 : 0 ≤ 1 - r ^ 2 / L ^ 2 := by
      rw [sub_nonneg, div_le_one hL2]
      exact h1
    have h3 := mul_nonneg hc.le h2
    linarith
  · intro h
    have h1 : L ^ 2 < r ^ 2 := by nlinarith
    have h2 : 1 - r ^ 2 / L ^ 2 < 0 := by
      rw [sub_neg, one_lt_div hL2]
      exact h1
    exact mul_neg_of_pos_of_neg hc h2

/-- 温度 T = (1 + 3r²/L²)/(4πr) は r = L で 1/(πL) -/
theorem ol_hp_temperature (L : ℝ) (hL : L ≠ 0) :
    (1 + 3 * L ^ 2 / L ^ 2) / (4 * π * L) = 1 / (π * L) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-! ### α-XI.7-B:単極子の芯(Prasad–Sommerfield) -/

/-- W = x/sinh x は W′ = −W·h(h = coth x − 1/x)をみたす -/
theorem ol_ps_W (x : ℝ) (hx : x ≠ 0) (hs : sinh x ≠ 0) :
    HasDerivAt (fun x => x / sinh x) (-(x / sinh x) * (cosh x / sinh x - 1 / x)) x := by
  have h := (hasDerivAt_id' x).div (Real.hasDerivAt_sinh x) hs
  convert h using 1
  field_simp
  ring

/-- h = coth x − 1/x は h′ = (1 − W²)/x² をみたす -/
theorem ol_ps_h (x : ℝ) (hx : x ≠ 0) (hs : sinh x ≠ 0) :
    HasDerivAt (fun x => cosh x / sinh x - x⁻¹) ((1 - (x / sinh x) ^ 2) / x ^ 2) x := by
  have h := ((Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hs).sub ((hasDerivAt_id' x).inv hx)
  have e : sinh x * sinh x - cosh x * cosh x = -1 := by
    linear_combination -(Real.cosh_sq x)
  convert h using 1
  rw [e]
  field_simp
  ring

/-! ### α-XV.8:球対称に縮約した作用とゲージの数え方 -/

/-- sin²χ(6Ω² − 6Ω□̂Ω) = 6r(r_ηη − r_χχ)、r = Ω sin χ(oq_radius_wave の関係 hw を使う) -/
theorem ol_reduced_action (S Ω0 Bx ree rcc : ℝ) (hw : ree - rcc = -S * (Bx - Ω0)) :
    S ^ 2 * (6 * Ω0 ^ 2 - 6 * Ω0 * Bx) = 6 * (Ω0 * S) * (ree - rcc) := by
  rw [hw]
  ring

/-- ゲージの摂動 f = cos χ cos 2η は r = f sin χ = ½ sin 2χ cos 2η(k = 2 のモード) -/
theorem ol_gauge_k2 (χ : ℝ) : cos χ * sin χ = sin (2 * χ) / 2 := by
  rw [sin_two_mul]
  ring

/-- 3 つの生成子が除く位相空間の次元 2 × 3 = 6 は、3 つの振動子(Ω の k = 1、k = 2、W の n = 0)の 2 + 2 + 2 -/
theorem ol_gauge_count : 2 * 3 = 2 + 2 + 2 := by norm_num

/-! ### α-X.10:楕円体の変形と随伴 Higgs -/

/-- 次元の数え方:54 = 1 + 9 + 20 + 24、45 = 6 + 15 + 24、(3,3):9 = 1 + 3 + 5 -/
theorem ol_rep_count : (54 : ℕ) = 1 + 9 + 20 + 24 ∧ (45 : ℕ) = 6 + 15 + 24 ∧ (9 : ℕ) = 1 + 3 + 5 := by
  norm_num

end CFT.OL
