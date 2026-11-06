/-
  新しい柱 4:滑らかさの地図(2026-11-06)

  静的な EYM(+ 宇宙定数 Λ)を固有距離のゲージ ds² = −e^{2ν}dt² + ds² + r(s)²dΩ² で書く(単位は首の半径 ℓ = 1)。
  κρ = 2W′²/r² + (1 − W²)²/r⁴、κp_s = 2W′²/r² − (1 − W²)²/r⁴、κp_⊥ = (1 − W²)²/r⁴。
  * 運動学:断面の形 r(s)。
  * 作用:EYM + Λ。
  * 力学(この節の結果):
    (1) 静的な喉はない:r′ = 0 の点では r″ = −2W′²/r ≤ 0(`no_static_throat`)。
        つまり静的な形は「くびれ」をもてない(ヌルエネルギー条件)。くびれの極限は r″ = 0 の円柱だけ。
    (2) 円柱の族:W = 0、半径 R の円柱は Λ = 1/R² − 1/R⁴ ≤ 1/4 のときだけ存在し、時間の向きの曲がり
        k² = (2 − R²)/R⁴(k² > 0 で AdS₂、k = 0 で平坦。k² < 0 の dS₂ は ν′ 定数の形では表せず範囲外)。等号 Λ = 1/4 ⇔ R² = 2(`cylinder_family`)。
        Λ = 0 では R = 1 = ℓ、k = 1(BM の喉の行き先)。
    (3) 静的宇宙 + YM:r = √2 sin(s/√2)、W = cos(s/√2)、ν = 0、Λ = 3/4 は厳密解(`esu_ym`)。
        閉じた静的解の列は Λ = 3/4(n = 1)から Λ = 1/4(n → ∞、R = √2 の円柱)まで(外部:Volkov ほか 1996、数値で確認)。
    (4) 喉の中の YM:AdS₂ の喉(R = 1、k = 1)では W″ + W′ + W = 0、解は e^{−s/2}cos(√3 s/2)
        (`throat_mode`)。喉の中の節の間隔は 2π/√3 で、その間に振幅は e^{−π/√3} 倍になる。
        (別の量:BM 列の 1 段ごとに喉は π/√3 伸び、質量の不足が e^{−π/√3} 倍になる。数値。)
        有効質量 −1 は AdS₂ の BF 下限 −1/4 を下回る(`bf_violation`)。
    (4′) 臨界の円柱(R = √2、Λ = 1/4)は磁荷 1 の RN–de Sitter の超冷極限(三つの地平線が一致、Plebański–Hacyan の
        Minkowski₂ × S²)。その上の YM の線形のモード cos(s/√2) は静的宇宙の W と同じ関数(`cylinder_mode`)。
    (5) 帽子と首の Ω の足し算:N± = 4A² + ABc(8 − 4w²)w ± 8ABswt(w = 1/sin u、t = cot u)
        (`superpos_null`)。極の近くで −4ABc w³ が支配し、ヌルエネルギー条件を破る。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CFT.Smooth

open Real

/-- 【柱 4】静的な喉はない:r′ = 0 の点で、tt 成分と ss 成分(r′ = 0 での拘束)から r″ = −2W′²/r ≤ 0 -/
theorem no_static_throat (r W Wp L r2 : ℝ) (hr : 0 < r)
    (htt : 2 * r * r2 = 1 - 0 ^ 2 - r ^ 2 * ((2 * Wp ^ 2 / r ^ 2 + (1 - W ^ 2) ^ 2 / r ^ 4) + L))
    (hss : -(1 / r ^ 2) + L - (2 * Wp ^ 2 / r ^ 2 - (1 - W ^ 2) ^ 2 / r ^ 4) = 0) :
    r2 = -(2 * Wp ^ 2 / r) ∧ r2 ≤ 0 := by
  have hr0 : r ≠ 0 := hr.ne'
  have hL : L = 1 / r ^ 2 + 2 * Wp ^ 2 / r ^ 2 - (1 - W ^ 2) ^ 2 / r ^ 4 := by linarith
  have e : r ^ 2 * ((2 * Wp ^ 2 / r ^ 2 + (1 - W ^ 2) ^ 2 / r ^ 4)
      + (1 / r ^ 2 + 2 * Wp ^ 2 / r ^ 2 - (1 - W ^ 2) ^ 2 / r ^ 4)) = 4 * Wp ^ 2 + 1 := by
    field_simp; ring
  rw [hL, e] at htt
  have h2 : r2 = -(2 * Wp ^ 2 / r) := by
    have h3 : r * r2 = -(2 * Wp ^ 2) := by linarith
    rw [eq_neg_iff_add_eq_zero, ← mul_left_cancel_iff_of_pos hr, mul_zero, mul_add, h3,
      mul_div_cancel₀ _ hr0]
    ring
  refine ⟨h2, ?_⟩
  rw [h2, neg_nonpos]
  exact div_nonneg (by positivity) hr.le

/-- 【柱 4】円柱の族:W = 0、r = R、r′ = r″ = 0、ν′ = k(定数)。tt 成分 0 = 1 − R²(1/R⁴ + Λ) と
θθ 成分 k² = 1/R⁴ − Λ ⇔ Λ = 1/R² − 1/R⁴、k² = (2 − R²)/R⁴
(k² > 0:AdS₂ × S²、k = 0:平坦 × S²。dS₂ × S² は ν′ が定数の形では表せず、この定理の範囲外) -/
theorem cylinder_family (R L k : ℝ) (hR : R ≠ 0) :
    (0 = 1 - R ^ 2 * (1 / R ^ 4 + L) ∧ k ^ 2 = 1 / R ^ 4 - L)
      ↔ (L = 1 / R ^ 2 - 1 / R ^ 4 ∧ k ^ 2 = (2 - R ^ 2) / R ^ 4) := by
  have h2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  constructor
  · rintro ⟨h1, h3⟩
    have h1' : R ^ 2 * (1 / R ^ 4 + L) = 1 := by linarith
    have e : L = (R ^ 2 * (1 / R ^ 4 + L)) / R ^ 2 - 1 / R ^ 4 := by
      field_simp
      ring
    rw [h1'] at e
    refine ⟨e, ?_⟩
    rw [h3, e]
    field_simp
    ring
  · rintro ⟨hL, hk⟩
    constructor
    · rw [hL]; field_simp <;> ring
    · rw [hk, hL]; field_simp; ring

/-- 【柱 4】円柱が存在する Λ の上限:1/R² − 1/R⁴ ≤ 1/4、等号 ⇔ R² = 2(平坦 × S²、半径 √2 ℓ) -/
theorem cylinder_max (R : ℝ) (hR : R ≠ 0) :
    1 / R ^ 2 - 1 / R ^ 4 ≤ 1 / 4 ∧ (1 / R ^ 2 - 1 / R ^ 4 = 1 / 4 ↔ R ^ 2 = 2) := by
  have h2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have e : 1 / 4 - (1 / R ^ 2 - 1 / R ^ 4) = (1 / R ^ 2 - 1 / 2) ^ 2 := by
    field_simp
    ring
  have hsq := sq_nonneg (1 / R ^ 2 - 1 / 2)
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : (1 / R ^ 2 - 1 / 2) ^ 2 = 0 := by linarith
    have h1 : 1 / R ^ 2 - 1 / 2 = 0 := (pow_eq_zero_iff two_ne_zero).mp h0
    have h3 : 1 / R ^ 2 = 1 / 2 := by linarith
    rw [div_eq_div_iff h2 two_ne_zero] at h3
    linarith
  · rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, h]
    norm_num

/-- 【柱 4】静的宇宙 + YM:a² = 2、r = a sin x、W = cos x(x = s/a)、ν = 0、Λ = 3/4。
r′ = cos x、r″ = −sin x/a、W′ = −sin x/a、W″ = −cos x/a² を入れると tt・ss・θθ・YM の式が成り立つ -/
theorem esu_ym (a x : ℝ) (ha : a ^ 2 = 2) (hs : sin x ≠ 0) :
    2 * (a * sin x) * (-(sin x) / a) = 1 - cos x ^ 2 - (a * sin x) ^ 2 *
      ((2 * (-(sin x) / a) ^ 2 / (a * sin x) ^ 2 + (1 - cos x ^ 2) ^ 2 / (a * sin x) ^ 4) + 3 / 4) ∧
    -((1 - cos x ^ 2) / (a * sin x) ^ 2) + 3 / 4
      - (2 * (-(sin x) / a) ^ 2 / (a * sin x) ^ 2 - (1 - cos x ^ 2) ^ 2 / (a * sin x) ^ 4) = 0 ∧
    (0 : ℝ) = (1 - cos x ^ 2) ^ 2 / (a * sin x) ^ 4 - 3 / 4 - (-(sin x) / a) / (a * sin x) ∧
    -(cos x) / a ^ 2 + cos x * (1 - cos x ^ 2) / (a * sin x) ^ 2 = 0 := by
  have ha0 : a ≠ 0 := by rintro rfl; norm_num at ha
  have hc : 1 - cos x ^ 2 = sin x ^ 2 := by rw [← sin_sq_add_cos_sq x]; ring
  have h4 : a ^ 4 = 4 := by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha]; norm_num
  rw [hc]
  simp only [mul_pow, div_pow, neg_sq, h4, ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp
    linear_combination (8 * sin x ^ 5) * ha
  · field_simp; ring

/-- 【柱 4】AdS₂ の喉の中の YM:W(s) = e^{−s/2}cos(√3 s/2) は W″ + W′ + W = 0 をみたす -/
theorem throat_mode (s : ℝ) :
    HasDerivAt (fun t => exp (-(t / 2)) * cos (√3 / 2 * t))
      (exp (-(s / 2)) * (-(1 / 2) * cos (√3 / 2 * s) - √3 / 2 * sin (√3 / 2 * s))) s ∧
    HasDerivAt (fun t => exp (-(t / 2)) * (-(1 / 2) * cos (√3 / 2 * t) - √3 / 2 * sin (√3 / 2 * t)))
      (exp (-(s / 2)) * (-(1 / 2) * cos (√3 / 2 * s) + √3 / 2 * sin (√3 / 2 * s))) s ∧
    exp (-(s / 2)) * (-(1 / 2) * cos (√3 / 2 * s) + √3 / 2 * sin (√3 / 2 * s))
      + exp (-(s / 2)) * (-(1 / 2) * cos (√3 / 2 * s) - √3 / 2 * sin (√3 / 2 * s))
      + exp (-(s / 2)) * cos (√3 / 2 * s) = 0 := by
  have hb : (√3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have he : HasDerivAt (fun t => exp (-(t / 2))) (exp (-(s / 2)) * (-(1 / 2))) s := by
    have := ((hasDerivAt_id' s).div_const 2).neg.exp
    convert this using 1
  have hcos : HasDerivAt (fun t => cos (√3 / 2 * t)) (-(sin (√3 / 2 * s)) * (√3 / 2)) s := by
    have := ((hasDerivAt_id' s).const_mul (√3 / 2)).cos
    convert this using 1; ring
  have hsin : HasDerivAt (fun t => sin (√3 / 2 * t)) (cos (√3 / 2 * s) * (√3 / 2)) s := by
    have := ((hasDerivAt_id' s).const_mul (√3 / 2)).sin
    convert this using 1; ring
  refine ⟨?_, ?_, ?_⟩
  · have := he.mul hcos
    convert this using 1; ring
  · have := he.mul ((hcos.const_mul (-(1 / 2))).sub (hsin.const_mul (√3 / 2)))
    convert this using 1
    linear_combination (exp (-(s / 2)) * cos (√3 / 2 * s)) * hb
  · ring

/-- 【柱 4】BF 下限を下回る:喉での有効質量 −1 は −1/4 より小さく、振動数 √(1 − 1/4) = √3/2。
節の間隔 π/(√3/2) の間に振幅は e^{−(1/2)·π/(√3/2)} = e^{−π/√3} 倍 -/
theorem bf_violation : (-1 : ℝ) < -1 / 4 ∧ √(1 - 1 / 4 : ℝ) = √3 / 2 ∧
    (1 / 2 : ℝ) * (π / (√3 / 2)) = π / √3 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num, Real.sqrt_div' 3 (by norm_num : (0 : ℝ) ≤ 4),
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  · rw [div_div_eq_mul_div]; ring

/-- 【柱 4】帽子と首の倍率の足し算 Ω = Ac + Bw(c = cos η、s = sin η、w = 1/sin u、t = cot u、
t² + 1 = w²)の null-null 成分:Ω_η = −As、Ω_ηη = −Ac、Ω_u = −Bwt、Ω_uu = Bw(w² + t²) から
N± = 4A² + ABc(8 − 4w²)w ± 8ABswt -/
theorem superpos_null (A B c s w t : ℝ) (h1 : c ^ 2 + s ^ 2 = 1) (h2 : t ^ 2 + 1 = w ^ 2) :
    (2 * (A * c + B * w) ^ 2 - 2 * (A * c + B * w) * (-(A * c) + B * w * (w ^ 2 + t ^ 2))
        + 4 * (-(A * s) + -(B * w * t)) ^ 2
        = 4 * A ^ 2 + A * B * c * (8 - 4 * w ^ 2) * w + 8 * A * B * s * w * t) ∧
    (2 * (A * c + B * w) ^ 2 - 2 * (A * c + B * w) * (-(A * c) + B * w * (w ^ 2 + t ^ 2))
        + 4 * (-(A * s) - -(B * w * t)) ^ 2
        = 4 * A ^ 2 + A * B * c * (8 - 4 * w ^ 2) * w - 8 * A * B * s * w * t) := by
  constructor
  · linear_combination (4 * A ^ 2) * h1 + (2 * B ^ 2 * w ^ 2 - 2 * A * B * c * w) * h2
  · linear_combination (4 * A ^ 2) * h1 + (2 * B ^ 2 * w ^ 2 - 2 * A * B * c * w) * h2

/-- 【柱 4】臨界の円柱(R² = 2、Λ = 1/4、ν′ = 0:超冷極限 Minkowski₂ × S²)の上の線形の YM:W″ + W/2 = 0。
解 W = cos(s/√2) は静的宇宙 + YM の W(`esu_ym`、a = √2)と同じ関数。節の間隔は π√2 -/
theorem cylinder_mode (s : ℝ) :
    HasDerivAt (fun t => cos (t / √2)) (-(sin (s / √2)) / √2) s ∧
    HasDerivAt (fun t => -(sin (t / √2)) / √2) (-(cos (s / √2)) / 2) s ∧
    -(cos (s / √2)) / 2 + cos (s / √2) / 2 = 0 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : √2 ≠ 0 := by positivity
  refine ⟨?_, ?_, by ring⟩
  · have := ((hasDerivAt_id' s).div_const √2).cos
    convert this using 1; ring
  · have := (((hasDerivAt_id' s).div_const √2).sin.neg).div_const √2
    convert this using 1
    field_simp

end CFT.Smooth
