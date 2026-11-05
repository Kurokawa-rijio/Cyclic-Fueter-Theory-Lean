/-
  α-XI.1:首の W の不安定性の時間スケールと長さのしきい値

  W のモードは m²ℓ² = −1(BF 限界 −1/4 の下、IX.15)。不安定性の速さについて分かること:
  (a) 純粋な AdS₂ には固有の時間スケールがない。Poincaré の座標 −(r²/ℓ²)dt² + (ℓ²/r²)dr² で
      モード e^{λt}f(r) の方程式 r²f″ + 2rf′ + f − ℓ⁴λ²f/r² = 0 は、f(r) ↦ f(cr)、λ ↦ λ/c で不変
      (`no_intrinsic_rate`)。成長の速さは、AdS₂ を切り取る場所(首と帽子の接合)で決まる。
  (b) 首は有限の長さ。大域的な AdS₂ の座標 ds² = (ℓ²/sin²u)(−dτ² + du²)(cosh(x/ℓ) = 1/sin u)で
      モードの方程式は f″ + f/sin²u = λ²f。比較のポテンシャル 1/sin²u ≥ 1/u²(sin u ≤ u)と、
      Liouville の変換 f = √u h(y)、y = log(u₂/u)(外部:二次形式の変数変換)で、
      二次形式は ∫(h′² − (3/4)h²)dy になる(1 − 1/4 = 3/4)。
      h = sin(πy/Y)(Y = log(u₂/u₁))で Q = (Y/2)((π/Y)² − 3/4)(`Q_value`)。
      Q < 0 ⇔ Y > 2π/√3(`Q_neg_iff`)。Rayleigh の原理(外部:自己共役拡張の min–max)から、
      Q < 0 なら成長するモードがある。
  (c) 首の長さへの読み替え:首の半分の長さ L(中心から接合まで)なら接合は sin u_c = sech(L/ℓ)。
      試験関数を [u_c, π/2] に置くと Y = log(π/(2u_c))。Jordan の不等式 sin u ≥ 2u/π と sech ≤ 2e^{−L/ℓ} から
      Y ≥ L/ℓ − log 2(`Y_lower`)。したがって L/ℓ > 2π/√3 + log 2 ≈ 4.32 なら首は確実に不安定
      (`long_neck_unstable`、十分条件)。短い首が安定かは未確認(下からの評価が必要)。
  成長率の具体的な値は、接合での境界条件に依存するので、ここでは決めない。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CFT.NeckInstability

open Real

/-- 【α-XI.1 (a)】スケール対称性:f が λ の解なら g(r) = f(cr) は λ/c の解(g′ = cf′、g″ = c²f″) -/
theorem no_intrinsic_rate (l lam c r f0 f1 f2 : ℝ) (hc : c ≠ 0) (hr : r ≠ 0)
    (h : (c * r) ^ 2 * f2 + 2 * (c * r) * f1 + f0 - l ^ 4 * lam ^ 2 * f0 / (c * r) ^ 2 = 0) :
    r ^ 2 * (c ^ 2 * f2) + 2 * r * (c * f1) + f0 - l ^ 4 * (lam / c) ^ 2 * f0 / r ^ 2 = 0 := by
  have e : r ^ 2 * (c ^ 2 * f2) + 2 * r * (c * f1) + f0 - l ^ 4 * (lam / c) ^ 2 * f0 / r ^ 2
      = (c * r) ^ 2 * f2 + 2 * (c * r) * f1 + f0 - l ^ 4 * lam ^ 2 * f0 / (c * r) ^ 2 := by
    field_simp <;> ring
  rw [e, h]

/-- g(r) = f(cr) の微分(連鎖律) -/
theorem scaled_deriv (f : ℝ → ℝ) (f1 c r : ℝ) (hf : HasDerivAt f f1 (c * r)) :
    HasDerivAt (fun x => f (c * x)) (f1 * c) r := by
  have h : HasDerivAt (fun x => c * x) c r := by simpa using (hasDerivAt_id' r).const_mul c
  exact hf.comp r h

/-- ∫₀^Y sin²(πy/Y) dy = Y/2 -/
theorem int_sin_sq (Y : ℝ) (hY : 0 < Y) : ∫ y in (0 : ℝ)..Y, sin (π / Y * y) ^ 2 = Y / 2 := by
  have hne : π / Y ≠ 0 := div_ne_zero pi_ne_zero hY.ne'
  have h := intervalIntegral.integral_comp_mul_left (fun x => sin x ^ 2) hne (a := 0) (b := Y)
  simp only at h
  rw [h, integral_sin_sq, mul_zero, div_mul_cancel₀ π hY.ne', sin_zero, sin_pi]
  simp only [smul_eq_mul]
  field_simp
  try ring

/-- ∫₀^Y cos²(πy/Y) dy = Y/2 -/
theorem int_cos_sq (Y : ℝ) (hY : 0 < Y) : ∫ y in (0 : ℝ)..Y, cos (π / Y * y) ^ 2 = Y / 2 := by
  have hne : π / Y ≠ 0 := div_ne_zero pi_ne_zero hY.ne'
  have h := intervalIntegral.integral_comp_mul_left (fun x => cos x ^ 2) hne (a := 0) (b := Y)
  simp only at h
  rw [h, integral_cos_sq, mul_zero, div_mul_cancel₀ π hY.ne', sin_zero, sin_pi]
  simp only [smul_eq_mul]
  field_simp
  try ring

/-- 【α-XI.1 (b)】試験関数 h = sin(πy/Y) の二次形式 Q = ∫(h′² − (3/4)h²) = (Y/2)((π/Y)² − 3/4) -/
theorem Q_value (Y : ℝ) (hY : 0 < Y) :
    ∫ y in (0 : ℝ)..Y, ((π / Y * cos (π / Y * y)) ^ 2 - 3 / 4 * sin (π / Y * y) ^ 2)
      = Y / 2 * ((π / Y) ^ 2 - 3 / 4) := by
  have c1 : Continuous fun y : ℝ => (π / Y * cos (π / Y * y)) ^ 2 := by fun_prop
  have c2 : Continuous fun y : ℝ => 3 / 4 * sin (π / Y * y) ^ 2 := by fun_prop
  rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
  simp only [mul_pow]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_sin_sq Y hY,
    int_cos_sq Y hY]
  ring

/-- 【α-XI.1 (b)】Q < 0 ⇔ Y > 2π/√3 -/
theorem Q_neg_iff (Y : ℝ) (hY : 0 < Y) : Y / 2 * ((π / Y) ^ 2 - 3 / 4) < 0 ↔ 2 * π / Real.sqrt 3 < Y := by
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpi := pi_pos
  have hY2 : 0 < Y ^ 2 := by positivity
  -- 両辺を同値な形 4π² < 3Y² に直す
  have eL : Y / 2 * ((π / Y) ^ 2 - 3 / 4) < 0 ↔ 4 * π ^ 2 < 3 * Y ^ 2 := by
    have e : Y / 2 * ((π / Y) ^ 2 - 3 / 4) = (4 * π ^ 2 - 3 * Y ^ 2) / (8 * Y) := by
      field_simp <;> ring
    rw [e, div_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · linarith
    · intro h; right; exact ⟨by linarith, by positivity⟩
  have eR : 2 * π / Real.sqrt 3 < Y ↔ 4 * π ^ 2 < 3 * Y ^ 2 := by
    rw [div_lt_iff₀ h3]
    have hYs : (Y * Real.sqrt 3) ^ 2 = 3 * Y ^ 2 := by rw [mul_pow, hs]; ring
    constructor
    · intro h
      have := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 2 * π) h
      nlinarith
    · intro h
      have hb : 0 ≤ Y * Real.sqrt 3 := by positivity
      have : (2 * π) ^ 2 < (Y * Real.sqrt 3) ^ 2 := by rw [hYs]; nlinarith
      exact lt_of_pow_lt_pow_left 2 hb this
  rw [eL, eR]

/-- 【α-XI.1 (c)】接合 sin u_c = sech(L/ℓ)、0 < u_c ≤ π/2 なら Y = log(π/(2u_c)) ≥ L/ℓ − log 2 -/
theorem Y_lower (L l uc : ℝ) (hl : 0 < l) (huc : 0 < uc) (huc2 : uc ≤ π / 2)
    (hjoin : sin uc = 1 / cosh (L / l)) : L / l - Real.log 2 ≤ Real.log (π / (2 * uc)) := by
  have hpi := pi_pos
  -- Jordan:2u/π ≤ sin u
  have hJ : 2 / π * uc ≤ sin uc := mul_le_sin huc.le huc2
  -- cosh x ≥ eˣ/2
  have hcosh : exp (L / l) / 2 ≤ cosh (L / l) := by
    rw [Real.cosh_eq]; have := exp_pos (-(L / l)); linarith
  have hch : 0 < cosh (L / l) := cosh_pos _
  -- 2u_c/π ≤ 1/cosh ≤ 2e^{−L/ℓ}
  have h1 : 2 / π * uc ≤ 2 / exp (L / l) := by
    calc 2 / π * uc ≤ sin uc := hJ
      _ = 1 / cosh (L / l) := hjoin
      _ ≤ 1 / (exp (L / l) / 2) := one_div_le_one_div_of_le (by positivity) hcosh
      _ = 2 / exp (L / l) := by field_simp
  -- π/(2u_c) ≥ e^{L/ℓ}/2
  have h2 : exp (L / l) / 2 ≤ π / (2 * uc) := by
    have he := exp_pos (L / l)
    rw [div_le_div_iff (by norm_num) (by positivity)]
    have : 2 * uc * exp (L / l) ≤ 2 * π := by
      have := h1
      rw [div_mul_eq_mul_div, div_le_div_iff hpi he] at this
      linarith
    linarith
  have h3 : Real.log (exp (L / l) / 2) ≤ Real.log (π / (2 * uc)) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_div (exp_pos _).ne' (by norm_num), Real.log_exp] at h3
  exact h3

/-- 【α-XI.1 (c)】L/ℓ > 2π/√3 + log 2(≈ 4.32)なら Y > 2π/√3:二次形式が負の試験関数があり、首は不安定 -/
theorem long_neck_unstable (L l uc : ℝ) (hl : 0 < l) (huc : 0 < uc) (huc2 : uc ≤ π / 2)
    (hjoin : sin uc = 1 / cosh (L / l)) (hL : 2 * π / Real.sqrt 3 + Real.log 2 < L / l) :
    let Y := Real.log (π / (2 * uc))
    0 < Y ∧ Y / 2 * ((π / Y) ^ 2 - 3 / 4) < 0 := by
  intro Y
  have hY : L / l - Real.log 2 ≤ Y := Y_lower L l uc hl huc huc2 hjoin
  have hpos : 0 < 2 * π / Real.sqrt 3 := by
    have := pi_pos; have := Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num); positivity
  have hY' : 2 * π / Real.sqrt 3 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  exact ⟨hY0, (Q_neg_iff Y hY0).2 hY'⟩

end CFT.NeckInstability
