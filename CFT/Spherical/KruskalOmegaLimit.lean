/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (d) の軽い部分：

  Ω → ∞ が特異点側の極限に対応すること。クルスカル型の正則座標では
  共形因子は Ω ∝ e^{-r/2M} / r で、r → 0⁺ で +∞ に発散する
  （Kruskal 1960, Szekeres 1960；Wald 1984 の教科書的事実）。
  本モジュールでは二重ヌル計量の 2 次元部分を -2Ω dU dV と書く流儀で
  Ω = 16 M^3 e^{-r/2M} / r（計量係数 2Ω = 32 M^3 e^{-r/2M} / r）と定義し、
  その正値性と r → 0⁺ での +∞ への発散を Lean の極限として証明する。
  指数因子 e^{-r/2M} → 1 と 1/r → +∞ の積の形で示す。

  残り：12-8 の (a)（特性データと角条件による二重ヌルゲージの固定）、
  (b)（Ω のゼロの位数による分類 — 一次ゼロ ↔ 有限温度、 二重ゼロ ↔ 極端・T = 0。
  温度の側は 6-2・9-3 で証明済み）、(c)（結合 A = Ω/(2r^2) の発散の仕方）。
  9-3 の残り（喉の固有距離の発散）とも直結する。

  数値確認：M = 1 で r = 0.1, 0.01, 0.001, 0.0001 のとき Ω は
  約 152, 1592, 15992, 159992 と ~16/r で発散する（python による確認）。
  数値確認は証明ではない（Lean で証明されているのは極限そのもの）。
-/
import Mathlib

open Filter Topology

namespace CFT.KruskalOmega

/-- クルスカル型の正則座標での共形因子。計量の 2 次元部分は
    `-2 * kruskalOmega M r * dU dV` で、計量係数 `2 * Ω = 32 M^3 e^{-r/2M} / r`。 -/
noncomputable def kruskalOmega (M r : ℝ) : ℝ :=
  (16 * M ^ 3 / r) * Real.exp (-r / (2 * M))

/-- クルスカル因子は M > 0, r > 0 で正。 -/
theorem kruskalOmega_pos (M r : ℝ) (hM : 0 < M) (hr : 0 < r) :
    0 < kruskalOmega M r := by
  unfold kruskalOmega
  apply mul_pos
  · exact div_pos (by positivity) hr
  · exact Real.exp_pos _

/-- 指数因子は r → 0⁺ で 1 に収束する。 -/
theorem kruskalExpFactor_tendsto_one (M : ℝ) :
    Tendsto (fun r : ℝ => Real.exp (-r / (2 * M))) (𝓝[>] 0) (𝓝 1) := by
  have hcont : Tendsto (fun r : ℝ => -r / (2 * M)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => -r / (2 * M)) := by fun_prop
    have h := hc.tendsto (0 : ℝ)
    rw [show (-(0 : ℝ) / (2 * M)) = 0 by simp] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h3 := (Real.continuous_exp.tendsto 0).comp hcont
  rwa [Real.exp_zero] at h3

/-- 一般形：(C / r) * exp(-r / (2M)) は r → 0⁺ で +∞ に発散する。 -/
theorem tendsto_div_mul_exp_atTop (C M : ℝ) (hC : 0 < C) :
    Tendsto (fun r : ℝ => (C / r) * Real.exp (-r / (2 * M))) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun r : ℝ => C * r⁻¹) (𝓝[>] 0) atTop :=
    Filter.Tendsto.const_mul_atTop hC tendsto_inv_nhdsGT_zero
  have h2 := kruskalExpFactor_tendsto_one M
  have h := Filter.Tendsto.atTop_mul one_pos h1 h2
  refine h.congr (fun r => ?_)
  simp only [div_eq_mul_inv]

/-- 12-8 (d)：クルスカル因子 Ω は r → 0⁺ で +∞ に発散する。 -/
theorem kruskalOmega_tendsto_atTop (M : ℝ) (hM : 0 < M) :
    Tendsto (kruskalOmega M) (𝓝[>] 0) atTop := by
  have h := tendsto_div_mul_exp_atTop (16 * M ^ 3) M (by positivity)
  exact h.congr (fun r => rfl)

/-- 計量係数 2Ω = 32M^3 e^{-r/2M} / r も r → 0⁺ で +∞ に発散する。 -/
theorem kruskalMetricCoeff_tendsto_atTop (M : ℝ) (hM : 0 < M) :
    Tendsto (fun r : ℝ => (32 * M ^ 3 / r) * Real.exp (-r / (2 * M)))
      (𝓝[>] 0) atTop :=
  tendsto_div_mul_exp_atTop (32 * M ^ 3) M (by positivity)

/-- 2 * Ω = 32M^3 e^{-r/2M} / r（計量係数との関係）。 -/
theorem two_mul_kruskalOmega (M r : ℝ) :
    2 * kruskalOmega M r = (32 * M ^ 3 / r) * Real.exp (-r / (2 * M)) := by
  unfold kruskalOmega
  field_simp
  ring

end CFT.KruskalOmega
