/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (c) の軽い部分：

  結合 A = Ω/(2r²) の発散の仕方。くさび系のエネルギー恒等式（4-5）に現れる
  係数 A（`WedgeBalance.wedgeAFun`）について、クルスカル型の正則座標での
  共形因子 Ω = 16M³e^{-r/2M}/r（`KruskalOmega.kruskalOmega`、12-8 (d) で
  証明済み）を代入すると A = (8M³/r³)·e^{-r/2M} となり、r → 0⁺ で +∞ に
  発散する。発散の速さも確定する：A·r³ → 8M³、すなわち A ~ 8M³/r³ で、
  Ω ~ 16M³/r よりもちょうど 1/(2r²) 倍だけ速い（A/Ω = 1/(2r²) → +∞）。
  したがって特異点側では結合 A は共形因子 Ω よりも強く発散し、W 方程式の
  右辺 A·(W − W³) の係数として支配的になる。

  残り：12-8 の (a)（特性データと角条件による二重ヌルゲージの固定）、
  (b) のくさび EYM 系の形での分類（近地平線極限 AdS₂ × S² など。
  温度の側は 6-2・9-3・`RNExtremalDoubleZero` で証明済み）、(c) の
  くさび系の一般の場への適用（ここではクルスカル因子という明示形での
  発散の仕方まで）。

  数値確認：M = 1 で r = 0.1, 0.01, 0.001, 0.0001 のとき A は
  約 7.6×10³, 8.0×10⁶, 8.0×10⁹, 8.0×10¹² と ~8/r³ で発散し、
  A·r³ → 8（python による確認）。数値確認は証明ではない
  （Lean で証明されているのは極限そのもの）。
-/
import Mathlib
import CFT.Spherical.KruskalOmegaLimit
import CFT.Spherical.WedgeEnergyBalance

open Filter Topology

namespace CFT.KruskalCoupling

/-- クルスカル因子から作る結合 A = Ω/(2r²)。くさび系のエネルギー恒等式に現れる
    係数 A（`WedgeBalance.wedgeAFun`）の、クルスカル型の正則座標での形。 -/
noncomputable def kruskalCoupling (M r : ℝ) : ℝ :=
  CFT.KruskalOmega.kruskalOmega M r / (2 * r ^ 2)

/-- A はくさび系の結合そのもの：定数場 Om ≡ Ω(M, r₀), r ≡ r₀ に対する
    `wedgeAFun` と一致する。 -/
theorem kruskalCoupling_eq_wedgeAFun (M r0 u v : ℝ) :
    CFT.WedgeBalance.wedgeAFun (fun _ _ => CFT.KruskalOmega.kruskalOmega M r0)
      (fun _ _ => r0) u v = kruskalCoupling M r0 := rfl

/-- A = (8M³/r³) · e^{-r/2M}（r ≠ 0）。 -/
theorem kruskalCoupling_eq (M r : ℝ) (hr : r ≠ 0) :
    kruskalCoupling M r = (8 * M ^ 3 / r ^ 3) * Real.exp (-r / (2 * M)) := by
  unfold kruskalCoupling CFT.KruskalOmega.kruskalOmega
  field_simp
  ring

/-- 結合 A は M > 0, r > 0 で正。 -/
theorem kruskalCoupling_pos (M r : ℝ) (hM : 0 < M) (hr : 0 < r) :
    0 < kruskalCoupling M r := by
  rw [kruskalCoupling_eq M r (ne_of_gt hr)]
  apply mul_pos
  · exact div_pos (by positivity) (by positivity)
  · exact Real.exp_pos _

/-- クルスカル因子は M > 0, r ≠ 0 で 0 でない。 -/
theorem kruskalOmega_ne_zero (M r : ℝ) (hM : 0 < M) (hr : r ≠ 0) :
    CFT.KruskalOmega.kruskalOmega M r ≠ 0 := by
  unfold CFT.KruskalOmega.kruskalOmega
  apply mul_ne_zero
  · exact div_ne_zero (by positivity) hr
  · exact Real.exp_ne_zero _

/-- 一般形：(C/r³) · exp(-r/(2M)) は r → 0⁺ で +∞ に発散する（C > 0）。 -/
theorem tendsto_div_pow_three_mul_exp_atTop (C M : ℝ) (hC : 0 < C) :
    Tendsto (fun r : ℝ => (C / r ^ 3) * Real.exp (-r / (2 * M))) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun r : ℝ => C * r⁻¹ ^ 3) (𝓝[>] 0) atTop :=
    Filter.Tendsto.const_mul_atTop hC
      ((tendsto_pow_atTop (show (3 : ℕ) ≠ 0 by norm_num)).comp
        tendsto_inv_nhdsGT_zero)
  have h2 := CFT.KruskalOmega.kruskalExpFactor_tendsto_one M
  have h := Filter.Tendsto.atTop_mul one_pos h1 h2
  refine h.congr (fun r => ?_)
  simp only [div_eq_mul_inv, inv_pow]

/-- 12-8 (c)：結合 A は r → 0⁺ で +∞ に発散する。 -/
theorem kruskalCoupling_tendsto_atTop (M : ℝ) (hM : 0 < M) :
    Tendsto (kruskalCoupling M) (𝓝[>] 0) atTop := by
  have h := tendsto_div_pow_three_mul_exp_atTop (8 * M ^ 3) M (by positivity)
  refine h.congr (fun r => ?_)
  by_cases hr : r = 0
  · subst hr; simp [kruskalCoupling]
  · rw [kruskalCoupling_eq M r hr]

/-- 発散の速さ：A · r³ → 8M³（r → 0⁺）。すなわち A ~ 8M³/r³ で、Ω ~ 16M³/r
    よりも 1/(2r²) 倍だけ速く発散する。 -/
theorem kruskalCoupling_mul_pow_three_tendsto (M : ℝ) :
    Tendsto (fun r : ℝ => kruskalCoupling M r * r ^ 3) (𝓝[>] 0) (𝓝 (8 * M ^ 3)) := by
  have heq : (fun r : ℝ => kruskalCoupling M r * r ^ 3)
      =ᶠ[𝓝[>] 0] (fun r : ℝ => (8 * M ^ 3) * Real.exp (-r / (2 * M))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hr)
    rw [kruskalCoupling_eq M r (ne_of_gt hr)]
    calc (8 * M ^ 3 / r ^ 3) * Real.exp (-r / (2 * M)) * r ^ 3
        = (8 * M ^ 3 / r ^ 3 * r ^ 3) * Real.exp (-r / (2 * M)) := by ring
      _ = (8 * M ^ 3) * Real.exp (-r / (2 * M)) := by
          rw [div_mul_cancel₀ _ hr3]
  have h := (tendsto_const_nhds (x := 8 * M ^ 3)).mul
    (CFT.KruskalOmega.kruskalExpFactor_tendsto_one M)
  exact Tendsto.congr' heq.symm (by simpa using h)

/-- A / Ω = 1/(2r²)（r ≠ 0, Ω ≠ 0）。 -/
theorem kruskalCoupling_div_kruskalOmega (M r : ℝ) (hr : r ≠ 0)
    (hOm : CFT.KruskalOmega.kruskalOmega M r ≠ 0) :
    kruskalCoupling M r / CFT.KruskalOmega.kruskalOmega M r = 1 / (2 * r ^ 2) := by
  unfold kruskalCoupling
  field_simp
  ring

/-- A は Ω よりも速く発散する：A/Ω = 1/(2r²) → +∞（r → 0⁺）。 -/
theorem kruskalCoupling_div_kruskalOmega_tendsto_atTop (M : ℝ) (hM : 0 < M) :
    Tendsto (fun r : ℝ => kruskalCoupling M r / CFT.KruskalOmega.kruskalOmega M r)
      (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun r : ℝ => (1 / 2 : ℝ) * r⁻¹ ^ 2) (𝓝[>] 0) atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 1 / 2)
      ((tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp
        tendsto_inv_nhdsGT_zero)
  refine h1.congr (fun r => ?_)
  by_cases hr : r = 0
  · subst hr; simp [kruskalCoupling]
  · rw [kruskalCoupling_div_kruskalOmega M r hr (kruskalOmega_ne_zero M r hM hr)]
    simp only [div_eq_mul_inv, inv_pow, mul_inv, one_mul]

end CFT.KruskalCoupling
