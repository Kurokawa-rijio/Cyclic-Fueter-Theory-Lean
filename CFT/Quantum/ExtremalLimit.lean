/-
  9-3 極限（エクストリーマル）極限（温度ゼロの極限の半分）

  6-2 の `rn_temperature`（T = (r₊ − r₋)/(4πr₊²)）と `rn_period`
  （β = 4πr₊²/(r₊ − r₋)）の当てはめ：
  * 温度は r₋ の連続関数で、r₋ → r₊ で 0 に収束する
    （`rn_temperature_tendsto_zero`）。r₋ について狭義単調減少
    （`rn_temperature_strictAntiOn`）。
  * 逆温度は r₋ → r₊⁻ で +∞ に発散する（`rn_period_tendsto_top`）。
    これが「首が長くなる」極限の観測量側の現れ。
  * まとめ `extremal_limit`：極限では T → 0 かつ β → +∞。
  残り：喉の固有距離そのものの発散（不適切積分の評価が要るため重い。
  温度の連続性の半分までで区切る）。
-/
import CFT.Quantum.ReissnerNordstromTemperature

open Real Filter Topology

namespace CFT.Extremal

/-- 温度は r₋ の連続関数。 -/
theorem rn_temperature_continuous (rp : ℝ) :
    Continuous (fun rm : ℝ => ((rp - rm) / rp ^ 2) / (4 * π)) := by
  fun_prop

/-- 極限 r₋ → r₊ で温度は 0 に収束する。 -/
theorem rn_temperature_tendsto_zero (rp : ℝ) :
    Tendsto (fun rm : ℝ => ((rp - rm) / rp ^ 2) / (4 * π)) (𝓝 rp) (𝓝 0) := by
  have h := (rn_temperature_continuous rp).tendsto rp
  simpa using h

/-- 温度は r₋ について狭義単調減少（r₋ が r₊ に近づくほど冷える）。 -/
theorem rn_temperature_strictAntiOn (rp : ℝ) (hp : 0 < rp) :
    StrictAntiOn (fun rm : ℝ => ((rp - rm) / rp ^ 2) / (4 * π)) (Set.Iic rp) := by
  intro a _ b _ hab
  have h1 : (rp - b) < (rp - a) := by linarith
  have hpos : (0 : ℝ) < 4 * π * rp ^ 2 := by positivity
  show ((rp - b) / rp ^ 2) / (4 * π) < ((rp - a) / rp ^ 2) / (4 * π)
  rw [CFT.Thermo.rn_temperature, CFT.Thermo.rn_temperature]
  exact (div_lt_div_iff_of_pos_right hpos).mpr h1

/-- 逆温度は極限で +∞ に発散する（「首が長くなる」側の観測量）。 -/
theorem rn_period_tendsto_top (rp : ℝ) (hp : 0 < rp) :
    Tendsto (fun rm : ℝ => 4 * π * rp ^ 2 / (rp - rm)) (𝓝[<] rp) atTop := by
  have hsub : Tendsto (fun rm : ℝ => rp - rm) (𝓝[<] rp) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun rm : ℝ => rp - rm) := by fun_prop
      have h2 := (hcont.tendsto rp).mono_left (nhdsWithin_le_nhds (s := Set.Iio rp))
      simpa using h2
    · filter_upwards [self_mem_nhdsWithin] with rm hrm
      exact sub_pos.mpr (Set.mem_Iio.mp hrm)
  have hinv : Tendsto (fun rm : ℝ => (rp - rm)⁻¹) (𝓝[<] rp) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hpos : (0 : ℝ) < 4 * π * rp ^ 2 := by positivity
  have hmul := Tendsto.const_mul_atTop hpos hinv
  simpa only [div_eq_mul_inv] using hmul

/-- まとめ：極限では T → 0 かつ β → +∞。 -/
theorem extremal_limit (rp : ℝ) (hp : 0 < rp) :
    Tendsto (fun rm : ℝ => ((rp - rm) / rp ^ 2) / (4 * π)) (𝓝 rp) (𝓝 0) ∧
    Tendsto (fun rm : ℝ => 4 * π * rp ^ 2 / (rp - rm)) (𝓝[<] rp) atTop :=
  ⟨rn_temperature_tendsto_zero rp, rn_period_tendsto_top rp hp⟩

end CFT.Extremal
