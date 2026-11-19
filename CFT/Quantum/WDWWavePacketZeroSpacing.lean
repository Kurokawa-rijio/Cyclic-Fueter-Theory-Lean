/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第十一段：零点の間隔の定量評価）。

  第十段までで、bump 波束の零点はちょうど第 n 零点 `phaseZero n`（n ≠ 0）であり、
  n ≥ 1 の零点は区間 (2πn, 2πn + 2π) 内にあることが示された。ここでは零点の間隔
  x_{n+1} − x_n を定量的に評価する。位相方程式 h(x_{n+1}) − h(x_n) = 2π と
  h(x) = x − 2 arctan(x/2) から、間隔は
    x_{n+1} − x_n = 2π + 2 (arctan(x_{n+1}/2) − arctan(x_n/2))
  と書ける（`phaseZero_succ_sub`）。arctan は狭義単調で π/2 未満なので、
  n ≥ 1 に対して
    2π < x_{n+1} − x_n < 3π − 2 arctan(πn)
  （`phaseZero_spacing_lower`・`phaseZero_spacing_upper`、まとめ
  `phaseZero_spacing_mem_Ioo`）。arctan(πn) → π/2 なので、挟み撃ちにより
  間隔は 2π に収束する（`tendsto_phaseZero_spacing`）。すなわち零点は漸近的に
  周期 2π で等間隔に並ぶ。残り：一般の重み g・一般の区間への拡張。
-/
import CFT.Quantum.WDWWavePacketZeros

namespace CFT.WDWWavePacketSpacing

open CFT.WDWWavePacketZeros CFT.WDWWavePacketZeroUnique
open Filter Topology

/-- 位相関数の差の表示。-/
theorem phaseFun_sub (x y : ℝ) :
    phaseFun x - phaseFun y
      = (x - y) - 2 * (Real.arctan (x / 2) - Real.arctan (y / 2)) := by
  simp only [phaseFun]
  ring

/-- 連続する零点の間隔の表示：位相方程式 h(x_{n+1}) − h(x_n) = 2π から。-/
theorem phaseZero_succ_sub (n : ℤ) :
    phaseZero (n + 1) - phaseZero n
      = 2 * Real.pi
        + 2 * (Real.arctan (phaseZero (n + 1) / 2)
          - Real.arctan (phaseZero n / 2)) := by
  have h1 := phaseZero_spec (n + 1)
  have h2 := phaseZero_spec n
  have hsub := phaseFun_sub (phaseZero (n + 1)) (phaseZero n)
  rw [h1, h2] at hsub
  have hcast : (((n + 1 : ℤ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hsub
  have hring : ((n : ℝ) + 1) * (2 * Real.pi) - (n : ℝ) * (2 * Real.pi)
      = 2 * Real.pi := by ring
  rw [hring] at hsub
  linarith

/-- 零点の列挙は狭義単調。-/
theorem phaseZero_strictMono : StrictMono phaseZero := by
  intro m n hmn
  apply strictMono_phaseFun.lt_iff_lt.mp
  rw [phaseZero_spec, phaseZero_spec]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) (by
    have hpi := Real.pi_pos
    linarith)

/-- n ≥ 1 の零点の間隔は 2π より大きい（arctan の狭義単調性から）。-/
theorem phaseZero_spacing_lower {n : ℤ} (hn : 1 ≤ n) :
    2 * Real.pi < phaseZero (n + 1) - phaseZero n := by
  have hlt : phaseZero n < phaseZero (n + 1) := phaseZero_strictMono (by omega)
  rw [phaseZero_succ_sub n]
  have harctan : Real.arctan (phaseZero n / 2)
      < Real.arctan (phaseZero (n + 1) / 2) :=
    Real.arctan_strictMono (by linarith)
  linarith

/-- n ≥ 1 の零点の間隔は 3π − 2 arctan(πn) より小さい。-/
theorem phaseZero_spacing_upper {n : ℤ} (hn : 1 ≤ n) :
    phaseZero (n + 1) - phaseZero n
      < 3 * Real.pi - 2 * Real.arctan (Real.pi * (n : ℝ)) := by
  have hmem := phaseZero_mem_Ioo_of_one_le hn
  have hpi := Real.pi_pos
  rw [phaseZero_succ_sub n]
  have h1 : Real.arctan (phaseZero (n + 1) / 2) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have h2 : Real.arctan (Real.pi * (n : ℝ)) < Real.arctan (phaseZero n / 2) := by
    apply Real.arctan_strictMono
    have h4 : (n : ℝ) * (2 * Real.pi) < phaseZero n := hmem.1
    have h5 : (n : ℝ) * (2 * Real.pi) = 2 * (Real.pi * (n : ℝ)) := by ring
    linarith
  linarith

/-- n ≥ 1 の零点の間隔は区間 (2π, 3π − 2 arctan(πn)) 内にある。-/
theorem phaseZero_spacing_mem_Ioo {n : ℤ} (hn : 1 ≤ n) :
    phaseZero (n + 1) - phaseZero n
      ∈ Set.Ioo (2 * Real.pi) (3 * Real.pi - 2 * Real.arctan (Real.pi * (n : ℝ))) :=
  ⟨phaseZero_spacing_lower hn, phaseZero_spacing_upper hn⟩

/-- arctan(πn) → π/2。-/
theorem tendsto_arctan_pi_nat :
    Filter.Tendsto (fun n : ℕ => Real.arctan (Real.pi * (n : ℝ))) Filter.atTop
      (𝓝 (Real.pi / 2)) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop Real.pi_pos
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h

/-- 零点の間隔は 2π に収束する：零点は漸近的に周期 2π で等間隔に並ぶ。-/
theorem tendsto_phaseZero_spacing :
    Filter.Tendsto (fun n : ℕ => phaseZero ((n : ℤ) + 1) - phaseZero (n : ℤ))
      Filter.atTop (𝓝 (2 * Real.pi)) := by
  have hupper : Filter.Tendsto
      (fun n : ℕ => 3 * Real.pi - 2 * Real.arctan (Real.pi * (n : ℝ)))
      Filter.atTop (𝓝 (2 * Real.pi)) := by
    have h := (tendsto_arctan_pi_nat.const_mul (2 : ℝ)).const_sub (3 * Real.pi)
    convert h using 1
    ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact (phaseZero_spacing_lower (n := (n : ℤ)) (by exact_mod_cast hn)).le
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact (phaseZero_spacing_upper (n := (n : ℤ)) (by exact_mod_cast hn)).le

end CFT.WDWWavePacketSpacing
