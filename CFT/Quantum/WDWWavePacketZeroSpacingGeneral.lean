import CFT.Quantum.WDWWavePacketZeroSpacing
import CFT.Quantum.WDWWavePacketZerosGeneral

/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第十三段：零点の間隔の一般区間版）。

  第十二段で、一般区間 [C₁, C₂]（L = C₂ − C₁）の bump 波束の零点は
  T₀,n = ħ·phaseZero n / L（n ≠ 0）に並ぶことが示された。ここでは第十一段の
  零点の間隔の定量評価をこのスケール版に広げる。第 n 零点を
  `genZero L ħ n = ħ·phaseZero n / L` と置けば、連続する零点の間隔は
  (ħ/L)·(x_{n+1} − x_n) に等しく（`genZero_succ_sub`）、n ≥ 1 に対して
    2π·ħ/L < T₀,n+1 − T₀,n < (ħ/L)·(3π − 2 arctan(πn))
  （`genZero_spacing_lower`・`genZero_spacing_upper`、まとめ
  `genZero_spacing_mem_Ioo`）。第十一段の収束を ħ/L 倍すれば、間隔は
  2π·ħ/L に収束する（`tendsto_genZero_spacing`）。すなわち一般区間の bump 波束の
  零点も、漸近的に周期 2πħ/L で等間隔に並ぶ。具体例 L = 2、ħ = 1 では間隔は
  π に収束する（`tendsto_genZero_spacing_example`）。さらに `genZero` が
  実際の波束の零点であること（`packetPhase_bump_genZero_is_zero`）と、
  連続する二つの波束の零点とその間隔の両側評価のまとめ
  （`packetPhase_bump_consec_zero_spacing`）も証明する。
  残り：一般の重み g への拡張。
-/

namespace CFT.WDWWavePacketSpacingGen

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen
  CFT.WDWWavePacketPhase CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay
  CFT.WDWWavePacketDecayExplicit CFT.WDWWavePacketClosedForm CFT.WDWWavePacketZero
  CFT.WDWWavePacketZeroUnique CFT.WDWWavePacketZeros CFT.WDWWavePacketSpacing
  CFT.WDWWavePacketZerosGen
open Filter Topology

/-- 一般区間の第 n 零点：T₀,n = ħ·phaseZero n / L（L = C₂ − C₁）。-/
noncomputable def genZero (L hbar : ℝ) (n : ℤ) : ℝ := hbar * phaseZero n / L

/-- 連続する零点の間隔の表示：第十二段のスケール則。-/
theorem genZero_succ_sub {L hbar : ℝ} (hL : L ≠ 0) (n : ℤ) :
    genZero L hbar (n + 1) - genZero L hbar n
      = hbar / L * (phaseZero (n + 1) - phaseZero n) := by
  unfold genZero
  field_simp
  ring

/-- n ≥ 1 の零点の間隔は 2π·ħ/L より大きい。-/
theorem genZero_spacing_lower {L hbar : ℝ} {n : ℤ} (hn : 1 ≤ n)
    (hL : 0 < L) (hhbar : 0 < hbar) :
    2 * Real.pi * hbar / L < genZero L hbar (n + 1) - genZero L hbar n := by
  have hpos : (0 : ℝ) < hbar / L := div_pos hhbar hL
  have h := mul_lt_mul_of_pos_left (phaseZero_spacing_lower hn) hpos
  rw [genZero_succ_sub hL.ne']
  have heq : 2 * Real.pi * hbar / L = hbar / L * (2 * Real.pi) := by ring
  rw [heq]
  exact h

/-- n ≥ 1 の零点の間隔は (ħ/L)·(3π − 2 arctan(πn)) より小さい。-/
theorem genZero_spacing_upper {L hbar : ℝ} {n : ℤ} (hn : 1 ≤ n)
    (hL : 0 < L) (hhbar : 0 < hbar) :
    genZero L hbar (n + 1) - genZero L hbar n
      < hbar / L * (3 * Real.pi - 2 * Real.arctan (Real.pi * (n : ℝ))) := by
  have hpos : (0 : ℝ) < hbar / L := div_pos hhbar hL
  have h := mul_lt_mul_of_pos_left (phaseZero_spacing_upper hn) hpos
  rw [genZero_succ_sub hL.ne']
  exact h

/-- n ≥ 1 の零点の間隔は区間 (2π·ħ/L, (ħ/L)·(3π − 2 arctan(πn))) 内にある。-/
theorem genZero_spacing_mem_Ioo {L hbar : ℝ} {n : ℤ} (hn : 1 ≤ n)
    (hL : 0 < L) (hhbar : 0 < hbar) :
    genZero L hbar (n + 1) - genZero L hbar n
      ∈ Set.Ioo (2 * Real.pi * hbar / L)
        (hbar / L * (3 * Real.pi - 2 * Real.arctan (Real.pi * (n : ℝ)))) :=
  ⟨genZero_spacing_lower hn hL hhbar, genZero_spacing_upper hn hL hhbar⟩

/-- 零点の間隔は 2π·ħ/L に収束する：一般区間の bump 波束の零点も漸近的に
    周期 2πħ/L で等間隔に並ぶ。-/
theorem tendsto_genZero_spacing {L hbar : ℝ} (hL : 0 < L) (hhbar : 0 < hbar) :
    Filter.Tendsto (fun n : ℕ => genZero L hbar ((n : ℤ) + 1) - genZero L hbar (n : ℤ))
      Filter.atTop (𝓝 (2 * Real.pi * hbar / L)) := by
  have h := tendsto_phaseZero_spacing.const_mul (hbar / L)
  have hlim : hbar / L * (2 * Real.pi) = 2 * Real.pi * hbar / L := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards with n
  exact (genZero_succ_sub (n := (n : ℤ)) hL.ne').symm

/-- `genZero` は実際の一般区間の bump 波束の零点である（n ≠ 0）。-/
theorem packetPhase_bump_genZero_is_zero {c l C₁ C₂ hbar : ℝ} (hlt : C₁ < C₂)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : 0 < hbar) {n : ℤ} (hn : n ≠ 0) :
    packetPhase c l C₁ C₂ (genZero (C₂ - C₁) hbar n) hbar (bumpG c l C₁ C₂) = 0 := by
  have hset := packetPhase_bump_zero_set_eq_general (c := c) (l := l) hlt hC₁ hl hhbar
  have hmem : genZero (C₂ - C₁) hbar n ∈
      {T₀ | packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂) = 0} := by
    rw [hset]
    exact ⟨n, hn, rfl⟩
  exact hmem

/-- 連続する二つの波束の零点と、その間隔の両側評価のまとめ。-/
theorem packetPhase_bump_consec_zero_spacing {c l C₁ C₂ hbar : ℝ} (hlt : C₁ < C₂)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hhbar : 0 < hbar) {n : ℤ} (hn : 1 ≤ n) :
    packetPhase c l C₁ C₂ (genZero (C₂ - C₁) hbar n) hbar (bumpG c l C₁ C₂) = 0 ∧
    packetPhase c l C₁ C₂ (genZero (C₂ - C₁) hbar (n + 1)) hbar (bumpG c l C₁ C₂) = 0 ∧
    2 * Real.pi * hbar / (C₂ - C₁)
      < genZero (C₂ - C₁) hbar (n + 1) - genZero (C₂ - C₁) hbar n ∧
    genZero (C₂ - C₁) hbar (n + 1) - genZero (C₂ - C₁) hbar n
      < hbar / (C₂ - C₁) * (3 * Real.pi - 2 * Real.arctan (Real.pi * (n : ℝ))) := by
  have hL : (0 : ℝ) < C₂ - C₁ := sub_pos.mpr hlt
  refine ⟨packetPhase_bump_genZero_is_zero hlt hC₁ hl hhbar (by omega),
    packetPhase_bump_genZero_is_zero hlt hC₁ hl hhbar (by omega),
    genZero_spacing_lower hn hL hhbar, genZero_spacing_upper hn hL hhbar⟩

/-- 具体例：c = ℓ = 1、C ∈ [9, 11]（L = 2）、ħ = 1 では零点の間隔は π に収束する。-/
theorem tendsto_genZero_spacing_example :
    Filter.Tendsto (fun n : ℕ => genZero 2 1 ((n : ℤ) + 1) - genZero 2 1 (n : ℤ))
      Filter.atTop (𝓝 Real.pi) := by
  have h := tendsto_genZero_spacing (L := 2) (hbar := 1) (by norm_num) (by norm_num)
  have heq : 2 * Real.pi * (1 : ℝ) / 2 = Real.pi := by ring
  rw [heq] at h
  exact h

end CFT.WDWWavePacketSpacingGen
