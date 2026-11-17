/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) の軽い部分：近地平線極限の計量の形（AdS₂ × S²）。

  極端 RN の計量は ds² = −f(r) dt² + dr²/f(r) + r² dΩ²、
  f(r) = (r − r₊)²/r²（`CFT.RNExtremalZero.rnF` の極端形）。
  近地平線スケーリング r = r₊ + λρ、t = τ/λ（λ → 0）では
  * 時間係数：f(r)/λ² = ρ²/(r₊ + λρ)² → ρ²/r₊²、
  * 動径係数：λ²/f(r) = (r₊ + λρ)²/ρ² → r₊²/ρ²、
  * 球面係数：r² = (r₊ + λρ)² → r₊²。
  極限の計量は −(ρ²/r₊²) dτ² + (r₊²/ρ²) dρ² + r₊² dΩ²、
  すなわち半径 r₊ の AdS₂ × S² である。ポアンカレ座標 u = r₊²/ρ では
  2 次元部分は (r₊²/u²)(−dτ² + du²)（ポアンカレ AdS₂、半径 r₊）に
  なる：時間係数はポアンカレ因子に等しく、動径係数はヤコビアン
  (dρ/du)² = (r₊²/u²)² を掛けると同じ因子になる。
  文献：極端 RN の近地平線極限 AdS₂ × S² は既知
  （Soni, Trivedi & Vishal, JHEP 09 (2018) 04；近極端の無限の喉は
  Guevara, arXiv:2511.18637 (2026)）。ここで証明するのはその計量の形の
  代数と極限であり、くさび EYM 系の形での分類そのものは残り。
  温度の側（T = 0 ⟺ 二重ゼロ）は `RNExtremalDoubleZero.lean` で証明済み。

  数値確認：r₊ = 1、ρ = 2、λ = 0.1 で時間係数 2.7778 → 4.0、
  動径係数 0.36 → 0.25、ポアンカレ因子 4.0（python による確認）。
  数値確認は証明ではない（Lean で証明されているのは恒等式と極限そのもの）。
-/
import Mathlib
import CFT.Quantum.RNExtremalDoubleZero

open Filter Topology

namespace CFT.RNExtremalNearHorizon

/-- 近地平線スケーリングでの時間係数 f(r)/λ²（ττ 成分、符号を除く）。 -/
noncomputable def nhTimeCoeff (rp ρ lam : ℝ) : ℝ :=
  CFT.RNExtremalZero.rnF rp rp (rp + lam * ρ) / lam ^ 2

/-- 近地平線スケーリングでの動径係数 λ²/f(r)（ρρ 成分）。 -/
noncomputable def nhRadialCoeff (rp ρ lam : ℝ) : ℝ :=
  lam ^ 2 / CFT.RNExtremalZero.rnF rp rp (rp + lam * ρ)

/-- 近地平線スケーリングでの球面係数 r²。 -/
noncomputable def nhSphereCoeff (rp ρ lam : ℝ) : ℝ :=
  (rp + lam * ρ) ^ 2

/-- 極限の係数三つ組（AdS₂ × S²、共通半径 r₊）。 -/
noncomputable def ads2S2Coeffs (rp ρ : ℝ) : ℝ × ℝ × ℝ :=
  (ρ ^ 2 / rp ^ 2, rp ^ 2 / ρ ^ 2, rp ^ 2)

/-- ポアンカレ座標 u = r₊²/ρ。 -/
noncomputable def nhPoincareCoord (rp ρ : ℝ) : ℝ := rp ^ 2 / ρ

/-- 時間係数の明示形。 -/
theorem nhTimeCoeff_eq (rp ρ lam : ℝ) (hlam : lam ≠ 0) (hden : rp + lam * ρ ≠ 0) :
    nhTimeCoeff rp ρ lam = ρ ^ 2 / (rp + lam * ρ) ^ 2 := by
  unfold nhTimeCoeff
  rw [CFT.RNExtremalZero.rnF_extremal_near_horizon rp (lam * ρ)]
  field_simp
  ring

/-- 動径係数の明示形。 -/
theorem nhRadialCoeff_eq (rp ρ lam : ℝ) (hlam : lam ≠ 0) (hρ : ρ ≠ 0) :
    nhRadialCoeff rp ρ lam = (rp + lam * ρ) ^ 2 / ρ ^ 2 := by
  unfold nhRadialCoeff
  rw [CFT.RNExtremalZero.rnF_extremal_near_horizon rp (lam * ρ)]
  field_simp
  ring

/-- 球面係数の明示形。 -/
theorem nhSphereCoeff_eq (rp ρ lam : ℝ) :
    nhSphereCoeff rp ρ lam = (rp + lam * ρ) ^ 2 := rfl

/-- 極限で分母が消えないこと：λ → 0 で r₊ + λρ ≠ 0 が eventually 成り立つ。 -/
theorem eventually_rp_add_ne_zero (rp ρ : ℝ) (hp : rp ≠ 0) :
    ∀ᶠ lam in 𝓝[≠] (0 : ℝ), rp + lam * ρ ≠ 0 := by
  have hc : Continuous (fun lam : ℝ => rp + lam * ρ) := by fun_prop
  have h := hc.tendsto (0 : ℝ)
  rw [show (rp + 0 * ρ) = rp by simp] at h
  exact (tendsto_nhdsWithin_of_tendsto_nhds h).eventually_ne hp

/-- 時間係数の極限：ρ²/r₊²。 -/
theorem nhTimeCoeff_tendsto (rp ρ : ℝ) (hp : rp ≠ 0) :
    Tendsto (fun lam : ℝ => nhTimeCoeff rp ρ lam) (𝓝[≠] 0) (𝓝 (ρ ^ 2 / rp ^ 2)) := by
  have h2 := eventually_rp_add_ne_zero rp ρ hp
  have heq : (fun lam : ℝ => nhTimeCoeff rp ρ lam) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun lam => ρ ^ 2 / (rp + lam * ρ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, h2] with lam hlam hden
    exact nhTimeCoeff_eq rp ρ lam hlam hden
  have hlim : Tendsto (fun lam : ℝ => ρ ^ 2 / (rp + lam * ρ) ^ 2)
      (𝓝[≠] 0) (𝓝 (ρ ^ 2 / rp ^ 2)) := by
    apply Filter.Tendsto.div tendsto_const_nhds _ (pow_ne_zero 2 hp)
    have hc : Continuous (fun lam : ℝ => (rp + lam * ρ) ^ 2) := by fun_prop
    have h := hc.tendsto (0 : ℝ)
    rw [show (rp + 0 * ρ) ^ 2 = rp ^ 2 by simp] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact hlim.congr' heq.symm

/-- 動径係数の極限：r₊²/ρ²。 -/
theorem nhRadialCoeff_tendsto (rp ρ : ℝ) (hρ : ρ ≠ 0) :
    Tendsto (fun lam : ℝ => nhRadialCoeff rp ρ lam) (𝓝[≠] 0) (𝓝 (rp ^ 2 / ρ ^ 2)) := by
  have heq : (fun lam : ℝ => nhRadialCoeff rp ρ lam) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun lam => (rp + lam * ρ) ^ 2 / ρ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact nhRadialCoeff_eq rp ρ lam hlam hρ
  have hlim : Tendsto (fun lam : ℝ => (rp + lam * ρ) ^ 2 / ρ ^ 2)
      (𝓝[≠] 0) (𝓝 (rp ^ 2 / ρ ^ 2)) := by
    apply Filter.Tendsto.div _ tendsto_const_nhds (pow_ne_zero 2 hρ)
    have hc : Continuous (fun lam : ℝ => (rp + lam * ρ) ^ 2) := by fun_prop
    have h := hc.tendsto (0 : ℝ)
    rw [show (rp + 0 * ρ) ^ 2 = rp ^ 2 by simp] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact hlim.congr' heq.symm

/-- 球面係数の極限：r₊²。 -/
theorem nhSphereCoeff_tendsto (rp ρ : ℝ) :
    Tendsto (fun lam : ℝ => nhSphereCoeff rp ρ lam) (𝓝[≠] 0) (𝓝 (rp ^ 2)) := by
  have hc : Continuous (fun lam : ℝ => (rp + lam * ρ) ^ 2) := by fun_prop
  have h := hc.tendsto (0 : ℝ)
  rw [show (rp + 0 * ρ) ^ 2 = rp ^ 2 by simp] at h
  exact (h.mono_left nhdsWithin_le_nhds).congr (fun lam => rfl)

/-- 三つの係数の同時極限：AdS₂ × S² の係数三つ組。 -/
theorem nearHorizon_coeffs_tendsto (rp ρ : ℝ) (hp : rp ≠ 0) (hρ : ρ ≠ 0) :
    Tendsto (fun lam : ℝ => (nhTimeCoeff rp ρ lam,
      (nhRadialCoeff rp ρ lam, nhSphereCoeff rp ρ lam)))
      (𝓝[≠] 0) (𝓝 (ρ ^ 2 / rp ^ 2, rp ^ 2 / ρ ^ 2, rp ^ 2)) :=
  (nhTimeCoeff_tendsto rp ρ hp).prod_mk_nhds
    ((nhRadialCoeff_tendsto rp ρ hρ).prod_mk_nhds (nhSphereCoeff_tendsto rp ρ))

/-- 同じ極限を `ads2S2Coeffs` の形で。 -/
theorem nearHorizon_tendsto_ads2S2Coeffs (rp ρ : ℝ) (hp : rp ≠ 0) (hρ : ρ ≠ 0) :
    Tendsto (fun lam : ℝ => (nhTimeCoeff rp ρ lam,
      (nhRadialCoeff rp ρ lam, nhSphereCoeff rp ρ lam)))
      (𝓝[≠] 0) (𝓝 (ads2S2Coeffs rp ρ)) :=
  nearHorizon_coeffs_tendsto rp ρ hp hρ

/-- 極限の 2 次元部分の行列式条件：時間係数 × 動径係数 = 1。 -/
theorem ads2S2Coeffs_mul (rp ρ : ℝ) (hp : rp ≠ 0) (hρ : ρ ≠ 0) :
    (ρ ^ 2 / rp ^ 2) * (rp ^ 2 / ρ ^ 2) = 1 := by
  field_simp

/-- 時間係数の極限はポアンカレ因子 r₊²/u² に等しい（u = r₊²/ρ）。 -/
theorem ads2_timeCoeff_poincare (rp ρ : ℝ) (hp : rp ≠ 0) :
    ρ ^ 2 / rp ^ 2 = rp ^ 2 / (nhPoincareCoord rp ρ) ^ 2 := by
  unfold nhPoincareCoord
  field_simp
  ring

/-- 動径係数にヤコビアン (dρ/du)² = (r₊²/u²)² を掛けるとポアンカレ因子になる。 -/
theorem ads2_radialCoeff_poincare (rp ρ : ℝ) (hp : rp ≠ 0) (hρ : ρ ≠ 0) :
    (rp ^ 2 / ρ ^ 2) * (rp ^ 2 / (nhPoincareCoord rp ρ) ^ 2) ^ 2
      = rp ^ 2 / (nhPoincareCoord rp ρ) ^ 2 := by
  unfold nhPoincareCoord
  field_simp
  ring

/-- まとめ：極限の係数は AdS₂ × S² の形を満たす。時間係数 × 動径係数 = 1、
    時間係数はポアンカレ因子、動径係数はヤコビアン付きでポアンカレ因子、
    球面係数は r₊²（AdS₂ の半径と S² の半径がともに r₊）。 -/
theorem nearHorizon_AdS2xS2 (rp ρ : ℝ) (hp : rp ≠ 0) (hρ : ρ ≠ 0) :
    (ρ ^ 2 / rp ^ 2) * (rp ^ 2 / ρ ^ 2) = 1 ∧
    ρ ^ 2 / rp ^ 2 = rp ^ 2 / (nhPoincareCoord rp ρ) ^ 2 ∧
    (rp ^ 2 / ρ ^ 2) * (rp ^ 2 / (nhPoincareCoord rp ρ) ^ 2) ^ 2
      = rp ^ 2 / (nhPoincareCoord rp ρ) ^ 2 ∧
    (ads2S2Coeffs rp ρ).2.2 = rp ^ 2 :=
  ⟨ads2S2Coeffs_mul rp ρ hp hρ,
   ads2_timeCoeff_poincare rp ρ hp,
   ads2_radialCoeff_poincare rp ρ hp hρ,
   rfl⟩

end CFT.RNExtremalNearHorizon
