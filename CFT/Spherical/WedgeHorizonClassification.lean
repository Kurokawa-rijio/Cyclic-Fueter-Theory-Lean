/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) のくさび EYM 系の形での分類の本体への一段：

  **対応仮説のもとでの分類表**。対応仮説とは、くさび解の共形因子 Ω が
  固定した v でのヌル切片上で、RN の計量関数 f(r) = (r − r₊)(r − r₋)/r²
  の正の定数倍・単調な再パラメータ化に等しいこと：
    Ω(u, v) = c · f(ρ(u))、c > 0、ρ(u₀) = r₊、ρ′(u₀) ≠ 0。
  この仮説のもとでは、Ω のゼロの位数から分類表のすべてが従う：

  * Ω の単純ゼロ ⟺ f の単純ゼロ ⟺ T > 0（有限温度の通常地平面）、
    喉の固有距離は有限（発散しない）；
  * Ω の二重以上のゼロ ⟺ f の二重ゼロ ⟺ 極端（r₊ = r₋）・T = 0、
    喉の固有距離は +∞（無限の喉）、近地平線極限は AdS₂ × S²。

  すでに証明済みの部品（`RNExtremalDoubleZero`：f のゼロの位数と温度の
  対応、`ExtremalThroatLength`／`NonextremalThroatLength`：喉の発散・
  有限性、`RNExtremalNearHorizon`：近地平線極限、`WedgeOmegaZeroOrder`：
  Ω のゼロの位数から結合 A = Ω/(2r²) への移行）を組み合わせる。
  残りは対応仮説そのものの証明 — 実際のくさび解（4-17 の局所解とその
  延長）と RN 側の地平線・喉との対応づけ。すなわちこの一段で、(b) の
  本体の残りは「対応仮説」という一つの明示的な仮説に集約された。
-/
import Mathlib
import CFT.Quantum.RNExtremalDoubleZero
import CFT.Quantum.RNExtremalNearHorizon
import CFT.Quantum.ExtremalThroatLength
import CFT.Quantum.NonextremalThroatLength
import CFT.Spherical.WedgeOmegaZeroOrder

open Real Filter Topology intervalIntegral

namespace CFT.WedgeHorizon

/-- 一次（単純）ゼロ：値が 0 で 1 階微分が ≠ 0。 -/
def SimpleZero (g : ℝ → ℝ) (x : ℝ) : Prop := g x = 0 ∧ deriv g x ≠ 0

/-- 二重以上のゼロ：値と 1 階微分がともに 0。 -/
def DoubleZeroOrMore (g : ℝ → ℝ) (x : ℝ) : Prop := g x = 0 ∧ deriv g x = 0

section Correspondence

variable {Om : ℝ → ℝ → ℝ} {v u₀ rp rm : ℝ} {ρ : ℝ → ℝ} {c : ℝ} {R : ℝ}

/-- 対応仮説のもとでの連鎖律：Ω の切片の微分は f′(r₊) の定数倍。 -/
theorem wedgeOmega_deriv_at_horizon (hρ0 : ρ u₀ = rp) (hρ : DifferentiableAt ℝ ρ u₀)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u)) (hp : rp ≠ 0) :
    deriv (fun u => Om u v) u₀
      = c * deriv (CFT.RNExtremalZero.rnF rp rm) rp * deriv ρ u₀ := by
  have hfun : (fun u => Om u v)
      = fun u => c * CFT.RNExtremalZero.rnF rp rm (ρ u) := funext hcorr
  have h1 : HasDerivAt (fun u => CFT.RNExtremalZero.rnF rp rm (ρ u))
      ((rp - rm) / rp ^ 2 * deriv ρ u₀) u₀ := by
    have hf : HasDerivAt (CFT.RNExtremalZero.rnF rp rm) ((rp - rm) / rp ^ 2) (ρ u₀) := by
      rw [hρ0]
      exact CFT.RNExtremalZero.rnF_hasDerivAt rp rm hp
    exact hf.comp u₀ hρ.hasDerivAt
  have h2d : deriv (fun u => c * CFT.RNExtremalZero.rnF rp rm (ρ u)) u₀
      = c * ((rp - rm) / rp ^ 2 * deriv ρ u₀) := (h1.const_mul c).deriv
  rw [hfun, h2d, CFT.RNExtremalZero.rnF_deriv_at_rp rp rm hp]
  ring

/-- 対応仮説のもとでのゼロの一致：Ω(u₀) = 0 ⟺ f(r₊) = 0。 -/
theorem wedgeOmega_zero_iff (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u)) :
    Om u₀ v = 0 ↔ CFT.RNExtremalZero.rnF rp rm rp = 0 := by
  rw [hcorr u₀, hρ0]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hc)
  · intro h
    rw [h, mul_zero]

/-- 対応仮説のもとでの単純ゼロの移行：Ω の単純ゼロ ⟺ f の単純ゼロ。 -/
theorem wedgeOmega_simple_zero_iff (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u)) (hp : rp ≠ 0) :
    SimpleZero (fun u => Om u v) u₀
      ↔ SimpleZero (CFT.RNExtremalZero.rnF rp rm) rp := by
  constructor
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeOmega_zero_iff hc hρ0 hcorr).mp h0, ?_⟩
    rw [wedgeOmega_deriv_at_horizon hρ0 hρ hcorr hp] at hd
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).2
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeOmega_zero_iff hc hρ0 hcorr).mpr h0, ?_⟩
    rw [wedgeOmega_deriv_at_horizon hρ0 hρ hcorr hp]
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hc) hd) hρd

/-- 対応仮説のもとでの二重以上のゼロの移行。 -/
theorem wedgeOmega_doubleZeroOrMore_iff (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u)) (hp : rp ≠ 0) :
    DoubleZeroOrMore (fun u => Om u v) u₀
      ↔ DoubleZeroOrMore (CFT.RNExtremalZero.rnF rp rm) rp := by
  constructor
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeOmega_zero_iff hc hρ0 hcorr).mp h0, ?_⟩
    rw [wedgeOmega_deriv_at_horizon hρ0 hρ hcorr hp] at hd
    rcases mul_eq_zero.mp hd with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (ne_of_gt hc)
      · exact h'
    · exact absurd h hρd
  · rintro ⟨h0, hd⟩
    refine ⟨(wedgeOmega_zero_iff hc hρ0 hcorr).mpr h0, ?_⟩
    rw [wedgeOmega_deriv_at_horizon hρ0 hρ hcorr hp, hd]
    simp

/-- 単純ゼロなら温度は正（有限温度の通常地平面）。 -/
theorem wedgeOmega_simple_zero_pos_temperature (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u))
    (hp : 0 < rp) (hm : rm < rp) :
    SimpleZero (fun u => Om u v) u₀ →
      deriv (CFT.RNExtremalZero.rnF rp rm) rp ≠ 0
        ∧ 0 < (rp - rm) / (4 * π * rp ^ 2) := by
  intro h
  exact ⟨((wedgeOmega_simple_zero_iff hc hρ0 hρ hρd hcorr (ne_of_gt hp)).mp h).2,
    (CFT.RNExtremalZero.rn_simple_zero_pos_temperature rp rm hp hm).2⟩

/-- 二重以上のゼロなら極端（r₊ = r₋）で温度は 0。 -/
theorem wedgeOmega_double_zero_extremal (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u)) (hp : rp ≠ 0) :
    DoubleZeroOrMore (fun u => Om u v) u₀ →
      rp = rm ∧ (rp - rm) / (4 * π * rp ^ 2) = 0 := by
  intro h
  have hd : deriv (CFT.RNExtremalZero.rnF rp rm) rp = 0 :=
    ((wedgeOmega_doubleZeroOrMore_iff hc hρ0 hρ hρd hcorr hp).mp h).2
  have hEq : rp = rm :=
    (CFT.RNExtremalZero.rnF_deriv_at_rp_eq_zero_iff rp rm hp).mp hd
  exact ⟨hEq, (CFT.RNExtremalZero.rn_temperature_zero_iff rp rm hp).mpr hEq⟩

/-- 二重以上のゼロなら喉の固有距離は +∞（無限の喉）。 -/
theorem wedgeOmega_double_zero_infinite_throat (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u))
    (hp : 0 < rp) (hR : 0 < R) :
    DoubleZeroOrMore (fun u => Om u v) u₀ →
      Tendsto (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R),
        (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹) (𝓝[>] 0) atTop := by
  intro h
  have hEq : rp = rm :=
    (wedgeOmega_double_zero_extremal hc hρ0 hρ hρd hcorr (ne_of_gt hp) h).1
  rw [← hEq]
  exact CFT.ExtremalThroat.extremal_throat_infinite rp R hp hR

/-- 二重以上のゼロなら近地平線極限は AdS₂ × S²（σ は近地平線座標）。 -/
theorem wedgeOmega_double_zero_near_horizon {σ : ℝ} (hp : rp ≠ 0) (hσ : σ ≠ 0) :
    DoubleZeroOrMore (fun u => Om u v) u₀ →
      Tendsto (fun lam : ℝ => (CFT.RNExtremalNearHorizon.nhTimeCoeff rp σ lam,
        (CFT.RNExtremalNearHorizon.nhRadialCoeff rp σ lam,
          CFT.RNExtremalNearHorizon.nhSphereCoeff rp σ lam)))
        (𝓝[≠] 0) (𝓝 (CFT.RNExtremalNearHorizon.ads2S2Coeffs rp σ)) := by
  intro _
  exact CFT.RNExtremalNearHorizon.nearHorizon_tendsto_ads2S2Coeffs rp σ hp hσ

/-- 単純ゼロなら喉の固有距離は有限（一様に有界）。 -/
theorem wedgeOmega_simple_zero_finite_throat (hm : 0 < rm) (hp : 0 < rp)
    (hmp : rm < rp) (hR : 0 < R) :
    SimpleZero (fun u => Om u v) u₀ →
      ∀ ε ∈ Set.Ioo 0 R,
        0 ≤ ∫ x in (rp + ε)..(rp + R),
            (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
          ∧ ∫ x in (rp + ε)..(rp + R),
              (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹
            ≤ ((rp + R) / Real.sqrt (rp - rm)) * (2 * Real.sqrt R) := by
  intro _
  exact CFT.NonextremalThroat.nonextremal_throat_finite rm rp R hm hmp hp hR

/-- 結合 A の単純ゼロも同じ分類に従う（Ω からの移行による）。 -/
theorem wedgeA_simple_zero_iff_rn {r : ℝ → ℝ → ℝ} (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u))
    (hOm : DifferentiableAt ℝ (fun u' => Om u' v) u₀)
    (hr : DifferentiableAt ℝ (fun u' => r u' v) u₀)
    (hr0 : r u₀ v ≠ 0) (hp : rp ≠ 0) :
    SimpleZero (fun u => CFT.WedgeBalance.wedgeAFun Om r u v) u₀
      ↔ SimpleZero (CFT.RNExtremalZero.rnF rp rm) rp := by
  constructor
  · rintro ⟨h0, hd⟩
    have hd' : CFT.Wedge.Du (CFT.WedgeBalance.wedgeAFun Om r) u₀ v ≠ 0 := hd
    have h := (CFT.WedgeOmegaZero.wedgeA_simple_zero_u hOm hr hr0).mp ⟨h0, hd'⟩
    exact (wedgeOmega_simple_zero_iff hc hρ0 hρ hρd hcorr hp).mp ⟨h.1, h.2⟩
  · rintro ⟨h0, hd⟩
    have h := (wedgeOmega_simple_zero_iff hc hρ0 hρ hρd hcorr hp).mpr ⟨h0, hd⟩
    have h' := (CFT.WedgeOmegaZero.wedgeA_simple_zero_u hOm hr hr0).mpr ⟨h.1, h.2⟩
    exact ⟨h'.1, h'.2⟩

/-- 結合 A の二重以上のゼロも同じ分類に従う（Ω からの移行による）。 -/
theorem wedgeA_doubleZeroOrMore_iff_rn {r : ℝ → ℝ → ℝ} (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u))
    (hOm : DifferentiableAt ℝ (fun u' => Om u' v) u₀)
    (hr : DifferentiableAt ℝ (fun u' => r u' v) u₀)
    (hr0 : r u₀ v ≠ 0) (hp : rp ≠ 0) :
    DoubleZeroOrMore (fun u => CFT.WedgeBalance.wedgeAFun Om r u v) u₀
      ↔ DoubleZeroOrMore (CFT.RNExtremalZero.rnF rp rm) rp := by
  constructor
  · rintro ⟨h0, hd⟩
    have hd' : CFT.Wedge.Du (CFT.WedgeBalance.wedgeAFun Om r) u₀ v = 0 := hd
    have h := (CFT.WedgeOmegaZero.wedgeA_zero_deriv_zero_u hOm hr hr0).mp ⟨h0, hd'⟩
    exact (wedgeOmega_doubleZeroOrMore_iff hc hρ0 hρ hρd hcorr hp).mp ⟨h.1, h.2⟩
  · rintro ⟨h0, hd⟩
    have h := (wedgeOmega_doubleZeroOrMore_iff hc hρ0 hρ hρd hcorr hp).mpr ⟨h0, hd⟩
    have h' := (CFT.WedgeOmegaZero.wedgeA_zero_deriv_zero_u hOm hr hr0).mpr ⟨h.1, h.2⟩
    exact ⟨h'.1, h'.2⟩

/-- まとめ：対応仮説のもとでの分類表。単純ゼロ ⟺ 有限温度・有限の喉、
    二重以上のゼロ ⟺ 極端・T = 0・無限の喉・近地平線 AdS₂ × S²。 -/
theorem wedge_horizon_classification (hc : 0 < c) (hρ0 : ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ ρ u₀) (hρd : deriv ρ u₀ ≠ 0)
    (hcorr : ∀ u, Om u v = c * CFT.RNExtremalZero.rnF rp rm (ρ u))
    (hp : 0 < rp) (hm : 0 < rm) (hmp : rm < rp)
    (hR : 0 < R) {σ : ℝ} (hσ : σ ≠ 0) :
    (SimpleZero (fun u => Om u v) u₀ →
      0 < (rp - rm) / (4 * π * rp ^ 2) ∧
      ¬ Tendsto (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R),
        (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹) (𝓝[>] 0) atTop) ∧
    (DoubleZeroOrMore (fun u => Om u v) u₀ →
      rp = rm ∧ (rp - rm) / (4 * π * rp ^ 2) = 0 ∧
      Tendsto (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R),
        (Real.sqrt (CFT.RNExtremalZero.rnF rp rm x))⁻¹) (𝓝[>] 0) atTop ∧
      Tendsto (fun lam : ℝ => (CFT.RNExtremalNearHorizon.nhTimeCoeff rp σ lam,
        (CFT.RNExtremalNearHorizon.nhRadialCoeff rp σ lam,
          CFT.RNExtremalNearHorizon.nhSphereCoeff rp σ lam)))
        (𝓝[≠] 0) (𝓝 (CFT.RNExtremalNearHorizon.ads2S2Coeffs rp σ))) := by
  refine ⟨fun h => ⟨(wedgeOmega_simple_zero_pos_temperature hc hρ0 hρ hρd hcorr hp hmp h).2,
      CFT.NonextremalThroat.nonextremal_throat_not_tendsto_atTop rm rp R hm hmp hp hR⟩,
    fun h => ⟨(wedgeOmega_double_zero_extremal hc hρ0 hρ hρd hcorr (ne_of_gt hp) h).1,
      (wedgeOmega_double_zero_extremal hc hρ0 hρ hρd hcorr (ne_of_gt hp) h).2,
      wedgeOmega_double_zero_infinite_throat hc hρ0 hρ hρd hcorr hp hR h,
      wedgeOmega_double_zero_near_horizon (ne_of_gt hp) hσ h⟩⟩

end Correspondence

end CFT.WedgeHorizon
