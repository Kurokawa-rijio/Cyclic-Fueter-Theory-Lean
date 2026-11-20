/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) の対応仮説への次の段：

  **対応仮説そのものの定式化**。`WedgeHorizonClassification` では対応仮説
  Ω(u, v) = c · f(ρ(u))（c > 0、ρ(u₀) = r₊、ρ′(u₀) ≠ 0）を各定理の仮定
  `hcorr` として渡していた。ここでは仮説を `HorizonCorrespondence`
  構造体として一つの Lean の対象にし、切片全体でのゼロ集合・符号の対応
  （`corr_zero_iff`・`corr_pos_iff`・`corr_neg_iff`）と、最初の地平線の
  f 側への移行（`corr_first_zero`・`corr_wedge_first_horizon`：Ω の最初
  のゼロは f の最初のゼロに移り、その手前では f > 0）を証明する。単純ゼロ
  の移行も構造体経由で分類表に接続する（`corr_simple_zero_iff`）。
  すなわち分類表の前提だった「対応仮説」が何を主張するのかが、構造体と
  その帰結として固定された。残りはこの仮説そのものの証明 — 実際のくさび
  解（4-17 の局所解とその延長）から ρ と c を構成すること。
-/
import Mathlib
import CFT.Spherical.WedgeHorizonFirstZero

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeFirstZero CFT.RNExtremalZero

namespace CFT.WedgeHorizonCorr

/-- 対応仮説：固定した v でのヌル切片上で、くさび解の共形因子 Ω が
    RN の計量関数 f の正の定数倍・再パラメータ化に等しいこと。 -/
structure HorizonCorrespondence (Om : ℝ → ℝ → ℝ) (v rp rm : ℝ) where
  c : ℝ
  ρ : ℝ → ℝ
  hc : 0 < c
  hcorr : ∀ u, Om u v = c * rnF rp rm (ρ u)

/-- 対応のもとでは、切片上での Ω のゼロ集合は f のゼロ集合（ρ 経由）と一致する。 -/
theorem corr_zero_iff {Om : ℝ → ℝ → ℝ} {v rp rm : ℝ}
    (H : HorizonCorrespondence Om v rp rm) (u : ℝ) :
    Om u v = 0 ↔ rnF rp rm (H.ρ u) = 0 := by
  rw [H.hcorr u]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt H.hc)
  · intro h
    rw [h, mul_zero]

/-- 対応のもとでは、Ω の正値性は f の正値性（ρ 経由）と一致する。 -/
theorem corr_pos_iff {Om : ℝ → ℝ → ℝ} {v rp rm : ℝ}
    (H : HorizonCorrespondence Om v rp rm) (u : ℝ) :
    0 < Om u v ↔ 0 < rnF rp rm (H.ρ u) := by
  rw [H.hcorr u]
  exact mul_pos_iff_of_pos_left H.hc

/-- 対応のもとでは、Ω の負値性は f の負値性（ρ 経由）と一致する。 -/
theorem corr_neg_iff {Om : ℝ → ℝ → ℝ} {v rp rm : ℝ}
    (H : HorizonCorrespondence Om v rp rm) (u : ℝ) :
    Om u v < 0 ↔ rnF rp rm (H.ρ u) < 0 := by
  rw [H.hcorr u]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, hx⟩ | ⟨hc', _⟩
    · exact hx
    · exact absurd hc' (not_lt_of_gt H.hc)
  · intro h
    exact mul_neg_of_pos_of_neg H.hc h

/-- 対応のもとでは、ρ(u₀) = r₊ なら u₀ は Ω のゼロ（地平線の候補）。 -/
theorem corr_zero_at_horizon {Om : ℝ → ℝ → ℝ} {v rp rm : ℝ}
    (H : HorizonCorrespondence Om v rp rm) {u₀ : ℝ} (hρ0 : H.ρ u₀ = rp) :
    Om u₀ v = 0 := by
  rw [H.hcorr u₀, hρ0, rnF_at_rp, mul_zero]

/-- 対応のもとでは、Ω の最初のゼロは f の最初のゼロに移る：その手前では
    f > 0 であり、f のゼロはすべてその地平線以上にある。 -/
theorem corr_first_zero {Om : ℝ → ℝ → ℝ} {v rp rm : ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn (fun u => Om u v) (Icc a b))
    (ha : 0 < Om a v) (hb : Om b v < 0)
    (H : HorizonCorrespondence Om v rp rm) :
    ∃ c ∈ Icc a b, rnF rp rm (H.ρ c) = 0 ∧
      (∀ u ∈ Ico a c, 0 < rnF rp rm (H.ρ u)) ∧
      ∀ z ∈ Icc a b, rnF rp rm (H.ρ z) = 0 → c ≤ z := by
  obtain ⟨c, hc, hfc, hpos, hmin⟩ := first_zero hab hf ha hb
  refine ⟨c, hc, (corr_zero_iff H c).mp hfc, ?_, ?_⟩
  · intro u hu
    exact (corr_pos_iff H u).mp (hpos u hu)
  · intro z hz hfz
    exact hmin z hz ((corr_zero_iff H z).mpr hfz)

/-- くさび解の版：`wedge_first_horizon` の最初の地平線は、対応のもとで
    f の最初のゼロに移る。 -/
theorem corr_wedge_first_horizon {a b : ℝ} {F : WedgeFields} {v : ℝ} {rp rm : ℝ}
    (ha : 0 ≤ a) (hv : v ∈ Icc (0 : ℝ) b) (hC2 : C2On a b F.Om)
    (hpos : 0 < F.Om 0 v) (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (H : HorizonCorrespondence F.Om v rp rm) :
    ∃ c ∈ Icc (0 : ℝ) a, rnF rp rm (H.ρ c) = 0 ∧
      (∀ u ∈ Ico (0 : ℝ) c, 0 < rnF rp rm (H.ρ u)) ∧
      ∀ z ∈ Icc (0 : ℝ) a, rnF rp rm (H.ρ z) = 0 → c ≤ z := by
  obtain ⟨c, hc, hfc, hpos', hmin⟩ := wedge_first_horizon ha hv hC2 hpos hneg
  refine ⟨c, hc, (corr_zero_iff H c).mp hfc, ?_, ?_⟩
  · intro u hu
    exact (corr_pos_iff H u).mp (hpos' u hu)
  · intro z hz hfz
    exact hmin z hz ((corr_zero_iff H z).mpr hfz)

/-- 構造体経由での単純ゼロの移行：分類表（`wedgeOmega_simple_zero_iff`）への接続。 -/
theorem corr_simple_zero_iff {Om : ℝ → ℝ → ℝ} {v rp rm : ℝ}
    (H : HorizonCorrespondence Om v rp rm) {u₀ : ℝ} (hρ0 : H.ρ u₀ = rp)
    (hρ : DifferentiableAt ℝ H.ρ u₀) (hρd : deriv H.ρ u₀ ≠ 0) (hp : rp ≠ 0) :
    CFT.WedgeHorizon.SimpleZero (fun u => Om u v) u₀ ↔
      CFT.WedgeHorizon.SimpleZero (rnF rp rm) rp :=
  CFT.WedgeHorizon.wedgeOmega_simple_zero_iff H.hc hρ0 hρ hρd H.hcorr hp

end CFT.WedgeHorizonCorr
