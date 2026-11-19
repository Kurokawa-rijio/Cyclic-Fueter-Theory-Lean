/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) のくさび EYM 系の形での分類への一段（2026-11-19）：

  4-17 の局所解（`wedge_local_existence_gen`：角で r > 0、Ω > 0 の C¹
  データに対し、角の近くの正方形 [0,ε]² の上で r、Ω ≥ r₀ > 0 の解がある）
  について、その正方形の上では Ω も r もゼロを持たないこと。
  すなわち、地平線（Ω の一次ゼロ）も極端地平線・喉（Ω の二重ゼロ）も、
  局所存在の正方形の中には現れない。結合 A = Ω/(2r²) についても同じ
  正方形の上でゼロを持たず、角での値は明示式
  A(0,0) = φ 1 0 / (2 * (φ 0 0)²) > 0 をとる。

  鍵は 4-17 の結論そのもの（r₀ ≤ r、r₀ ≤ Ω、r₀ > 0）で、ゼロの位数の
  移行（`wedgeA_eq_zero_iff`）により Ω の非ゼロ性が A にそのまま移る。
  残りは、実際のくさび解の Ω のゼロと地平線・喉との対応づけの本体
  （4-17 の局所解と 9-3 の喉の発散への接続）：正方形の外で Ω がゼロに
  なる場合の分類は、局所存在の範囲を超えるためここでは扱わない。
-/
import CFT.Spherical.WedgeLocalExistenceGeneral
import CFT.Spherical.WedgeOmegaZeroOrder

open Real Set Filter Topology CFT.Wedge CFT.WedgeExist CFT.WedgeUniq CFT.WedgeExistGen
  CFT.WedgeOmegaZero CFT.WedgeBalance

namespace CFT.WedgeLocalNoZero

/-- 4-17 の局所解は、その正方形の上では Ω も r もゼロを持たない。
    角での値はデータで決まる（角条件の値の部分）。 -/
theorem wedge_local_no_zero (φ ψ : Fin 3 → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h00 : ∀ i, φ i 0 = ψ i 0)
    (hr : 0 < φ 0 0) (hO : 0 < φ 1 0) :
    ∃ ε > 0, ∃ r₀ > 0, ∃ F : WedgeFields, WedgeEqsOn ε ε F ∧ GenDataOn ε ε φ ψ F
      ∧ (∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, r₀ ≤ F.r u v ∧ r₀ ≤ F.Om u v)
      ∧ (∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, F.Om u v ≠ 0 ∧ F.r u v ≠ 0)
      ∧ F.r 0 0 = φ 0 0 ∧ F.Om 0 0 = φ 1 0 ∧ F.W 0 0 = φ 2 0 := by
  obtain ⟨ε, hε, r₀, hr₀, F, eF, dF, _, _, _, pF⟩ :=
    wedge_local_existence_gen φ ψ hφ hψ h00 hr hO
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) ε := ⟨le_refl 0, hε.le⟩
  refine ⟨ε, hε, r₀, hr₀, F, ?_⟩
  refine ⟨eF, dF, pF, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨h1, h2⟩ := pF u hu v hv
    exact ⟨ne_of_gt (lt_of_lt_of_le hr₀ h2), ne_of_gt (lt_of_lt_of_le hr₀ h1)⟩
  · exact (dF.1 0 h0).1
  · exact (dF.1 0 h0).2.1
  · exact (dF.1 0 h0).2.2

/-- 4-17 の局所解について、結合 A = Ω/(2r²) も同じ正方形の上でゼロを持たない。
    Ω の非ゼロ性がゼロの位数の移行（`wedgeA_eq_zero_iff`）で A に移る。 -/
theorem wedge_local_coupling_ne_zero (φ ψ : Fin 3 → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h00 : ∀ i, φ i 0 = ψ i 0)
    (hr : 0 < φ 0 0) (hO : 0 < φ 1 0) :
    ∃ ε > 0, ∃ r₀ : ℝ, r₀ > 0 ∧ ∃ F : WedgeFields, WedgeEqsOn ε ε F ∧ GenDataOn ε ε φ ψ F
      ∧ ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, wedgeAFun F.Om F.r u v ≠ 0 := by
  obtain ⟨ε, hε, r₀, hr₀, F, eF, dF, _, hnz, _, _, _⟩ :=
    wedge_local_no_zero φ ψ hφ hψ h00 hr hO
  refine ⟨ε, hε, r₀, hr₀, F, eF, dF, fun u hu v hv => ?_⟩
  obtain ⟨hOm, hr⟩ := hnz u hu v hv
  exact fun h => hOm ((wedgeA_eq_zero_iff hr).mp h)

/-- 角での結合の値：A(0,0) = φ 1 0 / (2 * (φ 0 0)²) > 0。 -/
theorem wedge_local_coupling_corner (φ ψ : Fin 3 → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h00 : ∀ i, φ i 0 = ψ i 0)
    (hr : 0 < φ 0 0) (hO : 0 < φ 1 0) :
    ∃ ε > 0, ∃ r₀ : ℝ, r₀ > 0 ∧ ∃ F : WedgeFields, WedgeEqsOn ε ε F ∧ GenDataOn ε ε φ ψ F
      ∧ wedgeAFun F.Om F.r 0 0 = φ 1 0 / (2 * (φ 0 0) ^ 2)
      ∧ 0 < wedgeAFun F.Om F.r 0 0 := by
  obtain ⟨ε, hε, r₀, hr₀, F, eF, dF, _, _, hr00, hO00, _⟩ :=
    wedge_local_no_zero φ ψ hφ hψ h00 hr hO
  refine ⟨ε, hε, r₀, hr₀, F, eF, dF, ?_, ?_⟩
  · show F.Om 0 0 / (2 * (F.r 0 0) ^ 2) = φ 1 0 / (2 * (φ 0 0) ^ 2)
    rw [hr00, hO00]
  · rw [show wedgeAFun F.Om F.r 0 0 = φ 1 0 / (2 * (φ 0 0) ^ 2) by
      show F.Om 0 0 / (2 * (F.r 0 0) ^ 2) = φ 1 0 / (2 * (φ 0 0) ^ 2)
      rw [hr00, hO00]]
    exact div_pos hO (mul_pos two_pos (pow_pos hr 2))

end CFT.WedgeLocalNoZero
