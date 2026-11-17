import Mathlib
import CFT.Spherical.WedgeEYMSystem

/-!
  命題集 `LEAN_GAP_TREES.md` 9-1（シュワルツシルト極限：方程式の部分）：
  物質場（ゲージ場 W）を消した極限で、くさびの EYM 系が真空のアインシュタイン方程式に
  戻ることを示す。W ≡ 1 はヘッジホッグ・アンザッツの真空（場の強さ F = 0）で、
  このとき W 方程式は 0 = 0 になり、r 方程式と Ω 方程式からは (1 − W²)² の項が
  消えて、二重ヌル座標での真空方程式
    r_uv = −Ω/(2r) − r_u r_v/r
    Ω_uv = Ω_u Ω_v/Ω − 2Ω r_uv/r
  が残る。拘束も W の項が消えて真空の形になる。逆に真空の解は W ≡ 1 を付けて
  EYM 系の解に持ち上がる。すなわち方程式のレベルでは EYM 系と真空系は
  W ≡ 1 のもとで同値である。
  残り：二重ヌル座標でのシュワルツシルト解そのものの明示（r と Ω を u + v の
  関数として書くこと）と、ミスナー–シャープ質量の保存（真空では質量が定数に
  なること）。観測量の側（T = 1/(8πM)）は 6-1 で既に証明済み。
-/

namespace CFT.WedgeVacuum

open CFT.Wedge
open Real

/-- 真空の r 方程式の右辺（W ≡ 1 と置いた `rhsR`）。 -/
noncomputable def vacRhsR (Om ru rv r : ℝ) : ℝ :=
  -Om / (2 * r) - ru * rv / r

/-- 真空の Ω 方程式の右辺（W ≡ 1 と置いた `rhsOm`）。 -/
noncomputable def vacRhsOm (Om Ou Ov ruv r : ℝ) : ℝ :=
  Ou * Ov / Om - 2 * Om * ruv / r

/-- W ≡ 1 のとき `rhsR` は真空の右辺になる（(1 − 1²)² = 0）。 -/
theorem rhsR_one (Om ru rv r : ℝ) : rhsR Om 1 ru rv r = vacRhsR Om ru rv r := by
  simp [rhsR, vacRhsR]
  ring

/-- W ≡ 1 のとき `rhsOm` は真空の右辺になる（(1 − 1²)² = 0）。 -/
theorem rhsOm_one (Om Ou Ov ruv r : ℝ) :
    rhsOm Om Ou Ov ruv r 1 = vacRhsOm Om Ou Ov ruv r := by
  simp [rhsOm, vacRhsOm]

/-- W ≡ 1 のとき W 方程式の右辺は 0（場の強さが消える）。 -/
theorem rhsW_one (Om r : ℝ) : rhsW Om 1 r = 0 := by
  simp [rhsW]

/-- 定数関数の u 微分は 0。 -/
theorem Du_const (c : ℝ) (u v : ℝ) : Du (fun _ _ => c) u v = 0 := by
  simp [Du]

/-- 定数関数の v 微分は 0。 -/
theorem Dv_const (c : ℝ) (u v : ℝ) : Dv (fun _ _ => c) u v = 0 := by
  simp [Dv]

/-- 定数関数の混合微分は 0。 -/
theorem Duv_const (c : ℝ) (u v : ℝ) : Duv (fun _ _ => c) u v = 0 := by
  simp [Duv]

/-- 真空の未知関数（動径 r、計量関数 Ω）。W ≡ 1 の EYM 場からゲージ場を落としたもの。 -/
structure VacuumFields where
  r : ℝ → ℝ → ℝ
  Om : ℝ → ℝ → ℝ

/-- 真空の発展方程式（r 方程式と Ω 方程式）。 -/
def VacuumEvolutionEqs (G : VacuumFields) : Prop :=
  ∀ u v, Duv G.r u v = vacRhsR (G.Om u v) (Du G.r u v) (Dv G.r u v) (G.r u v)
    ∧ Duv G.Om u v
        = vacRhsOm (G.Om u v) (Du G.Om u v) (Dv G.Om u v) (Duv G.r u v) (G.r u v)

/-- 真空の拘束（W の項を落とした C_u、C_v）。 -/
def VacuumConstraints (G : VacuumFields) : Prop :=
  ∀ u v, Duu G.r u v - (Du G.Om u v / G.Om u v) * Du G.r u v = 0
    ∧ Dvv G.r u v - (Dv G.Om u v / G.Om u v) * Dv G.r u v = 0

/-- EYM 系の解で W ≡ 1 なら、その (r, Ω) は真空の発展方程式を満たす。 -/
theorem vacuumEvolution_of_wedge (F : WedgeFields)
    (hE : WedgeEvolutionEqs F) (hW : ∀ u v, F.W u v = 1) :
    VacuumEvolutionEqs ⟨F.r, F.Om⟩ := by
  intro u v
  obtain ⟨hR, hOm, -⟩ := hE u v
  rw [hW u v] at hR
  rw [rhsR_one] at hR
  rw [hW u v] at hOm
  rw [rhsOm_one] at hOm
  exact ⟨hR, hOm⟩

/-- EYM 系の拘束で W ≡ 1 なら、その (r, Ω) は真空の拘束を満たす。 -/
theorem vacuumConstraints_of_wedge (F : WedgeFields)
    (hC : WedgeConstraints F) (hW : ∀ u v, F.W u v = 1) :
    VacuumConstraints ⟨F.r, F.Om⟩ := by
  intro u v
  obtain ⟨hCu, hCv⟩ := hC u v
  have hWfun : F.W = fun _ _ => 1 := funext fun u => funext fun v => hW u v
  have hDuW : Du F.W u v = 0 := by
    rw [hWfun]
    simp [Du]
  have hDvW : Dv F.W u v = 0 := by
    rw [hWfun]
    simp [Dv]
  rw [hDuW] at hCu
  rw [hDvW] at hCv
  constructor
  · simpa using hCu
  · simpa using hCv

/-- 真空の解に W ≡ 1 を付けると EYM 系の発展方程式を満たす。 -/
theorem wedgeEvolution_of_vacuum (G : VacuumFields)
    (hE : VacuumEvolutionEqs G) :
    WedgeEvolutionEqs ⟨G.r, G.Om, fun _ _ => 1⟩ := by
  intro u v
  obtain ⟨hR, hOm⟩ := hE u v
  refine ⟨?_, ?_, ?_⟩
  · show Duv G.r u v = rhsR (G.Om u v) 1 (Du G.r u v) (Dv G.r u v) (G.r u v)
    rw [rhsR_one]
    exact hR
  · show Duv G.Om u v
        = rhsOm (G.Om u v) (Du G.Om u v) (Dv G.Om u v) (Duv G.r u v) (G.r u v) 1
    rw [rhsOm_one]
    exact hOm
  · show Duv (fun _ _ => (1 : ℝ)) u v = rhsW (G.Om u v) 1 (G.r u v)
    rw [Duv_const, rhsW_one]

/-- 真空の拘束を満たす (r, Ω) に W ≡ 1 を付けると EYM 系の拘束を満たす。 -/
theorem wedgeConstraints_of_vacuum (G : VacuumFields)
    (hC : VacuumConstraints G) :
    WedgeConstraints ⟨G.r, G.Om, fun _ _ => 1⟩ := by
  intro u v
  obtain ⟨hCu, hCv⟩ := hC u v
  constructor
  · show Duu G.r u v - (Du G.Om u v / G.Om u v) * Du G.r u v
        + 2 * (Du (fun _ _ => (1 : ℝ)) u v) ^ 2 / G.r u v = 0
    rw [Du_const]
    simpa using hCu
  · show Dvv G.r u v - (Dv G.Om u v / G.Om u v) * Dv G.r u v
        + 2 * (Dv (fun _ _ => (1 : ℝ)) u v) ^ 2 / G.r u v = 0
    rw [Dv_const]
    simpa using hCv

/-- 方程式のレベルでの同値：真空の発展方程式 ⟺ W ≡ 1 の EYM 発展方程式。 -/
theorem vacuumEvolution_iff (G : VacuumFields) :
    VacuumEvolutionEqs G ↔ WedgeEvolutionEqs ⟨G.r, G.Om, fun _ _ => 1⟩ :=
  ⟨wedgeEvolution_of_vacuum G,
    fun h => vacuumEvolution_of_wedge _ h (fun _ _ => rfl)⟩

/-- 拘束のレベルでの同値：真空の拘束 ⟺ W ≡ 1 の EYM 拘束。 -/
theorem vacuumConstraints_iff (G : VacuumFields) :
    VacuumConstraints G ↔ WedgeConstraints ⟨G.r, G.Om, fun _ _ => 1⟩ :=
  ⟨wedgeConstraints_of_vacuum G,
    fun h => vacuumConstraints_of_wedge _ h (fun _ _ => rfl)⟩

end CFT.WedgeVacuum
