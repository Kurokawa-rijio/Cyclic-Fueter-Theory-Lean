import CFT.Foundations.WedgeRhsLipschitz
import CFT.Foundations.WedgeIterationMap

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の第3層 (c)：矩形の小ささによる C¹ ノルムでの縮小評価 — の第2段。
  C¹ ノルム（矩形上の値・1階微分の sup ノルムの束）とジェット距離の定義、
  および反復写像の像の値の部分の縮小（面積因子 (u - u₀)(v - v₀) つき）を証明する。

  値の部分の縮小の要点：反復写像の像は特性データと凍結右辺の二重積分で
  表されるので、2つの凍結場に対する像の差は二重積分の差に等しい。
  凍結右辺の差は第1段（`CFT.Foundations.WedgeRhsLipschitz`）のリプシッツ評価で
  ジェット距離 D で抑えられ、二重積分の差は面積 × (定数 × D) で抑えられる。
  微分の部分の縮小（像の偏微分の差）は次の段。

  残り（4-17 の第3層 (c) の組み立て）：微分の部分の縮小と、C¹ ノルム全体での
  縮小（矩形を小さく取れば縮小定数 < 1）の証明。
  キャップ（r = 0）を含む版は 4-16 に残る。
-/

namespace CFT.WedgeC1

open MeasureTheory intervalIntegral
open scoped Interval Topology
open CFT.WaveIntegralEq
open CFT.Wedge
open CFT.WedgeRhsLip
open CFT.WedgeIterate

noncomputable section

/-- 矩形 [u₀, u] × [v₀, v] 上のスカラー関数の sup ノルム。 -/
noncomputable def supNormRect (f : ℝ → ℝ → ℝ) (u₀ u v₀ v : ℝ) : ℝ :=
  sSup { x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t| }

/-- 矩形上の各点評価が M で抑えられれば sup ノルムも M で抑えられる。 -/
theorem supNormRect_le {f : ℝ → ℝ → ℝ} {u₀ u v₀ v M : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (h : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |f s t| ≤ M) :
    supNormRect f u₀ u v₀ v ≤ M := by
  have hne : { x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t| }.Nonempty :=
    ⟨|f u₀ v₀|, ⟨u₀, Set.left_mem_Icc.mpr hu, v₀, Set.left_mem_Icc.mpr hv, rfl⟩⟩
  apply csSup_le hne
  rintro x ⟨s, hs, t, ht, rfl⟩
  exact h s hs t ht

/-- sup ノルムは非負である。 -/
theorem supNormRect_nonneg {f : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v) :
    0 ≤ supNormRect f u₀ u v₀ v := by
  show (0:ℝ) ≤ sSup { x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t| }
  by_cases hBdd : BddAbove { x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t| }
  · exact le_csSup_of_le hBdd
      ⟨u₀, Set.left_mem_Icc.mpr hu, v₀, Set.left_mem_Icc.mpr hv, rfl⟩ (abs_nonneg _)
  · rw [Real.sSup_of_not_bddAbove hBdd]

/-- 矩形上の各点評価が M で抑えられれば、sup ノルムを取る集合は上に有界である。 -/
theorem bddAbove_supNormRect_set {f : ℝ → ℝ → ℝ} {u₀ u v₀ v M : ℝ}
    (h : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |f s t| ≤ M) :
    BddAbove { x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t| } :=
  ⟨M, by rintro x ⟨s, hs, t, ht, rfl⟩; exact h s hs t ht⟩

/-- 上に有界ならば、矩形内の各点評価は sup ノルムで抑えられる。 -/
theorem le_supNormRect {f : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ}
    (hBdd : BddAbove { x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t| })
    {s t : ℝ} (hs : s ∈ Set.Icc u₀ u) (ht : t ∈ Set.Icc v₀ v) :
    |f s t| ≤ supNormRect f u₀ u v₀ v :=
  le_csSup hBdd ⟨s, hs, t, ht, rfl⟩

/-- 2つの場の C¹ 距離：矩形上の値と1階微分（r, Ω, W の各成分）の
    sup ノルムの最大値。 -/
noncomputable def wedgeC1Dist (F G : WedgeFields) (u₀ u v₀ v : ℝ) : ℝ :=
  max (supNormRect (fun s t => F.r s t - G.r s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => F.Om s t - G.Om s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => F.W s t - G.W s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => Du F.r s t - Du G.r s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => Dv F.r s t - Dv G.r s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => Du F.Om s t - Du G.Om s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => Dv F.Om s t - Dv G.Om s t) u₀ u v₀ v)
  (max (supNormRect (fun s t => Du F.W s t - Du G.W s t) u₀ u v₀ v)
       (supNormRect (fun s t => Dv F.W s t - Dv G.W s t) u₀ u v₀ v))))))))

/-- 2つの場のジェット距離：C¹ 距離に Ω 方程式の右辺が依存する
    r の混合微分 Duv r の差の sup ノルムを加えたもの。 -/
noncomputable def wedgeJetDist (F G : WedgeFields) (u₀ u v₀ v : ℝ) : ℝ :=
  max (wedgeC1Dist F G u₀ u v₀ v)
    (supNormRect (fun s t => Duv F.r s t - Duv G.r s t) u₀ u v₀ v)

/-- 矩形上の場の値・微分に対する一様な上界（両方の場について）。
    縮小評価の仮定を束ねたもの。 -/
structure WedgeRectBounds (F G : WedgeFields) (u₀ u v₀ v : ℝ)
    (M_Om M_W M_r r₀ Om₀ : ℝ) : Prop where
  rF_ge : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, r₀ ≤ F.r s t
  rG_ge : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, r₀ ≤ G.r s t
  rF_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.r s t| ≤ M_r
  rG_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |G.r s t| ≤ M_r
  OmF_ge : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Om₀ ≤ F.Om s t
  OmG_ge : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Om₀ ≤ G.Om s t
  OmF_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.Om s t| ≤ M_Om
  OmG_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |G.Om s t| ≤ M_Om
  WF_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.W s t| ≤ M_W
  WG_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |G.W s t| ≤ M_W

/-- 2つの場のジェットの差に対する一様な上界 D（矩形上）。
    ジェット距離の点ごとの形。 -/
structure WedgeJetLe (F G : WedgeFields) (u₀ u v₀ v D : ℝ) : Prop where
  r_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.r s t - G.r s t| ≤ D
  Om_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.Om s t - G.Om s t| ≤ D
  W_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.W s t - G.W s t| ≤ D
  ru_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t - Du G.r s t| ≤ D
  rv_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t - Dv G.r s t| ≤ D
  Ou_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t - Du G.Om s t| ≤ D
  Ov_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t - Dv G.Om s t| ≤ D
  Wu_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.W s t - Du G.W s t| ≤ D
  Wv_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.W s t - Dv G.W s t| ≤ D
  ruv_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv F.r s t - Duv G.r s t| ≤ D

/-- ジェットの差が矩形上で D で抑えられれば、ジェット距離も D で抑えられる。 -/
theorem wedgeJetDist_le_of_forall_le {F G : WedgeFields} {u₀ u v₀ v D : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v) (hD : WedgeJetLe F G u₀ u v₀ v D) :
    wedgeJetDist F G u₀ u v₀ v ≤ D := by
  apply max_le _ _
  · unfold wedgeC1Dist
    apply max_le _ _
    · exact supNormRect_le hu hv hD.r_le
    · apply max_le _ _
      · exact supNormRect_le hu hv hD.Om_le
      · apply max_le _ _
        · exact supNormRect_le hu hv hD.W_le
        · apply max_le _ _
          · exact supNormRect_le hu hv hD.ru_le
          · apply max_le _ _
            · exact supNormRect_le hu hv hD.rv_le
            · apply max_le _ _
              · exact supNormRect_le hu hv hD.Ou_le
              · apply max_le _ _
                · exact supNormRect_le hu hv hD.Ov_le
                · apply max_le _ _
                  · exact supNormRect_le hu hv hD.Wu_le
                  · exact supNormRect_le hu hv hD.Wv_le
  · exact supNormRect_le hu hv hD.ruv_le

/-- r 方程式の右辺のリプシッツ定数（ジェット距離 D に対する係数の和）。 -/
noncomputable def wedgeLipR (M_Om M_W M_u M_v M_r r₀ : ℝ) : ℝ :=
  (1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀)
    + (1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3
    + M_v / r₀ + M_u / r₀
    + (M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
       + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
       + M_u * M_v / r₀ ^ 2)

/-- Ω 方程式の右辺のリプシッツ定数（ジェット距離 D に対する係数の和）。 -/
noncomputable def wedgeLipOm (M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ : ℝ) : ℝ :=
  M_Ov / Om₀ + M_Ou / Om₀
    + (M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
       + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4)
    + 2 * M_Om / r₀
    + (2 * M_Om * M_uv / r₀ ^ 2
       + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8)
    + M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4

/-- W 方程式の右辺のリプシッツ定数（ジェット距離 D に対する係数の和）。 -/
noncomputable def wedgeLipW (M_Om M_W M_r r₀ : ℝ) : ℝ :=
  M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2)
    + M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2)
    + M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4

/-- リプシッツ定数は非負である（r 方程式）。 -/
theorem wedgeLipR_nonneg {M_Om M_W M_u M_v M_r r₀ : ℝ}
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v)
    (hMr : 0 ≤ M_r) (hr₀ : 0 < r₀) :
    0 ≤ wedgeLipR M_Om M_W M_u M_v M_r r₀ := by
  unfold wedgeLipR
  positivity

/-- リプシッツ定数は非負である（Ω 方程式）。 -/
theorem wedgeLipOm_nonneg {M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ : ℝ}
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r) (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀) :
    0 ≤ wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ := by
  unfold wedgeLipOm
  positivity

/-- リプシッツ定数は非負である（W 方程式）。 -/
theorem wedgeLipW_nonneg {M_Om M_W M_r r₀ : ℝ}
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r) (hr₀ : 0 < r₀) :
    0 ≤ wedgeLipW M_Om M_W M_r r₀ := by
  unfold wedgeLipW
  positivity

/-- 二重積分の差の評価（積分の差の形）：矩形上で右辺の差が M で抑えられれば、
    二重積分の差は矩形の面積 × M で抑えられる。 -/
theorem double_integral_sub_le' {F G : ℝ → ℝ → ℝ} {u₀ u v₀ v M : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hF_c : Continuous (Function.uncurry F)) (hG_c : Continuous (Function.uncurry G))
    (hFG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F s t - G s t| ≤ M) :
    |(∫ s in u₀..u, ∫ t in v₀..v, F s t) - (∫ s in u₀..u, ∫ t in v₀..v, G s t)|
      ≤ (u - u₀) * (v - v₀) * M := by
  have hFint : ∀ s, IntervalIntegrable (fun t => F s t) volume v₀ v := fun s =>
    (hF_c.comp (continuous_const.prod_mk continuous_id)).intervalIntegrable v₀ v
  have hGint : ∀ s, IntervalIntegrable (fun t => G s t) volume v₀ v := fun s =>
    (hG_c.comp (continuous_const.prod_mk continuous_id)).intervalIntegrable v₀ v
  have hFouter : IntervalIntegrable (fun s => ∫ t in v₀..v, F s t) volume u₀ u :=
    intervalIntegrable_param_integral_symm hu hv hF_c
  have hGouter : IntervalIntegrable (fun s => ∫ t in v₀..v, G s t) volume u₀ u :=
    intervalIntegrable_param_integral_symm hu hv hG_c
  have hinner : ∀ s, (∫ t in v₀..v, F s t) - (∫ t in v₀..v, G s t)
      = ∫ t in v₀..v, (F s t - G s t) := fun s =>
    (intervalIntegral.integral_sub (hFint s) (hGint s)).symm
  have houter : (∫ s in u₀..u, ∫ t in v₀..v, F s t)
        - (∫ s in u₀..u, ∫ t in v₀..v, G s t)
      = ∫ s in u₀..u, ((∫ t in v₀..v, F s t) - (∫ t in v₀..v, G s t)) :=
    (intervalIntegral.integral_sub hFouter hGouter).symm
  rw [houter]
  have hcongr : (∫ s in u₀..u, ((∫ t in v₀..v, F s t) - (∫ t in v₀..v, G s t)))
      = ∫ s in u₀..u, ∫ t in v₀..v, (F s t - G s t) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact hinner s
  rw [hcongr]
  exact double_integral_sub_le hu hv hFG

/-- 凍結右辺の差の評価（r 方程式）：ジェット距離 D で抑える。 -/
theorem wedgeRhsR_sub_le_of_jet_le {F G : WedgeFields}
    {s t M_Om M_W M_u M_v M_r r₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v)
    (hMr : 0 ≤ M_r)
    (hrF : r₀ ≤ F.r s t) (hrG : r₀ ≤ G.r s t)
    (hMrF : |F.r s t| ≤ M_r) (hMrG : |G.r s t| ≤ M_r)
    (hOmF : |F.Om s t| ≤ M_Om)
    (hWF : |F.W s t| ≤ M_W) (hWG : |G.W s t| ≤ M_W)
    (huF : |Du F.r s t| ≤ M_u)
    (hvF : |Dv F.r s t| ≤ M_v) (hvG : |Dv G.r s t| ≤ M_v)
    (hD : |F.r s t - G.r s t| ≤ D ∧ |F.Om s t - G.Om s t| ≤ D
      ∧ |F.W s t - G.W s t| ≤ D ∧ |Du F.r s t - Du G.r s t| ≤ D
      ∧ |Dv F.r s t - Dv G.r s t| ≤ D) :
    |wedgeRhsR F s t - wedgeRhsR G s t| ≤ wedgeLipR M_Om M_W M_u M_v M_r r₀ * D := by
  have h1 : (0:ℝ) ≤ (1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀) := by positivity
  have h2 : (0:ℝ) ≤ (1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3 := by positivity
  have h3 : (0:ℝ) ≤ M_v / r₀ := by positivity
  have h4 : (0:ℝ) ≤ M_u / r₀ := by positivity
  have h5 : (0:ℝ) ≤ M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
      + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
      + M_u * M_v / r₀ ^ 2 := by positivity
  calc |wedgeRhsR F s t - wedgeRhsR G s t|
      ≤ ((1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀)) * |F.Om s t - G.Om s t|
        + ((1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3) * |F.W s t - G.W s t|
        + (M_v / r₀) * |Du F.r s t - Du G.r s t|
        + (M_u / r₀) * |Dv F.r s t - Dv G.r s t|
        + (M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
           + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
           + M_u * M_v / r₀ ^ 2) * |F.r s t - G.r s t| :=
        wedgeRhsR_sub_le hr₀ hrF hrG hMrF hMrG hOmF hWF hWG huF hvF hvG
    _ ≤ ((1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀)) * D
        + ((1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3) * D
        + (M_v / r₀) * D + (M_u / r₀) * D
        + (M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
           + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
           + M_u * M_v / r₀ ^ 2) * D := by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · apply add_le_add
              · exact mul_le_mul_of_nonneg_left hD.2.1 h1
              · exact mul_le_mul_of_nonneg_left hD.2.2.1 h2
            · exact mul_le_mul_of_nonneg_left hD.2.2.2.1 h3
          · exact mul_le_mul_of_nonneg_left hD.2.2.2.2 h4
        · exact mul_le_mul_of_nonneg_left hD.1 h5
    _ = wedgeLipR M_Om M_W M_u M_v M_r r₀ * D := by
        unfold wedgeLipR
        ring

/-- 凍結右辺の差の評価（Ω 方程式）：ジェット距離 D で抑える。 -/
theorem wedgeRhsOm_sub_le_of_jet_le {F G : WedgeFields}
    {s t M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    (hrF : r₀ ≤ F.r s t) (hrG : r₀ ≤ G.r s t)
    (hMrF : |F.r s t| ≤ M_r) (hMrG : |G.r s t| ≤ M_r)
    (hOmF : Om₀ ≤ F.Om s t) (hOmG : Om₀ ≤ G.Om s t)
    (hOmMF : |F.Om s t| ≤ M_Om) (hOmMG : |G.Om s t| ≤ M_Om)
    (hOuF : |Du F.Om s t| ≤ M_Ou)
    (hOvF : |Dv F.Om s t| ≤ M_Ov) (hOvG : |Dv G.Om s t| ≤ M_Ov)
    (huvF : |Duv F.r s t| ≤ M_uv) (huvG : |Duv G.r s t| ≤ M_uv)
    (hWF : |F.W s t| ≤ M_W) (hWG : |G.W s t| ≤ M_W)
    (hD : |F.r s t - G.r s t| ≤ D ∧ |F.Om s t - G.Om s t| ≤ D
      ∧ |F.W s t - G.W s t| ≤ D ∧ |Du F.Om s t - Du G.Om s t| ≤ D
      ∧ |Dv F.Om s t - Dv G.Om s t| ≤ D ∧ |Duv F.r s t - Duv G.r s t| ≤ D) :
    |wedgeRhsOm F s t - wedgeRhsOm G s t|
      ≤ wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D := by
  have h1 : (0:ℝ) ≤ M_Ov / Om₀ := by positivity
  have h2 : (0:ℝ) ≤ M_Ou / Om₀ := by positivity
  have h3 : (0:ℝ) ≤ M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
      + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4 := by positivity
  have h4 : (0:ℝ) ≤ 2 * M_Om / r₀ := by positivity
  have h5 : (0:ℝ) ≤ 2 * M_Om * M_uv / r₀ ^ 2
      + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8 := by positivity
  have h6 : (0:ℝ) ≤ M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4 := by positivity
  calc |wedgeRhsOm F s t - wedgeRhsOm G s t|
      ≤ (M_Ov / Om₀) * |Du F.Om s t - Du G.Om s t|
        + (M_Ou / Om₀) * |Dv F.Om s t - Dv G.Om s t|
        + (M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
           + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4) * |F.Om s t - G.Om s t|
        + (2 * M_Om / r₀) * |Duv F.r s t - Duv G.r s t|
        + (2 * M_Om * M_uv / r₀ ^ 2
           + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8)
          * |F.r s t - G.r s t|
        + (M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4) * |F.W s t - G.W s t| :=
        wedgeRhsOm_sub_le hr₀ hOm₀ hrF hrG hMrF hMrG hOmF hOmG hOmMF hOmMG
          hOuF hOvF hOvG huvF huvG hWF hWG
    _ ≤ (M_Ov / Om₀) * D + (M_Ou / Om₀) * D
        + (M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
           + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4) * D
        + (2 * M_Om / r₀) * D
        + (2 * M_Om * M_uv / r₀ ^ 2
           + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8) * D
        + (M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4) * D := by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · apply add_le_add
              · apply add_le_add
                · exact mul_le_mul_of_nonneg_left hD.2.2.2.1 h1
                · exact mul_le_mul_of_nonneg_left hD.2.2.2.2.1 h2
              · exact mul_le_mul_of_nonneg_left hD.2.1 h3
            · exact mul_le_mul_of_nonneg_left hD.2.2.2.2.2 h4
          · exact mul_le_mul_of_nonneg_left hD.1 h5
        · exact mul_le_mul_of_nonneg_left hD.2.2.1 h6
    _ = wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D := by
        unfold wedgeLipOm
        ring

/-- 凍結右辺の差の評価（W 方程式）：ジェット距離 D で抑える。 -/
theorem wedgeRhsW_sub_le_of_jet_le {F G : WedgeFields}
    {s t M_Om M_W M_r r₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    (hrF : r₀ ≤ F.r s t) (hrG : r₀ ≤ G.r s t)
    (hMrF : |F.r s t| ≤ M_r) (hMrG : |G.r s t| ≤ M_r)
    (hOmF : |F.Om s t| ≤ M_Om)
    (hWF : |F.W s t| ≤ M_W) (hWG : |G.W s t| ≤ M_W)
    (hD : |F.r s t - G.r s t| ≤ D ∧ |F.Om s t - G.Om s t| ≤ D
      ∧ |F.W s t - G.W s t| ≤ D) :
    |wedgeRhsW F s t - wedgeRhsW G s t| ≤ wedgeLipW M_Om M_W M_r r₀ * D := by
  have h1 : (0:ℝ) ≤ M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2) := by positivity
  have h2 : (0:ℝ) ≤ M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2) := by positivity
  have h3 : (0:ℝ) ≤ M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4 := by positivity
  calc |wedgeRhsW F s t - wedgeRhsW G s t|
      ≤ (M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2)) * |F.Om s t - G.Om s t|
        + (M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2)) * |F.W s t - G.W s t|
        + (M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4) * |F.r s t - G.r s t| :=
        wedgeRhsW_sub_le hr₀ hrF hrG hMrF hMrG hOmF hWF hWG
    _ ≤ (M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2)) * D
        + (M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2)) * D
        + (M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4) * D := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hD.2.1 h1
          · exact mul_le_mul_of_nonneg_left hD.2.2 h2
        · exact mul_le_mul_of_nonneg_left hD.1 h3
    _ = wedgeLipW M_Om M_W M_r r₀ * D := by
        unfold wedgeLipW
        ring

/-- 反復写像の像の値の縮小（r 成分）：像の差は矩形の面積 × (定数 × D) で抑えられる。 -/
theorem wedgeIterate_r_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (u₀ v₀ : ℝ)
    {u v M_Om M_W M_u M_v M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v)
    (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hruF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t| ≤ M_u)
    (hrvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t| ≤ M_v)
    (hrvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.r s t| ≤ M_v)
    (hD : WedgeJetLe F G u₀ u v₀ v D)
    (hRhsRF_c : Continuous (Function.uncurry (wedgeRhsR F)))
    (hRhsRG_c : Continuous (Function.uncurry (wedgeRhsR G))) :
    |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
      ≤ (s - u₀) * (t - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) := by
  have hdiff : (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
      = (∫ s' in u₀..s, ∫ t' in v₀..t, wedgeRhsR F s' t')
        - (∫ s' in u₀..s, ∫ t' in v₀..t, wedgeRhsR G s' t') := by
    show goursatFromData p_r q_r (wedgeRhsR F) u₀ v₀ s t
        - goursatFromData p_r q_r (wedgeRhsR G) u₀ v₀ s t = _
    unfold goursatFromData
    ring
  rw [hdiff]
  apply double_integral_sub_le' hs ht hRhsRF_c hRhsRG_c
  intro s' hs' t' ht'
  have hs'u : s' ∈ Set.Icc u₀ u :=
    ⟨hs'.1, le_trans hs'.2 hsu⟩
  have ht'v : t' ∈ Set.Icc v₀ v :=
    ⟨ht'.1, le_trans ht'.2 htv⟩
  exact wedgeRhsR_sub_le_of_jet_le hr₀ hMOm hMW hMu hMv hMr
    (hB.rF_ge s' hs'u t' ht'v) (hB.rG_ge s' hs'u t' ht'v)
    (hB.rF_le s' hs'u t' ht'v) (hB.rG_le s' hs'u t' ht'v)
    (hB.OmF_le s' hs'u t' ht'v)
    (hB.WF_le s' hs'u t' ht'v) (hB.WG_le s' hs'u t' ht'v)
    (hruF s' hs'u t' ht'v)
    (hrvF s' hs'u t' ht'v) (hrvG s' hs'u t' ht'v)
    ⟨hD.r_le s' hs'u t' ht'v, hD.Om_le s' hs'u t' ht'v,
      hD.W_le s' hs'u t' ht'v, hD.ru_le s' hs'u t' ht'v,
      hD.rv_le s' hs'u t' ht'v⟩

/-- 反復写像の像の値の縮小（Ω 成分）：像の差は矩形の面積 × (定数 × D) で抑えられる。 -/
theorem wedgeIterate_Om_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (u₀ v₀ : ℝ)
    {u v M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hOuF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t| ≤ M_Ou)
    (hOvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t| ≤ M_Ov)
    (hOvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.Om s t| ≤ M_Ov)
    (hruvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv F.r s t| ≤ M_uv)
    (hruvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv G.r s t| ≤ M_uv)
    (hD : WedgeJetLe F G u₀ u v₀ v D)
    (hRhsOmF_c : Continuous (Function.uncurry (wedgeRhsOm F)))
    (hRhsOmG_c : Continuous (Function.uncurry (wedgeRhsOm G))) :
    |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
      ≤ (s - u₀) * (t - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) := by
  have hdiff : (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
      = (∫ s' in u₀..s, ∫ t' in v₀..t, wedgeRhsOm F s' t')
        - (∫ s' in u₀..s, ∫ t' in v₀..t, wedgeRhsOm G s' t') := by
    show goursatFromData p_Om q_Om (wedgeRhsOm F) u₀ v₀ s t
        - goursatFromData p_Om q_Om (wedgeRhsOm G) u₀ v₀ s t = _
    unfold goursatFromData
    ring
  rw [hdiff]
  apply double_integral_sub_le' hs ht hRhsOmF_c hRhsOmG_c
  intro s' hs' t' ht'
  have hs'u : s' ∈ Set.Icc u₀ u :=
    ⟨hs'.1, le_trans hs'.2 hsu⟩
  have ht'v : t' ∈ Set.Icc v₀ v :=
    ⟨ht'.1, le_trans ht'.2 htv⟩
  exact wedgeRhsOm_sub_le_of_jet_le hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMr
    (hB.rF_ge s' hs'u t' ht'v) (hB.rG_ge s' hs'u t' ht'v)
    (hB.rF_le s' hs'u t' ht'v) (hB.rG_le s' hs'u t' ht'v)
    (hB.OmF_ge s' hs'u t' ht'v) (hB.OmG_ge s' hs'u t' ht'v)
    (hB.OmF_le s' hs'u t' ht'v) (hB.OmG_le s' hs'u t' ht'v)
    (hOuF s' hs'u t' ht'v)
    (hOvF s' hs'u t' ht'v) (hOvG s' hs'u t' ht'v)
    (hruvF s' hs'u t' ht'v) (hruvG s' hs'u t' ht'v)
    (hB.WF_le s' hs'u t' ht'v) (hB.WG_le s' hs'u t' ht'v)
    ⟨hD.r_le s' hs'u t' ht'v, hD.Om_le s' hs'u t' ht'v,
      hD.W_le s' hs'u t' ht'v, hD.Ou_le s' hs'u t' ht'v,
      hD.Ov_le s' hs'u t' ht'v, hD.ruv_le s' hs'u t' ht'v⟩

/-- 反復写像の像の値の縮小（W 成分）：像の差は矩形の面積 × (定数 × D) で抑えられる。 -/
theorem wedgeIterate_W_sub_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ) (u₀ v₀ : ℝ)
    {u v M_Om M_W M_r r₀ Om₀ D : ℝ}
    (hr₀ : 0 < r₀)
    (hMOm : 0 ≤ M_Om) (hMW : 0 ≤ M_W) (hMr : 0 ≤ M_r)
    {s t : ℝ} (hs : u₀ ≤ s) (hsu : s ≤ u) (ht : v₀ ≤ t) (htv : t ≤ v)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hD : WedgeJetLe F G u₀ u v₀ v D)
    (hRhsWF_c : Continuous (Function.uncurry (wedgeRhsW F)))
    (hRhsWG_c : Continuous (Function.uncurry (wedgeRhsW G))) :
    |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
      ≤ (s - u₀) * (t - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) := by
  have hdiff : (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
      = (∫ s' in u₀..s, ∫ t' in v₀..t, wedgeRhsW F s' t')
        - (∫ s' in u₀..s, ∫ t' in v₀..t, wedgeRhsW G s' t') := by
    show goursatFromData p_W q_W (wedgeRhsW F) u₀ v₀ s t
        - goursatFromData p_W q_W (wedgeRhsW G) u₀ v₀ s t = _
    unfold goursatFromData
    ring
  rw [hdiff]
  apply double_integral_sub_le' hs ht hRhsWF_c hRhsWG_c
  intro s' hs' t' ht'
  have hs'u : s' ∈ Set.Icc u₀ u :=
    ⟨hs'.1, le_trans hs'.2 hsu⟩
  have ht'v : t' ∈ Set.Icc v₀ v :=
    ⟨ht'.1, le_trans ht'.2 htv⟩
  exact wedgeRhsW_sub_le_of_jet_le hr₀ hMOm hMW hMr
    (hB.rF_ge s' hs'u t' ht'v) (hB.rG_ge s' hs'u t' ht'v)
    (hB.rF_le s' hs'u t' ht'v) (hB.rG_le s' hs'u t' ht'v)
    (hB.OmF_le s' hs'u t' ht'v)
    (hB.WF_le s' hs'u t' ht'v) (hB.WG_le s' hs'u t' ht'v)
    ⟨hD.r_le s' hs'u t' ht'v, hD.Om_le s' hs'u t' ht'v,
      hD.W_le s' hs'u t' ht'v⟩

end

end CFT.WedgeC1
