import CFT.Foundations.WedgeDerivContraction

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の第3層 (c)：矩形の小ささによる C¹ ノルムでの縮小評価 — の第4段（最終組み立て）。
  9 成分（値 3＋1階微分 6）の縮小を C¹ ノルム全体に束ね、矩形を小さく取れば
  縮小定数 < 1 になることを証明する。

  束ねの要点：値の部分は面積因子 (s - u₀)(t - v₀)、微分の部分は辺の長さ
  (s - u₀)・(t - v₀) で抑えられた（第2・第3段）。辺の長さの最大を δ とし
  δ ≤ 1 とすれば、面積も δ² ≤ δ で抑えられるので、9 成分はすべて
  δ × (3 つのリプシッツ定数の最大) × D で抑えられる。δ を小さく取れば
  縮小定数 δ × LipMax < 1 になる。

  これで第3層 (c) は閉じた。残り（4-17 の完成）：バナッハ不動点定理の適用による
  局所解の存在そのもの。キャップ（r = 0）を含む版は 4-16 に残る。
-/

namespace CFT.WedgeC1Contract

open MeasureTheory intervalIntegral
open scoped Interval Topology
open CFT.Wedge
open CFT.WaveIntegralEq
open CFT.WedgeRhsLip
open CFT.WedgeIterate
open CFT.WedgeC1
open CFT.WedgeDeriv

noncomputable section

/-- 3 つのリプシッツ定数の最大値。縮小定数のリプシッツ側の因子。 -/
noncomputable def wedgeLipMax (M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ : ℝ) : ℝ :=
  max (wedgeLipR M_Om M_W M_u M_v M_r r₀)
    (max (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀)
      (wedgeLipW M_Om M_W M_r r₀))

/-- リプシッツ定数の最大値は非負である。 -/
theorem wedgeLipMax_nonneg {M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ : ℝ}
    (hMOm : 0 ≤ M_Om)
    (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v) (hMr : 0 ≤ M_r)
    (hr₀ : 0 < r₀) :
    0 ≤ wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ :=
  le_trans (wedgeLipR_nonneg hMOm hMW hMu hMv hMr hr₀) (le_max_left _ _)

/-- r 方程式のリプシッツ定数は最大値以下である。 -/
theorem wedgeLipR_le_wedgeLipMax {M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ : ℝ} :
    wedgeLipR M_Om M_W M_u M_v M_r r₀
      ≤ wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ :=
  le_max_left _ _

/-- Ω 方程式のリプシッツ定数は最大値以下である。 -/
theorem wedgeLipOm_le_wedgeLipMax {M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ : ℝ} :
    wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀
      ≤ wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- W 方程式のリプシッツ定数は最大値以下である。 -/
theorem wedgeLipW_le_wedgeLipMax {M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ : ℝ} :
    wedgeLipW M_Om M_W M_r r₀
      ≤ wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- C¹ ノルム全体での縮小（第3層 (c) の最終組み立て）：反復写像の像の C¹ 距離は
    (辺の長さの最大 δ) × (リプシッツ定数の最大) × (ジェット距離 D) で抑えられる。
    δ ≤ 1 のもとで、値の部分の面積因子も δ で抑えられる。 -/
theorem wedgeC1Dist_iterate_le {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (p_r' q_r' p_Om' q_Om' p_W' q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    {u v M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ D : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hδ : max (u - u₀) (v - v₀) ≤ 1)
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v) (hMr : 0 ≤ M_r)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hruF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t| ≤ M_u)
    (hrvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t| ≤ M_v)
    (hrvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.r s t| ≤ M_v)
    (hOuF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t| ≤ M_Ou)
    (hOvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t| ≤ M_Ov)
    (hOvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.Om s t| ≤ M_Ov)
    (hruvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv F.r s t| ≤ M_uv)
    (hruvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv G.r s t| ≤ M_uv)
    (hD : WedgeJetLe F G u₀ u v₀ v D)
    (hp_r : ∀ u, HasDerivAt p_r (p_r' u) u) (hp_r'c : Continuous p_r')
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hp_Om : ∀ u, HasDerivAt p_Om (p_Om' u) u) (hp_Om'c : Continuous p_Om')
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hp_W : ∀ u, HasDerivAt p_W (p_W' u) u) (hp_W'c : Continuous p_W')
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsR_F_c : Continuous (Function.uncurry (wedgeRhsR F)))
    (hrhsR_G_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_F_c : Continuous (Function.uncurry (wedgeRhsOm F)))
    (hrhsOm_G_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_F_c : Continuous (Function.uncurry (wedgeRhsW F)))
    (hrhsW_G_c : Continuous (Function.uncurry (wedgeRhsW G))) :
    wedgeC1Dist (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀)
        (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _)
    (hD.r_le u₀ (Set.left_mem_Icc.mpr hu) v₀ (Set.left_mem_Icc.mpr hv))
  have hδ0 : 0 ≤ max (u - u₀) (v - v₀) :=
    le_trans (sub_nonneg.mpr hu) (le_max_left _ _)
  have hLipR0 : 0 ≤ wedgeLipR M_Om M_W M_u M_v M_r r₀ :=
    wedgeLipR_nonneg hMOm hMW hMu hMv hMr hr₀
  have hLipOm0 : 0 ≤ wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ :=
    wedgeLipOm_nonneg hMOm hMOu hMOv hMuv hMW hMr hr₀ hOm₀
  have hLipW0 : 0 ≤ wedgeLipW M_Om M_W M_r r₀ :=
    wedgeLipW_nonneg hMOm hMW hMr hr₀
  have harea : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v,
      (s - u₀) * (t - v₀) ≤ max (u - u₀) (v - v₀) := by
    intro s hs t ht
    have hsδ : s - u₀ ≤ max (u - u₀) (v - v₀) :=
      le_trans (sub_le_sub_right hs.2 u₀) (le_max_left _ _)
    have htδ : t - v₀ ≤ max (u - u₀) (v - v₀) :=
      le_trans (sub_le_sub_right ht.2 v₀) (le_max_right _ _)
    calc (s - u₀) * (t - v₀)
        ≤ max (u - u₀) (v - v₀) * max (u - u₀) (v - v₀) :=
          mul_le_mul hsδ htδ (sub_nonneg.mpr ht.1) hδ0
      _ ≤ max (u - u₀) (v - v₀) * 1 :=
          mul_le_mul_of_nonneg_left hδ hδ0
      _ = max (u - u₀) (v - v₀) := mul_one _
  have hedge_u : ∀ s ∈ Set.Icc u₀ u, s - u₀ ≤ max (u - u₀) (v - v₀) := by
    intro s hs
    exact le_trans (sub_le_sub_right hs.2 u₀) (le_max_left _ _)
  have hedge_v : ∀ t ∈ Set.Icc v₀ v, t - v₀ ≤ max (u - u₀) (v - v₀) := by
    intro t ht
    exact le_trans (sub_le_sub_right ht.2 v₀) (le_max_right _ _)
  have hr_sup : supNormRect
        (fun s t => (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
          - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
          - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
        ≤ (s - u₀) * (t - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) :=
          wedgeIterate_r_sub_le p_r q_r p_Om q_Om p_W q_W u₀ v₀ hr₀ hMOm hMW hMu hMv hMr
            hs.1 hs.2 ht.1 ht.2 hB hruF hrvF hrvG hD hrhsR_F_c hrhsR_G_c
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) :=
          mul_le_mul_of_nonneg_right (harea s hs t ht) (mul_nonneg hLipR0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipR_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hOm_sup : supNormRect
        (fun s t => (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
          - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
          - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
        ≤ (s - u₀) * (t - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) :=
          wedgeIterate_Om_sub_le p_r q_r p_Om q_Om p_W q_W u₀ v₀ hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMr
            hs.1 hs.2 ht.1 ht.2 hB hOuF hOvF hOvG hruvF hruvG hD hrhsOm_F_c hrhsOm_G_c
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_right (harea s hs t ht) (mul_nonneg hLipOm0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipOm_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hW_sup : supNormRect
        (fun s t => (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
          - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |(wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
          - (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
        ≤ (s - u₀) * (t - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) :=
          wedgeIterate_W_sub_le p_r q_r p_Om q_Om p_W q_W u₀ v₀ hr₀ hMOm hMW hMr
            hs.1 hs.2 ht.1 ht.2 hB hD hrhsW_F_c hrhsW_G_c
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) :=
          mul_le_mul_of_nonneg_right (harea s hs t ht) (mul_nonneg hLipW0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipW_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hru_sup : supNormRect
        (fun s t => Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
          - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
          - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
        ≤ (t - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) :=
          wedgeIterate_r_uderiv_sub_le p_r q_r p_Om q_Om p_W q_W p_r' u₀ v₀
            hp_r hp_r'c hrhsR_F_c hrhsR_G_c hr₀ hMOm hMW hMu hMv hMr
            hs.1 hs.2 ht.1 ht.2 hB hruF hrvF hrvG hD
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) :=
          mul_le_mul_of_nonneg_right (hedge_v t ht) (mul_nonneg hLipR0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipR_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hrv_sup : supNormRect
        (fun s t => Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
          - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
        - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t
          - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).r s t|
        ≤ (s - u₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) :=
          wedgeIterate_r_vderiv_sub_le p_r q_r p_Om q_Om p_W q_W q_r' u₀ v₀
            hq_r hq_r'c hrhsR_F_c hrhsR_G_c hr₀ hMOm hMW hMu hMv hMr
            hs.1 hs.2 ht.1 ht.2 hB hruF hrvF hrvG hD
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipR M_Om M_W M_u M_v M_r r₀ * D) :=
          mul_le_mul_of_nonneg_right (hedge_u s hs) (mul_nonneg hLipR0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipR_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hOu_sup : supNormRect
        (fun s t => Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
          - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
          - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
        ≤ (t - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) :=
          wedgeIterate_Om_uderiv_sub_le p_r q_r p_Om q_Om p_W q_W p_Om' u₀ v₀
            hp_Om hp_Om'c hrhsOm_F_c hrhsOm_G_c hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMr
            hs.1 hs.2 ht.1 ht.2 hB hOuF hOvF hOvG hruvF hruvG hD
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_right (hedge_v t ht) (mul_nonneg hLipOm0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipOm_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hOv_sup : supNormRect
        (fun s t => Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
          - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
        - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t
          - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).Om s t|
        ≤ (s - u₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) :=
          wedgeIterate_Om_vderiv_sub_le p_r q_r p_Om q_Om p_W q_W q_Om' u₀ v₀
            hq_Om hq_Om'c hrhsOm_F_c hrhsOm_G_c hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMr
            hs.1 hs.2 ht.1 ht.2 hB hOuF hOvF hOvG hruvF hruvG hD
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipOm M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_right (hedge_u s hs) (mul_nonneg hLipOm0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipOm_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hWu_sup : supNormRect
        (fun s t => Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
          - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |Du (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
          - Du (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
        ≤ (t - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) :=
          wedgeIterate_W_uderiv_sub_le p_r q_r p_Om q_Om p_W q_W p_W' u₀ v₀
            hp_W hp_W'c hrhsW_F_c hrhsW_G_c hr₀ hMOm hMW hMr
            hs.1 hs.2 ht.1 ht.2 hB hD
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) :=
          mul_le_mul_of_nonneg_right (hedge_v t ht) (mul_nonneg hLipW0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipW_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  have hWv_sup : supNormRect
        (fun s t => Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
          - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by
    apply supNormRect_le hu hv
    intro s hs t ht
    show |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
        - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D
    calc |Dv (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t
          - Dv (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀).W s t|
        ≤ (s - u₀) * (wedgeLipW M_Om M_W M_r r₀ * D) :=
          wedgeIterate_W_vderiv_sub_le p_r q_r p_Om q_Om p_W q_W q_W' u₀ v₀
            hq_W hq_W'c hrhsW_F_c hrhsW_G_c hr₀ hMOm hMW hMr
            hs.1 hs.2 ht.1 ht.2 hB hD
      _ ≤ max (u - u₀) (v - v₀) * (wedgeLipW M_Om M_W M_r r₀ * D) :=
          mul_le_mul_of_nonneg_right (hedge_u s hs) (mul_nonneg hLipW0 hD0)
      _ ≤ max (u - u₀) (v - v₀)
            * (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ * D) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right wedgeLipW_le_wedgeLipMax hD0) hδ0
      _ = (max (u - u₀) (v - v₀)
            * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := by ring
  unfold wedgeC1Dist
  apply max_le _ _
  · exact hr_sup
  · apply max_le _ _
    · exact hOm_sup
    · apply max_le _ _
      · exact hW_sup
      · apply max_le _ _
        · exact hru_sup
        · apply max_le _ _
          · exact hrv_sup
          · apply max_le _ _
            · exact hOu_sup
            · apply max_le _ _
              · exact hOv_sup
              · apply max_le _ _
                · exact hWu_sup
                · exact hWv_sup

/-- 縮小定数 < 1 の場合：反復写像の像の C¹ 距離はもとのジェット距離より真に小さい。 -/
theorem wedgeC1Dist_iterate_lt {F G : WedgeFields}
    (p_r q_r p_Om q_Om p_W q_W : ℝ → ℝ)
    (p_r' q_r' p_Om' q_Om' p_W' q_W' : ℝ → ℝ) (u₀ v₀ : ℝ)
    {u v M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ D : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hδ : max (u - u₀) (v - v₀) ≤ 1)
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hMOm : 0 ≤ M_Om) (hMOu : 0 ≤ M_Ou) (hMOv : 0 ≤ M_Ov) (hMuv : 0 ≤ M_uv)
    (hMW : 0 ≤ M_W) (hMu : 0 ≤ M_u) (hMv : 0 ≤ M_v) (hMr : 0 ≤ M_r)
    (hB : WedgeRectBounds F G u₀ u v₀ v M_Om M_W M_r r₀ Om₀)
    (hruF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t| ≤ M_u)
    (hrvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t| ≤ M_v)
    (hrvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.r s t| ≤ M_v)
    (hOuF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t| ≤ M_Ou)
    (hOvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t| ≤ M_Ov)
    (hOvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv G.Om s t| ≤ M_Ov)
    (hruvF : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv F.r s t| ≤ M_uv)
    (hruvG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Duv G.r s t| ≤ M_uv)
    (hD : WedgeJetLe F G u₀ u v₀ v D)
    (hp_r : ∀ u, HasDerivAt p_r (p_r' u) u) (hp_r'c : Continuous p_r')
    (hq_r : ∀ v, HasDerivAt q_r (q_r' v) v) (hq_r'c : Continuous q_r')
    (hp_Om : ∀ u, HasDerivAt p_Om (p_Om' u) u) (hp_Om'c : Continuous p_Om')
    (hq_Om : ∀ v, HasDerivAt q_Om (q_Om' v) v) (hq_Om'c : Continuous q_Om')
    (hp_W : ∀ u, HasDerivAt p_W (p_W' u) u) (hp_W'c : Continuous p_W')
    (hq_W : ∀ v, HasDerivAt q_W (q_W' v) v) (hq_W'c : Continuous q_W')
    (hrhsR_F_c : Continuous (Function.uncurry (wedgeRhsR F)))
    (hrhsR_G_c : Continuous (Function.uncurry (wedgeRhsR G)))
    (hrhsOm_F_c : Continuous (Function.uncurry (wedgeRhsOm F)))
    (hrhsOm_G_c : Continuous (Function.uncurry (wedgeRhsOm G)))
    (hrhsW_F_c : Continuous (Function.uncurry (wedgeRhsW F)))
    (hrhsW_G_c : Continuous (Function.uncurry (wedgeRhsW G)))
    (hκ : max (u - u₀) (v - v₀)
        * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ < 1)
    (hDpos : 0 < D) :
    wedgeC1Dist (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀)
        (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀) u₀ u v₀ v < D := by
  have h := wedgeC1Dist_iterate_le p_r q_r p_Om q_Om p_W q_W
    p_r' q_r' p_Om' q_Om' p_W' q_W' u₀ v₀
    hu hv hδ hr₀ hOm₀ hMOm hMOu hMOv hMuv hMW hMu hMv hMr hB
    hruF hrvF hrvG hOuF hOvF hOvG hruvF hruvG hD
    hp_r hp_r'c hq_r hq_r'c hp_Om hp_Om'c hq_Om hq_Om'c hp_W hp_W'c hq_W hq_W'c
    hrhsR_F_c hrhsR_G_c hrhsOm_F_c hrhsOm_G_c hrhsW_F_c hrhsW_G_c
  calc wedgeC1Dist (wedgeIterate F p_r q_r p_Om q_Om p_W q_W u₀ v₀)
          (wedgeIterate G p_r q_r p_Om q_Om p_W q_W u₀ v₀) u₀ u v₀ v
      ≤ (max (u - u₀) (v - v₀)
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) * D := h
    _ < 1 * D := mul_lt_mul_of_pos_right hκ hDpos
    _ = D := one_mul D

/-- 矩形を小さく取れば縮小定数 < 1 になる：リプシッツ定数の最大値が正ならば、
    辺の長さの最大 δ を 1 以下かつ δ × LipMax < 1 になるように取れる。 -/
theorem exists_delta_contraction {M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ : ℝ}
    (hLip : 0 < wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1
      ∧ δ * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ < 1 := by
  refine ⟨min 1 (1 / (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ + 1)),
    lt_min one_pos (div_pos one_pos (by linarith)), min_le_left _ _, ?_⟩
  calc min 1 (1 / (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ + 1))
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀
      ≤ (1 / (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ + 1))
          * wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hLip)
    _ = wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀
          / (wedgeLipMax M_Om M_Ou M_Ov M_uv M_W M_u M_v M_r r₀ Om₀ + 1) := by
        rw [div_mul_eq_mul_div, one_mul]
    _ < 1 := (div_lt_one (by linarith)).mpr (lt_add_one _)

end

end CFT.WedgeC1Contract
