import CFT.Foundations.WedgeC1Norm

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の完成への第1段：C¹ 距離 `wedgeC1Dist` の距離構造。

  第3層 (c) までで、反復写像が C¹ 距離で縮小すること（縮小定数 < 1 にできること）
  が示された。バナッハ不動点定理を適用するには、さらに
  (i) C¹ 距離が距離の公理を満たすこと、
  (ii) 反復写像が閉球を自分自身に写すこと、
  (iii) その空間が完備であること、が要る。
  このモジュールは (i) を証明する：`wedgeC1Dist` は
  - 非負（`wedgeC1Dist_nonneg`）、自己距離 0（`wedgeC1Dist_self`）、
    対称（`wedgeC1Dist_comm`）、三角不等式（`wedgeC1Dist_triangle`）
    を満たす擬距離であり、
  - 矩形上では分離的である（`wedgeC1Dist_eq_zero_iff`：距離 0 ⟺ 9成分の
    ジェットが矩形上で一致）。
  ただし三角不等式と分離性は、場のジェットが矩形上で一様に有界であること
  （`WedgeJetBounded`）のもとで示す。矩形の外では距離は場を見ないので、
  これは `WedgeFields` 全体での距離ではなく、矩形上のジェットに対する
  擬距離＋分離性という、誠実な形の主張である。

  残り（4-17 の完成）：ジェット距離（Duv r を含む）全体での縮小、閉球への
  自己写像性、完備性の整備と不動点定理の適用。キャップ（r = 0）を含む版は
  4-16 に残る。
-/

namespace CFT.WedgeC1Metric

open MeasureTheory intervalIntegral
open scoped Interval Topology
open CFT.Wedge
open CFT.WedgeC1

noncomputable section

/-- sup ノルムの差の自明性：f - f の sup ノルムは 0。 -/
theorem supNormRect_sub_self {f : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v) :
    supNormRect (fun s t => f s t - f s t) u₀ u v₀ v = 0 := by
  apply le_antisymm
  · apply supNormRect_le hu hv
    intro s hs t ht
    simp
  · exact supNormRect_nonneg hu hv

/-- sup ノルムの差の対称性。 -/
theorem supNormRect_sub_comm {f g : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => f s t - g s t) u₀ u v₀ v
      = supNormRect (fun s t => g s t - f s t) u₀ u v₀ v := by
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨s, hs, t, ht, by rw [abs_sub_comm]⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨s, hs, t, ht, by rw [abs_sub_comm]⟩

/-- sup ノルムの三角不等式（差の形）。 -/
theorem supNormRect_sub_le {f g h : ℝ → ℝ → ℝ} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hfg : BddAbove {x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t - g s t|})
    (hgh : BddAbove {x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |g s t - h s t|}) :
    supNormRect (fun s t => f s t - h s t) u₀ u v₀ v
      ≤ supNormRect (fun s t => f s t - g s t) u₀ u v₀ v
        + supNormRect (fun s t => g s t - h s t) u₀ u v₀ v := by
  apply supNormRect_le hu hv
  intro s hs t ht
  have htri : |f s t - h s t| ≤ |f s t - g s t| + |g s t - h s t| := by
    have e : f s t - h s t = (f s t - g s t) + (g s t - h s t) := by ring
    rw [e]
    exact abs_add _ _
  calc |f s t - h s t|
      ≤ |f s t - g s t| + |g s t - h s t| := htri
    _ ≤ supNormRect (fun s t => f s t - g s t) u₀ u v₀ v
          + supNormRect (fun s t => g s t - h s t) u₀ u v₀ v := by
        apply add_le_add
        · exact le_supNormRect hfg hs ht
        · exact le_supNormRect hgh hs ht

/-- 2つの有界な関数の差の sup ノルムを取る集合は上に有界。 -/
theorem bddAbove_supNormRect_sub {f g : ℝ → ℝ → ℝ} {u₀ u v₀ v M : ℝ}
    (hf : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |f s t| ≤ M)
    (hg : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |g s t| ≤ M) :
    BddAbove {x | ∃ s ∈ Set.Icc u₀ u, ∃ t ∈ Set.Icc v₀ v, x = |f s t - g s t|} := by
  apply bddAbove_supNormRect_set
  intro s hs t ht
  have h1 : |f s t - g s t| ≤ |f s t| + |g s t| := by
    have h := abs_add (f s t) (-(g s t))
    rwa [← sub_eq_add_neg, abs_neg] at h
  exact le_trans h1 (add_le_add (hf s hs t ht) (hg s hs t ht))

/-- 矩形上の場のジェット（値と1階微分、9成分）に対する一様な上界。 -/
structure WedgeJetBounded (F : WedgeFields) (u₀ u v₀ v M : ℝ) : Prop where
  r_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.r s t| ≤ M
  Om_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.Om s t| ≤ M
  W_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F.W s t| ≤ M
  ru_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.r s t| ≤ M
  rv_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.r s t| ≤ M
  Ou_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.Om s t| ≤ M
  Ov_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.Om s t| ≤ M
  Wu_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Du F.W s t| ≤ M
  Wv_le : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |Dv F.W s t| ≤ M

/-- 2つの場のジェット（値と1階微分、9成分）が矩形上で一致すること。 -/
structure WedgeJetsEqOnRect (F G : WedgeFields) (u₀ u v₀ v : ℝ) : Prop where
  r_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, F.r s t = G.r s t
  Om_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, F.Om s t = G.Om s t
  W_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, F.W s t = G.W s t
  ru_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Du F.r s t = Du G.r s t
  rv_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Dv F.r s t = Dv G.r s t
  Ou_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Du F.Om s t = Du G.Om s t
  Ov_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Dv F.Om s t = Dv G.Om s t
  Wu_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Du F.W s t = Du G.W s t
  Wv_eq : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, Dv F.W s t = Dv G.W s t

/-- C¹ 距離は非負。 -/
theorem wedgeC1Dist_nonneg {F G : WedgeFields} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v) :
    0 ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_trans (supNormRect_nonneg hu hv) (le_max_left _ _)

/-- C¹ 距離の自己距離は 0。 -/
theorem wedgeC1Dist_self {F : WedgeFields} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v) :
    wedgeC1Dist F F u₀ u v₀ v = 0 := by
  unfold wedgeC1Dist
  simp only [supNormRect_sub_self hu hv]
  simp

/-- C¹ 距離は対称。 -/
theorem wedgeC1Dist_comm {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    wedgeC1Dist F G u₀ u v₀ v = wedgeC1Dist G F u₀ u v₀ v := by
  simp only [wedgeC1Dist, supNormRect_sub_comm]

/-- 各成分の sup ノルムは C¹ 距離以下（r 成分）。 -/
theorem supNormRect_r_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => F.r s t - G.r s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_left le_rfl

/-- 各成分の sup ノルムは C¹ 距離以下（Ω 成分）。 -/
theorem supNormRect_Om_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => F.Om s t - G.Om s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_left le_rfl)

/-- 各成分の sup ノルムは C¹ 距離以下（W 成分）。 -/
theorem supNormRect_W_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => F.W s t - G.W s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl))

/-- 各成分の sup ノルムは C¹ 距離以下（r の u 微分）。 -/
theorem supNormRect_ru_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => Du F.r s t - Du G.r s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_left le_rfl)))

/-- 各成分の sup ノルムは C¹ 距離以下（r の v 微分）。 -/
theorem supNormRect_rv_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => Dv F.r s t - Dv G.r s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_left le_rfl))))

/-- 各成分の sup ノルムは C¹ 距離以下（Ω の u 微分）。 -/
theorem supNormRect_Ou_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => Du F.Om s t - Du G.Om s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl)))))

/-- 各成分の sup ノルムは C¹ 距離以下（Ω の v 微分）。 -/
theorem supNormRect_Ov_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => Dv F.Om s t - Dv G.Om s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_left le_rfl))))))

/-- 各成分の sup ノルムは C¹ 距離以下（W の u 微分）。 -/
theorem supNormRect_Wu_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => Du F.W s t - Du G.W s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_left le_rfl)))))))

/-- 各成分の sup ノルムは C¹ 距離以下（W の v 微分）。 -/
theorem supNormRect_Wv_le_wedgeC1Dist {F G : WedgeFields} {u₀ u v₀ v : ℝ} :
    supNormRect (fun s t => Dv F.W s t - Dv G.W s t) u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v := by
  unfold wedgeC1Dist
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right le_rfl)))))))

/-- 9成分すべてが M で抑えられれば C¹ 距離も M で抑えられる。 -/
theorem wedgeC1Dist_le {F G : WedgeFields} {u₀ u v₀ v M : ℝ}
    (hr : supNormRect (fun s t => F.r s t - G.r s t) u₀ u v₀ v ≤ M)
    (hOm : supNormRect (fun s t => F.Om s t - G.Om s t) u₀ u v₀ v ≤ M)
    (hW : supNormRect (fun s t => F.W s t - G.W s t) u₀ u v₀ v ≤ M)
    (hru : supNormRect (fun s t => Du F.r s t - Du G.r s t) u₀ u v₀ v ≤ M)
    (hrv : supNormRect (fun s t => Dv F.r s t - Dv G.r s t) u₀ u v₀ v ≤ M)
    (hOu : supNormRect (fun s t => Du F.Om s t - Du G.Om s t) u₀ u v₀ v ≤ M)
    (hOv : supNormRect (fun s t => Dv F.Om s t - Dv G.Om s t) u₀ u v₀ v ≤ M)
    (hWu : supNormRect (fun s t => Du F.W s t - Du G.W s t) u₀ u v₀ v ≤ M)
    (hWv : supNormRect (fun s t => Dv F.W s t - Dv G.W s t) u₀ u v₀ v ≤ M) :
    wedgeC1Dist F G u₀ u v₀ v ≤ M := by
  unfold wedgeC1Dist
  apply max_le _ _
  · exact hr
  · apply max_le _ _
    · exact hOm
    · apply max_le _ _
      · exact hW
      · apply max_le _ _
        · exact hru
        · apply max_le _ _
          · exact hrv
          · apply max_le _ _
            · exact hOu
            · apply max_le _ _
              · exact hOv
              · apply max_le _ _
                · exact hWu
                · exact hWv

/-- C¹ 距離の三角不等式（ジェットが矩形上で一様に有界な場の上で）。 -/
theorem wedgeC1Dist_triangle {F G H : WedgeFields} {u₀ u v₀ v M : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hF : WedgeJetBounded F u₀ u v₀ v M)
    (hG : WedgeJetBounded G u₀ u v₀ v M)
    (hH : WedgeJetBounded H u₀ u v₀ v M) :
    wedgeC1Dist F H u₀ u v₀ v
      ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v := by
  apply wedgeC1Dist_le
  · calc supNormRect (fun s t => F.r s t - H.r s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => F.r s t - G.r s t) u₀ u v₀ v
            + supNormRect (fun s t => G.r s t - H.r s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.r_le hG.r_le)
            (bddAbove_supNormRect_sub hG.r_le hH.r_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_r_le_wedgeC1Dist supNormRect_r_le_wedgeC1Dist
  · calc supNormRect (fun s t => F.Om s t - H.Om s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => F.Om s t - G.Om s t) u₀ u v₀ v
            + supNormRect (fun s t => G.Om s t - H.Om s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.Om_le hG.Om_le)
            (bddAbove_supNormRect_sub hG.Om_le hH.Om_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_Om_le_wedgeC1Dist supNormRect_Om_le_wedgeC1Dist
  · calc supNormRect (fun s t => F.W s t - H.W s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => F.W s t - G.W s t) u₀ u v₀ v
            + supNormRect (fun s t => G.W s t - H.W s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.W_le hG.W_le)
            (bddAbove_supNormRect_sub hG.W_le hH.W_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_W_le_wedgeC1Dist supNormRect_W_le_wedgeC1Dist
  · calc supNormRect (fun s t => Du F.r s t - Du H.r s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => Du F.r s t - Du G.r s t) u₀ u v₀ v
            + supNormRect (fun s t => Du G.r s t - Du H.r s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.ru_le hG.ru_le)
            (bddAbove_supNormRect_sub hG.ru_le hH.ru_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_ru_le_wedgeC1Dist supNormRect_ru_le_wedgeC1Dist
  · calc supNormRect (fun s t => Dv F.r s t - Dv H.r s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => Dv F.r s t - Dv G.r s t) u₀ u v₀ v
            + supNormRect (fun s t => Dv G.r s t - Dv H.r s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.rv_le hG.rv_le)
            (bddAbove_supNormRect_sub hG.rv_le hH.rv_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_rv_le_wedgeC1Dist supNormRect_rv_le_wedgeC1Dist
  · calc supNormRect (fun s t => Du F.Om s t - Du H.Om s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => Du F.Om s t - Du G.Om s t) u₀ u v₀ v
            + supNormRect (fun s t => Du G.Om s t - Du H.Om s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.Ou_le hG.Ou_le)
            (bddAbove_supNormRect_sub hG.Ou_le hH.Ou_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_Ou_le_wedgeC1Dist supNormRect_Ou_le_wedgeC1Dist
  · calc supNormRect (fun s t => Dv F.Om s t - Dv H.Om s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => Dv F.Om s t - Dv G.Om s t) u₀ u v₀ v
            + supNormRect (fun s t => Dv G.Om s t - Dv H.Om s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.Ov_le hG.Ov_le)
            (bddAbove_supNormRect_sub hG.Ov_le hH.Ov_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_Ov_le_wedgeC1Dist supNormRect_Ov_le_wedgeC1Dist
  · calc supNormRect (fun s t => Du F.W s t - Du H.W s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => Du F.W s t - Du G.W s t) u₀ u v₀ v
            + supNormRect (fun s t => Du G.W s t - Du H.W s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.Wu_le hG.Wu_le)
            (bddAbove_supNormRect_sub hG.Wu_le hH.Wu_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_Wu_le_wedgeC1Dist supNormRect_Wu_le_wedgeC1Dist
  · calc supNormRect (fun s t => Dv F.W s t - Dv H.W s t) u₀ u v₀ v
        ≤ supNormRect (fun s t => Dv F.W s t - Dv G.W s t) u₀ u v₀ v
            + supNormRect (fun s t => Dv G.W s t - Dv H.W s t) u₀ u v₀ v :=
          supNormRect_sub_le hu hv
            (bddAbove_supNormRect_sub hF.Wv_le hG.Wv_le)
            (bddAbove_supNormRect_sub hG.Wv_le hH.Wv_le)
      _ ≤ wedgeC1Dist F G u₀ u v₀ v + wedgeC1Dist G H u₀ u v₀ v :=
          add_le_add supNormRect_Wv_le_wedgeC1Dist supNormRect_Wv_le_wedgeC1Dist

/-- ジェットが矩形上で一致すれば C¹ 距離は 0。 -/
theorem wedgeC1Dist_eq_zero_of_jetsEq {F G : WedgeFields} {u₀ u v₀ v : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (h : WedgeJetsEqOnRect F G u₀ u v₀ v) :
    wedgeC1Dist F G u₀ u v₀ v = 0 := by
  have h0 : ∀ f g : ℝ → ℝ → ℝ,
      (∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, f s t = g s t) →
      supNormRect (fun s t => f s t - g s t) u₀ u v₀ v = 0 := by
    intro f g hfg
    apply le_antisymm
    · apply supNormRect_le hu hv
      intro s hs t ht
      rw [hfg s hs t ht]
      simp
    · exact supNormRect_nonneg hu hv
  have hr0 := h0 F.r G.r h.r_eq
  have hOm0 := h0 F.Om G.Om h.Om_eq
  have hW0 := h0 F.W G.W h.W_eq
  have hru0 := h0 (fun s t => Du F.r s t) (fun s t => Du G.r s t) h.ru_eq
  have hrv0 := h0 (fun s t => Dv F.r s t) (fun s t => Dv G.r s t) h.rv_eq
  have hOu0 := h0 (fun s t => Du F.Om s t) (fun s t => Du G.Om s t) h.Ou_eq
  have hOv0 := h0 (fun s t => Dv F.Om s t) (fun s t => Dv G.Om s t) h.Ov_eq
  have hWu0 := h0 (fun s t => Du F.W s t) (fun s t => Du G.W s t) h.Wu_eq
  have hWv0 := h0 (fun s t => Dv F.W s t) (fun s t => Dv G.W s t) h.Wv_eq
  unfold wedgeC1Dist
  rw [hr0, hOm0, hW0, hru0, hrv0, hOu0, hOv0, hWu0, hWv0]
  simp

/-- C¹ 距離が 0 ならジェットは矩形上で一致する（有界性の下）。 -/
theorem wedgeJetsEq_of_wedgeC1Dist_eq_zero {F G : WedgeFields} {u₀ u v₀ v M : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hF : WedgeJetBounded F u₀ u v₀ v M)
    (hG : WedgeJetBounded G u₀ u v₀ v M)
    (h0 : wedgeC1Dist F G u₀ u v₀ v = 0) :
    WedgeJetsEqOnRect F G u₀ u v₀ v := by
  have key : ∀ f g : ℝ → ℝ → ℝ,
      (∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |f s t| ≤ M) →
      (∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |g s t| ≤ M) →
      supNormRect (fun s t => f s t - g s t) u₀ u v₀ v
        ≤ wedgeC1Dist F G u₀ u v₀ v →
      ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, f s t = g s t := by
    intro f g hf hg hle s hs t ht
    have hsup : supNormRect (fun s t => f s t - g s t) u₀ u v₀ v = 0 :=
      le_antisymm (hle.trans_eq h0) (supNormRect_nonneg hu hv)
    have hle2 : |f s t - g s t|
        ≤ supNormRect (fun s t => f s t - g s t) u₀ u v₀ v :=
      le_supNormRect (bddAbove_supNormRect_sub hf hg) hs ht
    rw [hsup] at hle2
    have hdiff : f s t - g s t = 0 :=
      abs_eq_zero.mp (le_antisymm hle2 (abs_nonneg _))
    exact sub_eq_zero.mp hdiff
  exact ⟨key F.r G.r hF.r_le hG.r_le supNormRect_r_le_wedgeC1Dist,
    key F.Om G.Om hF.Om_le hG.Om_le supNormRect_Om_le_wedgeC1Dist,
    key F.W G.W hF.W_le hG.W_le supNormRect_W_le_wedgeC1Dist,
    key (fun s t => Du F.r s t) (fun s t => Du G.r s t) hF.ru_le hG.ru_le
      supNormRect_ru_le_wedgeC1Dist,
    key (fun s t => Dv F.r s t) (fun s t => Dv G.r s t) hF.rv_le hG.rv_le
      supNormRect_rv_le_wedgeC1Dist,
    key (fun s t => Du F.Om s t) (fun s t => Du G.Om s t) hF.Ou_le hG.Ou_le
      supNormRect_Ou_le_wedgeC1Dist,
    key (fun s t => Dv F.Om s t) (fun s t => Dv G.Om s t) hF.Ov_le hG.Ov_le
      supNormRect_Ov_le_wedgeC1Dist,
    key (fun s t => Du F.W s t) (fun s t => Du G.W s t) hF.Wu_le hG.Wu_le
      supNormRect_Wu_le_wedgeC1Dist,
    key (fun s t => Dv F.W s t) (fun s t => Dv G.W s t) hF.Wv_le hG.Wv_le
      supNormRect_Wv_le_wedgeC1Dist⟩

/-- C¹ 距離の分離性（矩形上）：距離 0 ⟺ ジェットが矩形上で一致。 -/
theorem wedgeC1Dist_eq_zero_iff {F G : WedgeFields} {u₀ u v₀ v M : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hF : WedgeJetBounded F u₀ u v₀ v M)
    (hG : WedgeJetBounded G u₀ u v₀ v M) :
    wedgeC1Dist F G u₀ u v₀ v = 0 ↔ WedgeJetsEqOnRect F G u₀ u v₀ v :=
  ⟨wedgeJetsEq_of_wedgeC1Dist_eq_zero hu hv hF hG,
   wedgeC1Dist_eq_zero_of_jetsEq hu hv⟩

end

end CFT.WedgeC1Metric
