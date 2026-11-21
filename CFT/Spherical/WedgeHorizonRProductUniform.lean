/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **r_u·r_v の一様な正の下界（第四段：コンパクト長方形上の最小値による一様化）**。
  前段（`WedgeHorizonRProductStrict`）では、W の微分が区間内のどこかで
  非ゼロなら、内部の各点で r_u·r_v > 0（厳密）であることを示した。
  ここでは、角から離れたコンパクトな部分長方形 [u₀,u₁]×[v₀,v₁] の上では、
  r_u·r_v が連続関数（C2Data の `cont_u`・`cont_v`）であり、各点で正であることから、
  最小値の存在（極値定理 `IsCompact.exists_forall_le'`）により一様な正の
  下界 m > 0 が取れることを示す。すなわち
    ∃ m > 0, ∀ (u,v) ∈ [u₀,u₁]×[v₀,v₁], m ≤ r_u·r_v。
  角 (0,0) を含む長方形全体では r_u·r_v は角で 0 になるので、一様な正の
  下界は角から離れた部分長方形の上でのみ主張する。

  残りは、m の定量的な評価（W の微分の下界や r・Ω の一様な評価からの
  明示的な m の構成）と、ρ そのものの構成である。
-/
import CFT.Spherical.WedgeHorizonRProductStrict

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeRProductData CFT.CharUniqueness
open CFT.WedgeRProductSign CFT.WedgeRProductStrict

namespace CFT.WedgeRProductUniform

/-- コンパクト集合上で各点正の連続関数は、一様な正の下界をもつ。 -/
theorem exists_pos_lower_bound_of_continuousOn {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : IsCompact s) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ s, m ≤ f x :=
  hs.exists_forall_le' hf hpos

/-- r_u·r_v は（uncurry した）部分長方形上の連続関数。 -/
theorem rProduct_continuousOn {F : WedgeFields} {a b u₀ u₁ v₀ v₁ : ℝ}
    (hC2r : C2On a b F.r)
    (hu : Icc u₀ u₁ ⊆ Icc (0 : ℝ) a) (hv : Icc v₀ v₁ ⊆ Icc (0 : ℝ) b) :
    ContinuousOn (Function.uncurry fun u v => Du F.r u v * Dv F.r u v)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁) :=
  (hC2r.cont_u.mul hC2r.cont_v).mono (Set.prod_mono hu hv)

/-- 部分長方形上で各点正なら、一様な正の下界 m > 0 がある。 -/
theorem rProduct_uniform_of_pointwise_pos {F : WedgeFields} {a b u₀ u₁ v₀ v₁ : ℝ}
    (hC2r : C2On a b F.r)
    (hu₀₁ : u₀ ≤ u₁) (hv₀₁ : v₀ ≤ v₁)
    (hu : Icc u₀ u₁ ⊆ Icc (0 : ℝ) a) (hv : Icc v₀ v₁ ⊆ Icc (0 : ℝ) b)
    (hpos : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁, 0 < Du F.r u v * Dv F.r u v) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      m ≤ Du F.r u v * Dv F.r u v := by
  have hcomp : IsCompact (Icc u₀ u₁ ×ˢ Icc v₀ v₁) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨m, hm, hle⟩ := exists_pos_lower_bound_of_continuousOn hcomp
    (rProduct_continuousOn hC2r hu hv)
    (fun p hp => hpos p.1 hp.1 p.2 hp.2)
  exact ⟨m, hm, fun u hu' v hv' => hle (u, v) ⟨hu', hv'⟩⟩

/-- W の微分が各点の下で非ゼロなら、部分長方形上で一様な正の下界がある。 -/
theorem rProduct_uniform_of_exists_DW_ne_zero {F : WedgeFields} {a b u₀ u₁ v₀ v₁ : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om) (hC2W : C2On a b F.W)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu₀₁ : u₀ ≤ u₁) (hv₀₁ : v₀ ≤ v₁)
    (hu : Icc u₀ u₁ ⊆ Icc (0 : ℝ) a) (hv : Icc v₀ v₁ ⊆ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hrvv : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u' v'') (Dvv F.r u' v') v')
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun u'' => Du F.r u'' v') (Duu F.r u' v') u')
    (hW : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      (∃ u₁ ∈ Ioo (0 : ℝ) a, u₁ < u ∧ Du F.W u₁ v ≠ 0) ∧
      (∃ v₁ ∈ Ioo (0 : ℝ) b, v₁ < v ∧ Dv F.W u v₁ ≠ 0)) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      m ≤ Du F.r u v * Dv F.r u v := by
  apply rProduct_uniform_of_pointwise_pos hC2r hu₀₁ hv₀₁ hu hv
  intro u hu' v hv'
  obtain ⟨⟨u₁, hu₁, hu₁u, hWu⟩, ⟨v₁, hv₁, hv₁v, hWv⟩⟩ := hW u hu' v hv'
  exact rProduct_pos_of_exists_DW_ne_zero heq hdata hcon hC2r hC2Om hC2W ha hb ha2
    (hu hu') (hv hv') hOm hr hrvv hruu hu₁ hu₁u hWu hv₁ hv₁v hWv

end CFT.WedgeRProductUniform
