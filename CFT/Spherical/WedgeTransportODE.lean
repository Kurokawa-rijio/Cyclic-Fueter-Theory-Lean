import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 4-4（輸送部分の常微分方程式化、残りの局所存在）：
  4-2 の伝播恒等式 ∂_v C_u = -(r_v/r) C_u は、固定した特性曲線に沿えば
  v 方向の一階線形常微分方程式 y' = c(v) y（c = -(r'/r)）である。
  このモジュールでは Mathlib のピカール–リンデレーフ定理
  （`IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq`）を
  線形方程式に適用し、任意の初期データに対する局所解の存在を示す。
  リプシッツ定数は [t₀-1, t₀+1] 上での |c| の上限、区間の幅 δ は
  C * δ ≤ R を満たすよう選ぶ。明示解（積分因子による一般解の形）は
  `CFT.Spherical.WedgeTransportIntegratingFactor` に既にある。
-/

open Set

namespace CFT.WedgeTransportODE

/-- 一階線形輸送方程式 y' = c(t) y の局所存在（ピカール–リンデレーフ）。
    係数 c が連続なら、任意の初期データ y(t₀) = y₀ に対し t₀ のまわりで解が存在する。 -/
theorem transport_local_existence {c : ℝ → ℝ} (hc : Continuous c) (t₀ y₀ : ℝ) :
    ∃ δ > 0, ∃ y : ℝ → ℝ, y t₀ = y₀ ∧
      ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt y (c t * y t) t := by
  -- |c| を [t₀-1, t₀+1] 上で抑える
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨K, hBK⟩ : ∃ K : NNReal, ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ‖c t‖ ≤ (K : ℝ) :=
    ⟨⟨max B 0, le_max_right _ _⟩, fun t ht => (hB t ht).trans (le_max_left _ _)⟩
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.2
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by linarith
  have hy1 : (0 : ℝ) < |y₀| + 1 := by
    have h := abs_nonneg y₀
    linarith
  have hden : (0 : ℝ) < ((K : ℝ) + 1) * (|y₀| + 1) := mul_pos hK1 hy1
  set δ := min 1 (1 / (((K : ℝ) + 1) * (|y₀| + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min zero_lt_one (one_div_pos.mpr hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hpl : IsPicardLindelof (fun t y => c t * y) (t₀ - δ) t₀ (t₀ + δ) y₀ K 1
      ((K : ℝ) * (|y₀| + 1)) := by
    refine ⟨?_, zero_le_one, ?_, ?_, ?_, ?_⟩
    · exact ⟨by linarith, by linarith⟩
    · intro t ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      have hct : |c t| ≤ (K : ℝ) := by
        have h := hBK t ⟨by linarith [ht.1, hδ1], by linarith [ht.2, hδ1]⟩
        rwa [Real.norm_eq_abs] at h
      show dist (c t * x) (c t * y) ≤ (K : ℝ) * dist x y
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_right hct (abs_nonneg _)
    · intro x _
      exact hc.continuousOn.mul continuousOn_const
    · intro t ht x hx
      have hct : ‖c t‖ ≤ (K : ℝ) :=
        hBK t ⟨by linarith [ht.1, hδ1], by linarith [ht.2, hδ1]⟩
      have hxabs : ‖x‖ ≤ |y₀| + 1 := by
        have h : dist x y₀ ≤ 1 := hx
        rw [Real.dist_eq] at h
        rw [Real.norm_eq_abs]
        calc |x| = |y₀ + (x - y₀)| := by rw [show y₀ + (x - y₀) = x by ring]
          _ ≤ |y₀| + |x - y₀| := abs_add _ _
          _ ≤ |y₀| + 1 := add_le_add_left h _
      show ‖c t * x‖ ≤ (K : ℝ) * (|y₀| + 1)
      rw [norm_mul]
      exact mul_le_mul hct hxabs (norm_nonneg _) hKnn
    · have hmax : max ((t₀ + δ) - t₀) (t₀ - (t₀ - δ)) = δ := by
        rw [add_sub_cancel_left, sub_sub_self, max_self]
      rw [hmax]
      have hδle : δ ≤ 1 / (((K : ℝ) + 1) * (|y₀| + 1)) := min_le_right _ _
      have hne : ((K : ℝ) + 1) * (|y₀| + 1) ≠ 0 := ne_of_gt hden
      calc (K : ℝ) * (|y₀| + 1) * δ
          ≤ (K : ℝ) * (|y₀| + 1) * (1 / (((K : ℝ) + 1) * (|y₀| + 1))) :=
            mul_le_mul_of_nonneg_left hδle (mul_nonneg hKnn (le_of_lt hy1))
        _ = (K : ℝ) / ((K : ℝ) + 1) := by field_simp; ring
        _ ≤ 1 := (div_le_one hK1).mpr (le_add_of_nonneg_right zero_le_one)
  obtain ⟨y, hy0, hy⟩ := hpl.exists_forall_hasDerivWithinAt_Icc_eq y₀
  refine ⟨δ, hδpos, y, hy0, ?_⟩
  intro t ht
  exact (hy t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- 4-4（くさびへの適用）：固定した特性曲線に沿い、r が C¹ かつ r ≠ 0 ならば、
    輸送方程式 y' = -(r'/r) y は任意の初期データに対し局所解を持つ。
    係数は (-r')/r の形で書く（-(r'/r) と等しい）。 -/
theorem wedge_transport_local_existence {r : ℝ → ℝ} (hr : Differentiable ℝ r)
    (hderiv : Continuous (deriv r)) (hr0 : ∀ v, r v ≠ 0) (t₀ y₀ : ℝ) :
    ∃ δ > 0, ∃ y : ℝ → ℝ, y t₀ = y₀ ∧
      ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt y (((-deriv r t) / r t) * y t) t :=
  transport_local_existence (hderiv.neg.div hr.continuous hr0) t₀ y₀

end CFT.WedgeTransportODE
