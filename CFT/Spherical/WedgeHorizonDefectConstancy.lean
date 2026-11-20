/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **S = 0 から D = 0 へ**。前段（`WedgeHorizonDefectTransport`）では、
  欠陥 D(u, v) := (∂_u Ω)/Ω − g(r)·(∂_u r) の v 微分がソース項 S に等しい
  こと（D_v = S）が証明された。ここではその輸送方程式の構造を一段進める。
  鍵は、S が Ω_u をまったく含まないことである：`defectSource` の定義は
  Ω, r, W とその 1 階微分 r_u, r_v だけによる（`rhsR` は Ω_u を引数に
  取らない）。したがって D_v = S は、D についての同次方程式化で言えば
    D_v = 0·D + S
  の形であり、S = 0 なら D は v 方向に定数である。よって S = 0 のもとで
  一点 v₀ での D = 0 が成り立てば、区間全体で D = 0 が従う
  （`defect_eq_zero_of_source_zero`、平均値の定理による）。
  さらにそれを前段の対応定理（`wedge_correspondence_of_logDeriv_match`）
  と組み合わせれば、S = 0 と一点での一致から、区間上で
    Ω(u, v) = c · f(r(u, v))
  が従う（`wedge_correspondence_of_source_zero`、RN への特殊化も含む）。
  すなわち対応仮説の証明は、ρ そのものの構成（r の単調性だけでは足りない
  部分）と、S = 0 そのものの発展方程式からの導出だけを残す形になる。
  なお S = 0 は D = 0 の必要条件であって（前段）、ここで示すのは
  「S = 0 かつ一点での D = 0 ⟹ D ≡ 0」という十分方向の半分である。
-/
import CFT.Spherical.WedgeHorizonDefectTransport
import CFT.Spherical.WedgeHorizonRatioODE

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeDefectTransport
open CFT.WedgeHorizonRatioODE CFT.RNLogDeriv CFT.RNExtremalZero

namespace CFT.WedgeDefectConstancy

/-- ソース項 S は Ω_u を含まない：Ω, r, W と r_u, r_v が一致すれば
    S も一致する。すなわち輸送方程式 D_v = S は D_v = 0·D + S の形。 -/
theorem defectSource_eq_of_agree {F₁ F₂ : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hOm : F₁.Om u v = F₂.Om u v) (hr : F₁.r u v = F₂.r u v)
    (hW : F₁.W u v = F₂.W u v)
    (hru : Du F₁.r u v = Du F₂.r u v) (hrv : Dv F₁.r u v = Dv F₂.r u v) :
    defectSource F₁ g g' u v = defectSource F₂ g g' u v := by
  simp only [defectSource, rhsR]
  rw [hOm, hr, hW, hru, hrv]

/-- S = 0 なら欠陥 D は v 区間上で定数（平均値の定理による）。 -/
theorem defect_const_of_source_zero {F : WedgeFields} {g g' : ℝ → ℝ} {u c d : ℝ}
    (htrans : ∀ v' ∈ Icc c d,
      HasDerivAt (fun v'' => logDerivDefect F g u v'')
        (defectSource F g g' u v') v')
    (hS : ∀ v' ∈ Icc c d, defectSource F g g' u v' = 0) :
    ∀ v' ∈ Icc c d, logDerivDefect F g u v' = logDerivDefect F g u c := by
  apply CFT.WedgeHorizonRho.const_of_hasDerivAt_zero_Icc
  · intro x hx
    exact (htrans x hx).continuousAt.continuousWithinAt
  · intro x hx
    have h := htrans x hx
    rw [hS x hx] at h
    exact h

/-- S = 0 のもとで、一点 v₀ での D = 0 が成り立てば、区間全体で D = 0。 -/
theorem defect_eq_zero_of_source_zero {F : WedgeFields} {g g' : ℝ → ℝ}
    {u c d : ℝ} {v₀ : ℝ}
    (htrans : ∀ v' ∈ Icc c d,
      HasDerivAt (fun v'' => logDerivDefect F g u v'')
        (defectSource F g g' u v') v')
    (hS : ∀ v' ∈ Icc c d, defectSource F g g' u v' = 0)
    (hv₀ : v₀ ∈ Icc c d) (hD₀ : logDerivDefect F g u v₀ = 0) :
    ∀ v' ∈ Icc c d, logDerivDefect F g u v' = 0 := by
  intro v' hv'
  have h1 := defect_const_of_source_zero htrans hS v' hv'
  have h2 := defect_const_of_source_zero htrans hS v₀ hv₀
  rw [h1, ← h2]
  exact hD₀

/-- C² 級の解への適用版：混合微分の交換は `C2On` から引き出す。 -/
theorem defect_eq_zero_of_source_zero_of_C2 {F : WedgeFields} {g g' : ℝ → ℝ}
    {u a b c d : ℝ} {v₀ : ℝ}
    (heq : WedgeEvolutionEqs F)
    (hC2Om : C2On a b F.Om) (hC2r : C2On a b F.r)
    (hu : u ∈ Icc (0 : ℝ) a)
    (hc0 : 0 ≤ c) (hd : d ≤ b)
    (hOm : ∀ v' ∈ Icc c d, F.Om u v' ≠ 0) (hr : ∀ v' ∈ Icc c d, F.r u v' ≠ 0)
    (hg : ∀ v' ∈ Icc c d, HasDerivAt g (g' (F.r u v')) (F.r u v'))
    (hS : ∀ v' ∈ Icc c d, defectSource F g g' u v' = 0)
    (hv₀ : v₀ ∈ Icc c d) (hD₀ : logDerivDefect F g u v₀ = 0) :
    ∀ v' ∈ Icc c d, logDerivDefect F g u v' = 0 := by
  apply defect_eq_zero_of_source_zero _ hS hv₀ hD₀
  intro v' hv'
  exact defect_hasDerivAt_v_of_C2 heq (hOm v' hv') (hr v' hv') (hg v' hv')
    hC2Om hC2r hu ⟨le_trans hc0 hv'.1, le_trans hv'.2 hd⟩

/-- 主結果：S = 0 と、切片上の各点での一点での一致から、区間上で
    Ω(u, v) = c · f(r(u, v))。ここで g は f の対数微分
    （g·f = f′）とする。 -/
theorem wedge_correspondence_of_source_zero {F : WedgeFields} {g g' : ℝ → ℝ}
    {f : ℝ → ℝ} {a b c d : ℝ} {v v₀ : ℝ}
    (htrans : ∀ x ∈ Icc a b, ∀ v' ∈ Icc c d,
      HasDerivAt (fun v'' => logDerivDefect F g x v'')
        (defectSource F g g' x v') v')
    (hS : ∀ x ∈ Icc a b, ∀ v' ∈ Icc c d, defectSource F g g' x v' = 0)
    (hv₀ : v₀ ∈ Icc c d)
    (hD₀ : ∀ x ∈ Icc a b, logDerivDefect F g x v₀ = 0)
    (hv : v ∈ Icc c d)
    (hcont : ContinuousOn (fun x => F.Om x v / f (F.r x v)) (Icc a b))
    (hOm : ∀ x ∈ Icc a b, ∃ dOm, HasDerivAt (fun u => F.Om u v) dOm x)
    (hr : ∀ x ∈ Icc a b, ∃ dr, HasDerivAt (fun u => F.r u v) dr x)
    (hf : ∀ x ∈ Icc a b, ∃ df, HasDerivAt f df (F.r x v))
    (hgf : ∀ x ∈ Icc a b, ∀ df, HasDerivAt f df (F.r x v) →
      g (F.r x v) * f (F.r x v) = df)
    (hf0 : ∀ x ∈ Icc a b, f (F.r x v) ≠ 0)
    (hOm0 : ∀ x ∈ Icc a b, F.Om x v ≠ 0) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, F.Om x v = c * f (F.r x v) := by
  have hD : ∀ x ∈ Icc a b, logDerivDefect F g x v = 0 := by
    intro x hx
    exact defect_eq_zero_of_source_zero (htrans x hx) (hS x hx) hv₀ (hD₀ x hx) v hv
  apply CFT.WedgeHorizonRatioODE.wedge_correspondence_of_logDeriv_match
    hcont hOm hr hf hf0
  intro x hx dOm df dr hdOm hdf hdr
  have hDu : dOm = Du F.Om x v := hdOm.deriv.symm
  have hDr : dr = Du F.r x v := hdr.deriv.symm
  have hD0 := hD x hx
  unfold logDerivDefect at hD0
  have h1 : Du F.Om x v = (g (F.r x v) * Du F.r x v) * F.Om x v := by
    have h2 := sub_eq_zero.mp hD0
    rwa [div_eq_iff (hOm0 x hx)] at h2
  have hgdf := hgf x hx df hdf
  calc dOm * f (F.r x v)
      = Du F.Om x v * f (F.r x v) := by rw [hDu]
    _ = (g (F.r x v) * Du F.r x v) * F.Om x v * f (F.r x v) := by rw [h1]
    _ = F.Om x v * (df * dr) := by
        rw [hDr]
        have h3 : (g (F.r x v) * Du F.r x v) * F.Om x v * f (F.r x v)
            = F.Om x v * ((g (F.r x v) * f (F.r x v)) * Du F.r x v) := by ring
        rw [h3, hgdf]

/-- RN への特殊化：f = rnF、g = rnLogDeriv（対数微分の明示形）。 -/
theorem wedge_correspondence_of_source_zero_rn {F : WedgeFields} {rp rm : ℝ}
    {a b c d : ℝ} {v v₀ : ℝ}
    (htrans : ∀ x ∈ Icc a b, ∀ v' ∈ Icc c d,
      HasDerivAt (fun v'' => logDerivDefect F (rnLogDeriv rp rm) x v'')
        (defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) x v') v')
    (hS : ∀ x ∈ Icc a b, ∀ v' ∈ Icc c d,
      defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) x v' = 0)
    (hv₀ : v₀ ∈ Icc c d)
    (hD₀ : ∀ x ∈ Icc a b, logDerivDefect F (rnLogDeriv rp rm) x v₀ = 0)
    (hv : v ∈ Icc c d)
    (hcont : ContinuousOn (fun x => F.Om x v / rnF rp rm (F.r x v)) (Icc a b))
    (hOm : ∀ x ∈ Icc a b, ∃ dOm, HasDerivAt (fun u => F.Om u v) dOm x)
    (hr : ∀ x ∈ Icc a b, ∃ dr, HasDerivAt (fun u => F.r u v) dr x)
    (hrne : ∀ x ∈ Icc a b, F.r x v ≠ 0 ∧ F.r x v ≠ rp ∧ F.r x v ≠ rm)
    (hOm0 : ∀ x ∈ Icc a b, F.Om x v ≠ 0) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, F.Om x v = c * rnF rp rm (F.r x v) := by
  apply wedge_correspondence_of_source_zero htrans hS hv₀ hD₀ hv hcont hOm hr
  · intro x hx
    exact ⟨rnF rp rm (F.r x v) * rnLogDeriv rp rm (F.r x v),
      rnF_hasDerivAt_logDeriv (hrne x hx).1 (hrne x hx).2.1 (hrne x hx).2.2⟩
  · intro x hx df hdf
    have huniq := hdf.unique
      (rnF_hasDerivAt_logDeriv (hrne x hx).1 (hrne x hx).2.1 (hrne x hx).2.2)
    rw [mul_comm (rnLogDeriv rp rm (F.r x v)) (rnF rp rm (F.r x v))]
    exact huniq.symm
  · intro x hx
    exact rnF_ne_zero_of_ne (hrne x hx).1 (hrne x hx).2.1 (hrne x hx).2.2
  · exact hOm0

end CFT.WedgeDefectConstancy
