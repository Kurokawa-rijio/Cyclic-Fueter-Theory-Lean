/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **比 Ω/f(r) が定数になるための微分方程式の十分条件（対数微分の一致）**。
  前段（`WedgeHorizonRhoCandidate`）では、ρ := r が再パラメータ化の候補
  になること（r の単調性）と、比の関数が区間上で微分 0 を持てば比は定数
  であることを定式化した。ここではその「微分 0」の中身を、商の微分公式
  によって具体化する：比 R = g/h の導関数は
  (g′·h − g·h′)/h² であり、R′ = 0 は釣り合い条件 g′·h = g·h′ と同値で、
  g, h ≠ 0 のもとでは対数微分の一致 g′/g = h′/h と同値である。したがって
  切片上で対数微分が一致すれば比は定数になり、Ω = c·f(r) の形が従う。
  すなわち対応仮説 Ω = c·f(ρ) の証明は、切片上の一階の微分方程式の条件
  （対数微分の一致）に帰着される。くさびへの適用では h = f∘r として連鎖律
  を使い、主結果 `wedge_correspondence_of_logDeriv_match` として
  Ω(u, v) = c·f(r(u, v)) を区間上で得る。

  抽象部分は実解析の補題：商の微分公式（`ratio_hasDerivAt`）、
  微分 0 の条件（`ratio_deriv_zero_iff`）、対数微分との同値
  （`logDeriv_match_iff`）、一致からの定数性
  （`ratio_const_of_logDeriv_match`）と定数倍の形
  （`eq_const_mul_of_ratio_const`・`correspondence_of_logDeriv_match`）。
  残り：対数微分の一致そのものが実際のくさび解で成り立つことの証明
  （発展方程式からの導出）と、ρ そのものの構成（対応仮説そのもの）。
-/
import CFT.Spherical.WedgeHorizonRhoCandidate

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeCont CFT.WedgeFirstExit

namespace CFT.WedgeHorizonRatioODE

/-- 商の微分公式：比 R = g / h の導関数は (g′·h − g·h′)/h²。 -/
theorem ratio_hasDerivAt {g h : ℝ → ℝ} {u : ℝ} {dg dh : ℝ}
    (hg : HasDerivAt g dg u) (hh : HasDerivAt h dh u) (hh0 : h u ≠ 0) :
    HasDerivAt (fun x => g x / h x) ((dg * h u - g u * dh) / h u ^ 2) u :=
  hg.div hh hh0

/-- 比の微分が 0 になるのは、釣り合い条件 g′·h = g·h′ が成り立つとき。 -/
theorem ratio_deriv_zero_iff {g h : ℝ → ℝ} {u : ℝ} {dg dh : ℝ}
    (hg : HasDerivAt g dg u) (hh : HasDerivAt h dh u) (hh0 : h u ≠ 0) :
    (dg * h u - g u * dh) / h u ^ 2 = 0 ↔ dg * h u = g u * dh := by
  rw [div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (pow_ne_zero 2 hh0)
  · intro h
    exact Or.inl h

/-- 対数微分の一致：g, h ≠ 0 のもとで、釣り合い条件は
    g′/g = h′/h と同値。 -/
theorem logDeriv_match_iff {g h : ℝ → ℝ} {u : ℝ} {dg dh : ℝ}
    (hg0 : g u ≠ 0) (hh0 : h u ≠ 0) :
    dg * h u = g u * dh ↔ dg / g u = dh / h u := by
  rw [div_eq_div_iff hg0 hh0, mul_comm dh (g u)]

/-- 対数微分が区間上で一致すれば、比はその区間上で定数。 -/
theorem ratio_const_of_logDeriv_match {g h : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn (fun x => g x / h x) (Icc a b))
    (hg : ∀ x ∈ Icc a b, ∃ dg, HasDerivAt g dg x)
    (hh : ∀ x ∈ Icc a b, ∃ dh, HasDerivAt h dh x)
    (hh0 : ∀ x ∈ Icc a b, h x ≠ 0)
    (hmatch : ∀ x ∈ Icc a b, ∀ dg dh, HasDerivAt g dg x → HasDerivAt h dh x →
      dg * h x = g x * dh) :
    ∀ x ∈ Icc a b, g x / h x = g a / h a := by
  apply CFT.WedgeHorizonRho.const_of_hasDerivAt_zero_Icc hcont
  intro x hx
  obtain ⟨dg, hdg⟩ := hg x hx
  obtain ⟨dh, hdh⟩ := hh x hx
  have hder := ratio_hasDerivAt hdg hdh (hh0 x hx)
  have hzero : (dg * h x - g x * dh) / h x ^ 2 = 0 :=
    (ratio_deriv_zero_iff hdg hdh (hh0 x hx)).mpr (hmatch x hx dg dh hdg hdh)
  rwa [hzero] at hder

/-- 比が定数なら、g は h の定数倍になる。 -/
theorem eq_const_mul_of_ratio_const {g h : ℝ → ℝ} {a b : ℝ}
    (hconst : ∀ x ∈ Icc a b, g x / h x = g a / h a)
    (hh0 : ∀ x ∈ Icc a b, h x ≠ 0) :
    ∀ x ∈ Icc a b, g x = (g a / h a) * h x := by
  intro x hx
  exact (div_eq_iff (hh0 x hx)).mp (hconst x hx)

/-- 主結果（抽象版）：対数微分の一致から、区間上で g = c * h。 -/
theorem correspondence_of_logDeriv_match {g h : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn (fun x => g x / h x) (Icc a b))
    (hg : ∀ x ∈ Icc a b, ∃ dg, HasDerivAt g dg x)
    (hh : ∀ x ∈ Icc a b, ∃ dh, HasDerivAt h dh x)
    (hh0 : ∀ x ∈ Icc a b, h x ≠ 0)
    (hmatch : ∀ x ∈ Icc a b, ∀ dg dh, HasDerivAt g dg x → HasDerivAt h dh x →
      dg * h x = g x * dh) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, g x = c * h x :=
  ⟨g a / h a, eq_const_mul_of_ratio_const
    (ratio_const_of_logDeriv_match hcont hg hh hh0 hmatch) hh0⟩

section Wedge

variable {F : WedgeFields} {v : ℝ}

/-- くさび切片上の比 Ω/f(r) の微分公式（連鎖律つき）。 -/
theorem wedge_ratio_hasDerivAt {u : ℝ} {f : ℝ → ℝ} {dOm df dr : ℝ}
    (hOm : HasDerivAt (fun u => F.Om u v) dOm u)
    (hr : HasDerivAt (fun u => F.r u v) dr u)
    (hf : HasDerivAt f df (F.r u v))
    (hf0 : f (F.r u v) ≠ 0) :
    HasDerivAt (fun x => F.Om x v / f (F.r x v))
      ((dOm * f (F.r u v) - F.Om u v * (df * dr)) / f (F.r u v) ^ 2) u := by
  have hcomp : HasDerivAt (fun x => f (F.r x v)) (df * dr) u := by
    have h := hf.comp u hr
    simpa [Function.comp_def] using h
  exact ratio_hasDerivAt hOm hcomp hf0

/-- 主結果（くさび版）：切片上で対数微分が一致すれば、区間上で
    Ω(u, v) = c * f(r(u, v))。すなわち対応仮説の形 Ω = c·f(r) が、
    一階の微分方程式の条件（対数微分の一致）に帰着される。 -/
theorem wedge_correspondence_of_logDeriv_match {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn (fun u => F.Om u v / f (F.r u v)) (Icc a b))
    (hOm : ∀ x ∈ Icc a b, ∃ dOm, HasDerivAt (fun u => F.Om u v) dOm x)
    (hr : ∀ x ∈ Icc a b, ∃ dr, HasDerivAt (fun u => F.r u v) dr x)
    (hf : ∀ x ∈ Icc a b, ∃ df, HasDerivAt f df (F.r x v))
    (hf0 : ∀ x ∈ Icc a b, f (F.r x v) ≠ 0)
    (hmatch : ∀ x ∈ Icc a b, ∀ dOm df dr,
      HasDerivAt (fun u => F.Om u v) dOm x →
      HasDerivAt f df (F.r x v) →
      HasDerivAt (fun u => F.r u v) dr x →
      dOm * f (F.r x v) = F.Om x v * (df * dr)) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, F.Om x v = c * f (F.r x v) := by
  have hconst : ∀ x ∈ Icc a b,
      F.Om x v / f (F.r x v) = F.Om a v / f (F.r a v) := by
    apply CFT.WedgeHorizonRho.const_of_hasDerivAt_zero_Icc hcont
    intro x hx
    obtain ⟨dOm, hdOm⟩ := hOm x hx
    obtain ⟨dr, hdr⟩ := hr x hx
    obtain ⟨df, hdf⟩ := hf x hx
    have hder := wedge_ratio_hasDerivAt hdOm hdr hdf (hf0 x hx)
    have hzero : (dOm * f (F.r x v) - F.Om x v * (df * dr)) / f (F.r x v) ^ 2 = 0 := by
      rw [div_eq_zero_iff, sub_eq_zero]
      left
      exact hmatch x hx dOm df dr hdOm hdf hdr
    rwa [hzero] at hder
  exact ⟨F.Om a v / f (F.r a v), fun x hx =>
    (div_eq_iff (hf0 x hx)).mp (hconst x hx)⟩

end Wedge

end CFT.WedgeHorizonRatioODE
