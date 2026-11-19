/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) のくさび EYM 系の形での分類への一段（2026-11-19）：

  4-17 の局所解についての `WedgeLocalNoZero`（局所存在の正方形の上では
  Ω も r もゼロを持たない）を、任意の長方形上の延長解
  （`wedge_continuation`）へ広げる。延長解 F は、切り落としの箱
    m ≤ Ω ≤ B、m ≤ r ≤ B、|W|, |r_u|, |r_v|, |Ω_u|, |Ω_v| ≤ B
  の中にとどまる点では真の発展方程式をみたす。箱の中では m ≤ Ω かつ
  m ≤ r で m > 0 だから、Ω も r もゼロを持たず、ゼロの位数の移行
  （`wedgeA_eq_zero_iff`）により結合 A = Ω/(2r²) もゼロを持たない
  （`wedge_continuation_no_zero`）。対偶として、地平線（Ω = 0）は箱の
  外でしか現れず、その値は箱の下端 m より小さい
  （`wedge_horizon_exits_box`）。すなわち「地平線が現れるのは、解が箱を
  出るときだけ」という分類の半分が、任意の長方形の上で閉じた。
  箱にとどまる解には地平線がないことのまとめが
  `wedge_no_horizon_of_stays_in_box`。

  正直な限定：F は切り落とした系の解であり、真の発展方程式をみたすのは
  箱の中の点だけである（`WedgeContinuation` の限定と同じ）。したがって
  ここでの「地平線」は延長解 F の Ω のゼロの意味であり、RN 側の分類
  （`RNExtremalDoubleZero`）や 9-3 の喉の発散（`ExtremalThroatLength`・
  `NonextremalThroatLength`）との対応づけの本体——正方形の外で Ω が
  ゼロになる場合の分類——は、局所存在の範囲を超えるためここでは扱わない。
  残りはその対応づけの本体である。
-/
import CFT.Spherical.WedgeContinuation
import CFT.Spherical.WedgeOmegaZeroOrder

open Real Set CFT.Wedge CFT.WedgeUniq CFT.WedgeExist CFT.WedgeCont CFT.WedgeOmegaZero
  CFT.WedgeBalance

namespace CFT.WedgeContNoZero

/-- 延長解は、箱の中の点では Ω も r もゼロを持たず、結合 A もゼロを持たない。
    箱の条件 m ≤ Ω、m ≤ r と m > 0 から。 -/
theorem wedge_continuation_no_zero {a b B m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 < m) (hmB : m ≤ B) :
    ∃ F : WedgeFields, WedgeDataOn a b F ∧ C2On a b F.r ∧ C2On a b F.Om ∧ C2On a b F.W
      ∧ ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, Inside B m (ptOf F u v) →
        F.Om u v ≠ 0 ∧ F.r u v ≠ 0 ∧ wedgeAFun F.Om F.r u v ≠ 0 := by
  obtain ⟨F, hdata, hr, hO, hW, _⟩ := wedge_continuation ha hb hm hmB
  refine ⟨F, hdata, hr, hO, hW, fun u hu v hv hin => ?_⟩
  have hOm : m ≤ F.Om u v := hin.1
  have hr' : m ≤ F.r u v := hin.2.2.2.2.2.1
  have hOm0 : F.Om u v ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hOm)
  have hr0 : F.r u v ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hr')
  exact ⟨hOm0, hr0, fun hA => hOm0 ((wedgeA_eq_zero_iff hr0).mp hA)⟩

/-- 地平線（Ω = 0）は箱の外でしか現れない。その値は箱の下端 m より小さい。
    r = 0 についても同じ。 -/
theorem wedge_horizon_exits_box {a b B m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 < m) (hmB : m ≤ B) :
    ∃ F : WedgeFields, WedgeDataOn a b F ∧ C2On a b F.r ∧ C2On a b F.Om ∧ C2On a b F.W
      ∧ (∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, F.Om u v = 0 →
          F.Om u v < m ∧ ¬ Inside B m (ptOf F u v))
      ∧ ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, F.r u v = 0 →
          F.r u v < m ∧ ¬ Inside B m (ptOf F u v) := by
  obtain ⟨F, hdata, hr, hO, hW, hnz⟩ := wedge_continuation_no_zero ha hb hm hmB
  refine ⟨F, hdata, hr, hO, hW, ?_, ?_⟩
  · intro u hu v hv h0
    refine ⟨by rw [h0]; exact hm, fun hin => ?_⟩
    exact (hnz u hu v hv hin).1 h0
  · intro u hu v hv h0
    refine ⟨by rw [h0]; exact hm, fun hin => ?_⟩
    exact (hnz u hu v hv hin).2.1 h0

/-- 箱にとどまる解には地平線がない：長方形全体で箱の中にいる延長解は、
    その長方形のどこでも Ω・r・A がゼロにならない。 -/
theorem wedge_no_horizon_of_stays_in_box {a b B m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 < m) (hmB : m ≤ B) :
    ∃ F : WedgeFields, WedgeDataOn a b F ∧ C2On a b F.r ∧ C2On a b F.Om ∧ C2On a b F.W
      ∧ ((∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, Inside B m (ptOf F u v)) →
          ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
            F.Om u v ≠ 0 ∧ F.r u v ≠ 0 ∧ wedgeAFun F.Om F.r u v ≠ 0) := by
  obtain ⟨F, hdata, hr, hO, hW, hnz⟩ := wedge_continuation_no_zero ha hb hm hmB
  exact ⟨F, hdata, hr, hO, hW, fun hall u hu v hv => hnz u hu v hv (hall u hu v hv)⟩

end CFT.WedgeContNoZero
