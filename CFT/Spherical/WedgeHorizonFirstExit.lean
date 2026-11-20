/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) のくさび EYM 系の形での分類の本体への一段：

  **最初の地平線は箱の出口である**。`WedgeContinuationNoZero` で閉じたのは
  「地平線（Ω = 0）は箱の外でしか現れない」こと、`WedgeHorizonFirstZero`
  で閉じたのは「Ω が負になる点があれば最初のゼロが存在し、その手前では
  Ω > 0」ことだった。ここではその二つを組み合わせ、延長解のヌル切片上で
  Ω が負になる点があれば、**最初のゼロは箱の外の点**であり
  （`wedge_first_exit`）、その手前では Ω > 0、すべてのゼロはその地平線
  以上にあること、さらに単純ゼロならそこで Ω は実際に符号を変えること
  （`wedge_first_exit_crossing`）と、結合 A = Ω/(2r²) もその点でゼロに
  なること（`wedge_first_exit_coupling`、r ≠ 0 のもと）を証明する。
  まとめ（`wedge_first_exit_is_horizon`）は、最初の出口が Ω と A の
  ゼロであり、その手前では Ω > 0、単純なら符号を変える、という地平線と
  しての姿である。すなわち対応仮説（Ω(u, v) = c · f(ρ(u))）の証明に要る
  「地平線の位置」が、実際の延長解に対して「箱を出る点」として固定された。
  残りは、この出口の先での ρ と c の構成（対応仮説そのものの証明）である。

  正直な限定：ここでの「出口」は延長解 F（切り落とした系の解）の Ω の
  ゼロの意味であり、真の発展方程式をみたすのは箱の中の点だけである
  （`WedgeContinuation` の限定と同じ）。また単純性と r ≠ 0 は条件つきの
  仮定として残る。
-/
import CFT.Spherical.WedgeHorizonFirstZero
import CFT.Spherical.WedgeOmegaZeroOrder

open Real Set
open CFT.Wedge CFT.WedgeUniq CFT.WedgeExist CFT.WedgeCont CFT.WedgeContNoZero
  CFT.WedgeFirstZero CFT.WedgeOmegaZero CFT.WedgeBalance

namespace CFT.WedgeFirstExit

/-- 首のデータは正：neckOm v = ((cosh (v/√2))²)⁻¹ > 0。 -/
theorem neckOm_pos (v : ℝ) : 0 < neckOm v := by
  unfold neckOm
  exact inv_pos.mpr (pow_pos (Real.cosh_pos _) 2)

/-- 特性データを持つ場では、角での Ω の値は正：`WedgeDataOn` から
    `F.Om 0 v = neckOm v > 0`。 -/
theorem wedge_Om_zero_pos_of_data {a b : ℝ} {F : WedgeFields} {v : ℝ}
    (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b) : 0 < F.Om 0 v := by
  rw [(hdata.2 v hv).2.1]
  exact neckOm_pos v

/-- 特性データを持つ場では、Ω が負になる点があれば最初の地平線が存在する
    （`wedge_first_horizon` の角での正値性をデータから引き出す版）。 -/
theorem wedge_first_horizon_of_data {a b : ℝ} {F : WedgeFields} {v : ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om) (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
      ∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z :=
  wedge_first_horizon ha hv hC2 (wedge_Om_zero_pos_of_data hdata hv) hneg

/-- 最初の地平線は箱の出口である：延長解のヌル切片上で Ω が負になる点が
    あれば、最初のゼロは箱の外にあり、その手前では Ω > 0、すべてのゼロは
    その地平線以上にある。 -/
theorem wedge_first_exit {a b B m : ℝ} {F : WedgeFields} {v : ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om)
    (hexit : ∀ u ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' = 0 →
      ¬ Inside B m (ptOf F u v'))
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) ∧
      ¬ Inside B m (ptOf F c v) := by
  obtain ⟨c, hc, hfc, hpos, hmin⟩ := wedge_first_horizon_of_data ha hdata hv hC2 hneg
  exact ⟨c, hc, hfc, hpos, hmin, hexit c hc v hv hfc⟩

/-- 延長解の版：箱の外へ Ω が負になる点があれば、最初の地平線は箱の出口
    として存在する。`wedge_horizon_exits_box` の F とその性質を使う。 -/
theorem wedge_first_exit_of_continuation {a b B m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 < m) (hmB : m ≤ B) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) b) :
    ∃ F : WedgeFields, WedgeDataOn a b F ∧ C2On a b F.r ∧ C2On a b F.Om ∧ C2On a b F.W
      ∧ ((∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0) →
          ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
            (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) ∧
            ¬ Inside B m (ptOf F c v)) := by
  obtain ⟨F, hdata, hr, hO, hW, hexit, _⟩ := wedge_horizon_exits_box ha hb hm hmB
  exact ⟨F, hdata, hr, hO, hW,
    fun hneg => wedge_first_exit ha hdata hv hO (fun u hu v hv h0 => (hexit u hu v hv h0).2) hneg⟩

/-- 最初の出口が単純ゼロなら、そこで Ω は実際に符号を変える
    （単純性は最初のゼロに対する条件つきの仮定）。 -/
theorem wedge_first_exit_crossing {a b B m : ℝ} {F : WedgeFields} {v : ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om)
    (hexit : ∀ u ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' = 0 →
      ¬ Inside B m (ptOf F u v'))
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (hd : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 →
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) → Du F.Om c v ≠ 0) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
      (∃ δ > 0, (∀ x ∈ Ioo (c - δ) c, F.Om x v * Du F.Om c v < 0) ∧
        ∀ x ∈ Ioo c (c + δ), 0 < F.Om x v * Du F.Om c v) ∧
      ¬ Inside B m (ptOf F c v) := by
  obtain ⟨c, hc, hfc, hpos, hmin, hout⟩ := wedge_first_exit ha hdata hv hC2 hexit hneg
  exact ⟨c, hc, hfc, hpos, wedge_first_horizon_crossing hv hC2 hc hfc (hd c hc hfc hmin),
    hout⟩

/-- 最初の出口では結合 A もゼロになる（r ≠ 0 のもと）。 -/
theorem wedge_first_exit_coupling {a b B m : ℝ} {F : WedgeFields} {v : ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om)
    (hexit : ∀ u ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' = 0 →
      ¬ Inside B m (ptOf F u v'))
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (hr : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 → F.r c v ≠ 0) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ wedgeAFun F.Om F.r c v = 0 ∧
      (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) ∧
      ¬ Inside B m (ptOf F c v) := by
  obtain ⟨c, hc, hfc, hpos, hmin, hout⟩ := wedge_first_exit ha hdata hv hC2 hexit hneg
  exact ⟨c, hc, hfc, (wedgeA_eq_zero_iff (hr c hc hfc)).mpr hfc, hpos, hmin, hout⟩

/-- まとめ：最初の出口は地平線である — Ω と A のゼロで、その手前では
    Ω > 0、すべてのゼロはその地平線以上にあり、単純なら符号を変え、
    箱の外にある。 -/
theorem wedge_first_exit_is_horizon {a b B m : ℝ} {F : WedgeFields} {v : ℝ}
    (ha : 0 ≤ a) (hdata : WedgeDataOn a b F) (hv : v ∈ Icc (0 : ℝ) b)
    (hC2 : C2On a b F.Om)
    (hexit : ∀ u ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, F.Om u v' = 0 →
      ¬ Inside B m (ptOf F u v'))
    (hneg : ∃ u ∈ Icc (0 : ℝ) a, F.Om u v < 0)
    (hr : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 → F.r c v ≠ 0)
    (hd : ∀ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 →
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) → Du F.Om c v ≠ 0) :
    ∃ c ∈ Icc (0 : ℝ) a, F.Om c v = 0 ∧ wedgeAFun F.Om F.r c v = 0 ∧
      (∀ u ∈ Ico (0 : ℝ) c, 0 < F.Om u v) ∧
      (∀ z ∈ Icc (0 : ℝ) a, F.Om z v = 0 → c ≤ z) ∧
      (∃ δ > 0, (∀ x ∈ Ioo (c - δ) c, F.Om x v * Du F.Om c v < 0) ∧
        ∀ x ∈ Ioo c (c + δ), 0 < F.Om x v * Du F.Om c v) ∧
      ¬ Inside B m (ptOf F c v) := by
  obtain ⟨c, hc, hfc, hA, hpos, hmin, hout⟩ :=
    wedge_first_exit_coupling ha hdata hv hC2 hexit hneg hr
  exact ⟨c, hc, hfc, hA, hpos, hmin,
    wedge_first_horizon_crossing hv hC2 hc hfc (hd c hc hfc hmin), hout⟩

end CFT.WedgeFirstExit
