/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **外側・内側の零点の一意性・個数**。前段
  （`WedgeHorizonDefectB1W0Threshold`）で、0 < r₊ ≤ 99/100 なら
  g(r*) < 0（r* = √((r₊²+9)/18) は g の唯一の臨界点）が閉じた。
  ここでは、g(0) = 5r₊ > 0 と g(2) = 30 − 2r₊² + 5r₊ > 0 を端点に
  中間値の定理を使う。g は (0, r*] 上で狭義単調減少、[r*, ∞) 上で
  狭義単調増加する（前段 `WedgeHorizonDefectB1W0Deriv`）ので、
    * (0, r*) にちょうど一個の零点 r₁、
    * (r*, 2) にちょうど一個の零点 r₂
  があり、(0, ∞) での g の零点はこの二つに限る。P′ = −2g であるから、
  P の (0, ∞) での臨界点もちょうど r₁, r₂ である。
  さらに g の符号も三つの区間で確定する：(0, r₁) で正、(r₁, r₂) で負、
  (r₂, ∞) で正。すなわち P′ は (0, r₁) で負、(r₁, r₂) で正、
  (r₂, ∞) で負である。P の零点の個数の確定には、さらに P(r₁)・P(r₂)
  の符号が要るため、この段では扱わず次段以降に残す。
  式の確認は sympy による明示計算でも照合済み（g(2) の展開と r* < 2）。
-/
import CFT.Spherical.WedgeHorizonDefectB1W0Threshold
import CFT.Spherical.WedgeHorizonFirstZero

open Real Set Filter Topology
open CFT.WedgeDefectB1W0Zero
open CFT.WedgeDefectB1W0Deriv
open CFT.WedgeDefectB1W0Threshold
open CFT.WedgeFirstZero

namespace CFT.WedgeDefectB1W0Zeros

/-- 臨界点は 2 より小さい：r*² = (r₊²+9)/18 < 4。 -/
theorem defectQuarticCritPoint_lt_two {rp : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100) :
    defectQuarticCritPoint rp < 2 := by
  have hsq : (defectQuarticCritPoint rp) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [defectQuarticCritPoint_sq]
    have h2 : rp ^ 2 ≤ (99 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hrp.le hle 2
    nlinarith [h2]
  exact (sq_lt_sq₀ defectQuarticCritPoint_pos.le (by norm_num)).mp hsq

/-- g(2) = 30 − 2r₊² + 5r₊ > 0（0 < r₊ ≤ 99/100）。 -/
theorem defectCubicB1W0Deriv_at_two_pos {rp : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100) :
    0 < defectCubicB1W0Deriv 2 rp := by
  have h2 : rp ^ 2 ≤ (99 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hrp.le hle 2
  have heq : defectCubicB1W0Deriv 2 rp = 30 - 2 * rp ^ 2 + 5 * rp := by
    unfold defectCubicB1W0Deriv
    ring
  rw [heq]
  nlinarith [h2, hrp]

/-- 左側の零点の存在：(0, r*) に g の零点がある。 -/
theorem defectCubicB1W0Deriv_exists_zero_left {rp : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100) :
    ∃ r₁ ∈ Ioo 0 (defectQuarticCritPoint rp),
      defectCubicB1W0Deriv r₁ rp = 0 := by
  have hcont : ContinuousOn (fun r => defectCubicB1W0Deriv r rp)
      (Icc 0 (defectQuarticCritPoint rp)) :=
    defectCubicB1W0Deriv_continuous.continuousOn
  have ha : 0 < defectCubicB1W0Deriv 0 rp := by
    rw [defectCubicB1W0Deriv_at_zero]
    exact mul_pos (by norm_num) hrp
  have hb : defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp < 0 :=
    defectCubicB1W0Deriv_at_critPoint_neg_of_le_99 hrp hle
  exact exists_zero_of_sign_change defectQuarticCritPoint_pos hcont ha hb

/-- 右側の零点の存在：(r*, 2) に g の零点がある（−g に中間値の定理）。 -/
theorem defectCubicB1W0Deriv_exists_zero_right {rp : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100) :
    ∃ r₂ ∈ Ioo (defectQuarticCritPoint rp) 2,
      defectCubicB1W0Deriv r₂ rp = 0 := by
  have hlt : defectQuarticCritPoint rp < 2 := defectQuarticCritPoint_lt_two hrp hle
  have hcont : ContinuousOn (fun r => -defectCubicB1W0Deriv r rp)
      (Icc (defectQuarticCritPoint rp) 2) :=
    (defectCubicB1W0Deriv_continuous.neg).continuousOn
  have ha : 0 < -defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp :=
    neg_pos.mpr (defectCubicB1W0Deriv_at_critPoint_neg_of_le_99 hrp hle)
  have hb : -defectCubicB1W0Deriv 2 rp < 0 :=
    neg_lt_zero.mpr (defectCubicB1W0Deriv_at_two_pos hrp hle)
  obtain ⟨c, hc, hfc⟩ := exists_zero_of_sign_change hlt hcont ha hb
  refine ⟨c, hc, ?_⟩
  exact neg_eq_zero.mp hfc

/-- 左側の零点の一意性：(0, r*] での g の零点は r₁ に限る。 -/
theorem defectCubicB1W0Deriv_zero_left_eq {rp : ℝ} {r₁ x : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (hx : x ∈ Ioc 0 (defectQuarticCritPoint rp))
    (hxz : defectCubicB1W0Deriv x rp = 0) :
    x = r₁ := by
  have hinj : Set.InjOn (fun r => defectCubicB1W0Deriv r rp)
      (Ioc 0 (defectQuarticCritPoint rp)) :=
    defectCubicB1W0Deriv_strictAntiOn_Ioc_zero_crit.injOn
  apply hinj hx ⟨h1.1, h1.2.le⟩
  show defectCubicB1W0Deriv x rp = defectCubicB1W0Deriv r₁ rp
  rw [hxz, h1z]

/-- 右側の零点の一意性：[r*, ∞) での g の零点は r₂ に限る。 -/
theorem defectCubicB1W0Deriv_zero_right_eq {rp : ℝ} {r₂ x : ℝ}
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hx : x ∈ Ici (defectQuarticCritPoint rp))
    (hxz : defectCubicB1W0Deriv x rp = 0) :
    x = r₂ := by
  have hinj : Set.InjOn (fun r => defectCubicB1W0Deriv r rp)
      (Ici (defectQuarticCritPoint rp)) :=
    defectCubicB1W0Deriv_strictMonoOn_Ici_crit.injOn
  apply hinj hx h2.1.le
  show defectCubicB1W0Deriv x rp = defectCubicB1W0Deriv r₂ rp
  rw [hxz, h2z]

/-- g は (0, ∞) でちょうど二つの零点を持ち、一つは (0, r*)、一つは (r*, 2) にある。 -/
theorem defectCubicB1W0Deriv_exactly_two_zeros {rp : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < defectQuarticCritPoint rp ∧
      defectQuarticCritPoint rp < r₂ ∧ r₂ < 2 ∧
      defectCubicB1W0Deriv r₁ rp = 0 ∧ defectCubicB1W0Deriv r₂ rp = 0 ∧
      ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂ := by
  obtain ⟨r₁, h₁, hz₁⟩ := defectCubicB1W0Deriv_exists_zero_left hrp hle
  obtain ⟨r₂, h₂, hz₂⟩ := defectCubicB1W0Deriv_exists_zero_right hrp hle
  refine ⟨r₁, r₂, h₁.1, h₁.2, h₂.1, h₂.2, hz₁, hz₂, ?_⟩
  intro r hr hzr
  rcases le_total r (defectQuarticCritPoint rp) with hle' | hge'
  · left
    exact defectCubicB1W0Deriv_zero_left_eq h₁ hz₁ ⟨hr, hle'⟩ hzr
  · right
    exact defectCubicB1W0Deriv_zero_right_eq h₂ hz₂ hge' hzr

/-- g は (0, r₁) で正（左の零点の手前）。 -/
theorem defectCubicB1W0Deriv_pos_of_lt_left_zero {rp : ℝ} {r₁ x : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (hx : x ∈ Ioo 0 r₁) :
    0 < defectCubicB1W0Deriv x rp := by
  have h := defectCubicB1W0Deriv_strictAntiOn_Ioc_zero_crit
    ⟨hx.1, hx.2.le.trans h1.2.le⟩ ⟨h1.1, h1.2.le⟩ hx.2
  have h' : defectCubicB1W0Deriv r₁ rp < defectCubicB1W0Deriv x rp := h
  rw [h1z] at h'
  exact h'

/-- g は (r₁, r₂) で負（狭義単調性が r* で切り替わるため場合分け）。 -/
theorem defectCubicB1W0Deriv_neg_of_between_zeros {rp : ℝ} {r₁ r₂ x : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hx : x ∈ Ioo r₁ r₂) :
    defectCubicB1W0Deriv x rp < 0 := by
  rcases le_total x (defectQuarticCritPoint rp) with hle | hge
  · have hx0 : (0 : ℝ) < x := h1.1.trans hx.1
    have h := defectCubicB1W0Deriv_strictAntiOn_Ioc_zero_crit
      ⟨h1.1, h1.2.le⟩ ⟨hx0, hle⟩ hx.1
    have h' : defectCubicB1W0Deriv x rp < defectCubicB1W0Deriv r₁ rp := h
    rw [h1z] at h'
    exact h'
  · have h := defectCubicB1W0Deriv_strictMonoOn_Ici_crit
      hge h2.1.le hx.2
    have h' : defectCubicB1W0Deriv x rp < defectCubicB1W0Deriv r₂ rp := h
    rw [h2z] at h'
    exact h'

/-- g は (r₂, ∞) で正（右の零点の先）。 -/
theorem defectCubicB1W0Deriv_pos_of_gt_right_zero {rp : ℝ} {r₂ x : ℝ}
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hx : r₂ < x) :
    0 < defectCubicB1W0Deriv x rp := by
  have h := defectCubicB1W0Deriv_strictMonoOn_Ici_crit
    h2.1.le (h2.1.trans hx).le hx
  have h' : defectCubicB1W0Deriv r₂ rp < defectCubicB1W0Deriv x rp := h
  rw [h2z] at h'
  exact h'

/-- P の (0, ∞) での臨界点はちょうど r₁, r₂ である（P′ = −2g）。 -/
theorem defectQuarticB1W0_deriv_eq_zero_iff_of_zeros {rp : ℝ} {r₁ r₂ : ℝ}
    (h1 : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : defectCubicB1W0Deriv r₂ rp = 0)
    (huniq : ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun r => defectQuarticB1W0 r rp) r = 0 ↔ r = r₁ ∨ r = r₂ := by
  rw [defectQuarticB1W0_deriv_eq]
  constructor
  · intro h
    have hg : defectCubicB1W0Deriv r rp = 0 := by linarith
    exact huniq r hr hg
  · rintro (rfl | rfl)
    · rw [h1]; norm_num
    · rw [h2]; norm_num

end CFT.WedgeDefectB1W0Zeros
