/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **P(r₁)・P(r₂) の符号による P の零点の個数の確定**。前段
  （`WedgeHorizonDefectB1W0Zeros`）で、0 < r₊ ≤ 99/100 のもとで
  g は (0, ∞) でちょうど二つの零点 r₁ ∈ (0, r*)、r₂ ∈ (r*, 2) を持ち、
  P′ = −2g の符号は (0, r₁) で負、(r₁, r₂) で正、(r₂, ∞) で負である
  ことが閉じた。ここでは P の零点の個数を P(r₁)・P(r₂) の符号に
  帰着させる。P は (0, r₁] 上で狭義単調減少、[r₁, r₂] 上で狭義単調増加、
  [r₂, ∞) 上で狭義単調減少する（平均値の定理の系による）ので、
    * P(r₁) > 0 なら (0, r₂] に P の零点はない；
    * P(r₁) < 0 なら (0, r₁) にちょうど一個の零点がある；
    * P(r₁) < 0 < P(r₂) なら (r₁, r₂) にちょうど一個の零点がある；
    * P(r₂) > 0 なら (r₂, 2) にちょうど一個の零点があり、(r₂, ∞) には
      他に零点はない（Rolle の定理と g の零点の一意性による）。
  まとめとして、P(r₁) > 0 かつ P(r₂) > 0 なら P は (0, ∞) でちょうど
  一個の零点を持ち、それは (r₂, 2) にある。P(r₁)・P(r₂) の符号そのもの
  （数値的にはともに正：`/tmp/check_count2.py` で r₊ = 0.1〜0.99 で確認）
  の証明は次の段に残す。
-/
import CFT.Spherical.WedgeHorizonDefectB1W0Zeros

open Real Set Filter Topology
open CFT.WedgeDefectB1W0Zero
open CFT.WedgeDefectB1W0Deriv
open CFT.WedgeDefectB1W0Threshold
open CFT.WedgeDefectB1W0Zeros
open CFT.WedgeFirstZero

namespace CFT.WedgeDefectB1W0Count

/-- P は (0, r₁] 上で狭義単調減少（P′ = −2g < 0）。 -/
theorem defectQuarticB1W0_strictAntiOn_Ioc_zero_left {rp r₁ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0) :
    StrictAntiOn (fun r => defectQuarticB1W0 r rp) (Ioc 0 r₁) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r₁)
    (defectQuarticB1W0_continuous.continuousOn)
  intro x hx
  rw [interior_Ioc] at hx
  rw [defectQuarticB1W0_deriv_eq]
  have hg := defectCubicB1W0Deriv_pos_of_lt_left_zero h1 h1z hx
  linarith

/-- P は [r₁, r₂] 上で狭義単調増加（P′ = −2g > 0）。 -/
theorem defectQuarticB1W0_strictMonoOn_Icc_left_right {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0) :
    StrictMonoOn (fun r => defectQuarticB1W0 r rp) (Icc r₁ r₂) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc r₁ r₂)
    (defectQuarticB1W0_continuous.continuousOn)
  intro x hx
  rw [interior_Icc] at hx
  rw [defectQuarticB1W0_deriv_eq]
  have hg := defectCubicB1W0Deriv_neg_of_between_zeros h1 h1z h2 h2z hx
  linarith

/-- P は [r₂, ∞) 上で狭義単調減少（P′ = −2g < 0）。 -/
theorem defectQuarticB1W0_strictAntiOn_Ici_right {rp r₂ : ℝ}
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0) :
    StrictAntiOn (fun r => defectQuarticB1W0 r rp) (Ici r₂) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici r₂)
    (defectQuarticB1W0_continuous.continuousOn)
  intro x hx
  rw [interior_Ici] at hx
  rw [defectQuarticB1W0_deriv_eq]
  have hg := defectCubicB1W0Deriv_pos_of_gt_right_zero h2 h2z hx
  linarith

/-- P(r₁) > 0 なら (0, r₁] で P > 0。 -/
theorem defectQuarticB1W0_pos_of_critPos_left {rp r₁ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (hP1 : 0 < defectQuarticB1W0 r₁ rp) {x : ℝ} (hx : x ∈ Ioc 0 r₁) :
    0 < defectQuarticB1W0 x rp := by
  have hanti := defectQuarticB1W0_strictAntiOn_Ioc_zero_left h1 h1z
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have h := hanti hx ⟨h1.1, le_rfl⟩ hlt
    linarith
  · subst heq
    exact hP1

/-- P(r₁) > 0 なら [r₁, r₂] で P > 0。 -/
theorem defectQuarticB1W0_pos_of_critPos_mid {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hP1 : 0 < defectQuarticB1W0 r₁ rp) {x : ℝ} (hx : x ∈ Icc r₁ r₂) :
    0 < defectQuarticB1W0 x rp := by
  have hmono := defectQuarticB1W0_strictMonoOn_Icc_left_right h1 h1z h2 h2z
  have h := hmono.monotoneOn ⟨le_rfl, (h1.2.trans h2.1).le⟩ hx hx.1
  linarith

/-- P(r₂) < 0 なら [r₁, r₂] で P < 0。 -/
theorem defectQuarticB1W0_neg_of_critNeg_mid {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hP2 : defectQuarticB1W0 r₂ rp < 0) {x : ℝ} (hx : x ∈ Icc r₁ r₂) :
    defectQuarticB1W0 x rp < 0 := by
  have hmono := defectQuarticB1W0_strictMonoOn_Icc_left_right h1 h1z h2 h2z
  have h := hmono.monotoneOn hx ⟨(h1.2.trans h2.1).le, le_rfl⟩ hx.2
  linarith

/-- P(r₁) < 0 なら (0, r₁) に P の零点がある（中間値の定理）。 -/
theorem defectQuarticB1W0_exists_zero_left_of_critNeg {rp r₁ : ℝ} (hrp : 0 < rp)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (hP1 : defectQuarticB1W0 r₁ rp < 0) :
    ∃ r₀ ∈ Ioo 0 r₁, defectQuarticB1W0 r₀ rp = 0 :=
  exists_zero_of_sign_change h1.1
    defectQuarticB1W0_continuous.continuousOn
    (defectQuarticB1W0_pos_at_zero (ne_of_gt hrp))
    hP1

/-- (0, r₁] での P の零点は高々一個（狭義単調減少による単射性）。 -/
theorem defectQuarticB1W0_eq_of_zero_left {rp r₁ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0) {x y : ℝ}
    (hx : x ∈ Ioc 0 r₁) (hxz : defectQuarticB1W0 x rp = 0)
    (hy : y ∈ Ioc 0 r₁) (hyz : defectQuarticB1W0 y rp = 0) :
    x = y := by
  have hinj := (defectQuarticB1W0_strictAntiOn_Ioc_zero_left h1 h1z).injOn
  exact hinj hx hy (hxz.trans hyz.symm)

/-- P(r₁) < 0 なら (0, r₁) にちょうど一個の零点がある。 -/
theorem defectQuarticB1W0_exactly_one_zero_left_of_critNeg {rp r₁ : ℝ} (hrp : 0 < rp)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (hP1 : defectQuarticB1W0 r₁ rp < 0) :
    ∃ r₀ ∈ Ioo 0 r₁, defectQuarticB1W0 r₀ rp = 0 ∧
      ∀ r ∈ Ioc 0 r₁, defectQuarticB1W0 r rp = 0 → r = r₀ := by
  obtain ⟨r₀, hr₀, hz₀⟩ :=
    defectQuarticB1W0_exists_zero_left_of_critNeg hrp h1 hP1
  refine ⟨r₀, hr₀, hz₀, ?_⟩
  intro r hr hzr
  exact defectQuarticB1W0_eq_of_zero_left h1 h1z hr hzr ⟨hr₀.1, hr₀.2.le⟩ hz₀

/-- P(r₁) < 0 < P(r₂) なら (r₁, r₂) に P の零点がある（−P に中間値の定理）。 -/
theorem defectQuarticB1W0_exists_zero_mid_of_sign_change {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (hP1 : defectQuarticB1W0 r₁ rp < 0)
    (hP2 : 0 < defectQuarticB1W0 r₂ rp) :
    ∃ r₀ ∈ Ioo r₁ r₂, defectQuarticB1W0 r₀ rp = 0 := by
  have hlt : r₁ < r₂ := h1.2.trans h2.1
  have hcont : ContinuousOn (fun r => -defectQuarticB1W0 r rp) (Icc r₁ r₂) :=
    (defectQuarticB1W0_continuous.neg).continuousOn
  have ha : 0 < -defectQuarticB1W0 r₁ rp := neg_pos.mpr hP1
  have hb : -defectQuarticB1W0 r₂ rp < 0 := neg_lt_zero.mpr hP2
  obtain ⟨c, hc, hfc⟩ := exists_zero_of_sign_change hlt hcont ha hb
  exact ⟨c, hc, neg_eq_zero.mp hfc⟩

/-- [r₁, r₂] での P の零点は高々一個（狭義単調増加による単射性）。 -/
theorem defectQuarticB1W0_eq_of_zero_mid {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0) {x y : ℝ}
    (hx : x ∈ Icc r₁ r₂) (hxz : defectQuarticB1W0 x rp = 0)
    (hy : y ∈ Icc r₁ r₂) (hyz : defectQuarticB1W0 y rp = 0) :
    x = y := by
  have hinj := (defectQuarticB1W0_strictMonoOn_Icc_left_right h1 h1z h2 h2z).injOn
  exact hinj hx hy (hxz.trans hyz.symm)

/-- P(r₁) < 0 < P(r₂) なら (r₁, r₂) にちょうど一個の零点がある。 -/
theorem defectQuarticB1W0_exactly_one_zero_mid_of_sign_change {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hP1 : defectQuarticB1W0 r₁ rp < 0)
    (hP2 : 0 < defectQuarticB1W0 r₂ rp) :
    ∃ r₀ ∈ Ioo r₁ r₂, defectQuarticB1W0 r₀ rp = 0 ∧
      ∀ r ∈ Icc r₁ r₂, defectQuarticB1W0 r rp = 0 → r = r₀ := by
  obtain ⟨r₀, hr₀, hz₀⟩ :=
    defectQuarticB1W0_exists_zero_mid_of_sign_change h1 h2 hP1 hP2
  refine ⟨r₀, hr₀, hz₀, ?_⟩
  intro r hr hzr
  exact defectQuarticB1W0_eq_of_zero_mid h1 h1z h2 h2z hr hzr
    ⟨hr₀.1.le, hr₀.2.le⟩ hz₀

/-- P(r₁) = 0 なら (0, r₁] での P の零点は r₁ に限る。 -/
theorem defectQuarticB1W0_zero_left_eq_of_critZero {rp r₁ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (hP1 : defectQuarticB1W0 r₁ rp = 0) {x : ℝ} (hx : x ∈ Ioc 0 r₁)
    (hxz : defectQuarticB1W0 x rp = 0) :
    x = r₁ :=
  defectQuarticB1W0_eq_of_zero_left h1 h1z hx hxz ⟨h1.1, le_rfl⟩ hP1

/-- P(r₂) > 0 なら (r₂, 2) に P の零点がある（P(2) < 0 と中間値の定理）。 -/
theorem defectQuarticB1W0_exists_zero_right_of_critPos {rp r₂ : ℝ} (hrp : 0 < rp)
    (hle : rp ≤ 99 / 100)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (hP2 : 0 < defectQuarticB1W0 r₂ rp) :
    ∃ r₀ ∈ Ioo r₂ 2, defectQuarticB1W0 r₀ rp = 0 :=
  exists_zero_of_sign_change h2.2
    defectQuarticB1W0_continuous.continuousOn hP2
    (defectQuarticB1W0_neg_at_two hrp.le (by linarith))

/-- (r₂, ∞) での P の零点は高々一個（Rolle の定理と g の零点の一意性による）。 -/
theorem defectQuarticB1W0_eq_of_zero_right {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (huniq : ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂)
    {x y : ℝ} (hx : r₂ < x) (hxz : defectQuarticB1W0 x rp = 0)
    (hy : r₂ < y) (hyz : defectQuarticB1W0 y rp = 0) :
    x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exfalso
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt
      defectQuarticB1W0_continuous.continuousOn (hxz.trans hyz.symm)
    rw [defectQuarticB1W0_deriv_eq] at hc0
    have hgc : defectCubicB1W0Deriv c rp = 0 := by linarith
    have hcpos : 0 < c :=
      (defectQuarticCritPoint_pos.trans h2.1).trans (hx.trans hc.1)
    rcases huniq c hcpos hgc with hcr | hcr <;>
      linarith [hcr, h1.2, h2.1, hx, hc.1]
  · exact heq
  · exfalso
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hgt
      defectQuarticB1W0_continuous.continuousOn (hyz.trans hxz.symm)
    rw [defectQuarticB1W0_deriv_eq] at hc0
    have hgc : defectCubicB1W0Deriv c rp = 0 := by linarith
    have hcpos : 0 < c :=
      (defectQuarticCritPoint_pos.trans h2.1).trans (hy.trans hc.1)
    rcases huniq c hcpos hgc with hcr | hcr <;>
      linarith [hcr, h1.2, h2.1, hy, hc.1]

/-- P(r₂) > 0 なら (r₂, 2) にちょうど一個の零点があり、(r₂, ∞) には他にない。 -/
theorem defectQuarticB1W0_exactly_one_zero_right_of_critPos {rp r₁ r₂ : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (huniq : ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂)
    (hP2 : 0 < defectQuarticB1W0 r₂ rp) :
    ∃ r₀ ∈ Ioo r₂ 2, defectQuarticB1W0 r₀ rp = 0 ∧
      ∀ r : ℝ, r₂ < r → defectQuarticB1W0 r rp = 0 → r = r₀ := by
  obtain ⟨r₀, hr₀, hz₀⟩ :=
    defectQuarticB1W0_exists_zero_right_of_critPos hrp hle h2 hP2
  refine ⟨r₀, hr₀, hz₀, ?_⟩
  intro r hr hzr
  exact defectQuarticB1W0_eq_of_zero_right h1 h2 huniq hr hzr hr₀.1 hz₀

/-- P(r₁) > 0 なら (0, r₂] で P > 0（左区間と中間区間の組み合わせ）。 -/
theorem defectQuarticB1W0_pos_of_critPos {rp r₁ r₂ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hP1 : 0 < defectQuarticB1W0 r₁ rp) {x : ℝ} (hx : x ∈ Ioc 0 r₂) :
    0 < defectQuarticB1W0 x rp := by
  rcases le_total x r₁ with hle' | hge'
  · exact defectQuarticB1W0_pos_of_critPos_left h1 h1z hP1 ⟨hx.1, hle'⟩
  · exact defectQuarticB1W0_pos_of_critPos_mid h1 h1z h2 h2z hP1 ⟨hge', hx.2⟩

/-- 主結果：P(r₁) > 0 かつ P(r₂) > 0 なら P は (0, ∞) でちょうど一個の零点を持ち、
    それは (r₂, 2) にある。 -/
theorem defectQuarticB1W0_exactly_one_zero_of_critPos {rp r₁ r₂ : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (huniq : ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂)
    (hP1 : 0 < defectQuarticB1W0 r₁ rp)
    (hP2 : 0 < defectQuarticB1W0 r₂ rp) :
    ∃ r₀ : ℝ, r₂ < r₀ ∧ r₀ < 2 ∧ defectQuarticB1W0 r₀ rp = 0 ∧
      ∀ r : ℝ, 0 < r → defectQuarticB1W0 r rp = 0 → r = r₀ := by
  obtain ⟨r₀, hr₀, hz₀, huniq₀⟩ :=
    defectQuarticB1W0_exactly_one_zero_right_of_critPos hrp hle h1 h2 huniq hP2
  refine ⟨r₀, hr₀.1, hr₀.2, hz₀, ?_⟩
  intro r hr hzr
  rcases le_total r r₂ with hle' | hge'
  · exfalso
    have hpos := defectQuarticB1W0_pos_of_critPos h1 h1z h2 h2z hP1 ⟨hr, hle'⟩
    linarith
  · rcases lt_or_eq_of_le hge' with hlt | heq
    · exact huniq₀ r hlt hzr
    · subst heq
      linarith

end CFT.WedgeDefectB1W0Count
