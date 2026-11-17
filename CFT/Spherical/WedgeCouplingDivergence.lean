/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (c) の一般の場への適用：

  結合 A = Ω/(2r²) の発散の仕方について、`KruskalCouplingLimit` では
  クルスカル因子 Ω = 16M³e^{-r/2M}/r という明示形を代入して
  A = (8M³/r³)·e^{-r/2M} → +∞（r → 0⁺）を示した。ここでは明示形を
  使わず、一般の場 Ω, r に対して発散を証明する。発散を駆動するのは
  二つの機構のどちらかである：

  (i) Ω → +∞ かつ r² が有界なら A → +∞
      （`coupling_tendsto_atTop_of_Omega_tendsto`）。
  (ii) r → 0⁺ かつ Ω が正の定数で下から抑えられれば A → +∞
      （`coupling_tendsto_atTop_of_r_tendsto`）。

  どちらの場合も A/Ω = 1/(2r²) → +∞（r → 0⁺）であり、A は Ω よりも
  1/(2r²) 倍だけ速く発散する（`coupling_div_Omega_tendsto_atTop`）。
  くさび系の結合 `WedgeBalance.wedgeAFun` そのものへの版も付ける。
  一般補題はクルスカル因子の場合を回収することも確認する
  （`kruskalCoupling_tendsto_atTop_of_general`）。

  これで 12-8 (c) は、明示形での発散の仕方と一般の場への適用の
  両方が閉じた。残り：(a) 特性データと角条件による二重ヌルゲージの固定、
  (b) のくさび EYM 系の形での分類（近地平線極限 AdS₂ × S² など。
  温度の側は 6-2・9-3・`RNExtremalDoubleZero` で証明済み）。
-/
import Mathlib
import CFT.Spherical.WedgeEnergyBalance
import CFT.Spherical.KruskalOmegaLimit

open Filter Topology

namespace CFT.WedgeCouplingDivergence

/-- A/Ω = 1/(2r²)（Ω ≠ 0）。 -/
theorem coupling_div_Omega {α : Type*} (Om r : α → ℝ) (x : α) (hOm : Om x ≠ 0) :
    (Om x / (2 * (r x) ^ 2)) / Om x = 1 / (2 * (r x) ^ 2) := by
  rw [div_eq_iff hOm, div_mul_eq_mul_div, one_mul]

/-- Ω → +∞ かつ r² が有界なら A → +∞。 -/
theorem coupling_tendsto_atTop_of_Omega_tendsto {α : Type*} {l : Filter α}
    {Om r : α → ℝ} {R : ℝ} (hR : 0 < R)
    (hOm : Tendsto Om l atTop)
    (hr2 : ∀ᶠ x in l, (r x) ^ 2 ≤ R ^ 2)
    (hr0 : ∀ᶠ x in l, 0 < (r x) ^ 2) :
    Tendsto (fun x => Om x / (2 * (r x) ^ 2)) l atTop := by
  have hc : (0:ℝ) < 1 / (2 * R ^ 2) := by positivity
  have hbase : Tendsto (fun x => (1 / (2 * R ^ 2)) * Om x) l atTop :=
    Filter.Tendsto.const_mul_atTop hc hOm
  refine Filter.tendsto_atTop_mono' l ?_ hbase
  filter_upwards [hOm.eventually_ge_atTop 0, hr2, hr0] with x hx0 hx2 hxpos
  have hle : (1:ℝ) / (2 * R ^ 2) ≤ 1 / (2 * (r x) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h1 : (1 / (2 * R ^ 2)) * Om x ≤ Om x * (1 / (2 * (r x) ^ 2)) := by
    rw [mul_comm (1 / (2 * R ^ 2)) (Om x)]
    exact mul_le_mul_of_nonneg_left hle hx0
  have h2 : Om x * (1 / (2 * (r x) ^ 2)) = Om x / (2 * (r x) ^ 2) :=
    (div_eq_mul_one_div _ _).symm
  rw [h2] at h1
  exact h1

/-- r → 0⁺ かつ Ω が正の定数で下から抑えられれば A → +∞。 -/
theorem coupling_tendsto_atTop_of_r_tendsto {α : Type*} {l : Filter α}
    {Om r : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hr : Tendsto r l (𝓝[>] 0))
    (hOm : ∀ᶠ x in l, c ≤ Om x) :
    Tendsto (fun x => Om x / (2 * (r x) ^ 2)) l atTop := by
  have h1 : Tendsto (fun x => (1 / 2 : ℝ) * (r x)⁻¹ ^ 2) l atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 1 / 2)
      ((tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp
        (tendsto_inv_nhdsGT_zero.comp hr))
  have hbase : Tendsto (fun x => c * ((1 / 2 : ℝ) * (r x)⁻¹ ^ 2)) l atTop :=
    Filter.Tendsto.const_mul_atTop hc h1
  refine Filter.tendsto_atTop_mono' l ?_ hbase
  filter_upwards [hOm, hr.eventually (self_mem_nhdsWithin)] with x hcx hrx
  have hpos : (0:ℝ) ≤ (1 / 2 : ℝ) * (r x)⁻¹ ^ 2 := by positivity
  have h2 : c * ((1 / 2 : ℝ) * (r x)⁻¹ ^ 2) ≤ Om x * ((1 / 2 : ℝ) * (r x)⁻¹ ^ 2) :=
    mul_le_mul_of_nonneg_right hcx hpos
  have h3 : Om x * ((1 / 2 : ℝ) * (r x)⁻¹ ^ 2) = Om x / (2 * (r x) ^ 2) := by
    have hrne : r x ≠ 0 := ne_of_gt hrx
    field_simp
  rw [h3] at h2
  exact h2

/-- A/Ω = 1/(2r²) → +∞（r → 0⁺）。A は Ω よりも 1/(2r²) 倍だけ速く発散する。 -/
theorem coupling_div_Omega_tendsto_atTop {α : Type*} {l : Filter α}
    {Om r : α → ℝ}
    (hr : Tendsto r l (𝓝[>] 0))
    (hOm : ∀ᶠ x in l, Om x ≠ 0) :
    Tendsto (fun x => (Om x / (2 * (r x) ^ 2)) / Om x) l atTop := by
  have h1 : Tendsto (fun x => (1 / 2 : ℝ) * (r x)⁻¹ ^ 2) l atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 1 / 2)
      ((tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp
        (tendsto_inv_nhdsGT_zero.comp hr))
  apply h1.congr'
  filter_upwards [hOm, hr.eventually (self_mem_nhdsWithin)] with x hx hrx
  rw [coupling_div_Omega Om r x hx]
  have hrne : r x ≠ 0 := ne_of_gt hrx
  field_simp

/-- くさび系の結合 `wedgeAFun` そのもの：Ω → +∞ かつ r² 有界なら A → +∞。 -/
theorem wedge_coupling_tendsto_atTop_of_Omega_tendsto {l : Filter (ℝ × ℝ)}
    {Om r : ℝ → ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hOm : Tendsto (fun p : ℝ × ℝ => Om p.1 p.2) l atTop)
    (hr2 : ∀ᶠ p in l, (r p.1 p.2) ^ 2 ≤ R ^ 2)
    (hr0 : ∀ᶠ p in l, 0 < (r p.1 p.2) ^ 2) :
    Tendsto (fun p : ℝ × ℝ => CFT.WedgeBalance.wedgeAFun Om r p.1 p.2) l atTop :=
  coupling_tendsto_atTop_of_Omega_tendsto hR hOm hr2 hr0

/-- くさび系の結合 `wedgeAFun` そのもの：r → 0⁺ かつ Ω が正の定数で
    下から抑えられれば A → +∞。 -/
theorem wedge_coupling_tendsto_atTop_of_r_tendsto {l : Filter (ℝ × ℝ)}
    {Om r : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hr : Tendsto (fun p : ℝ × ℝ => r p.1 p.2) l (𝓝[>] 0))
    (hOm : ∀ᶠ p in l, c ≤ Om p.1 p.2) :
    Tendsto (fun p : ℝ × ℝ => CFT.WedgeBalance.wedgeAFun Om r p.1 p.2) l atTop :=
  coupling_tendsto_atTop_of_r_tendsto hc hr hOm

/-- くさび系の結合：A/Ω = 1/(2r²) → +∞（r → 0⁺）。 -/
theorem wedge_coupling_div_Omega_tendsto_atTop {l : Filter (ℝ × ℝ)}
    {Om r : ℝ → ℝ → ℝ}
    (hr : Tendsto (fun p : ℝ × ℝ => r p.1 p.2) l (𝓝[>] 0))
    (hOm : ∀ᶠ p in l, Om p.1 p.2 ≠ 0) :
    Tendsto (fun p : ℝ × ℝ =>
      CFT.WedgeBalance.wedgeAFun Om r p.1 p.2 / Om p.1 p.2) l atTop :=
  coupling_div_Omega_tendsto_atTop hr hOm

/-- 一般補題はクルスカル因子の場合を回収する：Ω = kruskalOmega M、r = id。 -/
theorem kruskalCoupling_tendsto_atTop_of_general (M : ℝ) (hM : 0 < M) :
    Tendsto (fun r : ℝ => CFT.KruskalOmega.kruskalOmega M r / (2 * r ^ 2))
      (𝓝[>] 0) atTop := by
  apply coupling_tendsto_atTop_of_r_tendsto (c := 1) one_pos tendsto_id
  exact (CFT.KruskalOmega.kruskalOmega_tendsto_atTop M hM).eventually_ge_atTop 1

end CFT.WedgeCouplingDivergence
