/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **S = 0 の角から離れた領域での導出（第一段：v 方向への伝播と R = 0 の判定）**。
  前段までで、S の v 微分の閉形 ∂_v S = (Ω_v/Ω)·S + R と、残余 R の係数
  （極端版）の明示公式・零点解析（C1・C2・C3・Q は地平線の外側で消えず、
  B1|_{W=0} は (0, ∞) でちょうど一個の零点 r₀ ∈ (r₂, 2) を持つ）が閉じた。
  ここでは二つのことを証明する。

  (1) S = 0 の伝播：R = 0 の v 区間上では S は線形 ODE ∂_v S = (Ω_v/Ω)·S
  をみたすので、区間内の一転で S = 0 なら区間全体で S = 0 になる
  （`defectSource_eq_zero_on_Icc_of_remainder_zero`）。鍵は実解析の一般補題
  （`eq_zero_of_hasDerivAt_eq_mul_of_exists_eq_zero`）で、補助関数
  ψ(t) = f(t)²·exp(−2M(t−a)) の単調性による。

  (2) R = 0 の判定：W = 0 かつ Dv W = 0 のもとで R は Dv r の二項だけになり
  （`defectSourceRemainder_eq_of_W_eq_zero_of_DvW_eq_zero`）、Dv r ≠ 0 なら
  R = 0 は一つの釣り合い式と同値
  （`defectSourceRemainder_eq_zero_iff_of_Dv_ne_zero`）。極端版でさらに
  Du r = 0 なら R = 0 ⟺ P(r) = 0 であり、P の零点の一意性から
  R = 0 ⟺ r = r₀（唯一の零点）になる
  （`defectSourceRemainder_extremal_eq_zero_iff_of_Du_eq_zero` と
  `..._of_rp`）。さらに P の符号は r₀ の両側で確定する
  （`defectQuarticB1W0_pos_of_lt_zero`・`defectQuarticB1W0_neg_of_gt_zero`）
  ので、Du r ≠ 0 の場合も R = 0 の点では Dv r·Du r の符号が r の r₀ に
  対する位置を決める（`defectSourceRemainder_extremal_eq_zero_side`）。

  これで「S = 0 の角から離れた領域での導出」は、R = 0 の領域と S = 0 の
  一点という二つの条件に帰着した。残りは、S = 0 になる一点の実際の構成と、
  ρ そのものの構成（対応仮説そのもの）である。
-/
import CFT.Spherical.WedgeHorizonDefectSourceDerivClosed
import CFT.Spherical.WedgeHorizonDefectRemainderExtremal
import CFT.Spherical.WedgeHorizonDefectB1W0CritSignRight
import CFT.Spherical.WedgeHorizonDefectC1Zero

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource
open CFT.WedgeDefectSourceDeriv CFT.WedgeDefectSourceDerivClosed
open CFT.WedgeDefectRemainderExtremal
open CFT.WedgeDefectB1W0Zero CFT.WedgeDefectB1W0Deriv CFT.WedgeDefectB1W0Count
open CFT.WedgeDefectB1W0CritSignRight CFT.WedgeDefectC1Zero
open CFT.RNLogDeriv

namespace CFT.WedgeDefectPropagation

/-- 線形 ODE の一意性の証明に使う補助関数 ψ(t) = f(t)²·exp(−2M(t−a))。 -/
noncomputable def odeSquareExp (f : ℝ → ℝ) (M a : ℝ) (t : ℝ) : ℝ :=
  (f t) ^ 2 * Real.exp (-2 * M * (t - a))

/-- 補助関数 ψ の微分公式。 -/
theorem odeSquareExp_hasDerivAt {f c : ℝ → ℝ} {M a t : ℝ}
    (hf : HasDerivAt f (c t * f t) t) :
    HasDerivAt (odeSquareExp f M a)
      (2 * (f t) ^ 2 * (c t - M) * Real.exp (-2 * M * (t - a))) t := by
  unfold odeSquareExp
  have h1 : HasDerivAt (fun s => (f s) ^ 2) (2 * f t * (c t * f t)) t := by
    have h := hf.pow 2
    simpa using h
  have h2 : HasDerivAt (fun s => Real.exp (-2 * M * (s - a)))
      (Real.exp (-2 * M * (t - a)) * (-2 * M)) t := by
    have h := (((hasDerivAt_id t).sub_const a).const_mul (-2 * M)).exp
    simpa using h
  have h3 := h1.mul h2
  convert h3 using 1
  ring

/-- ψ の微分は c(t) ≤ M のもとで 0 以下。 -/
theorem odeSquareExp_deriv_nonpos {f c : ℝ → ℝ} {M a t : ℝ}
    (hf : HasDerivAt f (c t * f t) t) (hc : c t ≤ M) :
    deriv (odeSquareExp f M a) t ≤ 0 := by
  rw [(odeSquareExp_hasDerivAt hf).deriv]
  have hexp : 0 < Real.exp (-2 * M * (t - a)) := Real.exp_pos _
  have hsq : (0 : ℝ) ≤ 2 * (f t) ^ 2 := by positivity
  have h1 : (2 : ℝ) * (f t) ^ 2 * (c t - M) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsq (sub_nonpos.mpr hc)
  exact mul_nonpos_of_nonpos_of_nonneg h1 hexp.le

/-- ψ の微分は M ≤ c(t) のもとで 0 以上。 -/
theorem odeSquareExp_deriv_nonneg {f c : ℝ → ℝ} {M a t : ℝ}
    (hf : HasDerivAt f (c t * f t) t) (hc : M ≤ c t) :
    0 ≤ deriv (odeSquareExp f M a) t := by
  rw [(odeSquareExp_hasDerivAt hf).deriv]
  have hexp : 0 < Real.exp (-2 * M * (t - a)) := Real.exp_pos _
  have hsq : (0 : ℝ) ≤ 2 * (f t) ^ 2 := by positivity
  have h1 : (0 : ℝ) ≤ 2 * (f t) ^ 2 * (c t - M) :=
    mul_nonneg hsq (sub_nonneg.mpr hc)
  exact mul_nonneg h1 hexp.le

/-- 線形 ODE の一意性（左端点版）：f′ = c·f、|c| ≤ M、f(a) = 0 なら [a, b] で f = 0。 -/
theorem eq_zero_of_hasDerivAt_eq_mul_of_eq_zero_left {f c : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (c t * f t) t)
    (hc : ∀ t ∈ Ioo a b, |c t| ≤ M)
    (h0 : f a = 0) {t : ℝ} (ht : t ∈ Icc a b) : f t = 0 := by
  have hcont : ContinuousOn (odeSquareExp f M a) (Icc a b) :=
    continuousOn_of_forall_continuousAt fun s hs =>
      (odeSquareExp_hasDerivAt (hf s hs)).continuousAt
  have hdiff : DifferentiableOn ℝ (odeSquareExp f M a) (interior (Icc a b)) := by
    intro s hs
    rw [interior_Icc] at hs
    exact (odeSquareExp_hasDerivAt (hf s ⟨hs.1.le, hs.2.le⟩)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (odeSquareExp f M a) (Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff (fun s hs => by
      rw [interior_Icc] at hs
      exact odeSquareExp_deriv_nonpos (hf s ⟨hs.1.le, hs.2.le⟩)
        (le_of_abs_le (hc s hs)))
  have hψa : odeSquareExp f M a a = 0 := by simp [odeSquareExp, h0]
  have hle : odeSquareExp f M a t ≤ odeSquareExp f M a a :=
    hanti (left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
  have hnn : 0 ≤ odeSquareExp f M a t :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hψt : odeSquareExp f M a t = 0 := by
    rw [hψa] at hle
    exact le_antisymm hle hnn
  have hsq : (f t) ^ 2 = 0 := by
    have h := hψt
    unfold odeSquareExp at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 (Real.exp_pos _).ne'
  exact sq_eq_zero_iff.mp hsq

/-- 線形 ODE の一意性（右端点版）：f(b) = 0 なら [a, b] で f = 0。 -/
theorem eq_zero_of_hasDerivAt_eq_mul_of_eq_zero_right {f c : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (c t * f t) t)
    (hc : ∀ t ∈ Ioo a b, |c t| ≤ M)
    (h0 : f b = 0) {t : ℝ} (ht : t ∈ Icc a b) : f t = 0 := by
  have hcont : ContinuousOn (odeSquareExp f (-M) b) (Icc a b) :=
    continuousOn_of_forall_continuousAt fun s hs =>
      (odeSquareExp_hasDerivAt (hf s hs)).continuousAt
  have hdiff : DifferentiableOn ℝ (odeSquareExp f (-M) b) (interior (Icc a b)) := by
    intro s hs
    rw [interior_Icc] at hs
    exact (odeSquareExp_hasDerivAt (hf s ⟨hs.1.le, hs.2.le⟩)).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (odeSquareExp f (-M) b) (Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff (fun s hs => by
      rw [interior_Icc] at hs
      exact odeSquareExp_deriv_nonneg (hf s ⟨hs.1.le, hs.2.le⟩)
        (neg_le_of_abs_le (hc s hs)))
  have hφb : odeSquareExp f (-M) b b = 0 := by simp [odeSquareExp, h0]
  have hle : odeSquareExp f (-M) b t ≤ odeSquareExp f (-M) b b :=
    hmono ht (right_mem_Icc.mpr (ht.1.trans ht.2)) ht.2
  have hnn : 0 ≤ odeSquareExp f (-M) b t :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hφt : odeSquareExp f (-M) b t = 0 := by
    rw [hφb] at hle
    exact le_antisymm hle hnn
  have hsq : (f t) ^ 2 = 0 := by
    have h := hφt
    unfold odeSquareExp at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 (Real.exp_pos _).ne'
  exact sq_eq_zero_iff.mp hsq

/-- 線形 ODE の一意性（両側版）：区間内の一点で 0 なら区間全体で 0。 -/
theorem eq_zero_of_hasDerivAt_eq_mul_of_exists_eq_zero {f c : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (c t * f t) t)
    (hc : ∀ t ∈ Ioo a b, |c t| ≤ M)
    (h0 : ∃ t₀ ∈ Icc a b, f t₀ = 0) {t : ℝ} (ht : t ∈ Icc a b) : f t = 0 := by
  obtain ⟨t₀, ht₀, hft₀⟩ := h0
  rcases le_total t t₀ with hle | hge
  · exact eq_zero_of_hasDerivAt_eq_mul_of_eq_zero_right
      (fun s hs => hf s ⟨hs.1, hs.2.trans ht₀.2⟩)
      (fun s hs => hc s ⟨hs.1, hs.2.trans_le ht₀.2⟩)
      hft₀ ⟨ht.1, hle⟩
  · exact eq_zero_of_hasDerivAt_eq_mul_of_eq_zero_left
      (fun s hs => hf s ⟨ht₀.1.trans hs.1, hs.2⟩)
      (fun s hs => hc s ⟨ht₀.1.trans_lt hs.1, hs.2⟩)
      hft₀ ⟨hge, ht.2⟩

/-- S = 0 の v 方向への伝播：区間上で R = 0 かつ一点で S = 0 なら区間全体で S = 0。 -/
theorem defectSource_eq_zero_on_Icc_of_remainder_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ} {u v₀ v₁ M : ℝ}
    (heq : WedgeEvolutionEqs F) (hcon : WedgeConstraints F)
    (hOm : ∀ v ∈ Icc v₀ v₁, F.Om u v ≠ 0)
    (hr : ∀ v ∈ Icc v₀ v₁, F.r u v ≠ 0)
    (hg : ∀ v ∈ Icc v₀ v₁, HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : ∀ v ∈ Icc v₀ v₁, HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : ∀ v ∈ Icc v₀ v₁, HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : ∀ v ∈ Icc v₀ v₁, HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : ∀ v ∈ Icc v₀ v₁, HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : ∀ v ∈ Icc v₀ v₁, HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : ∀ v ∈ Icc v₀ v₁, HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v)
    (hR : ∀ v ∈ Icc v₀ v₁, defectSourceRemainder F g g' g'' u v = 0)
    (hM : ∀ v ∈ Ioo v₀ v₁, |Dv F.Om u v / F.Om u v| ≤ M)
    (h0 : ∃ vstar ∈ Icc v₀ v₁, defectSource F g g' u vstar = 0)
    {v : ℝ} (hv : v ∈ Icc v₀ v₁) :
    defectSource F g g' u v = 0 := by
  apply eq_zero_of_hasDerivAt_eq_mul_of_exists_eq_zero
    (f := fun v' => defectSource F g g' u v')
    (c := fun v' => Dv F.Om u v' / F.Om u v')
  · intro t ht
    have h := defectSource_hasDerivAt_v_closed heq hcon (hOm t ht) (hr t ht)
      (hg t ht) (hg' t ht) (hOmv t ht) (hWv t ht) (hrv t ht) (hru t ht) (hrvv t ht)
    rw [hR t ht, add_zero] at h
    exact h
  · exact hM
  · exact h0
  · exact hv

/-- W = 0 かつ Dv W = 0 のもとで、残余 R は Dv r の二項だけになる。 -/
theorem defectSourceRemainder_eq_of_W_eq_zero_of_DvW_eq_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hW : F.W u v = 0) (hWv : Dv F.W u v = 0) :
    defectSourceRemainder F g g' g'' u v
      = Dv F.r u v * (F.Om u v / (F.r u v) ^ 5)
          * defectRemainderCoeffB1W0 g g' (F.r u v)
        + (Dv F.r u v) ^ 2 * (-(Du F.r u v) / (F.r u v) ^ 3)
          * defectRemainderCoeffC1 g g' g'' (F.r u v) := by
  rw [defectSourceRemainder_eq_coeffs, hWv, defectRemainderCoeffB1_eq, hW]
  simp

/-- W = 0、Dv W = 0、Dv r ≠ 0 のもとで、R = 0 は一つの釣り合い式と同値。 -/
theorem defectSourceRemainder_eq_zero_iff_of_Dv_ne_zero {F : WedgeFields}
    {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hW : F.W u v = 0) (hWv : Dv F.W u v = 0) (hrv : Dv F.r u v ≠ 0) :
    defectSourceRemainder F g g' g'' u v = 0 ↔
      F.Om u v / (F.r u v) ^ 5 * defectRemainderCoeffB1W0 g g' (F.r u v)
        + Dv F.r u v * ((-(Du F.r u v) / (F.r u v) ^ 3)
          * defectRemainderCoeffC1 g g' g'' (F.r u v)) = 0 := by
  have key : Dv F.r u v * (F.Om u v / (F.r u v) ^ 5
        * defectRemainderCoeffB1W0 g g' (F.r u v)
        + Dv F.r u v * ((-(Du F.r u v) / (F.r u v) ^ 3)
          * defectRemainderCoeffC1 g g' g'' (F.r u v)))
      = Dv F.r u v * (F.Om u v / (F.r u v) ^ 5)
          * defectRemainderCoeffB1W0 g g' (F.r u v)
        + (Dv F.r u v) ^ 2 * (-(Du F.r u v) / (F.r u v) ^ 3)
          * defectRemainderCoeffC1 g g' g'' (F.r u v) := by ring
  rw [defectSourceRemainder_eq_of_W_eq_zero_of_DvW_eq_zero hW hWv, ← key, mul_eq_zero]
  exact or_iff_right hrv

/-- 極端版・W = 0・Dv W = 0・Du r = 0 のもとで、R = 0 ⟺ P(r) = 0。 -/
theorem defectSourceRemainder_extremal_eq_zero_iff_of_Du_eq_zero {F : WedgeFields}
    {rp u v : ℝ}
    (hW : F.W u v = 0) (hWv : Dv F.W u v = 0)
    (hDu : Du F.r u v = 0) (hrv : Dv F.r u v ≠ 0)
    (hr : 0 < F.r u v) (hrne : F.r u v ≠ rp) (hOm : F.Om u v ≠ 0) :
    defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u v = 0 ↔
      defectQuarticB1W0 (F.r u v) rp = 0 := by
  have hr0 : F.r u v ≠ 0 := ne_of_gt hr
  have hB1 : defectRemainderCoeffB1W0 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (F.r u v)
      = defectQuarticB1W0 (F.r u v) rp / (F.r u v - rp) ^ 2 := by
    rw [defectRemainderCoeffB1W0_extremal hr0 hrne]
    rfl
  rw [defectSourceRemainder_eq_of_W_eq_zero_of_DvW_eq_zero hW hWv, hDu, hB1]
  simp only [neg_zero, zero_div, mul_zero, zero_mul, add_zero]
  constructor
  · intro h
    have hne1 : Dv F.r u v * (F.Om u v / (F.r u v) ^ 5) ≠ 0 :=
      mul_ne_zero hrv (div_ne_zero hOm (pow_ne_zero 5 hr0))
    have hne2 : (F.r u v - rp) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr hrne)
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hne1
    · exact (div_eq_zero_iff.mp h1).resolve_right hne2
  · intro h
    rw [h]
    simp

/-- 極端版・W = 0・Dv W = 0・Du r = 0 のもとで、R = 0 ⟺ r は P の唯一の零点 r₀。 -/
theorem defectSourceRemainder_extremal_eq_zero_iff_of_Du_eq_zero_of_rp
    {F : WedgeFields} {rp u v : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (hW : F.W u v = 0) (hWv : Dv F.W u v = 0)
    (hDu : Du F.r u v = 0) (hrv : Dv F.r u v ≠ 0)
    (hr : 0 < F.r u v) (hrne : F.r u v ≠ rp) (hOm : F.Om u v ≠ 0) :
    defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u v = 0 ↔
      ∃ r₀ : ℝ, 0 < r₀ ∧ defectQuarticB1W0 r₀ rp = 0 ∧ F.r u v = r₀ ∧
        ∀ r : ℝ, 0 < r → defectQuarticB1W0 r rp = 0 → r = r₀ := by
  rw [defectSourceRemainder_extremal_eq_zero_iff_of_Du_eq_zero hW hWv hDu hrv hr
    hrne hOm]
  constructor
  · intro hP
    obtain ⟨r₀, hr₀, hz₀, huniq₀⟩ :=
      defectQuarticB1W0_exactly_one_zero_of_rp hrp hle
    exact ⟨r₀, hr₀, hz₀, huniq₀ _ hr hP, huniq₀⟩
  · rintro ⟨r₀, -, hz₀, hr₀eq, -⟩
    rw [hr₀eq]
    exact hz₀

/-- P は唯一の零点 r₀ の左側で正。 -/
theorem defectQuarticB1W0_pos_of_lt_zero {rp r₁ r₂ r₀ : ℝ}
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hP1 : 0 < defectQuarticB1W0 r₁ rp)
    (hr₀ : r₂ < r₀) (hz₀ : defectQuarticB1W0 r₀ rp = 0)
    {x : ℝ} (hx : 0 < x) (hx₀ : x < r₀) :
    0 < defectQuarticB1W0 x rp := by
  rcases le_total x r₂ with hle' | hge'
  · exact defectQuarticB1W0_pos_of_critPos h1 h1z h2 h2z hP1 ⟨hx, hle'⟩
  · have hanti := defectQuarticB1W0_strictAntiOn_Ici_right h2 h2z
    have h : defectQuarticB1W0 r₀ rp < defectQuarticB1W0 x rp :=
      hanti (mem_Ici.mpr hge') (mem_Ici.mpr hr₀.le) hx₀
    rw [hz₀] at h
    exact h

/-- P は唯一の零点 r₀ の右側で負。 -/
theorem defectQuarticB1W0_neg_of_gt_zero {rp r₂ r₀ : ℝ}
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (hr₀ : r₂ < r₀) (hz₀ : defectQuarticB1W0 r₀ rp = 0)
    {x : ℝ} (hx₀ : r₀ < x) :
    defectQuarticB1W0 x rp < 0 := by
  have hanti := defectQuarticB1W0_strictAntiOn_Ici_right h2 h2z
  have h : defectQuarticB1W0 x rp < defectQuarticB1W0 r₀ rp :=
    hanti (mem_Ici.mpr hr₀.le) (mem_Ici.mpr (hr₀.trans hx₀).le) hx₀
  rw [hz₀] at h
  exact h

/-- 極端版・W = 0・Dv W = 0、地平線の外側では、R = 0 の点での Dv r·Du r の符号が
    r の r₀ に対する位置を決める。 -/
theorem defectSourceRemainder_extremal_eq_zero_side {F : WedgeFields}
    {rp r₁ r₂ u v : ℝ}
    (hrp : 0 < rp) (hle : rp ≤ 99 / 100)
    (h1 : r₁ ∈ Ioo 0 (defectQuarticCritPoint rp))
    (h1z : defectCubicB1W0Deriv r₁ rp = 0)
    (h2 : r₂ ∈ Ioo (defectQuarticCritPoint rp) 2)
    (h2z : defectCubicB1W0Deriv r₂ rp = 0)
    (huniq : ∀ r : ℝ, 0 < r → defectCubicB1W0Deriv r rp = 0 → r = r₁ ∨ r = r₂)
    (hP1 : 0 < defectQuarticB1W0 r₁ rp)
    (hW : F.W u v = 0) (hWv : Dv F.W u v = 0)
    (hrv : Dv F.r u v ≠ 0)
    (hr : rp < F.r u v) (hOm : 0 < F.Om u v)
    (hR : defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u v = 0) :
    ∃ r₀ : ℝ, r₂ < r₀ ∧ r₀ < 2 ∧ defectQuarticB1W0 r₀ rp = 0 ∧
      (0 < Dv F.r u v * Du F.r u v → F.r u v < r₀) ∧
      (Dv F.r u v * Du F.r u v < 0 → r₀ < F.r u v) := by
  obtain ⟨r₀, hr₀, hr₀2, hz₀, _huniq₀⟩ :=
    defectQuarticB1W0_exactly_one_zero hrp hle h1 h1z h2 h2z huniq
  have hr0 : F.r u v ≠ 0 := ne_of_gt (lt_trans hrp hr)
  have hC1 : 0 < defectRemainderCoeffC1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
      (rnLogDeriv'' rp rp) (F.r u v) :=
    defectRemainderCoeffC1_extremal_pos_of_gt hrp hr
  have hB1 : defectRemainderCoeffB1W0 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (F.r u v)
      = defectQuarticB1W0 (F.r u v) rp / (F.r u v - rp) ^ 2 := by
    rw [defectRemainderCoeffB1W0_extremal hr0 (ne_of_gt hr)]
    rfl
  have hbal := (defectSourceRemainder_eq_zero_iff_of_Dv_ne_zero hW hWv hrv).mp hR
  rw [hB1] at hbal
  -- 分母を払った釣り合い式
  have hkey : F.Om u v * defectQuarticB1W0 (F.r u v) rp * (F.r u v) ^ 3
      + Dv F.r u v * (-Du F.r u v) * defectRemainderCoeffC1 (rnLogDeriv rp rp)
        (rnLogDeriv' rp rp) (rnLogDeriv'' rp rp) (F.r u v)
        * (F.r u v) ^ 5 * (F.r u v - rp) ^ 2 = 0 := by
    have h1' : (F.r u v) ^ 5 ≠ 0 := pow_ne_zero 5 hr0
    have h2' : (F.r u v - rp) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hr))
    have h3' : (F.r u v) ^ 3 ≠ 0 := pow_ne_zero 3 hr0
    field_simp at hbal
    linear_combination hbal
  -- P = (Dv r·Du r) ×（正の因子）の形
  have hPeq : F.Om u v * defectQuarticB1W0 (F.r u v) rp * (F.r u v) ^ 3
      = Dv F.r u v * Du F.r u v * defectRemainderCoeffC1 (rnLogDeriv rp rp)
        (rnLogDeriv' rp rp) (rnLogDeriv'' rp rp) (F.r u v)
        * (F.r u v) ^ 5 * (F.r u v - rp) ^ 2 := by
    linear_combination hkey
  refine ⟨r₀, hr₀, hr₀2, hz₀, ?_, ?_⟩
  · intro hs
    have hpos : (0 : ℝ) < F.Om u v * (F.r u v) ^ 3 :=
      mul_pos hOm (pow_pos (lt_trans hrp hr) 3)
    have h1 : (0 : ℝ) < Dv F.r u v * Du F.r u v * defectRemainderCoeffC1
        (rnLogDeriv rp rp) (rnLogDeriv' rp rp) (rnLogDeriv'' rp rp) (F.r u v)
        * (F.r u v) ^ 5 * (F.r u v - rp) ^ 2 :=
      mul_pos (mul_pos (mul_pos hs hC1) (pow_pos (lt_trans hrp hr) 5))
        (pow_pos (sub_pos.mpr hr) 2)
    rw [← hPeq] at h1
    have h2p : (0 : ℝ) < (F.Om u v * (F.r u v) ^ 3)
        * defectQuarticB1W0 (F.r u v) rp := by
      have h3 : (F.Om u v * (F.r u v) ^ 3) * defectQuarticB1W0 (F.r u v) rp
          = F.Om u v * defectQuarticB1W0 (F.r u v) rp * (F.r u v) ^ 3 := by ring
      rw [h3]; exact h1
    have hP : 0 < defectQuarticB1W0 (F.r u v) rp := pos_of_mul_pos_right h2p hpos.le
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [← heq] at hP
      rw [hz₀] at hP
      exact lt_irrefl _ hP
    · have hneg := defectQuarticB1W0_neg_of_gt_zero h2 h2z hr₀ hz₀ hlt
      linarith
  · intro hs
    have hpos : (0 : ℝ) < F.Om u v * (F.r u v) ^ 3 :=
      mul_pos hOm (pow_pos (lt_trans hrp hr) 3)
    have h1n : Dv F.r u v * Du F.r u v * defectRemainderCoeffC1 (rnLogDeriv rp rp)
        (rnLogDeriv' rp rp) (rnLogDeriv'' rp rp) (F.r u v)
        * (F.r u v) ^ 5 * (F.r u v - rp) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hs hC1)
        (pow_pos (lt_trans hrp hr) 5)) (pow_pos (sub_pos.mpr hr) 2)
    rw [← hPeq] at h1n
    have h2n : (F.Om u v * (F.r u v) ^ 3)
        * defectQuarticB1W0 (F.r u v) rp < 0 := by
      have h3 : (F.Om u v * (F.r u v) ^ 3) * defectQuarticB1W0 (F.r u v) rp
          = F.Om u v * defectQuarticB1W0 (F.r u v) rp * (F.r u v) ^ 3 := by ring
      rw [h3]; exact h1n
    have hP : defectQuarticB1W0 (F.r u v) rp < 0 := by
      rcases mul_neg_iff.mp h2n with ⟨_, hPneg⟩ | ⟨hneg, _⟩
      · exact hPneg
      · exact absurd hneg (not_lt_of_ge hpos.le)
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq] at hP
      rw [hz₀] at hP
      exact lt_irrefl _ hP
    · have hpos' := defectQuarticB1W0_pos_of_lt_zero h1 h1z h2 h2z hP1 hr₀ hz₀
        (lt_trans hrp hr) hlt
      linarith

end CFT.WedgeDefectPropagation
