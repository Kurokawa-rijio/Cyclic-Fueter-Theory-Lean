/-
  α-IV.5(Z9-a, b, c):首の喉の有限時間崩壊を本当に証明する(微分不等式を仮定しない版)

  中心の式(喉 ∂_s r = 0 での固有時 τ についての常微分方程式、α-IV.3 で二重 null 方程式から導出):
      r̈ = acc(ℓ, r, ṙ, W) = −(ṙ² + 1 − ℓ²/r²)/(2r) − W²/r
  W は横向きの波の傾き W_l(源)。初期データの類:
      転回点から出発(r(τ₁) = r₁ > 0、ṙ(τ₁) = 0)、源について (rW)² ≥ κ、2κ ≥ ℓ²。
  以前の collapse_time、energy_inequality は「ṙ ≤ 0 が全時間で成り立つ」「微分不等式が全時間で成り立つ」を
  仮定していた。ここではそれらを方程式から導く:
    * acc_le:類の中では r̈ ≤ −1/(2r)(加速度は常に内向き)
    * rp_nonpos:ṙ ≤ 0 が全区間で成り立つ(Mathlib の境界比較定理)
    * rp_neg:τ > τ₁ で ṙ < 0(厳密)、r_lt:τ > τ₁ で r < r₁
    * energy_lower:r ṙ² ≥ r₁ − r(エネルギー不等式から)
    * psi_deriv:Ψ(x) = r₁ arccos √(x/r₁) + √(x(r₁ − x)) の微分は −√x/√(r₁ − x)
    * z9_collapse:正の解が [τ₁, τ₂] に存在するなら τ₂ − τ₁ < π r₁/2
      ⇒ 喉の正の解は固有時 π r₁/2 より長くは続かない。r₁ ≤ ℓ* なら t_sing < π ℓ*/2(Z9-b の目標)。
      (κ を一定に保つ場合の正確な崩壊時間は T = r₁[√c + (1 − c)/2·(π/2 − arcsin((c − 1)/(c + 1)))]、
       c = (2κ − ℓ²)/r₁²。c → 0 で π r₁/2 に一致し、境界は鋭い。sympy・数値で検算)
    * z9_reaches_zero:解が [τ₁, τ₁ + πr₁/2] 全体で続くなら、その中で r = 0 になる(中間値の定理)
    * z44_from_z9:これで α-VIII.7(Z44)の仮定 hcollapse が Z9 から供給される
  閾値が鋭いこと(Z9-a):
    * static_iff:(rW)² = κ 一定のとき、静止した喉(ṙ = 0、r̈ = 0)は r² = ℓ² − 2κ のときに限る
      ⇒ 2κ < ℓ² なら静止解があり(崩壊しない)、2κ ≥ ℓ² なら静止解はなく必ず崩壊する
    * neck_frequency:W = 0 の首 r = ℓ のまわりの線形化は r̈ = −(r − ℓ)/ℓ²(周期 2πℓ の振動、安定)
  質量の定義の再検算(Z9-b, c、台帳 e3f51db2 の注意):
    * ms_general:Misner–Sharp 2Gm = r(1 − h^{ab}∂_a r ∂_b r) は、h = diag(−N², 1)、∂_t r = N ṙ、∂_s r = 0 で r(1 + ṙ²)
    E = r(1 + ṙ²) + ℓ²/r = 2Gm_MS + ℓ²/r(E は MS 質量ではない、定義から)
    * rn_param:Reissner–Nordström f = 1 − E/r + ℓ²/r² では r(1 − f) + ℓ²/r = E:E は RN の質量母数 2GM
    * rn_extremal:E = 2ℓ(首の値)なら f = (1 − ℓ/r)²(極限 RN、首は極限 RN の地平面近傍 AdS₂ × S²)
    * ms_deriv:d(2Gm_MS)/dτ = ṙ(ℓ²/r² − 2W²)、E は dE/dτ = −2W²ṙ(既存 energy_deriv)
    * ms_increases:崩壊中(ṙ ≤ 0)、2(rW)² ≥ ℓ² なら MS 質量も増える
      ⇒ 崩壊の条件 2κ ≥ ℓ² は、MS 質量が増える条件と同じ一つの式(一つの質量変数で整理できた)
    * throat_trapped:喉では 2Gm_MS/r = 1 + ṙ² ≥ 1、二つの null 膨張は (2/r)ṙ(同符号):
      崩壊中の喉は捕捉面
-/
import CFT.AlphaCompleteA
import CFT.AlphaVIII_Z44
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real Set

namespace CFT.Z9

/-- 中心の式の右辺 -/
noncomputable def acc (l r rp W : ℝ) : ℝ := -(rp ^ 2 + 1 - l ^ 2 / r ^ 2) / (2 * r) - W ^ 2 / r

/-- 類の中では加速度は −1/(2r) 以下 -/
theorem acc_le (l r rp W κ : ℝ) (hr : 0 < r) (hk : l ^ 2 ≤ 2 * κ) (hW : κ ≤ W ^ 2 * r ^ 2) :
    acc l r rp W ≤ -1 / (2 * r) := by
  have hr3 : 0 < r ^ 3 := by positivity
  have e : acc l r rp W + 1 / (2 * r) = -(rp ^ 2) / (2 * r) + (l ^ 2 - 2 * (W ^ 2 * r ^ 2)) / (2 * r ^ 3) := by
    unfold acc; field_simp; ring
  have h1 : -(rp ^ 2) / (2 * r) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg rp]) (by positivity)
  have h2 : (l ^ 2 - 2 * (W ^ 2 * r ^ 2)) / (2 * r ^ 3) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have : acc l r rp W + 1 / (2 * r) ≤ 0 := by rw [e]; linarith
  have : -1 / (2 * r) = -(1 / (2 * r)) := by ring
  linarith

section collapse

variable (r rp W : ℝ → ℝ) (l κ τ1 τ2 r1 : ℝ)

/-- ṙ ≤ 0 が全区間で成り立つ -/
theorem rp_nonpos (hpos : ∀ τ ∈ Icc τ1 τ2, 0 < r τ)
    (h2 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2) (h0 : rp τ1 = 0) :
    ∀ τ ∈ Icc τ1 τ2, rp τ ≤ 0 := by
  have hIco : ∀ x ∈ Ico τ1 τ2, x ∈ Icc τ1 τ2 := fun x hx => Ico_subset_Icc_self hx
  refine image_le_of_deriv_right_lt_deriv_boundary' (f' := fun τ => acc l (r τ) (rp τ) (W τ))
    (B := fun _ => 0) (B' := fun _ => 0) ?_ ?_ (by simp [h0]) continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _) ?_
  · intro x hx; exact (h2 x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (h2 x (hIco x hx)).hasDerivWithinAt
  · intro x hx _
    have hx' := hIco x hx
    have := acc_le l (r x) (rp x) (W x) κ (hpos x hx') hk (hW x hx')
    have : -1 / (2 * r x) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith [hpos x hx'])
    simp only; linarith

/-- r は単調減少で r ≤ r₁ -/
theorem r_le (h1 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt r (rp τ) τ) (hdown : ∀ τ ∈ Icc τ1 τ2, rp τ ≤ 0)
    (hr1 : r τ1 = r1) : ∀ τ ∈ Icc τ1 τ2, r τ ≤ r1 := by
  have hanti : AntitoneOn r (Icc τ1 τ2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc τ1 τ2)
    · intro x hx; exact (h1 x hx).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Icc] at hx
      exact (h1 x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(h1 x (Ioo_subset_Icc_self hx)).deriv]; exact hdown x (Ioo_subset_Icc_self hx)
  intro τ hτ
  rw [← hr1]; exact hanti (left_mem_Icc.2 (le_trans hτ.1 hτ.2)) hτ hτ.1

/-- τ > τ₁ では ṙ ≤ −(τ − τ₁)/(4r₁) < 0 -/
theorem rp_bound (hpos : ∀ τ ∈ Icc τ1 τ2, 0 < r τ)
    (h1 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2) (h0 : rp τ1 = 0)
    (hr1 : r τ1 = r1) : ∀ τ ∈ Icc τ1 τ2, rp τ ≤ -(τ - τ1) / (4 * r1) := by
  have hdown := rp_nonpos r rp W l κ τ1 τ2 hpos h2 hk hW h0
  have hle := r_le r rp τ1 τ2 r1 h1 hdown hr1
  have hIco : ∀ x ∈ Ico τ1 τ2, x ∈ Icc τ1 τ2 := fun x hx => Ico_subset_Icc_self hx
  refine image_le_of_deriv_right_lt_deriv_boundary' (f' := fun τ => acc l (r τ) (rp τ) (W τ))
    (B := fun τ => -(τ - τ1) / (4 * r1)) (B' := fun _ => -1 / (4 * r1)) ?_ ?_ (by simp [h0])
    (by fun_prop) ?_ ?_
  · intro x hx; exact (h2 x hx).continuousAt.continuousWithinAt
  · intro x hx; exact (h2 x (hIco x hx)).hasDerivWithinAt
  · intro x _
    have := (((hasDerivAt_id x).sub_const τ1).neg.div_const (4 * r1)).hasDerivWithinAt (s := Ici x)
    convert this using 1
  · intro x hx _
    have hx' := hIco x hx
    have hrx := hpos x hx'
    have hr1p : 0 < r1 := by rw [← hr1]; exact hpos τ1 (left_mem_Icc.2 (le_trans hx.1 hx.2.le))
    have ha := acc_le l (r x) (rp x) (W x) κ hrx hk (hW x hx')
    have hb : -1 / (2 * r x) ≤ -1 / (2 * r1) := by
      rw [div_le_div_iff (by positivity) (by positivity)]; nlinarith [hle x hx']
    have hc : -1 / (2 * r1) < -1 / (4 * r1) := by
      rw [div_lt_div_iff (by positivity) (by positivity)]; nlinarith
    simp only; linarith

/-- τ > τ₁ では r < r₁ -/
theorem r_lt (hpos : ∀ τ ∈ Icc τ1 τ2, 0 < r τ)
    (h1 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2) (h0 : rp τ1 = 0)
    (hr1 : r τ1 = r1) : ∀ τ ∈ Ioc τ1 τ2, r τ < r1 := by
  have hb := rp_bound r rp W l κ τ1 τ2 r1 hpos h1 h2 hk hW h0 hr1
  have hstrict : StrictAntiOn r (Icc τ1 τ2) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc τ1 τ2)
    · intro x hx; exact (h1 x hx).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Icc] at hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(h1 x hx').deriv]
      have hr1p : 0 < r1 := by rw [← hr1]; exact hpos τ1 (left_mem_Icc.2 (le_trans hx'.1 hx'.2))
      have : -(x - τ1) / (4 * r1) < 0 := div_neg_of_neg_of_pos (by linarith [hx.1]) (by positivity)
      linarith [hb x hx']
  intro τ hτ
  rw [← hr1]
  exact hstrict (left_mem_Icc.2 (le_trans hτ.1.le hτ.2)) (Ioc_subset_Icc_self hτ) hτ.1

/-- エネルギー不等式の帰結:r ṙ² ≥ r₁ − r -/
theorem energy_lower (hpos : ∀ τ ∈ Icc τ1 τ2, 0 < r τ)
    (h1 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2) (h0 : rp τ1 = 0)
    (hr1 : r τ1 = r1) (h12 : τ1 ≤ τ2) : ∀ τ ∈ Icc τ1 τ2, r1 - r τ ≤ r τ * rp τ ^ 2 := by
  have hdown := rp_nonpos r rp W l κ τ1 τ2 hpos h2 hk hW h0
  have hle := r_le r rp τ1 τ2 r1 h1 hdown hr1
  have hE := CFT.AlphaCompleteA.energy_inequality r rp W l κ τ1 τ2 h12 hpos h1
    (fun τ hτ => by have := h2 τ hτ; unfold acc at this; exact this) hdown hW
  intro τ hτ
  have e := hE τ hτ
  rw [h0, hr1] at e
  have hr := hpos τ hτ
  have hr1p : 0 < r1 := by rw [← hr1]; exact hpos τ1 (left_mem_Icc.2 h12)
  have hrr := hle τ hτ
  -- (2κ − ℓ²)(1/r − 1/r₁) ≥ 0
  have hinv : 0 ≤ (2 * κ - l ^ 2) * (1 / r τ - 1 / r1) := by
    apply mul_nonneg (by linarith)
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hr hrr
  have e2 : r τ * (1 + rp τ ^ 2) + l ^ 2 / r τ - 2 * κ / r τ - (r1 * (1 + 0 ^ 2) + l ^ 2 / r1 - 2 * κ / r1)
      = r τ * rp τ ^ 2 - (r1 - r τ) - (2 * κ - l ^ 2) * (1 / r τ - 1 / r1) := by
    field_simp; ring
  nlinarith [e2, e, hinv]

end collapse

/-! ### 比較関数 Ψ -/

/-- Ψ(x) = r₁ arccos √(x/r₁) + √(x(r₁ − x)) -/
noncomputable def Psi (r1 x : ℝ) : ℝ := r1 * arccos (√(x / r1)) + √(x * (r1 - x))

theorem psi_deriv (r1 x : ℝ) (hx : 0 < x) (hx1 : x < r1) :
    HasDerivAt (Psi r1) (-(√x / √(r1 - x))) x := by
  have hr1 : 0 < r1 := lt_trans hx hx1
  have hb0 : 0 < r1 - x := by linarith
  set a := √x with ha
  set b := √(r1 - x) with hb
  set c := √r1 with hc
  have ha0 : 0 < a := Real.sqrt_pos.2 hx
  have hbp : 0 < b := Real.sqrt_pos.2 hb0
  have hc0 : 0 < c := Real.sqrt_pos.2 hr1
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb2 : b ^ 2 = r1 - x := Real.sq_sqrt hb0.le
  have hc2 : c ^ 2 = r1 := Real.sq_sqrt hr1.le
  have hy : √(x / r1) = a / c := Real.sqrt_div hx.le r1
  have hy0 : 0 < √(x / r1) := Real.sqrt_pos.2 (div_pos hx hr1)
  have hyne : x / r1 ≠ 0 := (div_pos hx hr1).ne'
  have hy1 : √(x / r1) < 1 := by
    rw [Real.sqrt_lt' one_pos]; rw [div_lt_iff hr1]; linarith
  have hsq : 1 - √(x / r1) ^ 2 = (r1 - x) / r1 := by
    rw [Real.sq_sqrt (div_pos hx hr1).le]; field_simp
  have hs1 : √(1 - √(x / r1) ^ 2) = b / c := by rw [hsq]; exact Real.sqrt_div hb0.le r1
  have hm : √(x * (r1 - x)) = a * b := Real.sqrt_mul hx.le _
  -- 合成
  have hd1 : HasDerivAt (fun x => √(x / r1)) (1 / r1 / (2 * √(x / r1))) x :=
    ((hasDerivAt_id x).div_const r1).sqrt hyne |>.congr_deriv (by simp)
  have hd2 := ((Real.hasDerivAt_arccos (by linarith) hy1.ne).comp x hd1).const_mul r1
  have hpne : x * (r1 - x) ≠ 0 := (mul_pos hx hb0).ne'
  have hd3 : HasDerivAt (fun x => √(x * (r1 - x))) ((1 * (r1 - x) + x * (-1)) / (2 * √(x * (r1 - x)))) x :=
    ((hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub r1)).sqrt hpne |>.congr_deriv (by simp)
  have h := hd2.add hd3
  have hf : Psi r1 = (fun x => r1 * (arccos ∘ fun x => √(x / r1)) x + √(x * (r1 - x))) := by
    funext y; simp [Psi]
  rw [hf]
  convert h using 1
  rw [hs1, hy, hm]
  field_simp
  linear_combination (2 * a * b ^ 2 * r1) * hc2 + (-4 * a * b ^ 2 * r1) * ha2

theorem psi_r1 (r1 : ℝ) (hr1 : 0 < r1) : Psi r1 r1 = 0 := by
  simp [Psi, div_self hr1.ne']

/-- 0 < x ≤ r₁ なら Ψ(x) < π r₁/2 -/
theorem psi_lt (r1 x : ℝ) (hx : 0 < x) (hx1 : x ≤ r1) : Psi r1 x < π * r1 / 2 := by
  have hr1 : 0 < r1 := lt_of_lt_of_le hx hx1
  set y := √(x / r1)
  have hy0 : 0 < y := Real.sqrt_pos.2 (div_pos hx hr1)
  have hy1 : y ≤ 1 := by
    rw [Real.sqrt_le_one]; rw [div_le_one hr1]; exact hx1
  -- arccos y = π/2 − arcsin y ≤ π/2 − y
  have has : y ≤ arcsin y := by
    have h0 : 0 ≤ arcsin y := Real.arcsin_nonneg.2 hy0.le
    have := Real.sin_le h0
    rwa [Real.sin_arcsin (by linarith) hy1] at this
  have hac : arccos y ≤ π / 2 - y := by rw [Real.arccos_eq_pi_div_two_sub_arcsin]; linarith
  -- r₁ y = √(x r₁) > √(x(r₁ − x))
  have hxy : √(x * (r1 - x)) < r1 * y := by
    have e : r1 * y = √(x * r1) := by
      simp only [y]
      rw [show x * r1 = (x / r1) * r1 ^ 2 by field_simp; ring, Real.sqrt_mul (div_pos hx hr1).le,
        Real.sqrt_sq hr1.le]; ring
    rw [e]; apply Real.sqrt_lt_sqrt (mul_nonneg hx.le (by linarith)); nlinarith
  unfold Psi
  have : r1 * arccos y ≤ r1 * (π / 2 - y) := mul_le_mul_of_nonneg_left hac hr1.le
  nlinarith

/-- **Z9 の本定理**:転回点 r(τ₁) = r₁ から、類 (rW)² ≥ κ、2κ ≥ ℓ² の中で、正の解が [τ₁, τ₂] に
    存在するなら τ₂ − τ₁ < π r₁/2 -/
theorem z9_collapse (r rp W : ℝ → ℝ) (l κ τ1 τ2 r1 : ℝ) (h12 : τ1 < τ2)
    (hpos : ∀ τ ∈ Icc τ1 τ2, 0 < r τ)
    (h1 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) : τ2 - τ1 < π * r1 / 2 := by
  have hr1p : 0 < r1 := by rw [← hr1]; exact hpos τ1 (left_mem_Icc.2 h12.le)
  have hdown := rp_nonpos r rp W l κ τ1 τ2 hpos h2 hk hW h0
  have hle := r_le r rp τ1 τ2 r1 h1 hdown hr1
  have hlt := r_lt r rp W l κ τ1 τ2 r1 hpos h1 h2 hk hW h0 hr1
  have hen := energy_lower r rp W l κ τ1 τ2 r1 hpos h1 h2 hk hW h0 hr1 h12.le
  let g : ℝ → ℝ := fun τ => Psi r1 (r τ) - τ
  have hcont : ContinuousOn g (Icc τ1 τ2) := by
    have hrc : ContinuousOn r (Icc τ1 τ2) := fun x hx => (h1 x hx).continuousAt.continuousWithinAt
    have hP : Continuous (Psi r1) := by
      unfold Psi
      exact (continuous_const.mul (Real.continuous_arccos.comp
        (Real.continuous_sqrt.comp (continuous_id.div_const _)))).add
        (Real.continuous_sqrt.comp (continuous_id.mul (continuous_const.sub continuous_id)))
    exact (hP.comp_continuousOn hrc).sub continuousOn_id
  have hderiv : ∀ x ∈ Ioo τ1 τ2, HasDerivAt g (-(√(r x) / √(r1 - r x)) * rp x - 1) x := by
    intro x hx
    have hx' := Ioo_subset_Icc_self hx
    have hP := psi_deriv r1 (r x) (hpos x hx') (hlt x (Ioo_subset_Ioc_self hx))
    exact (hP.comp x (h1 x hx')).sub (hasDerivAt_id x)
  have hnonneg : ∀ x ∈ Ioo τ1 τ2, 0 ≤ -(√(r x) / √(r1 - r x)) * rp x - 1 := by
    intro x hx
    have hx' := Ioo_subset_Icc_self hx
    have hr := hpos x hx'
    have hb0 : 0 < r1 - r x := by linarith [hlt x (Ioo_subset_Ioc_self hx)]
    have ha0 : 0 < √(r x) := Real.sqrt_pos.2 hr
    have hb : 0 < √(r1 - r x) := Real.sqrt_pos.2 hb0
    have ha2 : √(r x) ^ 2 = r x := Real.sq_sqrt hr.le
    have hb2 : √(r1 - r x) ^ 2 = r1 - r x := Real.sq_sqrt hb0.le
    have hd := hdown x hx'
    have he := hen x hx'
    -- −ṙ ≥ b/a ⇔ (aṙ)² ≥ b²
    have hsq : √(r1 - r x) ^ 2 ≤ (√(r x) * rp x) ^ 2 := by rw [mul_pow, ha2, hb2]; linarith
    have hab : √(r1 - r x) ≤ √(r x) * (-rp x) := by
      have h0' : 0 ≤ √(r x) * (-rp x) := mul_nonneg ha0.le (by linarith)
      nlinarith [sq_nonneg (√(r1 - r x) - √(r x) * (-rp x)), sq_nonneg (√(r1 - r x) + √(r x) * (-rp x))]
    have : -(√(r x) / √(r1 - r x)) * rp x - 1 = (√(r x) * (-rp x) - √(r1 - r x)) / √(r1 - r x) := by
      field_simp
    rw [this]; exact div_nonneg (by linarith) hb.le
  have hmono : MonotoneOn g (Icc τ1 τ2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc τ1 τ2) hcont
    · intro x hx; rw [interior_Icc] at hx; exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx; rw [(hderiv x hx).deriv]; exact hnonneg x hx
  have hg := hmono (left_mem_Icc.2 h12.le) (right_mem_Icc.2 h12.le) h12.le
  simp only [g, hr1, psi_r1 r1 hr1p] at hg
  have hfin := psi_lt r1 (r τ2) (hpos τ2 (right_mem_Icc.2 h12.le)) (hle τ2 (right_mem_Icc.2 h12.le))
  linarith

/-- 系(Z9-b):r₁ ≤ ℓ なら崩壊までの固有時は πℓ/2 より短い -/
theorem z9_before_half_period (r rp W : ℝ → ℝ) (l κ τ1 τ2 r1 : ℝ) (h12 : τ1 < τ2)
    (hpos : ∀ τ ∈ Icc τ1 τ2, 0 < r τ)
    (h1 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 τ2, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) (hrl : r1 ≤ l) : τ2 - τ1 < π * l / 2 := by
  have := z9_collapse r rp W l κ τ1 τ2 r1 h12 hpos h1 h2 hk hW h0 hr1
  have : π * r1 / 2 ≤ π * l / 2 := by have := pi_pos; nlinarith
  linarith

/-- 系:解が区間 [τ₁, τ₁ + πr₁/2] 全体で(C¹ で)続くなら、その中で r は 0 になる -/
theorem z9_reaches_zero (r rp W : ℝ → ℝ) (l κ τ1 r1 : ℝ) (hr1p : 0 < r1)
    (h1 : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) : ∃ T ∈ Icc τ1 (τ1 + π * r1 / 2), r T = 0 := by
  have hlen : τ1 < τ1 + π * r1 / 2 := by have := pi_pos; linarith [mul_pos this hr1p]
  by_cases hall : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), 0 < r τ
  · have := z9_collapse r rp W l κ τ1 _ r1 hlen hall h1 h2 hk hW h0 hr1
    linarith
  · push_neg at hall
    obtain ⟨τ, hτ, hle⟩ := hall
    have hc : ContinuousOn r (Icc τ1 τ) := fun x hx =>
      (h1 x ⟨hx.1, le_trans hx.2 hτ.2⟩).continuousAt.continuousWithinAt
    have hivt := intermediate_value_Icc' hτ.1 hc
    obtain ⟨T, hT, hrT⟩ := hivt ⟨hle, by rw [hr1]; exact hr1p.le⟩
    exact ⟨T, ⟨hT.1, le_trans hT.2 hτ.2⟩, hrT⟩

/-- Z44 の仮定 hcollapse を Z9 から供給する:中心の式の解で、喉に Killing スピノルはない -/
theorem z44_from_z9 (r rp W : ℝ → ℝ) (l κ r1 : ℝ) (hr1p : 0 < r1)
    (h1 : ∀ τ, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ, HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ, κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp 0 = 0) (hr1 : r 0 = r1)
    (ε : ℝ → Fin 4 → ℝ × ℝ) (hε : ∀ t, ε t ≠ 0) (Ks : ℝ → ℝ)
    (hiso : ∀ t, (∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) * rp t + Ks t * 0 = 0) : False := by
  obtain ⟨T, -, hT⟩ := z9_reaches_zero r rp W l κ 0 r1 hr1p (fun τ _ => h1 τ) (fun τ _ => h2 τ) hk
    (fun τ _ => hW τ) h0 hr1
  exact CFT.Z44.no_killing_spinor r rp h1 ⟨by rw [hr1]; exact hr1p, T, hT⟩ ε hε Ks hiso

/-! ### 閾値の鋭さ -/

/-- (rW)² = κ のとき、静止した喉は r² = ℓ² − 2κ に限る -/
theorem static_iff (l r W κ : ℝ) (hr : 0 < r) (hW : W ^ 2 * r ^ 2 = κ) :
    acc l r 0 W = 0 ↔ r ^ 2 = l ^ 2 - 2 * κ := by
  have hr3 : (0 : ℝ) < 2 * r ^ 3 := by positivity
  have e : acc l r 0 W = (l ^ 2 - 2 * κ - r ^ 2) / (2 * r ^ 3) := by
    unfold acc; rw [← hW]; field_simp; ring
  rw [e, div_eq_zero_iff, or_iff_left hr3.ne']
  constructor <;> intro h <;> linarith

/-- 2κ ≥ ℓ² なら静止した喉はない、2κ < ℓ² なら r = √(ℓ² − 2κ) が静止解 -/
theorem static_dichotomy (l W κ : ℝ) :
    (l ^ 2 ≤ 2 * κ → ∀ r, 0 < r → W ^ 2 * r ^ 2 = κ → acc l r 0 W ≠ 0) ∧
    (2 * κ < l ^ 2 → ∀ W', W' ^ 2 * (l ^ 2 - 2 * κ) = κ →
      acc l √(l ^ 2 - 2 * κ) 0 W' = 0) := by
  constructor
  · intro hk r hr hW h
    have := (static_iff l r W κ hr hW).1 h
    nlinarith [sq_pos_of_pos hr]
  · intro hk W' hW'
    have hpos : 0 < l ^ 2 - 2 * κ := by linarith
    have hs : √(l ^ 2 - 2 * κ) ^ 2 = l ^ 2 - 2 * κ := Real.sq_sqrt hpos.le
    apply (static_iff l _ W' κ (Real.sqrt_pos.2 hpos) (by rw [hs]; exact hW')).2 hs

/-- W = 0 の首 r = ℓ のまわりの線形化:F(r) = −(1 − ℓ²/r²)/(2r) の r = ℓ での微分は −1/ℓ² -/
theorem neck_frequency (l : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun r => -(1 - l ^ 2 / r ^ 2) / (2 * r)) (-1 / l ^ 2) l := by
  have h := ((((hasDerivAt_id l).pow 2).inv (pow_ne_zero 2 hl)).const_mul (l ^ 2)).const_sub 1
    |>.neg.div ((hasDerivAt_id l).const_mul 2) (by simp [hl])
  have hf : (fun r => -(1 - l ^ 2 / r ^ 2) / (2 * r)) =
      fun r => (-(1 - l ^ 2 * (id r ^ 2)⁻¹)) / (2 * id r) := by funext r; simp [div_eq_mul_inv]
  rw [hf]; convert h using 1; simp; field_simp; ring

/-! ### 質量の定義 -/

/-- Misner–Sharp:r(1 − h^{ab}∂_a r ∂_b r)、h = diag(−N², 1)、∂_t r = N ṙ、∂_s r = 0 -/
theorem ms_general (r N rp : ℝ) (hN : N ≠ 0) :
    r * (1 - ((-1 / N ^ 2) * (N * rp) ^ 2 + 1 * 0 ^ 2)) = r * (1 + rp ^ 2) := by
  field_simp; ring

/-- RN:f = 1 − E/r + ℓ²/r² なら r(1 − f) + ℓ²/r = E(E は RN の質量母数 2GM) -/
theorem rn_param (r E l : ℝ) (hr : r ≠ 0) : r * (1 - (1 - E / r + l ^ 2 / r ^ 2)) + l ^ 2 / r = E := by
  field_simp; ring

/-- 首の E = 2ℓ は極限 RN:f = (1 − ℓ/r)² -/
theorem rn_extremal (r l : ℝ) (hr : r ≠ 0) : 1 - 2 * l / r + l ^ 2 / r ^ 2 = (1 - l / r) ^ 2 := by
  field_simp; ring

theorem neck_E (l : ℝ) (hl : l ≠ 0) : l * (1 + 0 ^ 2) + l ^ 2 / l = 2 * l := by field_simp; ring

/-- 中心の式のもとで d(2Gm_MS)/dτ = ṙ(ℓ²/r² − 2W²) -/
theorem ms_deriv (r rp W : ℝ → ℝ) (l τ : ℝ) (hr : r τ ≠ 0)
    (h1 : HasDerivAt r (rp τ) τ) (h2 : HasDerivAt rp (acc l (r τ) (rp τ) (W τ)) τ) :
    HasDerivAt (fun τ => r τ * (1 + rp τ ^ 2)) (rp τ * (l ^ 2 / r τ ^ 2 - 2 * W τ ^ 2)) τ := by
  have h := h1.mul ((h2.pow 2).const_add 1)
  convert h using 1
  unfold acc; simp only [Nat.cast_ofNat]; field_simp; ring

/-- 崩壊中で 2(rW)² ≥ ℓ² なら MS 質量の微分は 0 以上 -/
theorem ms_increases (r rp W l : ℝ) (hr : 0 < r) (hrp : rp ≤ 0) (hW : l ^ 2 ≤ 2 * (W ^ 2 * r ^ 2)) :
    0 ≤ rp * (l ^ 2 / r ^ 2 - 2 * W ^ 2) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have : l ^ 2 / r ^ 2 - 2 * W ^ 2 ≤ 0 := by
    rw [sub_nonpos, div_le_iff hr2]; linarith
  nlinarith

/-- 喉では 2Gm_MS ≥ r、null 膨張 θ± = (2/r)(±∂_s r + ṙ) は ∂_s r = 0 で同じ (2/r)ṙ -/
theorem throat_trapped (r rp : ℝ) (hr : 0 < r) (hrp : rp < 0) :
    r ≤ r * (1 + rp ^ 2) ∧ (2 / r) * (0 + rp) < 0 ∧ (2 / r) * (-0 + rp) < 0 := by
  refine ⟨by nlinarith [sq_nonneg rp], ?_, ?_⟩ <;>
  · simp; exact mul_neg_of_pos_of_neg (by positivity) hrp

end CFT.Z9
