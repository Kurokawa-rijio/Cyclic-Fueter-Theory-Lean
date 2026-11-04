/-
  α-VIII.3(Z41):弦理論の作用でのアトラクター(ディラトンを含む)

  監査の指摘:エントロピー関数を Einstein–Maxwell(ディラトンなし)から作っていて、弦理論の作用からではない。
  ここではヘテロティック弦の 4 次元の低エネルギー作用を、Einstein–ディラトン–Maxwell(結合 a = 1)に
  切り詰めたものを使う(外部:Garfinkle–Horowitz–Strominger 1991、Sen 1992。二つの U(1) に電荷 q と
  磁荷 p を分けて置けば F∧F̃ = 0 で axion は生じず、この切り詰めは無矛盾)。
    L = (1/16π)[R − 2(∂φ)² − e^{−2φ} F_{μν}F^{μν}](G = 1)
  近地平線 ds² = v₁(−r²dt² + dr²/r²) + v₂ dΩ²、F_rt = e、F_θφ = p sinθ、φ = u(定数)、w = e^{−2u} > 0。
  S² で積分したラグランジアンは(AlphaVIII_Attractor の f に e^{−2u} がかかる)
    f = ¼(2v₁ − 2v₂ + w(2e²v₂/v₁ − 2p²v₁/v₂))、ℰ = 2π(qe − f)。
  (外部:Sen 2005)ℰ の臨界点 ⇔ 近地平線の運動方程式、臨界値 = Wald のエントロピー。

  Lean で示すこと
  * ∂_u ℰ = 0 ⇔ ∂_w ℰ = 0(w = e^{−2u}、連鎖律 `dw_du`)。
  * p, q > 0 なら臨界点は一つ:v₁ = v₂ = 2pq、e = p、w = e^{−2u} = q/p(`string_attractor`)。
    臨界値 ℰ = 2πpq = (面積 4πv₂)/4(`string_entropy`)。
  * 磁荷だけ(q = 0、p ≠ 0)では臨界点がない(`no_attractor_magnetic`)。ディラトンは w → 0(u → ∞)へ逃げ、
    地平線の面積 2pq → 0。ダンベルの首(磁荷 p = 1 だけ)は、弦理論の作用では O(α′⁰) のアトラクターではない。
  * 有効ポテンシャル V(w) = wp² + q²/w(Ferrara–Gibbons–Kallosh 1997):V ≥ 2pq で、等号は w = q/p だけ
    (`veff_min`、`veff_attained`)。臨界点はポテンシャルの最小点で安定(アトラクター)、v₂ = V_min。
    q = 0 では V > 0 だが下限 0 は達成されない(`veff_magnetic_runaway`)。
  * 首との一致:√v₂ = ℓ* ⇔ 2pq = ℓ*²(`neck_condition`)。p = 1 なら電荷 q = ℓ*²/2 が必要。
    台帳の Z41(ディラトンを止めた Einstein–Maxwell の切り詰め)で √v₂ = ℓ* になったのは、
    ディラトンが固定されている場合に当たる。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Basic

namespace CFT.StringAttractor

open Real Filter Topology

noncomputable section

/-- S² で積分したラグランジアン(w = e^{−2u}) -/
def fD (p v1 v2 e w : ℝ) : ℝ := (1 / 4) * (2 * v1 - 2 * v2 + w * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2))

/-- エントロピー関数 ℰ = 2π(qe − f) -/
def entropyD (p q v1 v2 e w : ℝ) : ℝ := 2 * π * (q * e - fD p v1 v2 e w)

/-- ∂_w f(f は w について 1 次) -/
theorem fD_deriv_w (p v1 v2 e w : ℝ) :
    HasDerivAt (fun x => fD p v1 v2 e x) ((1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2)) w := by
  simp only [fD]
  have h := (((hasDerivAt_id' w).mul_const (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2)).const_add
    (2 * v1 - 2 * v2)).const_mul (1 / 4 : ℝ)
  convert h using 1
  ring

/-- 連鎖律:w = e^{−2u} なら ∂_u = −2w ∂_w。w > 0 なので ∂_u = 0 ⇔ ∂_w = 0 -/
theorem dw_du (p v1 v2 e u : ℝ) :
    HasDerivAt (fun x => fD p v1 v2 e (exp (-2 * x)))
      ((1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) * (-2 * exp (-2 * u))) u ∧
    ((1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) * (-2 * exp (-2 * u)) = 0 ↔
      (1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) = 0) := by
  constructor
  · have hu : HasDerivAt (fun x => exp (-2 * x)) (exp (-2 * u) * (-2)) u := by
      have := ((hasDerivAt_id' u).const_mul (-2 : ℝ)).exp
      simpa using this
    have h := (fD_deriv_w p v1 v2 e (exp (-2 * u))).comp u hu
    rw [show (1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) * (-2 * exp (-2 * u))
      = (1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) * (exp (-2 * u) * (-2)) by ring]
    exact h
  · have : -2 * exp (-2 * u) ≠ 0 := by have := exp_pos (-2 * u); nlinarith
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_right this
    · intro h; rw [h, zero_mul]

/-- 【α-VIII.3】弦理論の作用のアトラクター:p, q > 0 なら臨界点は v₁ = v₂ = 2pq、e = p、w = q/p だけ -/
theorem string_attractor (p q v1 v2 e w : ℝ) (hp : 0 < p) (hq : 0 < q) (h1 : 0 < v1) (h2 : 0 < v2)
    (hw : 0 < w)
    (de : q - w * e * v2 / v1 = 0)
    (dv1 : (1 / 4) * (2 - w * (2 * e ^ 2 * v2 / v1 ^ 2 + 2 * p ^ 2 / v2)) = 0)
    (dv2 : (1 / 4) * (-2 + w * (2 * e ^ 2 / v1 + 2 * p ^ 2 * v1 / v2 ^ 2)) = 0)
    (dw : (1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) = 0) :
    v1 = 2 * p * q ∧ v2 = 2 * p * q ∧ e = p ∧ w = q / p := by
  have a1 := h1.ne'; have a2 := h2.ne'
  have k1 : w * (2 * e ^ 2 * v2 / v1 ^ 2 + 2 * p ^ 2 / v2) = 2 := by linarith
  have k2 : w * (2 * e ^ 2 / v1 + 2 * p ^ 2 * v1 / v2 ^ 2) = 2 := by linarith
  have k3 : 2 * e ^ 2 * v2 / v1 = 2 * p ^ 2 * v1 / v2 := by linarith
  have k4 : q = w * e * v2 / v1 := by linarith
  have m1 : w * (2 * e ^ 2 * v2 ^ 2 + 2 * p ^ 2 * v1 ^ 2) = 2 * (v1 ^ 2 * v2) := by
    have e1 : 2 * e ^ 2 * v2 ^ 2 + 2 * p ^ 2 * v1 ^ 2
        = (2 * e ^ 2 * v2 / v1 ^ 2 + 2 * p ^ 2 / v2) * (v1 ^ 2 * v2) := by
      field_simp <;> ring
    rw [e1, ← mul_assoc, k1]
  have m2 : w * (2 * e ^ 2 * v2 ^ 2 + 2 * p ^ 2 * v1 ^ 2) = 2 * (v1 * v2 ^ 2) := by
    have e1 : 2 * e ^ 2 * v2 ^ 2 + 2 * p ^ 2 * v1 ^ 2
        = (2 * e ^ 2 / v1 + 2 * p ^ 2 * v1 / v2 ^ 2) * (v1 * v2 ^ 2) := by
      field_simp <;> ring
    rw [e1, ← mul_assoc, k2]
  have m3 : e ^ 2 * v2 ^ 2 = p ^ 2 * v1 ^ 2 := by
    have e1 : e ^ 2 * v2 ^ 2 = (2 * e ^ 2 * v2 / v1) * (v1 * v2) / 2 := by field_simp <;> ring
    have e2 : p ^ 2 * v1 ^ 2 = (2 * p ^ 2 * v1 / v2) * (v1 * v2) / 2 := by field_simp <;> ring
    rw [e1, e2, k3]
  have m4 : q * v1 = w * e * v2 := by rw [k4]; field_simp
  -- v₁ = v₂
  have hv : v1 = v2 := by
    have : v1 * v2 * (v1 - v2) = 0 := by linear_combination (m2 - m1) / 2
    have h12 : v1 * v2 ≠ 0 := mul_ne_zero a1 a2
    linarith [(mul_eq_zero.mp this).resolve_left h12]
  rw [← hv] at m1 m3 m4 ⊢
  have hv0 : v1 ^ 2 ≠ 0 := pow_ne_zero 2 a1
  have hep : e ^ 2 = p ^ 2 := mul_right_cancel₀ hv0 m3
  have hqe : q = w * e := mul_right_cancel₀ a1 (by linear_combination m4)
  have he_pos : 0 < e := by
    by_contra hneg; push_neg at hneg
    have : w * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw.le hneg
    linarith
  have he : e = p := by
    have h' : (e - p) * (e + p) = 0 := by linear_combination hep
    have : e + p ≠ 0 := by linarith
    linarith [(mul_eq_zero.mp h').resolve_right this]
  have hwq : w = q / p := by
    rw [hqe, he]; field_simp
  have h3 : v1 = 2 * w * p ^ 2 := by
    have k : w * (4 * p ^ 2 * v1 ^ 2) = 2 * (v1 ^ 2 * v1) := by
      linear_combination m1 - 2 * w * v1 ^ 2 * hep
    have : v1 ^ 2 * (v1 - 2 * w * p ^ 2) = 0 := by linear_combination -k / 2
    linarith [(mul_eq_zero.mp this).resolve_left hv0]
  have hfin : v1 = 2 * p * q := by
    rw [h3, hwq]; field_simp; ring
  exact ⟨hfin, hfin, he, hwq⟩

/-- 【α-VIII.3】臨界値 ℰ = 2πpq = (地平線の面積 4πv₂)/4 -/
theorem string_entropy (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    entropyD p q (2 * p * q) (2 * p * q) p (q / p) = 2 * π * p * q ∧
    2 * π * p * q = 4 * π * (2 * p * q) / 4 := by
  have hp0 := hp.ne'; have hq0 := hq.ne'
  constructor
  · simp only [entropyD, fD]; field_simp; ring
  · ring

/-- 【α-VIII.3】磁荷だけ(q = 0、p ≠ 0)では臨界点はない:ディラトンが逃げる -/
theorem no_attractor_magnetic (p v1 v2 e w : ℝ) (hp : p ≠ 0) (h1 : 0 < v1) (h2 : 0 < v2) (hw : 0 < w)
    (de : 0 - w * e * v2 / v1 = 0)
    (dw : (1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) = 0) : False := by
  have a1 := h1.ne'; have a2 := h2.ne'
  have he : e = 0 := by
    have h0 : w * e * v2 / v1 = 0 := by linarith
    have : w * e * v2 = 0 := (div_eq_zero_iff.mp h0).resolve_right a1
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hw.ne'
      · exact h'
    · exact absurd h a2
  have k : (1 / 4) * (2 * e ^ 2 * v2 / v1 - 2 * p ^ 2 * v1 / v2) = -(1 / 2) * (p ^ 2 * v1 / v2) := by
    rw [he]; ring
  have : p ^ 2 * v1 / v2 = 0 := by rw [k] at dw; linarith
  have : p ^ 2 * v1 = 0 := by
    rcases div_eq_zero_iff.mp this with h | h
    · exact h
    · exact absurd h a2
  rcases mul_eq_zero.mp this with h | h
  · exact hp (pow_eq_zero_iff (by norm_num) |>.mp h)
  · exact a1 h

/-- 有効ポテンシャル V(w) = wp² + q²/w(w = e^{−2u}) -/
def veff (p q w : ℝ) : ℝ := w * p ^ 2 + q ^ 2 / w

/-- 【α-VIII.3】V ≥ 2pq(p, q > 0、w > 0):V − 2pq = (wp − q)²/w ≥ 0 -/
theorem veff_min (p q w : ℝ) (hp : 0 < p) (hq : 0 < q) (hw : 0 < w) : 2 * p * q ≤ veff p q w := by
  have hw0 := hw.ne'
  have : veff p q w - 2 * p * q = (w * p - q) ^ 2 / w := by
    simp only [veff]; field_simp; ring
  have : 0 ≤ (w * p - q) ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  linarith

/-- 等号は w = q/p だけ:臨界点はポテンシャルの最小点(安定なアトラクター)で、v₂ = V_min = 2pq -/
theorem veff_attained (p q w : ℝ) (hp : 0 < p) (hq : 0 < q) (hw : 0 < w) :
    veff p q w = 2 * p * q ↔ w = q / p := by
  have hw0 := hw.ne'; have hp0 := hp.ne'
  have key : veff p q w - 2 * p * q = (w * p - q) ^ 2 / w := by
    simp only [veff]; field_simp; ring
  constructor
  · intro h
    have : (w * p - q) ^ 2 / w = 0 := by linarith
    have : (w * p - q) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h hw0
    have h0 : w * p - q = 0 := (pow_eq_zero_iff two_ne_zero).mp this
    field_simp; linarith
  · intro h
    have : (w * p - q) ^ 2 / w = 0 := by
      rw [h, div_mul_cancel₀ q hp0, sub_self]; simp
    linarith

/-- 二階微分 V″ = 2q²/w³ > 0(最小点は非退化) -/
theorem veff_second (p q w : ℝ) (hq : q ≠ 0) (hw : 0 < w) : 0 < 2 * q ^ 2 / w ^ 3 := by
  have : 0 < q ^ 2 := by positivity
  positivity

/-- 【α-VIII.3】磁荷だけ:V = wp² > 0 だが w → 0 で 0 に近づき、最小点はない(ディラトンの逃走) -/
theorem veff_magnetic_runaway (p : ℝ) (hp : p ≠ 0) :
    (∀ w > 0, 0 < veff p 0 w) ∧ Tendsto (fun w => veff p 0 w) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · intro w hw
    show 0 < w * p ^ 2 + (0 : ℝ) ^ 2 / w
    rw [show (0 : ℝ) ^ 2 / w = 0 by simp, add_zero]
    positivity
  · have h : Tendsto (fun w : ℝ => w * p ^ 2) (𝓝 0) (𝓝 (0 * p ^ 2)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards with w
    simp [veff]

/-- 首との一致:√v₂ = ℓ* ⇔ 2pq = ℓ*²(ℓ* > 0、pq > 0) -/
theorem neck_condition (p q l : ℝ) (hl : 0 < l) (hpq : 0 < p * q) :
    Real.sqrt (2 * p * q) = l ↔ 2 * p * q = l ^ 2 := by
  constructor
  · intro h; rw [← h, Real.sq_sqrt (by linarith)]
  · intro h; rw [h, Real.sqrt_sq hl.le]

end

end CFT.StringAttractor
