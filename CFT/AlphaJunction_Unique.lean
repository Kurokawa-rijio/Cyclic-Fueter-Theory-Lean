/-
  定理 A:帽子と首のつなぎ方の一意性(2026-11-11)

  球対称・磁気的で、時間対称な切り口のゲージ場がスピン接続型(W = r′)の類の中では、
  帽子(r = ℓ sin(x/ℓ))と首(r = ℓ)のつなぎ方に選択の余地がない:
  * `ju_location`:面積半径が連続になる場所は赤道 x = πℓ/2 だけ。
  * `ju_C1_auto`:そこでは r′ = cos(x/ℓ) = 0 で、首の r′ = 0 と自動的に一致する(C¹)。
  * `ju_cap_second`:帽子の r″ は赤道で −1/ℓ。首は 0。拘束の根はこの二つだけ(rr_two_roots)なので C² にできない。
  * 時間的な管ではつなげない(rj_tube_mismatch)。
  * `ju_jump_fixed`:ヌルの前線の上で [W_u] は角の値 1/(√2ℓ) のまま。大きさも選べない。
  * `ju_theorem_A`:以上を一つにまとめたもの。
  これは「つなぐならこうなるしかない」という定理で、「なぜつなぐのか」(定理 B)は含まない。
-/
import CFT.AlphaReal_Junction
import CFT.AlphaReal_Rest

open Real Set

namespace CFT.JU

/-- つなぐ場所:帽子の面積半径 ℓ sin(x/ℓ) が首の ℓ に等しいのは赤道だけ -/
theorem ju_location (l x : ℝ) (hl : 0 < l) (hx0 : 0 < x) (hx1 : x < π * l) :
    l * sin (x / l) = l ↔ x = π * l / 2 := by
  have hl' : l ≠ 0 := hl.ne'
  constructor
  · intro h
    have hs : sin (x / l) = 1 := mul_left_cancel₀ hl' (h.trans (mul_one l).symm)
    have hs2 : sin (x / l) ^ 2 = 1 := by rw [hs]; norm_num
    have h2 : cos (x / l) ^ 2 = 0 := by linarith [sin_sq_add_cos_sq (x / l)]
    have hc : cos (x / l) = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
    have hθ0 : 0 < x / l := div_pos hx0 hl
    have hθ1 : x / l < π := by rw [div_lt_iff hl]; exact hx1
    have e : x / l = π / 2 :=
      Real.injOn_cos ⟨hθ0.le, hθ1.le⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        (by rw [hc, cos_pi_div_two])
    rw [div_eq_div_iff hl' two_ne_zero] at e
    linarith
  · intro h
    have e : π * l / 2 / l = π / 2 := by field_simp <;> ring
    rw [h, e, sin_pi_div_two, mul_one]

/-- 赤道では帽子の r′ = cos(x/ℓ) = 0。首の r′ = 0 と一致する(C¹ は自動) -/
theorem ju_C1_auto (l x : ℝ) (hl : l ≠ 0) (h : x = π * l / 2) : cos (x / l) = 0 := by
  have e : π * l / 2 / l = π / 2 := by field_simp <;> ring
  rw [h, e, cos_pi_div_two]

/-- 帽子の r″(r′ = cos(x/ℓ) の微分)は赤道で −1/ℓ -/
theorem ju_cap_second (l : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun x => cos (x / l)) (-1 / l) (π * l / 2) := by
  have h := ((hasDerivAt_id' (π * l / 2)).div_const l).cos
  have e : π * l / 2 / l = π / 2 := by field_simp <;> ring
  convert h using 1
  rw [e, sin_pi_div_two]
  ring

/-- 跳びの大きさ:角で帽子 W_u = 1/(√2ℓ)、首 W_u = 0 なら、前線の上のすべての点で [W_u] = 1/(√2ℓ) ≠ 0 -/
theorem ju_jump_fixed {v0 v1 l : ℝ} (hl : 0 < l) {Wup Wum Wuvp Wuvm Gf : ℝ → ℝ}
    (hp : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wup (Wuvp v) (Icc v0 v1) v)
    (hm : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wum (Wuvm v) (Icc v0 v1) v)
    (sP : ∀ v ∈ Icc v0 v1, Wuvp v = Gf v) (sM : ∀ v ∈ Icc v0 v1, Wuvm v = Gf v)
    (cP : Wup v0 = 1 / (Real.sqrt 2 * l)) (cM : Wum v0 = 0) :
    ∀ v ∈ Icc v0 v1, Wup v - Wum v = 1 / (Real.sqrt 2 * l) ∧ Wup v - Wum v ≠ 0 := by
  intro v hv
  have h := CFT.RJ.rj_Wu_transport (v0 := v0) (v1 := v1) hp hm sP sM v hv
  rw [cP, cM, sub_zero] at h
  refine ⟨h, ?_⟩
  rw [h]
  exact (div_pos one_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hl)).ne'

/-- 定理 A(切り口の部分):場所は赤道だけ、C¹ は自動、r″ は −1/ℓ と 0 で一致せず、拘束の根はこの二つだけ、
  時間的な管ではつなげない -/
theorem ju_theorem_A (l x τ : ℝ) (hl : 0 < l) (hx0 : 0 < x) (hx1 : x < π * l)
    (hτ : τ ≠ 0) (hτl : τ ^ 2 ≤ l ^ 2) :
    (l * sin (x / l) = l ↔ x = π * l / 2)
    ∧ (x = π * l / 2 → cos (x / l) = 0)
    ∧ HasDerivAt (fun x => cos (x / l)) (-1 / l) (π * l / 2)
    ∧ (-1 / l ≠ (0 : ℝ))
    ∧ (∀ y : ℝ, 2 * l ^ 2 * y ^ 2 + 2 * l * y + l ^ 2 * (1 - 0 ^ 2) ^ 2 / l ^ 2 - (1 - 0 ^ 2) = 0
        ↔ y = 0 ∨ y = -1 / l)
    ∧ Real.sqrt (l ^ 2 - τ ^ 2) ≠ l :=
  ⟨ju_location l x hl hx0 hx1, ju_C1_auto l x hl.ne', ju_cap_second l hl.ne',
    div_ne_zero (by norm_num) hl.ne', fun y => CFT.RR.rr_two_roots l y hl.ne',
    CFT.RJ.rj_tube_mismatch l τ hτ hτl⟩

end CFT.JU
