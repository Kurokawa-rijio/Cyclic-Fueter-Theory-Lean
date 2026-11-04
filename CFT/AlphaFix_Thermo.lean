/-
  独立監査(2026-11-04)の指摘を受けた作り直し:α-IX.24、IX.27、IX.30、IX.33、IX.34

  運動学・作用・力学の対で書く。
  * IX.24(運動学:首の磁荷 Q、地平線 r₊。作用:Euclid の EH + GHY + Maxwell。力学:分配関数の集団)
      旧版は電荷の場合の値 I = β(M − ΦQ)/2 を仮定していた(監査:磁荷では作用が違う)。ここでは
      Maxwell の項を磁荷の場について実際に積分する:F = Q sin θ dθ∧dφ で F² = 2Q²/r⁴、
      (1/16π)·β·4π∫_{r₊}^∞ F² r² dr = βΦQ/2(`maxwell_magnetic`、Φ = Q/r₊)。重力の部分 βM/2 は
      GHY 項と背景の差し引きによる評価(Gibbons–Hawking 1977、外部)。合わせて
      I = β(M + ΦQ)/2 = β(M − TS)(`magnetic_action`):磁荷を固定した正準集団(Hawking–Ross 1995)。
      S = βM − I = πr₊² = A/4。電荷のときは Maxwell の項の符号が逆で I = β(M − TS − ΦQ)(`electric_action`)。
  * IX.33(運動学:磁荷の首につながる RN の枝。作用:IX.24 の I。力学:相の比較)
      F = M − TS = r₊/4 + 3Q²/(4r₊)(`free_energy`)。同じ温度の二つの r₁ < r₂ では r₁r₂ > 3Q²
      (`same_T_product`)、したがって F(r₁) < F(r₂)(`small_branch_preferred`):極限(首、T = 0)につながる
      小さい枝が熱力学的に選ばれる。小さい枝は比熱が正(dT/dr₊ > 0 ⇔ r₊² < 3Q²、`heat_capacity_sign`)。
      W の凝縮(IX.15)は W = 0 での Landau の関数の W² の係数が負であること(AlphaIX_Second `landau`、
      温度 0 のエネルギー関数)。宇宙定数を前提にする Hawking–Page の式はダンベルには当てはまらないので、
      比較はこの磁荷の正準集団で行う。
  * IX.27(運動学:質量殻、p² = mq² の非相対論の尺度。力学:Jüttner → Maxwell)
      m(√(1 + x/m) − 1) → x/2(m → ∞、`nr_limit`)、したがって e^{−β(E − m)} → e^{−βq²/2}
      (`juttner_to_maxwell`)。優関数:m ≥ 1 で m(√(1 + x/m) − 1) ≥ √(1 + x) − 1(`nr_monotone`)。
      積分の極限は優収束定理(外部、優関数 e^{−β(√(1+q²) − 1)} は可積分)。
  * IX.30(運動学:有限系のエネルギー準位。力学:KMS ⇒ 揺動散逸)
      周波数 ω の重み:g(ω) = Σ_{E_m − E_k = ω} p_m w_km(G_AB の成分)、h(ω) = Σ p_k w_km(H_BA の成分)。
      KMS(IX.26)の成分の式は g = e^{−βω}h(`kms_weights`)。S = h + g、χ″ = h − g とおくと
      KMS だけから S(ω) sinh(βω/2) = χ″(ω) cosh(βω/2)(`fdt_from_kms`、`fdt_spectral`)。
  * IX.34(運動学:はりねずみ n̂ = x̂、球面の座標。力学:写像の次数 = 磁荷)
      n·(∂_θn × ∂_φn) = sin θ(`hedgehog_jacobian`)、次数 = (1/4π)∫₀^{2π}∫₀^π sin θ = 1(`hedgehog_degree`)。
      π₂(S²) = ℤ と次数による分類は外部。
-/
import CFT.AlphaIX_Thermo
import CFT.AlphaIX_Stat
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace CFT.FixThermo

open Real Set MeasureTheory Filter Topology

/-! ### IX.24 磁荷の首の Euclid 作用 -/

/-- ∫_{r₊}^∞ dr/r² = 1/r₊ -/
theorem int_inv_sq (rp : ℝ) (hp : 0 < rp) : ∫ r in Ioi rp, (r ^ 2)⁻¹ = rp⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hp
  have e : ∫ r in Ioi rp, (r ^ 2)⁻¹ = ∫ r in Ioi rp, r ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 ≤ r := le_of_lt (lt_trans hp hr)
    show (r ^ 2)⁻¹ = r ^ (-2 : ℝ)
    rw [Real.rpow_neg hr0, Real.rpow_two]
  rw [e, h]
  norm_num [Real.rpow_neg_one]

/-- 磁荷の RN の Euclid 作用:I = βM/2(重力の部分)+ (1/16π)·β·4π∫_{r₊}^∞ F² r² dr、F² = 2Q²/r⁴ -/
noncomputable def Imag (β rp Q : ℝ) : ℝ :=
  β * Thermo.Mrn rp Q / 2 + 1 / (16 * π) * (β * (4 * π)) * ∫ r in Ioi rp, 2 * Q ^ 2 / r ^ 4 * r ^ 2

/-- 【α-IX.24】Maxwell の項:(1/16π)·β·4π∫ 2Q²/r⁴·r² dr = βΦQ/2(Φ = Q/r₊) -/
theorem maxwell_magnetic (β rp Q : ℝ) (hp : 0 < rp) :
    1 / (16 * π) * (β * (4 * π)) * (∫ r in Ioi rp, 2 * Q ^ 2 / r ^ 4 * r ^ 2)
      = β * (Q / rp) * Q / 2 := by
  have e : ∫ r in Ioi rp, 2 * Q ^ 2 / r ^ 4 * r ^ 2 = ∫ r in Ioi rp, 2 * Q ^ 2 * (r ^ 2)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : r ≠ 0 := (lt_trans hp hr).ne'
    show 2 * Q ^ 2 / r ^ 4 * r ^ 2 = 2 * Q ^ 2 * (r ^ 2)⁻¹
    field_simp
    ring
  rw [e, integral_mul_left, int_inv_sq rp hp]
  have := pi_ne_zero
  have := hp.ne'
  field_simp
  ring

/-- 【α-IX.24】磁荷の首:I = β(M − TS)(磁荷を固定した正準集団)、S = βM − I = πr₊² = A/4
(T = (r₊ − Q²/r₊)/(4πr₊²)、βT = 1) -/
theorem magnetic_action (β rp Q : ℝ) (hp : 0 < rp)
    (hβ : β * ((rp - Q ^ 2 / rp) / (4 * π * rp ^ 2)) = 1) :
    Imag β rp Q = β * (Thermo.Mrn rp Q - (rp - Q ^ 2 / rp) / (4 * π * rp ^ 2) * (π * rp ^ 2)) ∧
    β * Thermo.Mrn rp Q - Imag β rp Q = π * rp ^ 2 := by
  have hsm := Thermo.smarr rp Q hp.ne'
  unfold Imag
  rw [maxwell_magnetic β rp Q hp, hsm]
  constructor
  · ring
  · linear_combination (π * rp ^ 2) * hβ

/-- 比較:電荷のとき(Maxwell の項の符号が逆)は I = β(M − TS − ΦQ) -/
theorem electric_action (β rp Q : ℝ) (hp : 0 < rp) :
    β * Thermo.Mrn rp Q / 2 - β * (Q / rp) * Q / 2
      = β * (Thermo.Mrn rp Q - (rp - Q ^ 2 / rp) / (4 * π * rp ^ 2) * (π * rp ^ 2) - Q / rp * Q) := by
  rw [Thermo.smarr rp Q hp.ne']
  ring

/-! ### IX.33 磁荷の正準集団での相の比較 -/

/-- F = M − TS = r₊/4 + 3Q²/(4r₊) -/
theorem free_energy (rp Q : ℝ) (hp : rp ≠ 0) :
    Thermo.Mrn rp Q - (rp - Q ^ 2 / rp) / (4 * π * rp ^ 2) * (π * rp ^ 2)
      = rp / 4 + 3 * Q ^ 2 / (4 * rp) := by
  have := pi_ne_zero
  unfold Thermo.Mrn
  field_simp
  ring

/-- 同じ温度の二つの r₁ ≠ r₂ では r₁r₂ > 3Q² -/
theorem same_T_product (r1 r2 Q : ℝ) (h1 : 0 < r1) (h2 : 0 < r2) (hne : r1 ≠ r2) (hQ : Q ≠ 0)
    (hT : (r1 - Q ^ 2 / r1) / (4 * π * r1 ^ 2) = (r2 - Q ^ 2 / r2) / (4 * π * r2 ^ 2)) :
    3 * Q ^ 2 < r1 * r2 := by
  have hpi := pi_pos
  have hπ := pi_ne_zero
  have hr1 := h1.ne'
  have hr2 := h2.ne'
  have hT' : (r1 ^ 2 - Q ^ 2) * r2 ^ 3 = (r2 ^ 2 - Q ^ 2) * r1 ^ 3 := by
    have e1 : (r1 - Q ^ 2 / r1) / (4 * π * r1 ^ 2) = (r1 ^ 2 - Q ^ 2) / (4 * π * r1 ^ 3) := by
      field_simp; ring
    have e2 : (r2 - Q ^ 2 / r2) / (4 * π * r2 ^ 2) = (r2 ^ 2 - Q ^ 2) / (4 * π * r2 ^ 3) := by
      field_simp; ring
    rw [e1, e2, div_eq_div_iff (by positivity) (by positivity)] at hT
    have h4 : (4 * π) ≠ 0 := by positivity
    have h5 : 4 * π * ((r1 ^ 2 - Q ^ 2) * r2 ^ 3) = 4 * π * ((r2 ^ 2 - Q ^ 2) * r1 ^ 3) := by
      linear_combination hT
    exact mul_left_cancel₀ h4 h5
  have hsub : r2 - r1 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have key : r1 ^ 2 * r2 ^ 2 = Q ^ 2 * (r1 ^ 2 + r1 * r2 + r2 ^ 2) := by
    apply mul_left_cancel₀ hsub
    linear_combination hT'
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hd : 0 < (r1 - r2) ^ 2 := by
    have : r1 - r2 ≠ 0 := sub_ne_zero.2 hne
    positivity
  have h3 : r1 * r2 * (r1 * r2 - 3 * Q ^ 2) = Q ^ 2 * (r1 - r2) ^ 2 := by linear_combination key
  have h4 : 0 < r1 * r2 * (r1 * r2 - 3 * Q ^ 2) := by rw [h3]; exact mul_pos hQ2 hd
  have h5 : 0 < r1 * r2 := mul_pos h1 h2
  have h6 : 0 < r1 * r2 - 3 * Q ^ 2 := pos_of_mul_pos_right h4 h5.le
  linarith

/-- 【α-IX.33】同じ温度なら小さい枝(極限 = 首につながる)の自由エネルギーが低い -/
theorem small_branch_preferred (r1 r2 Q : ℝ) (h1 : 0 < r1) (hlt : r1 < r2) (hQ : Q ≠ 0)
    (hT : (r1 - Q ^ 2 / r1) / (4 * π * r1 ^ 2) = (r2 - Q ^ 2 / r2) / (4 * π * r2 ^ 2)) :
    r1 / 4 + 3 * Q ^ 2 / (4 * r1) < r2 / 4 + 3 * Q ^ 2 / (4 * r2) := by
  have h2 : 0 < r2 := lt_trans h1 hlt
  have hr1 := h1.ne'
  have hr2 := h2.ne'
  have hp := same_T_product r1 r2 Q h1 h2 hlt.ne hQ hT
  have e : r2 / 4 + 3 * Q ^ 2 / (4 * r2) - (r1 / 4 + 3 * Q ^ 2 / (4 * r1))
      = (r2 - r1) * (r1 * r2 - 3 * Q ^ 2) / (4 * r1 * r2) := by
    field_simp; ring
  have : 0 < (r2 - r1) * (r1 * r2 - 3 * Q ^ 2) / (4 * r1 * r2) := by
    apply div_pos
    · exact mul_pos (by linarith) (by linarith)
    · positivity
  linarith

/-- 比熱の符号:T ∝ g(r) = 1/r − Q²/r³、g′(r) = −1/r² + 3Q²/r⁴ > 0 ⇔ r² < 3Q² -/
theorem heat_capacity_sign (r Q : ℝ) (hr : 0 < r) :
    HasDerivAt (fun x => 1 / x - Q ^ 2 / x ^ 3) (-1 / r ^ 2 + 3 * Q ^ 2 / r ^ 4) r ∧
    (0 < -1 / r ^ 2 + 3 * Q ^ 2 / r ^ 4 ↔ r ^ 2 < 3 * Q ^ 2) := by
  have hr0 := hr.ne'
  constructor
  · have h1 := (hasDerivAt_const r (1 : ℝ)).div (hasDerivAt_id' r) hr0
    have h2 := (hasDerivAt_const r (Q ^ 2)).div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr0)
    convert h1.sub h2 using 1
    simp only [Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl]
    field_simp
    ring
  · have e : -1 / r ^ 2 + 3 * Q ^ 2 / r ^ 4 = (3 * Q ^ 2 - r ^ 2) / r ^ 4 := by
      field_simp; ring
    rw [e, div_pos_iff_of_pos_right (by positivity)]
    constructor <;> intro h <;> linarith

/-! ### IX.27 Jüttner から Maxwell へ -/

/-- √(1 + t) ≥ 1 + t/2 − t²/8(0 ≤ t ≤ 8) -/
theorem sqrt_lower (t : ℝ) (h0 : 0 ≤ t) (h8 : t ≤ 8) : 1 + t / 2 - t ^ 2 / 8 ≤ Real.sqrt (1 + t) := by
  by_cases hneg : 1 + t / 2 - t ^ 2 / 8 ≤ 0
  · exact le_trans hneg (Real.sqrt_nonneg _)
  push_neg at hneg
  have h1 : (1 + t / 2 - t ^ 2 / 8) ^ 2 ≤ 1 + t := by
    nlinarith [mul_nonneg (pow_nonneg h0 3) (sub_nonneg.2 h8)]
  calc 1 + t / 2 - t ^ 2 / 8 = Real.sqrt ((1 + t / 2 - t ^ 2 / 8) ^ 2) := (Real.sqrt_sq hneg.le).symm
    _ ≤ Real.sqrt (1 + t) := Real.sqrt_le_sqrt h1

/-- 【α-IX.27】m(√(1 + x/m) − 1) → x/2(m → ∞) -/
theorem nr_limit (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun m : ℝ => m * (Real.sqrt (1 + x / m) - 1)) atTop (𝓝 (x / 2)) := by
  have hlow : Tendsto (fun m : ℝ => x / 2 - x ^ 2 / 8 / m) atTop (𝓝 (x / 2)) := by
    have h0 : Tendsto (fun m : ℝ => x ^ 2 / 8 / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => x / 2) atTop (𝓝 (x / 2))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 1 (x / 8))] with m hm
    have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
    have hm0 : 0 < m := by linarith
    have hm0' : m ≠ 0 := hm0.ne'
    have ht0 : 0 ≤ x / m := div_nonneg hx hm0.le
    have ht8 : x / m ≤ 8 := by
      rw [div_le_iff₀ hm0]; have := le_trans (le_max_right _ _) hm; linarith
    have key := sqrt_lower (x / m) ht0 ht8
    have e : x / 2 - x ^ 2 / 8 / m = m * (1 + x / m / 2 - (x / m) ^ 2 / 8 - 1) := by
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hm0.le
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hm0' : m ≠ 0 := hm.ne'
    have ht0 : 0 ≤ x / m := div_nonneg hx hm.le
    have hs : Real.sqrt (1 + x / m) ≤ 1 + x / m / 2 := by
      have hpos : 0 ≤ 1 + x / m / 2 := by positivity
      calc Real.sqrt (1 + x / m) ≤ Real.sqrt ((1 + x / m / 2) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x / m / 2)])
        _ = 1 + x / m / 2 := Real.sqrt_sq hpos
    have e : x / 2 = m * (1 + x / m / 2 - 1) := by field_simp; ring
    calc m * (Real.sqrt (1 + x / m) - 1) ≤ m * (1 + x / m / 2 - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hm.le
      _ = x / 2 := e.symm

/-- 【α-IX.27】p² = mq² の尺度で e^{−β(E − m)} → e^{−βq²/2}(Maxwell 分布) -/
theorem juttner_to_maxwell (β q : ℝ) :
    Tendsto (fun m : ℝ => rexp (-β * (Real.sqrt (m ^ 2 + m * q ^ 2) - m))) atTop
      (𝓝 (rexp (-β * (q ^ 2 / 2)))) := by
  have h := nr_limit (q ^ 2) (sq_nonneg q)
  have h2 : Tendsto (fun m : ℝ => Real.sqrt (m ^ 2 + m * q ^ 2) - m) atTop (𝓝 (q ^ 2 / 2)) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm0 : m ≠ 0 := hm.ne'
    have e : Real.sqrt (m ^ 2 + m * q ^ 2) = m * Real.sqrt (1 + q ^ 2 / m) := by
      rw [show m ^ 2 + m * q ^ 2 = m ^ 2 * (1 + q ^ 2 / m) by field_simp; ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le]
    rw [e]; ring
  exact (Real.continuous_exp.tendsto _).comp (h2.const_mul (-β))

/-- 優関数:m ≥ 1 なら √(1 + x) − 1 ≤ m(√(1 + x/m) − 1) -/
theorem nr_monotone (x m : ℝ) (hx : 0 ≤ x) (hm : 1 ≤ m) :
    Real.sqrt (1 + x) - 1 ≤ m * (Real.sqrt (1 + x / m) - 1) := by
  have hm0 : 0 < m := by linarith
  have hm0' : m ≠ 0 := hm0.ne'
  have hxm : 0 ≤ x / m := div_nonneg hx hm0.le
  have hs1 : 1 ≤ Real.sqrt (1 + x / m) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + x / m) := Real.sqrt_le_sqrt (by linarith)
  have hss : Real.sqrt (1 + x / m) ^ 2 = 1 + x / m := Real.sq_sqrt (by linarith)
  generalize Real.sqrt (1 + x / m) = s at hs1 hss ⊢
  have hx' : x = m * (s ^ 2 - 1) := by
    have : x / m = s ^ 2 - 1 := by linarith
    field_simp at this; linear_combination this
  have hR : 0 ≤ m * (s - 1) + 1 := by nlinarith [mul_nonneg hm0.le (sub_nonneg.2 hs1)]
  have key : 1 + x ≤ (m * (s - 1) + 1) ^ 2 := by
    rw [hx']
    nlinarith [mul_nonneg (mul_nonneg hm0.le (sub_nonneg.2 hm)) (sq_nonneg (s - 1))]
  have : Real.sqrt (1 + x) ≤ m * (s - 1) + 1 :=
    calc Real.sqrt (1 + x) ≤ Real.sqrt ((m * (s - 1) + 1) ^ 2) := Real.sqrt_le_sqrt key
      _ = m * (s - 1) + 1 := Real.sqrt_sq hR
  linarith

/-! ### IX.30 KMS から揺動散逸の関係 -/

/-- 【α-IX.30】KMS の成分の式 g = e^{−βω}h だけから (h + g) sinh(βω/2) = (h − g) cosh(βω/2) -/
theorem fdt_from_kms (β ω g h : ℝ) (hkms : g = rexp (-(β * ω)) * h) :
    (h + g) * sinh (β * ω / 2) = (h - g) * cosh (β * ω / 2) := by
  have k := Stat.fdt β ω 0
  simp only [mul_zero, Real.exp_zero, sub_zero, neg_mul] at k
  rw [hkms]
  linear_combination h * k

section Spectral

variable {n : ℕ} (E : Fin n → ℝ) (β : ℝ) (w : Fin n → Fin n → ℝ)

/-- G_AB の周波数 ω の重み g(ω) = Σ_{E_m − E_k = ω} e^{−βE_m} w_km -/
noncomputable def gω (ω : ℝ) : ℝ :=
  ∑ k, ∑ m, if E m - E k = ω then rexp (-β * E m) * w k m else 0

/-- H_BA の周波数 ω の重み h(ω) = Σ_{E_m − E_k = ω} e^{−βE_k} w_km -/
noncomputable def hω (ω : ℝ) : ℝ :=
  ∑ k, ∑ m, if E m - E k = ω then rexp (-β * E k) * w k m else 0

/-- 【α-IX.30】KMS(IX.26)の成分:g(ω) = e^{−βω} h(ω)(詳細つり合い p_m = e^{−βω}p_k) -/
theorem kms_weights (ω : ℝ) : gω E β w ω = rexp (-(β * ω)) * hω E β w ω := by
  unfold gω hω
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h
  · rw [← h, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · simp

/-- 【α-IX.30】揺動散逸の関係 S(ω) = coth(βω/2) χ″(ω)(S = h + g、χ″ = h − g) -/
theorem fdt_spectral (ω : ℝ) :
    (hω E β w ω + gω E β w ω) * sinh (β * ω / 2) = (hω E β w ω - gω E β w ω) * cosh (β * ω / 2) :=
  fdt_from_kms β ω _ _ (kms_weights E β w ω)

end Spectral

/-! ### IX.34 はりねずみの次数 -/

/-- n = (sin θ cos φ, sin θ sin φ, cos θ) で n·(∂_θn × ∂_φn) = sin θ -/
theorem hedgehog_jacobian (θ φ : ℝ) :
    (sin θ * cos φ) * ((cos θ * sin φ) * 0 - (-sin θ) * (sin θ * cos φ))
      + (sin θ * sin φ) * ((-sin θ) * (-(sin θ * sin φ)) - (cos θ * cos φ) * 0)
      + cos θ * ((cos θ * cos φ) * (sin θ * cos φ) - (cos θ * sin φ) * (-(sin θ * sin φ)))
      = sin θ := by
  have h1 := sin_sq_add_cos_sq θ
  have h2 := sin_sq_add_cos_sq φ
  linear_combination (sin θ ^ 3 + sin θ * cos θ ^ 2) * h2 + sin θ * h1

/-- 【α-IX.34】次数 = (1/4π)∫₀^{2π}∫₀^π n·(∂_θn × ∂_φn) dθ dφ = 1 -/
theorem hedgehog_degree : 1 / (4 * π) * ∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π, sin θ = 1 := by
  simp only [integral_sin, cos_zero, cos_pi, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have := pi_ne_zero
  field_simp
  ring

/-! ### 非空性(X.6) -/

/-- magnetic_action の仮定をみたす例:r₊ = 2、Q = 1、β = 32π/3 -/
theorem nonempty_magnetic : ∃ β rp Q : ℝ, 0 < rp ∧ β * ((rp - Q ^ 2 / rp) / (4 * π * rp ^ 2)) = 1 :=
  ⟨32 * π / 3, 2, 1, by norm_num, by have := pi_ne_zero; field_simp <;> ring⟩

/-- same_T_product の仮定をみたす例:r₁ = 1、r₂ = 2、Q² = 4/7 -/
theorem nonempty_same_T :
    ∃ r1 r2 Q : ℝ, 0 < r1 ∧ r1 < r2 ∧ Q ≠ 0 ∧
      (r1 - Q ^ 2 / r1) / (4 * π * r1 ^ 2) = (r2 - Q ^ 2 / r2) / (4 * π * r2 ^ 2) := by
  refine ⟨1, 2, 2 / Real.sqrt 7, by norm_num, by norm_num, ?_, ?_⟩
  · have : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
    positivity
  · have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    have hs : Real.sqrt 7 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have hQ : (2 / Real.sqrt 7) ^ 2 = 4 / 7 := by rw [div_pow, h7]; norm_num
    rw [hQ]
    have := pi_ne_zero
    field_simp <;> ring

end CFT.FixThermo
