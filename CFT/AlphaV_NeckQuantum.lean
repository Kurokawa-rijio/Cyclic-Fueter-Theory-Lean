/-
  α-V.7-N:首 AdS₂ × S² の上の共形場の量子応力とその反作用
  α-V.7′:背景 SU(2) 場の量子揺らぎ(β 関数の項 ∝ F²)と反作用

  V.7-N の入力(V.7 と同じ三つ)
  (A1) トレースアノマリー ⟨T^μ_μ⟩ = (ħ/16π²)(c_E C² − a_E E₄)(b = 0 の繰り込み、自由な共形場)
  (A2) 応力の保存と、首の対称性 SO(2,1) × SO(3) をもつ状態
  (A3) 半径の等しい AdS₂ × S²(Bertotti–Robinson)は共形平坦(外部の事実)。共形真空では
       ⟨T^μ_ν⟩ = β ⁽³⁾H^μ_ν(Brown–Ottewill、Page。β = −ħa_E/(8π²) は V.7 `beta_from_anomaly`)
  Lean で示すこと
  * neck_ricci:首(N″ = N/ℓ²、A = 1、R = ℓ)の Ricci の固有値は (−1/ℓ², −1/ℓ², 1/ℓ², 1/ℓ²)
    (AlphaS4_Curv の Levi-Civita の計算から)。
  * neck_H3:⁽³⁾H^μ_ν = −k² δ^μ_ν(k = 1/ℓ²)、跡 −4k²。
  * neck_curvature_invariants:K = 8k²、R_μνR^μν = 4k²、R = 0 なら C² = 0、E₄ = −8k² = 2 tr ⁽³⁾H。
  * neck_trace_consistent:β ⁽³⁾H の跡 = アノマリー −(ħa_E/16π²)E₄。
  * 状態の項:対称性をもつ保存した跡ゼロのテンソルは κ k² diag(−1, −1, 1, 1) の形(外部:不変テンソルの分類)。
    これは磁場の応力と同じ形なので、磁荷の繰り込みに吸収される。共形真空では κ = 0。
  * 反作用(1 次):⟨T^μ_ν⟩ = (ħa_E/8π²)k² δ は負の宇宙定数と同じ働き。Einstein 方程式
      AdS 成分:−x = −ℓ²x² + ε/ℓ²、S² 成分:y = ℓ²x² + ε/ℓ²(x = 1/r²、y = 1/L²、ε = Għa_E/(πℓ²))
    の解 x = (1 + √(1 + 4ε))/(2ℓ²)、y = x + 2ε/ℓ²(`neck_backreaction`)。
    ℓ²(1 − ε) ≤ ℓ²/(1 + ε) ≤ r² ≤ ℓ²(球は縮む、δr²/ℓ² = −ε + O(ε²))、L ≤ r(`neck_radius_bounds`)。
    ε = a_E g²/(4π²)(ℓ² = 4πGħ/g²、`epsilon_value`)。L ≠ r になると共形平坦でなくなるので、この解は ε の 1 次まで。
  V.7′ の入力
  (B1) Yang–Mills のトレースアノマリー(Collins–Duncan–Joglekar 1977)と 1 ループの β 関数
       (Gross–Wilczek、Politzer 1973):SU(2) の純粋な YM で b₀ = 22/3。
       背景場の方法の 1 ループで、跡は tr = 6c/a⁴(帽子の磁場 F² = 4g²ρ = 6/a⁴、`cap_F2`)、
       c = b₀ħ/(32π²)(符号は μ∂_μ(1/g²) = b₀/(8π²) との整合で決まる)。
  Lean で示すこと
  * rho_beta_conserved:ρ_β = (κ − 6c log a)/a⁴ は保存則 ρ̇ = −(ȧ/a)(4ρ + 6c/a⁴) をみたす。
  * rho_beta_unique:同じ跡の解は ρ_β と κ/a⁴ の差しかない。
  * running_coupling:古典の ρ = 3/(2g²a⁴) と合わせると ρ = (3/(2a⁴))·(1/g²(μ))、
      1/g²(μ) = 1/g² + (b₀/8π²) log μ、μ = 1/a(漸近的自由性:a → 0 で 1/g² → ∞)。
    つまり帽子の量子反作用は、結合定数が帽子の大きさの尺度で走ることそのもの。
  * 首:W のモードが負(IX.15)なので、1 ループの有効作用は虚部をもつ(Nielsen–Olesen の不安定性)。
    首には安定な実の量子応力はなく、反作用は W の凝縮として現れる(AlphaIX_JT `gaussian_negative_mode`)。
-/
import CFT.AlphaS4_Curv
import CFT.AlphaV_FRW
import CFT.AlphaV_Anomaly

namespace CFT.NeckQuantum

open Real Set

/-! ### 首の Ricci(Levi-Civita の公式から) -/

section Ricci

open CFT.S4

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

set_option maxHeartbeats 0 in
/-- 【α-V.7-N】首 −N²dt² + dx² + ℓ²dΩ²(∂_t N = 0、N″ = N/ℓ²)の Ricci の混合成分 -/
theorem neck_ricci (N l s c : S) (H : SphD d N 1 l s c) (hN0 : d 0 N = 0)
    (hNxx : d 1 (d 1 N) = N * l⁻¹ ^ 2) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    -(N⁻¹ ^ 2) * Ric d (GD d N 1 l s c) 0 0 = -(l⁻¹ ^ 2) ∧
    (1 : S)⁻¹ ^ 2 * Ric d (GD d N 1 l s c) 1 1 = -(l⁻¹ ^ 2) ∧
    l⁻¹ ^ 2 * Ric d (GD d N 1 l s c) 2 2 = l⁻¹ ^ 2 ∧
    l⁻¹ ^ 2 * s⁻¹ ^ 2 * Ric d (GD d N 1 l s c) 3 3 = l⁻¹ ^ 2 := by
  have hN := H.hN
  have hs := H.hs
  have hl := H.hR
  have d1 : ∀ i, d i (1 : S) = 0 := fun i => (d i).map_one_eq_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ricD_00 d N 1 l s c H]
    simp [d1, hN0, hNxx, hl0, hl1]
    try field_simp
    try ring
  · rw [ricD_11 d N 1 l s c H]
    simp [d1, hN0, hNxx, hl0, hl1]
    try field_simp
    try ring
  · rw [ricD_22 d N 1 l s c H]
    simp [d1, hN0, hNxx, hl0, hl1]
  · rw [ricD_33 d N 1 l s c H]
    simp [d1, hN0, hNxx, hl0, hl1]
    try field_simp

end Ricci

/-! ### ⁽³⁾H と曲率の不変量 -/

section H3

variable {S : Type*} [Field S] [CharZero S]

/-- 【α-V.7-N】固有値 (−k, −k, k, k) で ⁽³⁾H^μ_μ = −k²(各成分)、跡 −4k² -/
theorem neck_H3 (k : S) :
    (∀ m, CFT.FRW.H3mix ![-k, -k, k, k] m = -k ^ 2) ∧ ∑ m, CFT.FRW.H3mix ![-k, -k, k, k] m = -4 * k ^ 2 := by
  have h : ∀ m, CFT.FRW.H3mix ![-k, -k, k, k] m = -k ^ 2 := by
    intro m
    fin_cases m <;>
      simp [CFT.FRW.H3mix, Fin.sum_univ_four] <;> ring
  refine ⟨h, ?_⟩
  rw [Fin.sum_univ_four, h 0, h 1, h 2, h 3]; ring

/-- 【α-V.7-N】K = 8k²、Ric² = 4k²、R = 0 なら C² = K − 2Ric² + R²/3 = 0、E₄ = K − 4Ric² + R² = −8k² = 2 tr ⁽³⁾H -/
theorem neck_curvature_invariants (k : S) :
    let K := 8 * k ^ 2
    let Ric2 := 4 * k ^ 2
    let Rs : S := 0
    K - 2 * Ric2 + Rs ^ 2 / 3 = 0 ∧ K - 4 * Ric2 + Rs ^ 2 = -8 * k ^ 2 ∧ -8 * k ^ 2 = 2 * (-4 * k ^ 2) := by
  intro K Ric2 Rs
  refine ⟨?_, ?_, ?_⟩ <;> simp only [K, Ric2, Rs] <;> ring

end H3

/-- 【α-V.7-N】跡の整合:β ⁽³⁾H の跡 −4βk² = −(ħa_E/16π²)E₄(β = −ħa_E/(8π²)、E₄ = −8k²) -/
theorem neck_trace_consistent (hb aE k : ℝ) :
    -4 * (-(hb * aE / (8 * π ^ 2))) * k ^ 2 = -(hb * aE / (16 * π ^ 2)) * (-8 * k ^ 2) := by
  have := pi_ne_zero
  field_simp <;> ring

/-! ### 首の反作用(1 次) -/

/-- 【α-V.7-N】Einstein 方程式の解:x = (1 + √(1 + 4ε))/(2ℓ²) は ℓ²x² − x − ε/ℓ² = 0、
y := ℓ²x² + ε/ℓ² = x + 2ε/ℓ² -/
theorem neck_backreaction (l ε : ℝ) (hl : l ≠ 0) (hε : 0 ≤ ε) :
    let x := (1 + Real.sqrt (1 + 4 * ε)) / (2 * l ^ 2)
    l ^ 2 * x ^ 2 - x - ε / l ^ 2 = 0 ∧ l ^ 2 * x ^ 2 + ε / l ^ 2 = x + 2 * ε / l ^ 2 := by
  intro x
  have hs : Real.sqrt (1 + 4 * ε) ^ 2 = 1 + 4 * ε := Real.sq_sqrt (by linarith)
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have key : l ^ 2 * x ^ 2 - x - ε / l ^ 2 = 0 := by
    have e : l ^ 2 * x ^ 2 - x - ε / l ^ 2 = (Real.sqrt (1 + 4 * ε) ^ 2 - (1 + 4 * ε)) / (4 * l ^ 2) := by
      simp only [x]; field_simp <;> ring
    rw [e, hs, sub_self, zero_div]
  refine ⟨key, ?_⟩
  linear_combination key

/-- 【α-V.7-N】半径の評価:ℓ²/(1 + ε) ≤ r² = 1/x ≤ ℓ²(球は縮む)、y ≥ x(L ≤ r) -/
theorem neck_radius_bounds (l ε : ℝ) (hl : l ≠ 0) (hε : 0 ≤ ε) :
    let x := (1 + Real.sqrt (1 + 4 * ε)) / (2 * l ^ 2)
    l ^ 2 / (1 + ε) ≤ 1 / x ∧ 1 / x ≤ l ^ 2 ∧ x ≤ x + 2 * ε / l ^ 2 := by
  intro x
  have hl2 : 0 < l ^ 2 := by positivity
  have hs1 : 1 ≤ Real.sqrt (1 + 4 * ε) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * ε by linarith)
    rwa [Real.sqrt_one] at this
  have hs2 : Real.sqrt (1 + 4 * ε) ≤ 1 + 2 * ε := by
    have := Real.sqrt_le_sqrt (show 1 + 4 * ε ≤ (1 + 2 * ε) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have e : 1 / x = 2 * l ^ 2 / (1 + Real.sqrt (1 + 4 * ε)) := by
    simp only [x]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e, div_le_div_iff (by linarith) (by linarith)]
    nlinarith
  · rw [e, div_le_iff₀ (by linarith)]
    nlinarith
  · have : 0 ≤ 2 * ε / l ^ 2 := by positivity
    linarith

/-- ε = Għa_E/(πℓ²) = a_E g²/(4π²)(ℓ² = 4πGħ/g²) -/
theorem epsilon_value (G hb g aE l : ℝ) (hG : G ≠ 0) (hb0 : hb ≠ 0) (hg : g ≠ 0)
    (hl : l ^ 2 = 4 * π * G * hb / g ^ 2) : G * hb * aE / (π * l ^ 2) = aE * g ^ 2 / (4 * π ^ 2) := by
  have := pi_ne_zero
  rw [hl]; field_simp <;> ring

/-! ### V.7′:β 関数の項と走る結合定数 -/

/-- 帽子の磁場:純粋に磁気的なら F² = 2ΣB² = 4g²ρ、ρ = 3/(2g²a⁴) で F² = 6/a⁴ -/
theorem cap_F2 (g a : ℝ) (hg : g ≠ 0) (ha : a ≠ 0) : 4 * g ^ 2 * (3 / (2 * g ^ 2 * a ^ 4)) = 6 / a ^ 4 := by
  field_simp <;> ring

/-- ρ_β = (κ − 6c log a)/a⁴ -/
noncomputable def rhoB (κ c : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ := (κ - 6 * c * Real.log (a t)) / a t ^ 4

/-- 【α-V.7′】ρ_β は保存則 ρ̇ = −(ȧ/a)(4ρ + 6c/a⁴) をみたす(a > 0) -/
theorem rho_beta_conserved (κ c : ℝ) (a : ℝ → ℝ) (ad t : ℝ) (ha : HasDerivAt a ad t) (hpos : 0 < a t) :
    HasDerivAt (rhoB κ c a) (-(ad / a t) * (4 * rhoB κ c a t + 6 * c / a t ^ 4)) t := by
  have ha0 := hpos.ne'
  have hlog := (ha.log ha0).const_mul (6 * c)
  have hnum := hlog.const_sub κ
  have h := hnum.div (ha.pow 4) (pow_ne_zero 4 ha0)
  show HasDerivAt (fun y => (κ - 6 * c * Real.log (a y)) / a y ^ 4)
    (-(ad / a t) * (4 * ((κ - 6 * c * Real.log (a t)) / a t ^ 4) + 6 * c / a t ^ 4)) t
  convert h using 1
  simp only [Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl]
  field_simp <;> ring

/-- 【α-V.7′】一意性:同じ跡の解は ρ_β と κ′/a⁴ の差しかない(a⁴(ρ − ρ_β) は一定) -/
theorem rho_beta_unique (κ c : ℝ) (a ad ρ : ℝ → ℝ) (t0 t1 : ℝ)
    (ha : ∀ t ∈ Icc t0 t1, HasDerivAt a (ad t) t) (hpos : ∀ t ∈ Icc t0 t1, 0 < a t)
    (hρ : ∀ t ∈ Icc t0 t1, HasDerivAt ρ (-(ad t / a t) * (4 * ρ t + 6 * c / a t ^ 4)) t) :
    ∀ t ∈ Icc t0 t1, a t ^ 4 * (ρ t - rhoB κ c a t) = a t0 ^ 4 * (ρ t0 - rhoB κ c a t0) := by
  have hd : ∀ t ∈ Icc t0 t1, HasDerivAt (fun τ => a τ ^ 4 * (ρ τ - rhoB κ c a τ)) 0 t := by
    intro t ht
    have hq := rho_beta_conserved κ c a (ad t) t (ha t ht) (hpos t ht)
    have h := ((ha t ht).pow 4).mul ((hρ t ht).sub hq)
    refine h.congr_deriv ?_
    have h0 := (hpos t ht).ne'
    simp only [Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl]
    field_simp <;> ring
  have hcont : ContinuousOn (fun τ => a τ ^ 4 * (ρ τ - rhoB κ c a τ)) (Icc t0 t1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hder : ∀ t ∈ Ico t0 t1,
      HasDerivWithinAt (fun τ => a τ ^ 4 * (ρ τ - rhoB κ c a τ)) 0 (Ici t) t :=
    fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hder

/-- 【α-V.7′】走る結合定数:κ = 0、c = b₀/(32π²)(ħ = 1)なら
3/(2g²a⁴) + ρ_β = (3/(2a⁴))(1/g² + (b₀/8π²) log(1/a)) -/
theorem running_coupling (g b0 a : ℝ) (hg : g ≠ 0) (ha : 0 < a) :
    3 / (2 * g ^ 2 * a ^ 4) + (0 - 6 * (b0 / (32 * π ^ 2)) * Real.log a) / a ^ 4
      = 3 / (2 * a ^ 4) * (1 / g ^ 2 + b0 / (8 * π ^ 2) * Real.log (1 / a)) := by
  have := pi_ne_zero
  have ha0 := ha.ne'
  rw [one_div, Real.log_inv]
  field_simp <;> ring

end CFT.NeckQuantum
