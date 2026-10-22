/-
  段階 3 の閉鎖:α-II.4 の厳密な窓と α-III.6 の非自明な平坦極限(2026-10-21 の外部監査の論証を Lean に)

  A. α-II.4:旧 window は角括弧が負であること(hneg)を仮定に置いていた。Bochner から出るのは κ ≤ 0 だけ。
    * disc_identity:Σc = 0、Σ_{i<j}c_ic_j = −3/4、c₁c₂c₃ = C/4 なら Π_{i<j}(c_i − c_j)² = (27/16)(1 − C²)
    * C_strict:c が相異なれば −1 < C < 1
    * window_strict:t > 0、t² = 12 − 2x(x = R ℓ²)、角括弧 2ℓ√R + tC ≤ 0、C > −1 ⇒ x < 2
    * strict_window:相異なる固有値 λ が (I) の関係 Σλ² = R²/4 + R/(2ℓ²) を満たし κ ≤ 0 なら 0 < Rℓ² < 2。
      角度の表示 λ_i = R/3 + q c_i は仮定せず、λ から作る(R > 0 と Rℓ² < 6 も固有値の相異から出る)
    * c2_window:C2 枠の各点で、固有値が相異なり (I) が成り立つなら 0 < Rℓ² < 2(kappa_nonpos と合わせる)
  B. α-III.6:密度 ρ₀ > 0 を固定し、帽子の半径 a → ∞ と G(a) = 3/(8πρ₀a²) → 0 を同時にとる
    (6/a² = 16πG(a)ρ₀ を保つ)。固有半径 s を固定して
    * flat_r:r_a(s) = a sin(s/a) → s、flat_rp:r_a′ = cos(s/a) → 1、flat_G:G(a) → 0
    * cap_mass_exact:m_a = M₂/(2G(a)) = (4π/3)ρ₀ r_a³(有限の a で厳密)
    * flat_mass:m_a(s) → (4π/3)ρ₀ s³、cap_mass_rate:dm_a/ds = 4πρ₀ r_a² r_a′、flat_mass_rate_limit:→ 4πρ₀ s²
    G を固定して a → ∞ とすると ρ = 3/(8πGa²) → 0 で真空に退化するので、非零の密度には同時の極限が要る。
-/
import CFT.Cartan.BochnerSign
import CFT.AlphaII
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

open Real Filter Topology

namespace CFT.S3

/-! ### A. α-II.4 の厳密な窓 -/

theorem disc_identity (c1 c2 c3 C : ℝ) (he1 : c1 + c2 + c3 = 0) (he2 : c1 * c2 + c2 * c3 + c3 * c1 = -3 / 4)
    (he3 : c1 * c2 * c3 = C / 4) :
    (c1 - c2) ^ 2 * (c2 - c3) ^ 2 * (c1 - c3) ^ 2 = 27 / 16 * (1 - C ^ 2) := by
  have h3 : c3 = -c1 - c2 := by linarith
  subst h3
  have hC : C = 4 * (c1 * c2 * (-c1 - c2)) := by linarith
  subst hC
  linear_combination (-4*c1^4 - 8*c1^3*c2 - 12*c1^2*c2^2 - 3*c1^2 - 8*c1*c2^3 - 3*c1*c2 - 4*c2^4
    - 3*c2^2 - 9/4) * he2

theorem C_strict (c1 c2 c3 C : ℝ) (he1 : c1 + c2 + c3 = 0) (he2 : c1 * c2 + c2 * c3 + c3 * c1 = -3 / 4)
    (he3 : c1 * c2 * c3 = C / 4) (h12 : c1 ≠ c2) (h23 : c2 ≠ c3) (h13 : c1 ≠ c3) :
    -1 < C ∧ C < 1 := by
  have hd := disc_identity c1 c2 c3 C he1 he2 he3
  have hpos : 0 < (c1 - c2) ^ 2 * (c2 - c3) ^ 2 * (c1 - c3) ^ 2 := by
    have := sub_ne_zero.mpr h12; have := sub_ne_zero.mpr h23; have := sub_ne_zero.mpr h13
    positivity
  rw [hd] at hpos
  have h1 : C ^ 2 < 1 := by linarith
  exact abs_lt.mp ((sq_lt_one_iff_abs_lt_one C).mp h1)

/-- 角括弧 ≤ 0 と C > −1 から x < 2(旧 window の hneg を弱めた形) -/
theorem window_strict (sR l t C : ℝ) (hsR : 0 < sR) (hl : 0 < l) (ht : 0 < t)
    (ht2 : t ^ 2 = 12 - 2 * (sR ^ 2 * l ^ 2)) (hC : -1 < C) (hbr : 2 * l * sR + t * C ≤ 0) :
    sR ^ 2 * l ^ 2 < 2 := by
  by_contra hx
  push_neg at hx
  have h1 : t ≤ 2 * l * sR := by
    have : t ^ 2 ≤ (2 * l * sR) ^ 2 := by nlinarith
    have h0 : 0 ≤ 2 * l * sR := by positivity
    nlinarith [sq_nonneg (t - 2 * l * sR), sq_nonneg (t + 2 * l * sR)]
  have h2 : -t < t * C := by nlinarith
  linarith

set_option maxHeartbeats 4000000 in
/-- 固有値から:相異なる λ、(I) の関係、κ ≤ 0 ⇒ 0 < Rℓ² < 2 -/
theorem strict_window (l1 l2 l3 l : ℝ) (hl : 0 < l) (h12 : l1 ≠ l2) (h23 : l2 ≠ l3) (h13 : l1 ≠ l3)
    (hI : l1 ^ 2 + l2 ^ 2 + l3 ^ 2 = (l1 + l2 + l3) ^ 2 / 4 + (l1 + l2 + l3) / (2 * l ^ 2))
    (hκ : (l1 + l2 - (l1 + l2 + l3) / 2) * (l1 - l2) ^ 2 + (l2 + l3 - (l1 + l2 + l3) / 2) * (l2 - l3) ^ 2
      + (l1 + l3 - (l1 + l2 + l3) / 2) * (l1 - l3) ^ 2 ≤ 0) :
    0 < (l1 + l2 + l3) * l ^ 2 ∧ (l1 + l2 + l3) * l ^ 2 < 2 := by
  obtain ⟨R, hR⟩ : ∃ R, R = l1 + l2 + l3 := ⟨_, rfl⟩
  rw [← hR] at hI hκ ⊢
  have hl2 : 0 < l ^ 2 := by positivity
  have hI' : (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) * (4 * l ^ 2) = R ^ 2 * l ^ 2 + 2 * R := by
    rw [hI]; field_simp; ring
  have hspread : 0 < (l1 - l2) ^ 2 + (l2 - l3) ^ 2 + (l1 - l3) ^ 2 := by
    have := sub_ne_zero.mpr h12; positivity
  have key : R * (6 - R * l ^ 2) = 4 * l ^ 2 * ((l1 - l2) ^ 2 + (l2 - l3) ^ 2 + (l1 - l3) ^ 2) := by
    rw [hR] at hI' ⊢; linear_combination (-3 : ℝ) * hI'
  have hprod : 0 < R * (6 - R * l ^ 2) := by rw [key]; positivity
  have hRpos : 0 < R := by
    by_contra h; push_neg at h
    have : 0 ≤ 6 - R * l ^ 2 := by nlinarith
    nlinarith
  have h6 : R * l ^ 2 < 6 := by
    by_contra h; push_neg at h; nlinarith
  refine ⟨by positivity, ?_⟩
  obtain ⟨sR, hsR⟩ : ∃ sR, sR = √R := ⟨_, rfl⟩
  have hsR0 : 0 < sR := by rw [hsR]; exact Real.sqrt_pos.mpr hRpos
  have hsR2 : sR ^ 2 = R := by rw [hsR]; exact Real.sq_sqrt hRpos.le
  obtain ⟨t, htd⟩ : ∃ t, t = √(12 - 2 * (sR ^ 2 * l ^ 2)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htd]; exact Real.sqrt_pos.mpr (by rw [hsR2]; linarith)
  have ht2 : t ^ 2 = 12 - 2 * (sR ^ 2 * l ^ 2) := by rw [htd]; exact Real.sq_sqrt (by rw [hsR2]; linarith)
  obtain ⟨q, hq⟩ : ∃ q, q = sR * t / (6 * l) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqne : q ≠ 0 := hq0.ne'
  obtain ⟨c1, hc1⟩ : ∃ c, c = (l1 - R / 3) / q := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = (l2 - R / 3) / q := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = (l3 - R / 3) / q := ⟨_, rfl⟩
  have hl1 : l1 = R / 3 + q * c1 := by rw [hc1]; field_simp; ring
  have hl2' : l2 = R / 3 + q * c2 := by rw [hc2]; field_simp; ring
  have hl3 : l3 = R / 3 + q * c3 := by rw [hc3]; field_simp; ring
  have he1 : c1 + c2 + c3 = 0 := by
    have : q * (c1 + c2 + c3) = 0 := by linear_combination -(hl1 + hl2' + hl3) - hR
    exact (mul_eq_zero.mp this).resolve_left hqne
  have hq2 : q ^ 2 * (36 * l ^ 2) = R * t ^ 2 := by
    rw [hq, ← hsR2]; field_simp; ring
  have hsq : q ^ 2 * (c1 ^ 2 + c2 ^ 2 + c3 ^ 2) = 3 / 2 * q ^ 2 := by
    -- Σ(λ − R/3)² = R(6 − Rℓ²)/(12ℓ²) = (3/2)q²
    have hs : (q * c1) ^ 2 + (q * c2) ^ 2 + (q * c3) ^ 2 = (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) - R ^ 2 / 3 := by
      have e1 : q * c1 = l1 - R / 3 := by linarith
      have e2 : q * c2 = l2 - R / 3 := by linarith
      have e3 : q * c3 = l3 - R / 3 := by linarith
      rw [e1, e2, e3, hR]; ring
    have hS : (l1 ^ 2 + l2 ^ 2 + l3 ^ 2) - R ^ 2 / 3 = R * (6 - R * l ^ 2) / (12 * l ^ 2) := by
      rw [eq_div_iff (by positivity)]; linear_combination (3 : ℝ) * hI'
    have h36 : R * (6 - R * l ^ 2) / (12 * l ^ 2) = 3 / 2 * q ^ 2 := by
      have hlne : l ≠ 0 := hl.ne'
      rw [div_eq_iff (by positivity)]
      have : t ^ 2 = 12 - 2 * (R * l ^ 2) := by rw [ht2, hsR2]
      linear_combination (-1/2 : ℝ) * hq2 - (R / 2) * this
    linear_combination hs + hS + h36
  have hsq' : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 = 3 / 2 := by
    have := pow_ne_zero 2 hqne
    have h := hsq; rw [← sub_eq_zero] at h
    have : q ^ 2 * (c1 ^ 2 + c2 ^ 2 + c3 ^ 2 - 3 / 2) = 0 := by linear_combination h
    linarith [(mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hqne)]
  have he2 : c1 * c2 + c2 * c3 + c3 * c1 = -3 / 4 := by
    have : (c1 + c2 + c3) ^ 2 = 0 := by rw [he1]; ring
    linear_combination (1/2 : ℝ) * this - (1/2 : ℝ) * hsq'
  obtain ⟨C, hCd⟩ : ∃ C, C = 4 * (c1 * c2 * c3) := ⟨_, rfl⟩
  have he3 : c1 * c2 * c3 = C / 4 := by rw [hCd]; ring
  have hc12 : c1 ≠ c2 := by intro h; apply h12; rw [hl1, hl2', h]
  have hc23 : c2 ≠ c3 := by intro h; apply h23; rw [hl2', hl3, h]
  have hc13 : c1 ≠ c3 := by intro h; apply h13; rw [hl1, hl3, h]
  have hCs := (C_strict c1 c2 c3 C he1 he2 he3 hc12 hc23 hc13).1
  have hk0 := CFT.AlphaII.kappa_closed sR t l C c1 c2 c3 hl.ne' he1 he2 he3 (by rw [ht2]; ring)
  have hsym := CFT.AlphaII.kappa_sym l1 l2 l3
  simp only at hk0 hsym
  have e : (l1 + l2 + l3) ^ 3 - 4 * (l1 + l2 + l3) * (l1 * l2 + l2 * l3 + l3 * l1) + 9 * (l1 * l2 * l3)
      = (6 - R * l ^ 2) * sR ^ 3 / (48 * l ^ 3) * (2 * l * sR + t * C) := by
    rw [hl1, hl2', hl3, ← hsR2, hq]
    linear_combination hk0
  have hκ' : (6 - R * l ^ 2) * sR ^ 3 / (48 * l ^ 3) * (2 * l * sR + t * C) ≤ 0 := by
    rw [← e, ← hsym]; rw [hR] at hκ; linarith [hκ]
  have hpre : 0 < (6 - R * l ^ 2) * sR ^ 3 / (48 * l ^ 3) := by
    have : 0 < 6 - R * l ^ 2 := by linarith
    positivity
  have hbr : 2 * l * sR + t * C ≤ 0 := by
    by_contra h; push_neg at h; have := mul_pos hpre h; linarith
  have := window_strict sR l t C hsR0 hl ht0 ht2 hCs hbr
  rw [hsR2] at this; linarith

/-- C2 枠の各点で:Ricci 固有値が相異なり (I) が成り立つなら 0 < Rℓ² < 2(κ < 0 は仮定しない) -/
theorem c2_window {Rg : Type*} [CommRing Rg] [Algebra ℚ Rg] {F : CFT.Cartan.Frame Rg} {lam : Fin 3 → Rg}
    (H : CFT.Cartan.C2 F lam) (ev : Rg →+* ℝ) (l : ℝ) (hl : 0 < l)
    (h01 : ev (lam 0) ≠ ev (lam 1)) (h12 : ev (lam 1) ≠ ev (lam 2)) (h02 : ev (lam 0) ≠ ev (lam 2))
    (hI : ev (lam 0) ^ 2 + ev (lam 1) ^ 2 + ev (lam 2) ^ 2
      = (ev (lam 0) + ev (lam 1) + ev (lam 2)) ^ 2 / 4 + (ev (lam 0) + ev (lam 1) + ev (lam 2)) / (2 * l ^ 2)) :
    0 < (ev (lam 0) + ev (lam 1) + ev (lam 2)) * l ^ 2 ∧ (ev (lam 0) + ev (lam 1) + ev (lam 2)) * l ^ 2 < 2 := by
  have hk := H.kappa_nonpos ev
  simp only at hk
  exact strict_window _ _ _ l hl h01 h12 h02 hI (by linarith)

/-! ### B. α-III.6 の非自明な平坦極限 -/

/-- r_a(s) = a sin(s/a) → s(a → ∞) -/
theorem flat_r (s : ℝ) : Tendsto (fun a : ℝ => a * sin (s / a)) atTop (𝓝 s) := by
  by_cases hs : s = 0
  · subst hs; simp
  have hslope := (hasDerivAt_sin 0).tendsto_slope_zero
  simp only [zero_add, sin_zero, sub_zero, cos_zero, smul_eq_mul] at hslope
  have hu : Tendsto (fun a : ℝ => s / a) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.div_atTop tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with a ha
      exact div_ne_zero hs ha.ne'
  have := (hslope.comp hu).const_mul s
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  simp only [Function.comp]
  field_simp

/-- r_a′ = cos(s/a) → 1 -/
theorem flat_rp (s : ℝ) : Tendsto (fun a : ℝ => cos (s / a)) atTop (𝓝 1) := by
  have h : Tendsto (fun a : ℝ => s / a) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  simpa using (continuous_cos.tendsto 0).comp h

/-- G(a) = 3/(8πρ₀a²) → 0 -/
theorem flat_G (ρ0 : ℝ) : Tendsto (fun a : ℝ => 3 / (8 * π * ρ0 * a ^ 2)) atTop (𝓝 0) := by
  by_cases hρ : ρ0 = 0
  · subst hρ; simp
  have h : Tendsto (fun a : ℝ => (3 / (8 * π * ρ0)) * (a ^ 2)⁻¹) atTop (𝓝 ((3 / (8 * π * ρ0)) * 0)) :=
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha
  field_simp

/-- 曲率と源の関係 6/a² = 16πG(a)ρ₀ と、有限の a での厳密な質量 m_a = M₂/(2G(a)) = (4π/3)ρ₀ r_a³ -/
theorem cap_mass_exact (ρ0 a s : ℝ) (hρ : ρ0 ≠ 0) (ha : a ≠ 0) :
    6 / a ^ 2 = 16 * π * (3 / (8 * π * ρ0 * a ^ 2)) * ρ0 ∧
    (a * sin (s / a) * (1 - cos (s / a) ^ 2)) / (2 * (3 / (8 * π * ρ0 * a ^ 2)))
      = 4 * π / 3 * ρ0 * (a * sin (s / a)) ^ 3 := by
  have hπ : π ≠ 0 := pi_ne_zero
  constructor
  · field_simp; ring
  · rw [show 1 - cos (s / a) ^ 2 = sin (s / a) ^ 2 by rw [← sin_sq_add_cos_sq (s / a)]; ring]
    field_simp; ring

/-- m_a(s) → (4π/3)ρ₀ s³ -/
theorem flat_mass (ρ0 s : ℝ) :
    Tendsto (fun a : ℝ => 4 * π / 3 * ρ0 * (a * sin (s / a)) ^ 3) atTop (𝓝 (4 * π / 3 * ρ0 * s ^ 3)) :=
  tendsto_const_nhds.mul ((flat_r s).pow 3)

/-- dm_a/ds = 4πρ₀ r_a² r_a′(有限の a で厳密) -/
theorem cap_mass_rate (ρ0 a s : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun s => 4 * π / 3 * ρ0 * (a * sin (s / a)) ^ 3)
      (4 * π * ρ0 * (a * sin (s / a)) ^ 2 * cos (s / a)) s := by
  have h1 : HasDerivAt (fun s => a * sin (s / a)) (cos (s / a)) s := by
    have := ((hasDerivAt_id s).div_const a).sin.const_mul a
    convert this using 1; simp only [id]; field_simp
  have := (h1.pow 3).const_mul (4 * π / 3 * ρ0)
  convert this using 1; push_cast; ring

/-- dm_a/ds → 4πρ₀ s² -/
theorem flat_mass_rate_limit (ρ0 s : ℝ) :
    Tendsto (fun a : ℝ => 4 * π * ρ0 * (a * sin (s / a)) ^ 2 * cos (s / a)) atTop (𝓝 (4 * π * ρ0 * s ^ 2)) := by
  have := (tendsto_const_nhds (x := 4 * π * ρ0)).mul ((flat_r s).pow 2) |>.mul (flat_rp s)
  simpa using this

end CFT.S3
