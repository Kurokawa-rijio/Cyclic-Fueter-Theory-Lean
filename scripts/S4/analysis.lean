/-! ### D. 実解析:拘束の輸送、Gudermann と Mercator、波面の出会い、帽子の崩壊、平坦極限、Z9 の整理 -/

section Analysis
open Real Filter Topology Set CFT.AlphaIV

/-- 拘束の輸送:∂_v C = −(r_v/r) C(constraint_prop_u)、初期の特性線で C = 0、r > 0 なら C ≡ 0 -/
theorem constraint_transport {v0 v1 : ℝ} {r rv C C' : ℝ → ℝ}
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hC : ∀ v ∈ Icc v0 v1, HasDerivWithinAt C (C' v) (Icc v0 v1) v)
    (heq : ∀ v ∈ Icc v0 v1, C' v = -(rv v * (r v)⁻¹) * C v) (h0 : C v0 = 0)
    (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0) : ∀ v ∈ Icc v0 v1, C v = 0 :=
  CFT.S4J.jump_transport hr hC (fun v hv => by rw [heq v hv]; field_simp [hpos v hv]; ring) h0 hpos

/-- W_uv の右辺(AlphaIV の FW)は Ω = e^{2σ} で goursat_W の右辺と同じ -/
theorem fw_eq (r σ W : ℝ) : FW r σ W = 2⁻¹ * exp (2 * σ) * W * (1 - W ^ 2) * r⁻¹ ^ 2 := by
  simp only [FW]; ring

/-- 首の波面 z_ℓ(t) = ℓ arsinh(tan(t/ℓ)) -/
noncomputable def zfront (l t : ℝ) : ℝ := l * arsinh (tan (t / l))

/-- z_ℓ(ℓ gd(z/ℓ)) = z(すべての z) -/
theorem front_gd_inv (l z : ℝ) (hl : l ≠ 0) : zfront l (l * gd (z / l)) = z := by
  simp only [zfront]
  rw [show l * gd (z / l) / l = gd (z / l) by field_simp, tan_gd, arsinh_sinh]
  field_simp

/-- 主値の帯 |t| < πℓ/2 で ℓ gd(z_ℓ(t)/ℓ) = t:z_ℓ と t ↦ ℓ gd(·/ℓ) は互いに逆 -/
theorem gd_front_inv (l t : ℝ) (hl : 0 < l) (ht : |t| < π * l / 2) : l * gd (zfront l t / l) = t := by
  have h1 : -(π / 2) < t / l := by
    rw [lt_div_iff hl]; have := neg_abs_le t; nlinarith
  have h2 : t / l < π / 2 := by
    rw [div_lt_iff hl]; have := le_abs_self t; nlinarith
  simp only [zfront, gd]
  rw [show l * arsinh (tan (t / l)) / l = arsinh (tan (t / l)) by field_simp, sinh_arsinh, arctan_tan h1 h2]
  field_simp

/-- cos(gd y) = sech y -/
theorem cos_gd (y : ℝ) : cos (gd y) = 1 / cosh y := by
  rw [gd, cos_arctan, ← cosh_sq', sqrt_sq (cosh_pos y).le]

/-- Mercator:gd′ = cos ∘ gd。したがって緯度 φ = gd(y) で球面の dφ² + cos²φ dλ² = sech²y (dy² + dλ²) -/
theorem mercator (y : ℝ) : HasDerivAt gd (cos (gd y)) y := by
  rw [cos_gd]; exact gd_deriv y

/-- 首の Mercator 座標:t(y) = ℓ gd(y/ℓ) は dt/dy = cos(t/ℓ)。したがって
  −dt² + cos²(t/ℓ)dz² = cos²(t/ℓ)(−dy² + dz²)(同じ Gudermann 写像が首の 2 次元の計量を共形平坦にする) -/
theorem neck_mercator (l y : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun y => l * gd (y / l)) (cos (l * gd (y / l) / l)) y := by
  have h := ((gd_deriv (y / l)).comp y ((hasDerivAt_id y).div_const l)).const_mul l
  rw [show l * gd (y / l) / l = gd (y / l) by field_simp, cos_gd]
  convert h using 1
  simp only [id]; field_simp

/-- 原点を通る未来向き・右向きのヌル曲線(dt/dz = cos(t/ℓ)、主値の帯の中)は t = ℓ gd(z/ℓ) に限る。
  台帳 Z10 の t/ℓ* = gd(z/ℓ*)。これは Mercator 座標での 45° の航程線 y = z の像:座標の対応であって、
  球面(K = +1)と首の 2 次元部分(K = −1/ℓ²、AdS₂)の力学的な同値ではない -/
theorem null_curve_unique (l : ℝ) (hl : 0 < l) (T T' : ℝ → ℝ) (hT : ∀ z, HasDerivAt T (T' z) z)
    (hnull : ∀ z, T' z = cos (T z / l)) (hstrip : ∀ z, |T z| < π * l / 2) (h0 : T 0 = 0) :
    ∀ z, T z = l * gd (z / l) := by
  have hcos : ∀ z, 0 < cos (T z / l) := by
    intro z
    apply cos_pos_of_mem_Ioo
    constructor
    · rw [lt_div_iff hl]; have := neg_abs_le (T z); have := hstrip z; nlinarith
    · rw [div_lt_iff hl]; have := le_abs_self (T z); have := hstrip z; nlinarith
  have hd : ∀ z, HasDerivAt (fun z => zfront l (T z) - z) 0 z := by
    intro z
    have h := ((front_deriv l (T z) hl (hcos z)).comp z (hT z)).sub (hasDerivAt_id z)
    convert h using 1
    rw [hnull z]; field_simp [(hcos z).ne']
  have hconst : ∀ z, zfront l (T z) - z = zfront l (T 0) - 0 := fun z =>
    is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) z 0
  intro z
  have e := hconst z
  rw [h0, show zfront l 0 = 0 by simp [zfront]] at e
  have hz : zfront l (T z) = z := by linarith
  rw [← gd_front_inv l (T z) hl (hstrip z), hz]

/-- 長さ L の首の両端からの波面 z_L = −L/2 + z_ℓ(t)、z_R = L/2 − z_ℓ(t) が出会うのは t = ℓ gd(L/(2ℓ)) のときに限る
  (上界でなく等式。t* < πℓ/2 は fronts_meet_before) -/
theorem fronts_meet_iff (l L t : ℝ) (hl : 0 < l) (ht : |t| < π * l / 2) :
    -(L / 2) + zfront l t = L / 2 - zfront l t ↔ t = l * gd (L / (2 * l)) := by
  constructor
  · intro h
    have hz : zfront l t = L / 2 := by linarith
    rw [← gd_front_inv l t hl ht, hz]; congr 2; field_simp
  · intro h
    have : zfront l t = L / 2 := by
      rw [h, show L / (2 * l) = (L / 2) / l by field_simp]; exact front_gd_inv l (L / 2) hl.ne'
    linarith

/-- 帽子の加速度:tt 成分 a′² + a² = ℓ² と θθ 成分 2aa″ − a′² + a² + ℓ² = 0 から a″ = −a -/
theorem cap_accel (a a1 a2 l : ℝ) (ha : a ≠ 0) (h00 : a1 ^ 2 + a ^ 2 = l ^ 2)
    (h22 : 2 * a * a2 - a1 ^ 2 + a ^ 2 + l ^ 2 = 0) : a2 = -a := by
  have : 2 * a * (a2 + a) = 0 := by linear_combination h22 + h00
  have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero ha)
  linarith

/-- 時間対称な初期値 a(0) = ℓ、a′(0) = 0 で a″ = −a の解は a = ℓ cos η だけ -/
theorem cap_unique (l : ℝ) (A A' : ℝ → ℝ) (h1 : ∀ η, HasDerivAt A (A' η) η)
    (h2 : ∀ η, HasDerivAt A' (-A η) η) (h0 : A 0 = l) (h0' : A' 0 = 0) : ∀ η, A η = l * cos η := by
  let E : ℝ → ℝ := fun η => (A η - l * cos η) ^ 2 + (A' η + l * sin η) ^ 2
  have hE : ∀ η, HasDerivAt E 0 η := by
    intro η
    have h := (((h1 η).sub ((hasDerivAt_cos η).const_mul l)).pow 2).add
      (((h2 η).add ((hasDerivAt_sin η).const_mul l)).pow 2)
    convert h using 1
    push_cast; ring
  have hc : ∀ η, E η = E 0 := fun η =>
    is_const_of_deriv_eq_zero (fun z => (hE z).differentiableAt) (fun z => (hE z).deriv) η 0
  intro η
  have e := hc η
  simp only [E, h0, h0', cos_zero, sin_zero, mul_one, mul_zero, sub_self, add_zero] at e
  have h3 : (A η - l * cos η) ^ 2 = 0 := by
    have := sq_nonneg (A' η + l * sin η); nlinarith [sq_nonneg (A η - l * cos η)]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  linarith

/-- 中心の固有時 t(η) = ∫₀^η a = ℓ sin η(dt = a dη)、崩壊 η = π/2 で t = ℓ -/
theorem cap_proper_time (l η : ℝ) :
    HasDerivAt (fun η => l * sin η) (l * cos η) η ∧ l * sin (π / 2) = l :=
  ⟨by simpa using (hasDerivAt_sin η).const_mul l, by simp⟩

/-- 帽子の YM のエネルギー密度(rho_tube の Rho、W = cos χ、W_χ/A = −sin χ/a)は ρ̂ = 3/(2a⁴) -/
theorem cap_density (a X Y : ℝ) (ha : a ≠ 0) (hX : X ≠ 0) (hXY : X ^ 2 + Y ^ 2 = 1) :
    CFT.S4J.Rho (a * X) Y 0 (-X / a) = 3 / (2 * a ^ 4) := by
  simp only [CFT.S4J.Rho]
  have hY : 1 - Y ^ 2 = X ^ 2 := by linarith
  rw [hY]; field_simp; ring

/-- 崩壊:a = ℓ cos η → 0(η → π/2⁻)で ρ̂ = 3/(2a⁴) → ∞(中心の測地線に沿って曲率の不変量が発散) -/
theorem cap_crunch (l : ℝ) (hl : 0 < l) :
    Tendsto (fun η => 3 / (2 * (l * cos η) ^ 4)) (𝓝[<] (π / 2)) atTop := by
  have h1 : Tendsto (fun η => l * cos η) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    have hc := tendsto_cos_pi_div_two
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (tendsto_nhdsWithin_iff.mp hc).1
      simpa using this.const_mul l
    · filter_upwards [(tendsto_nhdsWithin_iff.mp hc).2] with η hη
      exact mul_pos hl hη
  have h2 : Tendsto (fun η => 2 * (l * cos η) ^ 4) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((tendsto_nhdsWithin_iff.mp h1).1.pow 4).const_mul 2
      simpa using this
    · filter_upwards [(tendsto_nhdsWithin_iff.mp h1).2] with η hη
      have : 0 < (l * cos η) ^ 4 := pow_pos hη 4
      linarith
  have h3 := (tendsto_inv_nhdsGT_zero.comp h2).const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  refine h3.congr' ?_
  filter_upwards with η
  simp [div_eq_mul_inv]

/-- t_sing = ℓ < πℓ/2(Z9 の目標) -/
theorem t_sing_lt (l : ℝ) (hl : 0 < l) : l < π * l / 2 := by
  have := pi_gt_three; nlinarith

/-- 接合から帽子へ向かう波面は共形座標で χ = π/2 − η(dχ = −dη)。η < π/2 なら中心 χ = 0 はまだ波面の外
  (厳密な FRW の領域)にある。波面が中心に着く η = π/2 は崩壊の瞬間に一致する -/
theorem center_before_front (η : ℝ) (h : η < π / 2) : (0 : ℝ) < π / 2 - η := by linarith

/-- 平坦極限:到着時計 ℓ gd(z/ℓ) → z(ℓ → ∞) -/
theorem flat_clock (z : ℝ) : Tendsto (fun l : ℝ => l * gd (z / l)) atTop (𝓝 z) := by
  by_cases hz : z = 0
  · subst hz; simp [gd_zero]
  have hslope := gd_deriv_zero.tendsto_slope_zero
  simp only [zero_add, gd_zero, sub_zero, smul_eq_mul] at hslope
  have hu : Tendsto (fun l : ℝ => z / l) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.div_atTop tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with l hl
      exact div_ne_zero hz hl.ne'
  have := (hslope.comp hu).const_mul z
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  simp only [Function.comp]
  field_simp

/-- arsinh ∘ tan の 0 での微分は 1 -/
theorem front_deriv_zero : HasDerivAt (fun x => arsinh (tan x)) 1 0 := by
  have ht := hasDerivAt_tan (by simp : cos (0 : ℝ) ≠ 0)
  have h := (hasDerivAt_arsinh (tan 0)).comp (0 : ℝ) ht
  simpa using h

/-- 平坦極限:波面 ℓ arsinh(tan(t/ℓ)) → t -/
theorem flat_front (t : ℝ) : Tendsto (fun l : ℝ => zfront l t) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · subst ht; simp [zfront]
  have hslope := front_deriv_zero.tendsto_slope_zero
  simp only [zero_add, tan_zero, arsinh_zero, sub_zero, smul_eq_mul] at hslope
  have hu : Tendsto (fun l : ℝ => t / l) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.div_atTop tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with l hl
      exact div_ne_zero ht hl.ne'
  have := (hslope.comp hu).const_mul t
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  simp only [Function.comp, zfront]
  field_simp

/-- 平坦極限:計量の係数 cos²(t/ℓ) → 1、時計の速さ sech(z/ℓ) → 1 -/
theorem flat_metric (t z : ℝ) :
    Tendsto (fun l : ℝ => cos (t / l) ^ 2) atTop (𝓝 1) ∧
    Tendsto (fun l : ℝ => 1 / cosh (z / l)) atTop (𝓝 1) := by
  have h : ∀ x : ℝ, Tendsto (fun l : ℝ => x / l) atTop (𝓝 0) := fun x =>
    tendsto_const_nhds.div_atTop tendsto_id
  constructor
  · simpa using ((continuous_cos.tendsto 0).comp (h t)).pow 2
  · have := (continuous_cosh.tendsto 0).comp (h z)
    simpa using this.inv₀ (by simp)

/-- Z9 の正しい形:正の解が [τ₁, T) で類の条件を満たすなら T − τ₁ ≤ πr₁/2(最大の存在区間の長さ) -/
theorem z9_maximal (r rp W : ℝ → ℝ) (l κ τ1 T r1 : ℝ) (hT : τ1 < T)
    (hpos : ∀ τ ∈ Ico τ1 T, 0 < r τ)
    (h1 : ∀ τ ∈ Ico τ1 T, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Ico τ1 T, HasDerivAt rp (CFT.Z9.acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Ico τ1 T, κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) : T - τ1 ≤ π * r1 / 2 := by
  have hr1p : 0 < r1 := by rw [← hr1]; exact hpos τ1 ⟨le_refl _, hT⟩
  by_contra hlt
  push_neg at hlt
  set τ2 := τ1 + π * r1 / 2 with hτ2
  have hp : 0 < π * r1 / 2 := by have := pi_pos; positivity
  have hsub : ∀ τ ∈ Icc τ1 τ2, τ ∈ Ico τ1 T := fun τ hτ => ⟨hτ.1, by linarith [hτ.2]⟩
  have := CFT.Z9.z9_collapse r rp W l κ τ1 τ2 r1 (by linarith) (fun τ hτ => hpos τ (hsub τ hτ))
    (fun τ hτ => h1 τ (hsub τ hτ)) (fun τ hτ => h2 τ (hsub τ hτ)) hk (fun τ hτ => hW τ (hsub τ hτ)) h0 hr1
  linarith

/-- 旧 z9_reaches_zero の仮定は κ > 0 では両立しない(r = 0 の点で κ ≤ W²r² = 0 が破れる)。
  したがってその結論は空虚で、正しい形は z9_collapse、z9_maximal -/
theorem z9_reaches_zero_vacuous (r rp W : ℝ → ℝ) (l κ τ1 r1 : ℝ) (hr1p : 0 < r1) (hκ : 0 < κ)
    (h1 : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), HasDerivAt rp (CFT.Z9.acc l (r τ) (rp τ) (W τ)) τ)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ τ ∈ Icc τ1 (τ1 + π * r1 / 2), κ ≤ W τ ^ 2 * r τ ^ 2)
    (h0 : rp τ1 = 0) (hr1 : r τ1 = r1) : False := by
  obtain ⟨T, hT, hrT⟩ := CFT.Z9.z9_reaches_zero r rp W l κ τ1 r1 hr1p h1 h2 hk hW h0 hr1
  have := hW T hT
  rw [hrT] at this
  simp at this
  linarith

end Analysis
