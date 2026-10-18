/-
  α-IV 時間発展:波面・崩壊・時計(Z8, Z9, Z10, Z10′, Z13)

  形式化した内容
  * α-IV.2 (Z8)   二重 null 方程式の W_uv = e^{2σ}W(1−W²)/(2r²) は W_u を含まない。
                   よって (r, σ, W) が波面で連続なら [W_u] は波面に沿って一定。
                   拘束式 r_uu − 2σ_u r_u + 2W_u²/r = 0 から [r_uu] = −(2/r)[W_u²]
  * α-IV.4 (Z9-b旧) 中心の式 r″ = −(r′² + 1 − ℓ²/r²)/(2r) − W²/r のもとで
                   E = r(1 + r′²) + ℓ²/r は dE/dτ = −2W²r′(W = 0 なら首の第一積分)
  * α-IV.7 (Z10)  gd x = arctan(sinh x):tan(gd x) = sinh x、gd′ = sech。
                   波面 z(t) = ℓ arsinh(tan(t/ℓ)) は dz/dt = 1/cos(t/ℓ)(首の null 線)
  * α-IV.8 (Z10′) 首の両端からの波面は t* = ℓ gd(L/2ℓ) < πℓ/2 で出会う。キャップの寿命は ℓ
  * α-IV.9 (Z0-f) gd′(0) = 1(ℓ → ∞ で τ = ℓ gd(z/ℓ) → z)
  * α-IV.12 (Z13) WKB の厳密性:Ψ = e^{iaσ(b)}/σ(b)、σ² = Cb − 4c²(b² + ℓ²) は
                   首の Wheeler–DeWitt 方程式を厳密に満たす(導関数の連鎖律は仮定として与える)

  外部定理
  * α-IV.1 (Z1)   一意な弱解の存在:Rauch–Reed 1981/1985(Lean では扱わない)
-/
import CFT.Basic

open Real

namespace CFT.AlphaIV

/-! ### α-IV.2 跳びの輸送 -/

/-- W_uv の右辺(W_u を含まない) -/
noncomputable def FW (r σ W : ℝ) : ℝ := exp (2 * σ) * W * (1 - W ^ 2) / (2 * r ^ 2)

/-- 波面 u = u₀ の両側で W_u^± の v 微分がともに FW(r, σ, W)(r, σ, W は連続で両側共通)
    なら、跳び [W_u] = W_u⁺ − W_u⁻ は v によらない -/
theorem jump_const (Wp Wm r σ W : ℝ → ℝ)
    (hp : ∀ v, HasDerivAt Wp (FW (r v) (σ v) (W v)) v)
    (hm : ∀ v, HasDerivAt Wm (FW (r v) (σ v) (W v)) v) :
    ∀ v w, Wp v - Wm v = Wp w - Wm w := by
  have hd : ∀ v, HasDerivAt (fun v => Wp v - Wm v) 0 v := by
    intro v
    have := (hp v).sub (hm v)
    simpa using this
  have hdiff : Differentiable ℝ (fun v => Wp v - Wm v) := fun v => (hd v).differentiableAt
  intro v w
  exact is_const_of_deriv_eq_zero hdiff (fun v => (hd v).deriv) v w

/-- 拘束式 r_uu = 2σ_u r_u − 2W_u²/r が両側で成り立ち、r, σ_u, r_u が連続なら
    [r_uu] = −(2/r)[W_u²] -/
theorem ruu_jump (r su ru Wup Wum ruup ruum : ℝ)
    (hp : ruup = 2 * su * ru - 2 * Wup ^ 2 / r) (hm : ruum = 2 * su * ru - 2 * Wum ^ 2 / r) :
    ruup - ruum = -(2 / r) * (Wup ^ 2 - Wum ^ 2) := by
  rw [hp, hm]
  ring

/-! ### α-IV.4 中心の質量の単調性 -/

/-- 中心の式のもとで E = r(1 + r′²) + ℓ²/r の微分は −2W²r′ -/
theorem energy_deriv (r rp W : ℝ → ℝ) (l τ : ℝ) (hr : r τ ≠ 0)
    (h1 : HasDerivAt r (rp τ) τ)
    (h2 : HasDerivAt rp (-(rp τ ^ 2 + 1 - l ^ 2 / r τ ^ 2) / (2 * r τ) - W τ ^ 2 / r τ) τ) :
    HasDerivAt (fun τ => r τ * (1 + rp τ ^ 2) + l ^ 2 / r τ) (-2 * W τ ^ 2 * rp τ) τ := by
  have hA := h1.mul ((h2.pow 2).const_add 1)
  have hB := (h1.inv hr).const_mul (l ^ 2)
  have h := hA.add hB
  convert h using 1
  norm_num
  field_simp
  ring

/-- 系:崩壊中(r′ ≤ 0)は E が減らない -/
theorem energy_nondecreasing (W rp : ℝ) (h : rp ≤ 0) : 0 ≤ -2 * W ^ 2 * rp := by
  have : 0 ≤ W ^ 2 := sq_nonneg W
  nlinarith

/-! ### α-IV.7 Gudermann 関数 -/

/-- gd x = arctan(sinh x) -/
noncomputable def gd (x : ℝ) : ℝ := arctan (sinh x)

theorem tan_gd (x : ℝ) : tan (gd x) = sinh x := tan_arctan _

/-- gd′ = 1/cosh -/
theorem gd_deriv (x : ℝ) : HasDerivAt gd (1 / cosh x) x := by
  have h := (hasDerivAt_arctan (sinh x)).comp x (hasDerivAt_sinh x)
  have hc : cosh x ≠ 0 := (cosh_pos x).ne'
  convert h using 1
  rw [← cosh_sq']
  field_simp
  ring

/-- cos u > 0 なら √(1 + tan²u) = 1/cos u -/
theorem sqrt_one_add_tan_sq (u : ℝ) (hc : 0 < cos u) : √(1 + tan u ^ 2) = 1 / cos u := by
  have h : 1 + tan u ^ 2 = (1 / cos u) ^ 2 := by
    rw [tan_eq_sin_div_cos]
    field_simp
  rw [h, Real.sqrt_sq (by positivity)]

/-- 首の null 線:z(t) = ℓ arsinh(tan(t/ℓ)) は dz/dt = 1/cos(t/ℓ) を満たす -/
theorem front_deriv (l t : ℝ) (hl : 0 < l) (hc : 0 < cos (t / l)) :
    HasDerivAt (fun t => l * arsinh (tan (t / l))) (1 / cos (t / l)) t := by
  have hc0 : cos (t / l) ≠ 0 := hc.ne'
  have ht := (hasDerivAt_tan hc0).comp t ((hasDerivAt_id t).div_const l)
  have h := ((hasDerivAt_arsinh (tan (t / l))).comp t ht).const_mul l
  convert h using 1
  rw [sqrt_one_add_tan_sq _ hc]
  field_simp
  ring

/-! ### α-IV.8 時計 -/

/-- 長さ L の首の両端から出た波面は t* = ℓ gd(L/2ℓ) で出会い、t* < πℓ/2 -/
theorem fronts_meet_before (l L : ℝ) (hl : 0 < l) : l * gd (L / (2 * l)) < π / 2 * l := by
  have := arctan_lt_pi_div_two (sinh (L / (2 * l)))
  rw [gd]
  nlinarith

/-- 波面の到着時刻 τ = ℓ gd(z/ℓ) は常に πℓ/2 未満 -/
theorem arrival_bound (l z : ℝ) (hl : 0 < l) : l * gd (z / l) < π / 2 * l := by
  have := arctan_lt_pi_div_two (sinh (z / l))
  rw [gd]
  nlinarith

/-- キャップ(a = ℓ cos η、t = ℓ sin η)は η = π/2 で潰れ、そのときの固有時は ℓ -/
theorem cap_lifetime (l : ℝ) : l * cos (π / 2) = 0 ∧ l * sin (π / 2) = l := by
  simp

/-! ### α-IV.9 平坦極限 -/

theorem gd_deriv_zero : HasDerivAt gd 1 0 := by
  have := gd_deriv 0
  simpa using this

theorem gd_zero : gd 0 = 0 := by simp [gd]

/-! ### α-IV.12 WKB の厳密性(首の Wheeler–DeWitt 方程式) -/

/-- Ψ = e^{iaσ}/σ の導関数は連鎖律から
    Ψ_a = iσΨ、Ψ_aa = −σ²Ψ、Ψ_b = (iaσ′ − σ′/σ)Ψ、Ψ_ab = iσ′Ψ + iσΨ_b。
    σ² = Cb − 4c²(b² + ℓ²)、σσ′ = (C − 8c²b)/2 のとき
    −(1/4c)(aΨ_aa − 2bΨ_ab) − c a (b² − ℓ²) Ψ = 0 -/
theorem wdw_exact (a b c l C : ℝ) (σ σ' Ψ : ℂ) (hc : c ≠ 0) (hσ : σ ≠ 0)
    (hs2 : σ ^ 2 = C * b - 4 * c ^ 2 * (b ^ 2 + l ^ 2))
    (hss : σ * σ' = (C - 8 * c ^ 2 * b) / 2) :
    let Ψa := Complex.I * σ * Ψ
    let Ψaa := -(σ ^ 2) * Ψ
    let Ψb := (Complex.I * a * σ' - σ' / σ) * Ψ
    let Ψab := Complex.I * σ' * Ψ + Complex.I * σ * Ψb;
    -(1 / (4 * c)) * (a * Ψaa - 2 * b * Ψab) - c * a * (b ^ 2 - l ^ 2) * Ψ = 0 := by
  intro Ψa Ψaa Ψb Ψab
  simp only [Ψaa, Ψab, Ψb]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcinv : (c : ℂ) * (c : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc'
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (4 * (c : ℂ))⁻¹ * a * Ψ * hs2 - (4 * (c : ℂ))⁻¹ * 2 * b * a * Ψ * hss
    + (4 * (c : ℂ))⁻¹ * 2 * a * b * σ * σ' * Ψ * hI
    - (4 * (c : ℂ))⁻¹ * 2 * b * Complex.I * σ' * Ψ * hinv
    + (c : ℂ) * a * Ψ * (b ^ 2 - l ^ 2) * hcinv

end CFT.AlphaIV
