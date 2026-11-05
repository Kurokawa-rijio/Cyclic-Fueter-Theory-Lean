/-
  確かめが足りなかった項目を、ダンベルの量子と力学で作り直す(2026-11-05)

  * IX.29(運動学:首の JT(IX.12)。作用:Schwarzian)
      鞍点(Laplace 変換)の主要項だけで dS/dE = 1/T を確かめていた点を、厳密な状態密度
      ρ(E) ∝ sinh(2π√(2CE)) で確かめ直す。S(E) = log sinh x(x = 2π√(2CE))の微分は
        1/T = dS/dE = 2πC coth x / √(2CE) = 4π²C coth x / x(`micro_exact_deriv`、`micro_exact_inv_T`)。
      coth x = 1 + 2/(e^{2x} − 1)(`coth_eq`)なので、主要項 4π²C/x との差は指数関数的に小さい
      (`micro_exact_bound`)。主要項からは E = 2π²CT²。正準集団の ⟨E⟩ = 3T/2 + 2π²CT²(IX.14)との相対的な差は
      3/(4π²CT)(`canonical_vs_micro`):C = φ_r/(2G) が大きい(首が古典的な)ほど二つの集団は一致する。
      ρ(E) の Laplace 変換が Z(IX.14)になることは外部(Stanford–Witten)。
  * V.7′(運動学:帽子 a(τ)。作用:1 ループの YM の有効作用)
      反作用の二つの項(⁽³⁾H の項 β_g(−3X²) と走る結合の項 ρ_β)を合わせた全体が保存する(`total_conserved`):
        ρ̇_tot = −3(ȧ/a)(ρ_tot + p_tot)、p_β = ρ_β/3 + 2c/a⁴。
      帽子 a = ℓ cos η では X = (ȧ² + 1)/a² = ℓ²/a⁴(`cap_X`)、ρ_H = −3β_gℓ⁴/a⁸、
      古典の輻射 ρ_cl = 3/(2g²a⁴) との比は −2g²β_gℓ⁴/a⁴(`cap_backreaction_ratio`):
      量子の反作用は帽子の始まり(a = ℓ)では g²β_g の大きさで小さく、崩壊(a → 0)に近づくと大きくなる。
  * XI.2(運動学:首 = 極限の地平線 AdS₂ × S²。作用:L = −F²/4 + α(F²)²)
      極限の条件を「M(r) の極値」(アトラクターの形)で書く。f = 1 − 2M/r + p²/r² − k/r⁶ について
        f(r) = 0 ∧ f′(r) = 0 ⇔ M = M(r) ∧ M′(r) = 0(`extremal_iff_critical`)、
        M′(r) = 0 ⇔ p² = r² + 5k/r⁴(`critical_radius`)。
      極限の首では M = r + 2k/r⁵(`extremal_mass`)、4k < r⁶(摂動の範囲)なら M < p(`extremal_lighter`)。
      k > 0 のとき首の半径は r < p(`neck_shrinks`)。Wald のエントロピーの補正は外部。
-/
import CFT.AlphaIX_JT
import CFT.AlphaV_FRW
import CFT.AlphaV_NeckQuantum
import CFT.AlphaIX_Thermo

namespace CFT.FixDyn

open Real

/-! ### IX.29 厳密な状態密度 -/

/-- 【α-IX.29】S(E) = log sinh(2π√(2CE)) の微分 = 2πC cosh x/(sinh x · √(2CE)) -/
theorem micro_exact_deriv (C E : ℝ) (hC : 0 < C) (hE : 0 < E) :
    HasDerivAt (fun e => Real.log (sinh (2 * π * Real.sqrt (2 * C * e))))
      (2 * π * C * cosh (2 * π * Real.sqrt (2 * C * E))
        / (sinh (2 * π * Real.sqrt (2 * C * E)) * Real.sqrt (2 * C * E))) E := by
  have hpos : 0 < 2 * C * E := by positivity
  have hs : 0 < Real.sqrt (2 * C * E) := Real.sqrt_pos.2 hpos
  have hx : 0 < 2 * π * Real.sqrt (2 * C * E) := by have := pi_pos; positivity
  have hsh : 0 < sinh (2 * π * Real.sqrt (2 * C * E)) := Real.sinh_pos_iff.2 hx
  have h1 : HasDerivAt (fun e => 2 * C * e) (2 * C) E := by
    convert (hasDerivAt_id' E).const_mul (2 * C) using 1; ring
  have h2 := (h1.sqrt hpos.ne').const_mul (2 * π)
  have h3 := (Real.hasDerivAt_sinh _).comp E h2
  have h4 := h3.log hsh.ne'
  convert h4 using 1
  try simp only [Function.comp_apply]
  field_simp <;> ring

/-- coth x = 1 + 2/(e^{2x} − 1)(x > 0) -/
theorem coth_eq (x : ℝ) (hx : 0 < x) : cosh x / sinh x = 1 + 2 / (rexp (2 * x) - 1) := by
  have hsh : sinh x ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
  have he : rexp (2 * x) - 1 ≠ 0 := by
    have : 1 < rexp (2 * x) := Real.one_lt_exp_iff.2 (by linarith)
    linarith
  rw [div_eq_iff hsh, Real.cosh_eq, Real.sinh_eq,
    show rexp (2 * x) = rexp x * rexp x by rw [← Real.exp_add]; ring_nf, Real.exp_neg]
  have hex : rexp x ≠ 0 := (exp_pos x).ne'
  rw [show rexp (2 * x) = rexp x * rexp x by rw [← Real.exp_add]; ring_nf] at he
  field_simp
  ring

/-- 【α-IX.29】1/T = 4π²C coth x / x(x = 2π√(2CE)) -/
theorem micro_exact_inv_T (C x : ℝ) (hx : 0 < x) (hs : 0 < x / (2 * π)) :
    2 * π * C * cosh x / (sinh x * (x / (2 * π))) = 4 * π ^ 2 * C * (cosh x / sinh x) / x := by
  have hsh : sinh x ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
  have hπ := pi_pos.ne'
  field_simp <;> ring

/-- 【α-IX.29】主要項 4π²C/x との差は指数関数的に小さい:
4π²C/x ≤ 4π²C coth x / x ≤ (4π²C/x)(1 + 2/(e^{2x} − 1)) -/
theorem micro_exact_bound (C x : ℝ) (hC : 0 < C) (hx : 0 < x) :
    4 * π ^ 2 * C / x ≤ 4 * π ^ 2 * C * (cosh x / sinh x) / x ∧
    4 * π ^ 2 * C * (cosh x / sinh x) / x = 4 * π ^ 2 * C / x * (1 + 2 / (rexp (2 * x) - 1)) := by
  have he : 0 < rexp (2 * x) - 1 := by
    have : 1 < rexp (2 * x) := Real.one_lt_exp_iff.2 (by linarith)
    linarith
  rw [coth_eq x hx]
  have hA : 0 < 4 * π ^ 2 * C / x := by have := pi_pos; positivity
  have ht : (0 : ℝ) ≤ 2 / (rexp (2 * x) - 1) := by positivity
  have e : 4 * π ^ 2 * C * (1 + 2 / (rexp (2 * x) - 1)) / x
      = 4 * π ^ 2 * C / x * (1 + 2 / (rexp (2 * x) - 1)) := by ring
  refine ⟨?_, e⟩
  rw [e]
  nlinarith [mul_nonneg hA.le ht]

/-- 【α-IX.29】正準集団の ⟨E⟩ = 3T/2 + 2π²CT² と微視的な主要項 E = 2π²CT² の相対的な差は 3/(4π²CT) -/
theorem canonical_vs_micro (C T : ℝ) (hC : 0 < C) (hT : 0 < T) :
    (3 * T / 2 + 2 * π ^ 2 * C * T ^ 2 - 2 * π ^ 2 * C * T ^ 2) / (2 * π ^ 2 * C * T ^ 2)
      = 3 / (4 * π ^ 2 * C * T) := by
  have hπ := pi_pos.ne'
  have hC' := hC.ne'
  have hT' := hT.ne'
  field_simp <;> ring

/-- 【α-IX.29】IX.14 の ⟨E⟩ = 3/(2β) + 2π²C/β² は T = 1/β で 3T/2 + 2π²CT² -/
theorem canonical_energy_T (C T : ℝ) (hT : 0 < T) :
    3 / (2 * (1 / T)) + 2 * π ^ 2 * C / (1 / T) ^ 2 = 3 * T / 2 + 2 * π ^ 2 * C * T ^ 2 := by
  have hT' := hT.ne'
  field_simp <;> ring

/-! ### V.7′ 反作用の全体の保存 -/

/-- 【α-V.7′】⁽³⁾H の項(係数 β_g)と走る結合の項 ρ_β の和は保存する:
ρ̇_tot = −3(ȧ/a)(ρ_tot + p_tot)、p_H = β_g(4uX − X²)、p_β = ρ_β/3 + 2c/a⁴ -/
theorem total_conserved (βg κ c : ℝ) (a ad : ℝ → ℝ) (add t : ℝ) (ha : HasDerivAt a (ad t) t)
    (had : HasDerivAt ad add t) (hpos : 0 < a t) :
    HasDerivAt (fun τ => βg * (-3 * (CFT.FRW.Xf a ad τ * CFT.FRW.Xf a ad τ)) + CFT.NeckQuantum.rhoB κ c a τ)
      (-3 * (ad t / a t) *
        ((βg * (-3 * (CFT.FRW.Xf a ad t * CFT.FRW.Xf a ad t)) + CFT.NeckQuantum.rhoB κ c a t)
          + (βg * (4 * (add / a t) * CFT.FRW.Xf a ad t - CFT.FRW.Xf a ad t * CFT.FRW.Xf a ad t)
            + (CFT.NeckQuantum.rhoB κ c a t / 3 + 2 * c / a t ^ 4)))) t := by
  have h1 := (CFT.FRW.h3_conserved a ad add t ha had hpos.ne').const_mul βg
  have h2 := CFT.NeckQuantum.rho_beta_conserved κ c a (ad t) t ha hpos
  convert h1.add h2 using 1
  ring

/-- 【α-V.7′】帽子 a = ℓ cos η(共形時間)で、宇宙時間の ȧ = a′/a を入れると X = (ȧ² + 1)/a² = ℓ²/a⁴ -/
theorem cap_X (l η : ℝ) (hl : l ≠ 0) (hc : cos η ≠ 0) :
    (((l * -sin η) / (l * cos η)) ^ 2 + 1) / (l * cos η) ^ 2 = l ^ 2 / (l * cos η) ^ 4 := by
  have hlc : l * cos η ≠ 0 := mul_ne_zero hl hc
  have e : (l * -sin η) ^ 2 + (l * cos η) ^ 2 = l ^ 2 := by
    linear_combination l ^ 2 * sin_sq_add_cos_sq η
  have e2 : ((l * -sin η) / (l * cos η)) ^ 2 + 1 = l ^ 2 / (l * cos η) ^ 2 := by
    rw [← e]; field_simp
  rw [e2]
  ring

/-- 【α-V.7′】帽子の ρ_H = −3β_gX² = −3β_gℓ⁴/a⁸ と古典の輻射 ρ_cl = 3/(2g²a⁴) の比は −2g²β_gℓ⁴/a⁴ -/
theorem cap_backreaction_ratio (βg g l a : ℝ) (hg : g ≠ 0) (ha : a ≠ 0) :
    (βg * (-3 * ((l ^ 2 / a ^ 4) * (l ^ 2 / a ^ 4)))) / (3 / (2 * g ^ 2 * a ^ 4))
      = -(2 * g ^ 2 * βg * l ^ 4 / a ^ 4) := by
  field_simp <;> ring

/-- 【α-V.7′】比の大きさ 2g²|β_g|ℓ⁴/a⁴ は a が小さくなるほど大きい(a₂ < a₁ ⇒ 比が大きい) -/
theorem backreaction_grows (gb l a1 a2 : ℝ) (hgb : 0 < gb) (hl : l ≠ 0) (h2 : 0 < a2) (h12 : a2 < a1) :
    2 * gb * l ^ 4 / a1 ^ 4 < 2 * gb * l ^ 4 / a2 ^ 4 := by
  have hl4 : 0 < l ^ 4 := by positivity
  have hp : a2 ^ 4 < a1 ^ 4 := pow_lt_pow_left h12 h2.le (by norm_num)
  have h1 := one_div_lt_one_div_of_lt (pow_pos h2 4) hp
  have hc : 0 < 2 * gb * l ^ 4 := by positivity
  calc 2 * gb * l ^ 4 / a1 ^ 4 = 2 * gb * l ^ 4 * (1 / a1 ^ 4) := by ring
    _ < 2 * gb * l ^ 4 * (1 / a2 ^ 4) := mul_lt_mul_of_pos_left h1 hc
    _ = 2 * gb * l ^ 4 / a2 ^ 4 := by ring

/-! ### XI.2 アトラクターの形の極限の条件 -/

/-- 地平線の質量 M(r) = (r/2)(1 + p²/r² − k/r⁶) の微分 M′(r) = 1/2 − p²/(2r²) + 5k/(2r⁶) -/
theorem mass_deriv (p k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x => x / 2 * (1 + p ^ 2 / x ^ 2 - k / x ^ 6))
      (1 / 2 - p ^ 2 / (2 * r ^ 2) + 5 * k / (2 * r ^ 6)) r := by
  have e : (fun x : ℝ => x / 2 * (1 + p ^ 2 / x ^ 2 - k / x ^ 6))
      =ᶠ[nhds r] fun x => x / 2 + p ^ 2 / 2 * x⁻¹ - k / 2 * (x ^ 5)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    field_simp <;> ring
  have h1 := (hasDerivAt_id' r).div_const 2
  have h2 := (hasDerivAt_inv hr).const_mul (p ^ 2 / 2)
  have h3 := ((hasDerivAt_pow 5 r).inv (pow_ne_zero 5 hr)).const_mul (k / 2)
  refine HasDerivAt.congr_of_eventuallyEq ?_ e
  convert (h1.add h2).sub h3 using 1
  simp only [Nat.cast_ofNat, show (5 : ℕ) - 1 = 4 from rfl]
  field_simp <;> ring

/-- 【α-XI.2】極限 ⇔ M の臨界点:f(r) = 0 ∧ f′(r) = 0 ⇔ M = M(r) ∧ M′(r) = 0
(f = 1 − 2M/r + p²/r² − k/r⁶、f′ = 2M/r² − 2p²/r³ + 6k/r⁷) -/
theorem extremal_iff_critical (M p k r : ℝ) (hr : r ≠ 0) :
    (1 - 2 * M / r + p ^ 2 / r ^ 2 - k / r ^ 6 = 0 ∧ 2 * M / r ^ 2 - 2 * p ^ 2 / r ^ 3 + 6 * k / r ^ 7 = 0) ↔
    (M = r / 2 * (1 + p ^ 2 / r ^ 2 - k / r ^ 6) ∧ 1 / 2 - p ^ 2 / (2 * r ^ 2) + 5 * k / (2 * r ^ 6) = 0) := by
  rw [CFT.Thermo.horizon_iff M p k r hr]
  constructor
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    rw [hM] at hd
    have e : 2 * (r / 2 * (1 + p ^ 2 / r ^ 2 - k / r ^ 6)) / r ^ 2 - 2 * p ^ 2 / r ^ 3 + 6 * k / r ^ 7
        = 2 / r * (1 / 2 - p ^ 2 / (2 * r ^ 2) + 5 * k / (2 * r ^ 6)) := by
      field_simp <;> ring
    rw [e] at hd
    rcases mul_eq_zero.1 hd with h | h
    · exact absurd h (div_ne_zero two_ne_zero hr)
    · exact h
  · rintro ⟨hM, hd⟩
    refine ⟨hM, ?_⟩
    rw [hM]
    have e : 2 * (r / 2 * (1 + p ^ 2 / r ^ 2 - k / r ^ 6)) / r ^ 2 - 2 * p ^ 2 / r ^ 3 + 6 * k / r ^ 7
        = 2 / r * (1 / 2 - p ^ 2 / (2 * r ^ 2) + 5 * k / (2 * r ^ 6)) := by
      field_simp <;> ring
    rw [e, hd, mul_zero]

/-- 【α-XI.2】M′(r) = 0 ⇔ p² = r² + 5k/r⁴(首の半径の補正) -/
theorem critical_radius (p k r : ℝ) (hr : r ≠ 0) :
    1 / 2 - p ^ 2 / (2 * r ^ 2) + 5 * k / (2 * r ^ 6) = 0 ↔ p ^ 2 = r ^ 2 + 5 * k / r ^ 4 := by
  have e : 1 / 2 - p ^ 2 / (2 * r ^ 2) + 5 * k / (2 * r ^ 6) = (r ^ 2 + 5 * k / r ^ 4 - p ^ 2) / (2 * r ^ 2) := by
    field_simp <;> ring
  rw [e, div_eq_zero_iff]
  have : 2 * r ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hr)
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h this
  · intro h; left; linarith

/-- 【α-XI.2】極限の首では M = r + 2k/r⁵ -/
theorem extremal_mass (p k r : ℝ) (hr : r ≠ 0) (hp : p ^ 2 = r ^ 2 + 5 * k / r ^ 4) :
    r / 2 * (1 + p ^ 2 / r ^ 2 - k / r ^ 6) = r + 2 * k / r ^ 5 := by
  rw [hp]; field_simp <;> ring

/-- 【α-XI.2】k > 0、4k < r⁶(摂動の範囲)なら極限の M は磁荷 p より軽い(穏やかな WGC) -/
theorem extremal_lighter (p k r : ℝ) (hr : 0 < r) (hp0 : 0 < p) (hk : 0 < k) (hsmall : 4 * k < r ^ 6)
    (hp : p ^ 2 = r ^ 2 + 5 * k / r ^ 4) : r + 2 * k / r ^ 5 < p := by
  have hr5 : 0 < r ^ 5 := by positivity
  have hM : 0 < r + 2 * k / r ^ 5 := by positivity
  have key : (r + 2 * k / r ^ 5) ^ 2 < p ^ 2 := by
    rw [hp]
    have e : r ^ 2 + 5 * k / r ^ 4 - (r + 2 * k / r ^ 5) ^ 2 = k * (r ^ 6 - 4 * k) / r ^ 10 := by
      field_simp <;> ring
    have : 0 < k * (r ^ 6 - 4 * k) / r ^ 10 := by
      apply div_pos (mul_pos hk (by linarith)) (by positivity)
    linarith
  nlinarith [key, hM, hp0]

/-- 【α-XI.2】k > 0 なら首の半径は r < p(補正で首が細くなる) -/
theorem neck_shrinks (p k r : ℝ) (hr : 0 < r) (hp0 : 0 < p) (hk : 0 < k)
    (hp : p ^ 2 = r ^ 2 + 5 * k / r ^ 4) : r < p := by
  have : 0 < 5 * k / r ^ 4 := by positivity
  nlinarith [hp, this]

end CFT.FixDyn
