/-
  段階 17(2026-11-11):残りの命題と、Ω の量子幾何学(α-XV)

  ■ α-XIV.8(帽子と首の倍率の足し算、完全な否定):Ω = A cos η + B/sin u(ℓ = 1)。
    * `oq_M_superpos`:kl 成分 M = 2A² + 4AB cos η/sin³u + 2B²/sin⁴u。
    * `oq_D`:よって (1 − W²)² = D := A²S⁴ + 2ABcS + B²(S = sin u、c = cos η)。
    * `oq_product`:D を η、u で微分した式と、N₊ − N₋ から出る W_η W_u = AB sin η cos u/sin u を合わせると
      AB sin η cos u·(4W²D + S²(2A²S³ + ABc)) = 0。
    * `oq_cubic_no_four`、`oq_no_superposition`:W² = 1 − σ√D(σ = ±1)を入れると r = √D の 3 次式
      4σr³ − (4 + S/2)r² + κ = 0 になる。S を止めて c を動かすと r は区間を動くが、3 次式の根は 3 個まで。
      したがって AB ≠ 0 の足し算は、どの時間帯でも(開集合の上で)EYM の解にならない。
  ■ α-X.11(帽子の線形摂動、共形平坦な部分を閉じる):
    * `oq_osc_unique`:y″ = −κy(κ > 0)、y(0) = y′(0) = 0 なら y = 0(エネルギーの議論)。
    * `oq_osc_solution`:q″ = −q の解は q(0)cos η + q′(0)sin η だけ。
    * `oq_fc_over_sin`:f_χχ sin χ = cos χ f_χ なら f_χ/sin χ の χ 微分は 0。
  ■ α-X.11-W(新、YM の試験場のスペクトル):δW = sin²χ·u(cos χ) とおくと
    δW_χχ + (1 − 3cos²χ)δW/sin²χ = sin²χ[(1 − x²)u″ − 5xu′ − u](`oq_testfield`)。
    Gegenbauer C_n^{(2)} で固有値 −(n² + 4n + 1) < 0(`oq_spectrum`):磁気的な実の W の摂動はすべて振動する。
  ■ α-XV(新、Ω の量子幾何学):
    * `oq_action_quadratic`:共形の枠の Einstein–Hilbert の密度 √g R = 6Ω² − 6Ω□̂Ω(Ω の 2 次式:自由場)。
    * `oq_radius_wave`:面積半径 r = Ω sin χ について r_ηη − r_χχ = −sin χ(□̂Ω − Ω)。
      トレースの方程式 ⇔ r が平らな 2 次元の波動方程式をみたす。
    * `oq_periodic`、`oq_antipodal`:r = F(η + χ) − F(η − χ)(χ = 0 で r = 0)。もう一方の極 χ = π でも r = 0 なら
      F は周期 2π。このとき対蹠の写像 (η, χ) ↦ (η + π, π − χ) で r ↦ −r(Ω ↦ −Ω、計量 Ω²ĝ は同じ)。
    * `oq_cap_dalembert`:帽子は F = (ℓ/2) sin。
    * `oq_energy_coeff`、`oq_classical_scale`、`oq_quantized_scale`:一様なモードの Ω の(負の)エネルギーの大きさ
      (3π/4G)(Ω̇² + Ω²) と YM のエネルギー 3π²/g² の釣り合い ⇔ ℓ² = 4πG/g²。振動数 1 の調和振動子として
      (n + ½) とおくと ℓ²/G = 4(n + ½)/(3π)、g²/(4π) = 3π/(4n + 2)(XII.8 の候補の出どころ、ℏ = 1)。
    * `oq_sl2_bracket`:三つの共形 Killing ベクトルは sl(2,ℝ) をなす。`oq_neck_invariant`、`oq_neck_unique`:
      首はその三つすべてで不変なただ一つの配位。`oq_potential_shift`:帽子の上の YM のポテンシャルは真空 + 3。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open Real

namespace CFT.OQ

/-! ### α-XIV.8:足し算は解にならない -/

/-- Ω = A c + B w(c = cos η、s = sin η、w = 1/sin u、t = cot u、w² = 1 + t²)。
  Ω_ηη = −A c、Ω_uu = B w(2w² − 1)、Ω_η = −A s、Ω_u = −B w t を入れた kl 成分 -/
theorem oq_M_superpos (A B c s w t : ℝ) (hw : w ^ 2 = 1 + t ^ 2) (hcs : s ^ 2 + c ^ 2 = 1) :
    -2 * (A * c + B * w) * (-(A * c) - B * w * (2 * w ^ 2 - 1))
      + 2 * ((-(A * s)) ^ 2 - (-(B * w * t)) ^ 2)
      = 2 * A ^ 2 + 4 * A * B * c * w ^ 3 + 2 * B ^ 2 * w ^ 4 := by
  linear_combination (2 * A ^ 2) * hcs + (2 * B ^ 2 * w ^ 2) * hw

/-- (1 − W²)² = sin⁴u·M/2 = A²S⁴ + 2ABcS + B² -/
theorem oq_D (A B c S : ℝ) (hS : S ≠ 0) :
    S ^ 4 * (2 * A ^ 2 + 4 * A * B * c * (1 / S) ^ 3 + 2 * B ^ 2 * (1 / S) ^ 4) / 2
      = A ^ 2 * S ^ 4 + 2 * A * B * c * S + B ^ 2 := by
  field_simp
  ring

/-- D = (1 − W²)² を η と u で微分した式(h1、h2)と W_η W_u·S = AB s C(h3、N₊ − N₋ から)を合わせる -/
theorem oq_product (A B c s S C W We Wu D : ℝ)
    (h1 : -4 * (W * (1 - W ^ 2)) * We = -2 * A * B * s * S)
    (h2 : -4 * (W * (1 - W ^ 2)) * Wu = 4 * A ^ 2 * S ^ 3 * C + 2 * A * B * c * C)
    (h3 : We * Wu * S = A * B * s * C) (hD : (1 - W ^ 2) ^ 2 = D) :
    A * B * s * C * (4 * W ^ 2 * D + S ^ 2 * (2 * A ^ 2 * S ^ 3 + A * B * c)) = 0 := by
  have e1 : 16 * (W ^ 2 * D) * (We * Wu)
      = (-2 * A * B * s * S) * (4 * A ^ 2 * S ^ 3 * C + 2 * A * B * c * C) := by
    rw [← h1, ← h2, ← hD]; ring
  linear_combination (S / 4) * e1 - (4 * W ^ 2 * D) * h3

/-- 2 次の項と定数項だけをもつ 3 次式 k r³ + a r² + e(k ≠ 0)は、相異なる 4 点で 0 になれない -/
theorem oq_cubic_no_four (k a e r1 r2 r3 r4 : ℝ) (hk : k ≠ 0)
    (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h14 : r1 ≠ r4) (h23 : r2 ≠ r3) (h24 : r2 ≠ r4) (h34 : r3 ≠ r4)
    (p1 : k * r1 ^ 3 + a * r1 ^ 2 + e = 0) (p2 : k * r2 ^ 3 + a * r2 ^ 2 + e = 0)
    (p3 : k * r3 ^ 3 + a * r3 ^ 2 + e = 0) (p4 : k * r4 ^ 3 + a * r4 ^ 2 + e = 0) : False := by
  have q12 : k * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + a * (r1 + r2) = 0 := by
    have h : (r1 - r2) * (k * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + a * (r1 + r2)) = 0 := by
      linear_combination p1 - p2
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h12)
  have q13 : k * (r1 ^ 2 + r1 * r3 + r3 ^ 2) + a * (r1 + r3) = 0 := by
    have h : (r1 - r3) * (k * (r1 ^ 2 + r1 * r3 + r3 ^ 2) + a * (r1 + r3)) = 0 := by
      linear_combination p1 - p3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h13)
  have q14 : k * (r1 ^ 2 + r1 * r4 + r4 ^ 2) + a * (r1 + r4) = 0 := by
    have h : (r1 - r4) * (k * (r1 ^ 2 + r1 * r4 + r4 ^ 2) + a * (r1 + r4)) = 0 := by
      linear_combination p1 - p4
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h14)
  have s3 : k * (r1 + r2 + r3) + a = 0 := by
    have h : (r2 - r3) * (k * (r1 + r2 + r3) + a) = 0 := by linear_combination q12 - q13
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h23)
  have s4 : k * (r1 + r2 + r4) + a = 0 := by
    have h : (r2 - r4) * (k * (r1 + r2 + r4) + a) = 0 := by linear_combination q12 - q14
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h24)
  have h : k * (r3 - r4) = 0 := by linear_combination s3 - s4
  exact (mul_ne_zero hk (sub_ne_zero.mpr h34)) h

/-- α-XIV.8:S = sin u を止め、cos η の 4 つの値 cᵢ で r_i = √D_i が相異なるとする(AB ≠ 0 なら可能)。
  各点で −S²(2A²S³ + ABcᵢ) = 4W²D、W² = 1 − σrᵢ、rᵢ² = Dᵢ が成り立つことはない -/
theorem oq_no_superposition (A B S σ : ℝ) (c r : Fin 4 → ℝ) (hσ : σ ≠ 0)
    (hr : ∀ i j, i ≠ j → r i ≠ r j)
    (hD : ∀ i, r i ^ 2 = A ^ 2 * S ^ 4 + 2 * A * B * c i * S + B ^ 2)
    (hrel : ∀ i, -(S ^ 2 * (2 * A ^ 2 * S ^ 3 + A * B * c i)) = 4 * (1 - σ * r i) * r i ^ 2) : False := by
  have p : ∀ i, (4 * σ) * r i ^ 3 + (-(4 + S / 2)) * r i ^ 2
      + (-(3 / 2) * A ^ 2 * S ^ 5 + B ^ 2 * S / 2) = 0 := by
    intro i
    linear_combination hrel i - (S / 2) * hD i
  exact oq_cubic_no_four (4 * σ) (-(4 + S / 2)) (-(3 / 2) * A ^ 2 * S ^ 5 + B ^ 2 * S / 2)
    (r 0) (r 1) (r 2) (r 3) (mul_ne_zero (by norm_num) hσ)
    (hr 0 1 (by decide)) (hr 0 2 (by decide)) (hr 0 3 (by decide)) (hr 1 2 (by decide))
    (hr 1 3 (by decide)) (hr 2 3 (by decide)) (p 0) (p 1) (p 2) (p 3)

/-! ### α-X.11:常微分方程式の一意性 -/

/-- y″ = −κy(κ > 0)、y(0) = y′(0) = 0 なら y ≡ 0 -/
theorem oq_osc_unique {y y1 : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) (hy : ∀ x, HasDerivAt y (y1 x) x)
    (hy1 : ∀ x, HasDerivAt y1 (-(κ * y x)) x) (h0 : y 0 = 0) (h1 : y1 0 = 0) : ∀ x, y x = 0 := by
  have hE : ∀ x, HasDerivAt (fun x => κ * (y x * y x) + y1 x * y1 x) 0 x := by
    intro x
    have h := (((hy x).mul (hy x)).const_mul κ).add ((hy1 x).mul (hy1 x))
    convert h using 1
    ring
  intro x
  have hc := is_const_of_deriv_eq_zero (fun x => (hE x).differentiableAt) (fun x => (hE x).deriv) x 0
  simp only [h0, h1, mul_zero, add_zero] at hc
  have a := mul_nonneg hκ.le (mul_self_nonneg (y x))
  have b := mul_self_nonneg (y1 x)
  have e : κ * (y x * y x) = 0 := by linarith
  rcases mul_eq_zero.mp e with h | h
  · exact absurd h hκ.ne'
  · exact mul_self_eq_zero.mp h

/-- q″ = −q の解は q(0)cos η + q′(0)sin η だけ -/
theorem oq_osc_solution {q q1 : ℝ → ℝ} (hq : ∀ x, HasDerivAt q (q1 x) x)
    (hq1 : ∀ x, HasDerivAt q1 (-(q x)) x) : ∀ x, q x = q 0 * cos x + q1 0 * sin x := by
  have key := oq_osc_unique (κ := 1) one_pos
    (y := fun x => q x - (q 0 * cos x + q1 0 * sin x))
    (y1 := fun x => q1 x - (q 0 * -sin x + q1 0 * cos x))
    (fun x => (hq x).sub (((hasDerivAt_cos x).const_mul (q 0)).add ((hasDerivAt_sin x).const_mul (q1 0))))
    (fun x => by
      have h := (hq1 x).sub ((((hasDerivAt_sin x).neg).const_mul (q 0)).add
        ((hasDerivAt_cos x).const_mul (q1 0)))
      convert h using 1
      ring)
    (by simp) (by simp)
  intro x
  have := key x
  simp only at this
  linarith

/-- f_χχ sin χ = cos χ f_χ(rr_chi_ode の結論)なら、f_χ/sin χ の χ 微分は 0 -/
theorem oq_fc_over_sin {Fc Fcc : ℝ → ℝ} (χ : ℝ) (hFc : HasDerivAt Fc (Fcc χ) χ) (hS : sin χ ≠ 0)
    (hode : Fcc χ * sin χ - cos χ * Fc χ = 0) : HasDerivAt (fun χ => Fc χ / sin χ) 0 χ := by
  have h := hFc.div (hasDerivAt_sin χ) hS
  convert h using 1
  rw [eq_comm, div_eq_zero_iff]
  left
  linear_combination hode

/-! ### α-X.11-W:YM の試験場のスペクトル -/

/-- δW = S²u(x)(x = C = cos χ、S = sin χ)。δW_χχ = 2(C² − S²)u − 5S²C u′ + S⁴u″ を入れると
  δW_χχ + (1 − 3C²)u = S²[(1 − C²)u″ − 5C u′ − u] -/
theorem oq_testfield (S C U U1 U2 : ℝ) (h : S ^ 2 + C ^ 2 = 1) :
    (2 * (C ^ 2 - S ^ 2) * U - 5 * S ^ 2 * C * U1 + S ^ 4 * U2) + (1 - 3 * C ^ 2) * U
      = S ^ 2 * ((1 - C ^ 2) * U2 - 5 * C * U1 - U) := by
  linear_combination (-U + S ^ 2 * U2) * h

/-- Gegenbauer の方程式 (1 − x²)u″ − 5xu′ + n(n + 4)u = 0 の解では固有値は −(n² + 4n + 1) < 0:
  g″ = −(n² + 4n + 1)g で、すべてのモードが振動する(n = 0 は共形 Killing のゲージモード、振動数 1) -/
theorem oq_spectrum (n : ℕ) (x U U1 U2 : ℝ)
    (hG : (1 - x ^ 2) * U2 - 5 * x * U1 + (n : ℝ) * (n + 4) * U = 0) :
    (1 - x ^ 2) * U2 - 5 * x * U1 - U = -((n : ℝ) ^ 2 + 4 * n + 1) * U
      ∧ 0 < (n : ℝ) ^ 2 + 4 * n + 1 := by
  constructor
  · linear_combination hG
  · positivity

/-! ### α-XV:Ω の量子幾何学 -/

/-- 共形の枠の Einstein–Hilbert の密度:√g R = Ω⁴·(6 − 6□̂Ω/Ω)/Ω² = 6Ω² − 6Ω□̂Ω(Ω の 2 次式) -/
theorem oq_action_quadratic (Ω Bx : ℝ) (hΩ : Ω ≠ 0) :
    Ω ^ 4 * ((6 - 6 * Bx / Ω) / Ω ^ 2) = 6 * Ω ^ 2 - 6 * Ω * Bx := by
  field_simp
  ring

/-- 面積半径 r = Ω sin χ:r_ηη = Ω_ηη S、r_χχ = Ω_χχ S + 2Ω_χ C − Ω S。
  r_ηη − r_χχ = −S·(−Ω_ηη + Ω_χχ + 2(C/S)Ω_χ − Ω):トレースの方程式 ⇔ r は 2 次元の波動方程式の解 -/
theorem oq_radius_wave (S C Ω0 Ωc Ωcc Ωee : ℝ) (hS : S ≠ 0) :
    Ωee * S - (Ωcc * S + 2 * Ωc * C - Ω0 * S)
      = -S * (-Ωee + Ωcc + 2 * (C / S) * Ωc - Ω0) := by
  field_simp
  ring

/-- r = F(η + χ) − F(η − χ) がもう一方の極 χ = π でも 0 なら、F は周期 2π -/
theorem oq_periodic (F : ℝ → ℝ) (hpole : ∀ η, F (η + π) - F (η - π) = 0) :
    ∀ x, F (x + 2 * π) = F x := by
  intro x
  have h := hpole (x + π)
  rw [show x + π + π = x + 2 * π by ring, show x + π - π = x by ring] at h
  linarith

/-- 対蹠の写像 (η, χ) ↦ (η + π, π − χ) で r ↦ −r(sin(π − χ) = sin χ なので Ω ↦ −Ω、計量 Ω²ĝ は不変):
  Ω = 0 の面(始まりと終わり)を越えると、宇宙は対蹠の像として繰り返す -/
theorem oq_antipodal (F : ℝ → ℝ) (hper : ∀ x, F (x + 2 * π) = F x) (η χ : ℝ) :
    F ((η + π) + (π - χ)) - F ((η + π) - (π - χ)) = -(F (η + χ) - F (η - χ)) := by
  rw [show η + π + (π - χ) = (η - χ) + 2 * π by ring, hper, show η + π - (π - χ) = η + χ by ring]
  ring

/-- 帽子:ℓ cos η sin χ = F(η + χ) − F(η − χ)、F = (ℓ/2) sin -/
theorem oq_cap_dalembert (l η χ : ℝ) :
    l * cos η * sin χ = l / 2 * sin (η + χ) - l / 2 * sin (η - χ) := by
  rw [sin_add, sin_sub]
  ring

/-- 一様なモードの作用の係数:(1/(16πG))·6·(S³ の体積 2π²) = 3π/(4G) -/
theorem oq_energy_coeff (G : ℝ) (hG : G ≠ 0) : 1 / (16 * π * G) * 6 * (2 * π ^ 2) = 3 * π / (4 * G) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- 拘束(全エネルギー 0):(3π/(4G))ℓ² = 3π²/g² ⇔ ℓ² = 4πG/g² -/
theorem oq_classical_scale (G g l : ℝ) (hG : G ≠ 0) (hg : g ≠ 0) :
    3 * π / (4 * G) * l ^ 2 = 3 * π ^ 2 / g ^ 2 ↔ l ^ 2 = 4 * π * G / g ^ 2 := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  constructor
  · intro h
    rw [eq_div_iff hg2]
    field_simp at h
    have h3 : 3 * π ≠ 0 := mul_ne_zero (by norm_num) hπ
    have e : 3 * π * (l ^ 2 * g ^ 2 - 4 * π * G) = 0 := by linear_combination h
    have := (mul_eq_zero.mp e).resolve_left h3
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- 振動数 1 の調和振動子として両方のエネルギーを n + ½ とおくと(ℏ = 1)
  ℓ²/G = 4(n + ½)/(3π)、g²/(4π) = 3π/(4n + 2) -/
theorem oq_quantized_scale (G g l : ℝ) (n : ℕ) (hG : G ≠ 0) (hg : g ≠ 0)
    (hΩ : 3 * π / (4 * G) * l ^ 2 = n + 1 / 2) (hYM : 3 * π ^ 2 / g ^ 2 = n + 1 / 2) :
    l ^ 2 / G = 4 * (n + 1 / 2) / (3 * π) ∧ g ^ 2 / (4 * π) = 3 * π / (4 * n + 2) := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hn : (4 * (n : ℝ) + 2) ≠ 0 := by positivity
  constructor
  · rw [← hΩ]
    field_simp
    ring
  · rw [div_eq_div_iff (mul_ne_zero (by norm_num) hπ) hn]
    have h2 : 3 * π ^ 2 = (n + 1 / 2) * g ^ 2 := by
      rw [← hYM]; field_simp
    linear_combination (-4 : ℝ) * h2

/-! ### α-XV.6、XV.7:ゲージ代数 sl(2,ℝ) と、首の不変性 -/

/-- 共形 Killing ベクトル ξ₁ = (sC, cS)、ξ₂ = (cC, −sS)((η, χ) 成分、c = cos η、s = sin η、C = cos χ、S = sin χ)の
  交換子:[ξ₁, ξ₂] = −∂_η。∂_η との交換子 [∂_η, ξ₁] = ξ₂、[∂_η, ξ₂] = −ξ₁ と合わせて so(2,1) ≅ sl(2,ℝ)
  (偏微分は手で入れた:∂_η(sC) = cC、∂_χ(sC) = −sS など) -/
theorem oq_sl2_bracket (c s C S : ℝ) (h1 : s ^ 2 + c ^ 2 = 1) (h2 : S ^ 2 + C ^ 2 = 1) :
    (s * C) * (-(s * C)) + (c * S) * (-(c * S)) - (c * C) * (c * C) - (-(s * S)) * (-(s * S)) = -1
      ∧ (s * C) * (-(c * S)) + (c * S) * (-(s * C)) - (c * C) * (-(s * S)) - (-(s * S)) * (c * C) = 0 := by
  constructor
  · linear_combination (-(S ^ 2 + C ^ 2)) * h1 - h2
  · ring

/-- 首 Ω = ℓ/sin χ、W = 0 は三つの生成子すべてで不変:δΩ = ξ(Ω) + ψΩ = 0(ξ₁:ψ = cC、ξ₂:ψ = −sC)。
  帽子のゲージの対称性(静的宇宙の共形 Killing)は、ちょうど首 AdS₂ の等長変換 -/
theorem oq_neck_invariant (l c s C S : ℝ) (hS : S ≠ 0) :
    (c * S) * (-(l * C / S ^ 2)) + (c * C) * (l / S) = 0
      ∧ (-(s * S)) * (-(l * C / S ^ 2)) + (-(s * C)) * (l / S) = 0 := by
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- 逆:静的で ξ₁ で不変(sin χ Ω_χ + cos χ Ω = 0)なら Ω sin χ は定数、つまり Ω = 定数/sin χ(首だけ) -/
theorem oq_neck_unique {Ω Ωc : ℝ → ℝ} (χ : ℝ) (hΩ : HasDerivAt Ω (Ωc χ) χ)
    (hinv : sin χ * Ωc χ + cos χ * Ω χ = 0) : HasDerivAt (fun χ => Ω χ * sin χ) 0 χ := by
  have h := hΩ.mul (hasDerivAt_sin χ)
  convert h using 1
  linear_combination -hinv

/-- 帽子の上の YM のポテンシャルは、真空(W = ±1)の上のポテンシャル −2/sin²χ に定数 3 を足したもの。
  真空の上の振動数 n + 2(整数)に対し、帽子の上では ω² = (n + 2)² − 3 -/
theorem oq_potential_shift (S C : ℝ) (hS : S ≠ 0) (h : S ^ 2 + C ^ 2 = 1) :
    (1 - 3 * C ^ 2) / S ^ 2 = (1 - 3 * 1 ^ 2) / S ^ 2 + 3 := by
  rw [show 1 - 3 * C ^ 2 = 3 * S ^ 2 - 2 by linear_combination (-3 : ℝ) * h]
  field_simp
  ring

end CFT.OQ
