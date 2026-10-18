/-
  完全化(その1):α-VI.6、α-IV.12、α-IV.3、α-IV.8、α-IV.5

  * α-VI.6 (Z35)  H の偏微分も Lean で検算(K, T と合わせて Poisson 括弧の入力をすべて検算)
  * α-IV.12 (Z13) Hamilton–Jacobi:S = aσ(b) は H(a, b, ∂S/∂a, ∂S/∂b) = 0 を厳密に満たす
  * α-IV.3 (Z9-a) 中心の常微分方程式を二重 null 方程式から導出(σ の時間微分が打ち消し合う)
  * α-IV.8 (Z10′) 首の lapse が sech(t/ℓ) のとき、波面の到着固有時は τ(z) = ℓ gd(z/ℓ)
  * α-IV.5 (Z9-c) 有限時間崩壊:(rW_l)² ≥ κ > ℓ²/2 なら
        (i) エネルギー不等式 r′² ≥ (κ − ℓ²/2)(1/r² − 1/r₁²)
        (ii) 崩壊までの固有時 Δτ ≤ r₁²/√(κ − ℓ²/2)
-/
import CFT.AlphaIV
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

namespace CFT.AlphaCompleteA

/-! ### α-VI.6 H の偏微分 -/

/-- 首の縮約 Hamiltonian -/
noncomputable def Hfun (a b pa pb c l : ℝ) : ℝ :=
  1 / (4 * c) * (a * pa ^ 2 / b ^ 2 - 2 * pa * pb / b) - c * a * (1 - l ^ 2 / b ^ 2)

theorem H_a (a b pa pb c l : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun x => Hfun x b pa pb c l) (-c + c * l ^ 2 / b ^ 2 + pa ^ 2 / (4 * b ^ 2 * c)) a := by
  have h := ((((hasDerivAt_id a).mul_const (pa ^ 2 / b ^ 2)).sub_const (2 * pa * pb / b)).const_mul
    (1 / (4 * c))).sub (((hasDerivAt_id a).const_mul c).mul_const (1 - l ^ 2 / b ^ 2))
  have hf : (fun x => Hfun x b pa pb c l) =
      (fun x => 1 / (4 * c) * (id x * (pa ^ 2 / b ^ 2) - 2 * pa * pb / b) - c * id x * (1 - l ^ 2 / b ^ 2)) := by
    funext x; simp only [Hfun, id]; ring
  rw [hf]
  convert h using 1
  field_simp
  ring

theorem H_pb (a b pa pb c l : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun x => Hfun a b pa x c l) (-pa / (2 * b * c)) pb := by
  have h := (((hasDerivAt_id pb).const_mul (2 * pa / b)).const_sub (a * pa ^ 2 / b ^ 2)).const_mul
    (1 / (4 * c)) |>.sub_const (c * a * (1 - l ^ 2 / b ^ 2))
  have hf : (fun x => Hfun a b pa x c l) =
      (fun x => 1 / (4 * c) * (a * pa ^ 2 / b ^ 2 - 2 * pa / b * id x) - c * a * (1 - l ^ 2 / b ^ 2)) := by
    funext x; simp only [Hfun, id]; ring
  rw [hf]
  convert h using 1
  field_simp
  ring

theorem H_pa (a b pa pb c l : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun x => Hfun a b x pb c l) ((a * pa - b * pb) / (2 * b ^ 2 * c)) pa := by
  have h := ((((hasDerivAt_id pa).pow 2).const_mul (a / b ^ 2)).sub
    ((hasDerivAt_id pa).const_mul (2 * pb / b))).const_mul (1 / (4 * c))
    |>.sub_const (c * a * (1 - l ^ 2 / b ^ 2))
  have hf : (fun x => Hfun a b x pb c l) =
      (fun x => 1 / (4 * c) * (a / b ^ 2 * id x ^ 2 - 2 * pb / b * id x) - c * a * (1 - l ^ 2 / b ^ 2)) := by
    funext x; simp only [Hfun, id]; ring
  rw [hf]
  convert h using 1
  simp only [id, Nat.cast_ofNat]
  field_simp
  ring

theorem H_b (a b pa pb c l : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun x => Hfun a x pa pb c l)
      ((-4 * a * c ^ 2 * l ^ 2 + pa * (-a * pa + b * pb)) / (2 * b ^ 3 * c)) b := by
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(b ^ 2)⁻¹) b := hasDerivAt_inv hb
  have hinv2 : HasDerivAt (fun x : ℝ => (x⁻¹) ^ 2) (2 * b⁻¹ * (-(b ^ 2)⁻¹)) b := by
    simpa using hinv.pow 2
  have h := ((((hinv2.const_mul (a * pa ^ 2)).sub (hinv.const_mul (2 * pa * pb))).const_mul
    (1 / (4 * c))).sub (((hinv2.const_mul (l ^ 2)).const_sub 1).const_mul (c * a)))
  have hf : (fun x => Hfun a x pa pb c l) =
      (fun x => 1 / (4 * c) * (a * pa ^ 2 * (x⁻¹) ^ 2 - 2 * pa * pb * x⁻¹)
        - c * a * (1 - l ^ 2 * (x⁻¹) ^ 2)) := by
    funext x; simp only [Hfun]; ring
  rw [hf]
  convert h using 1
  field_simp
  ring

/-! ### α-IV.12 Hamilton–Jacobi の厳密解 -/

/-- S = aσ(b)(p_a = σ、p_b = aσ′)、σ² = Cb − 4c²(b² + ℓ²)、σσ′ = (C − 8c²b)/2 なら H = 0 -/
theorem hj_exact (a b c l C σ σ' : ℝ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs2 : σ ^ 2 = C * b - 4 * c ^ 2 * (b ^ 2 + l ^ 2)) (hss : σ * σ' = (C - 8 * c ^ 2 * b) / 2) :
    Hfun a b σ (a * σ') c l = 0 := by
  have h1 : 4 * c * b ^ 2 * Hfun a b σ (a * σ') c l
      = a * σ ^ 2 - 2 * a * b * (σ * σ') - 4 * c ^ 2 * a * (b ^ 2 - l ^ 2) := by
    simp only [Hfun]; field_simp; ring
  have h2 : a * σ ^ 2 - 2 * a * b * (σ * σ') - 4 * c ^ 2 * a * (b ^ 2 - l ^ 2) = 0 := by
    rw [hs2, hss]; ring
  have h3 : 4 * c * b ^ 2 ≠ 0 := by positivity
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left h3

/-! ### α-IV.3 中心の常微分方程式の導出 -/

/-- 二重 null 計量 −2e^{2σ}du dv + r²dΩ² の中心(鏡映対称 u ↔ v、W = 0)で:
    r_u = r_v、r_uu = r_vv、σ_u = σ_v、W_v = −W_u。
    方程式 r_uv = (q²ℓ²(1−W²)²/(2r²) − r_u r_v − q²/2)/r(q = e^σ)と
    拘束 r_uu − 2σ_u r_u + 2W_u²/r = 0。
    t = (u+v)/2、s = (v−u)/2、固有時 dτ = √2 q dt、固有長 dl = √2 q ds とすると
    r′ = r_t/(√2q)、W_l = W_s/(√2q)、r″ = (r_tt − σ_t r_t)/(2q²)(連鎖律)。
    このとき r″ = −(r′² + 1 − ℓ²/r²)/(2r) − W_l²/r -/
theorem center_ode (r q ru ruu ruv σu Wu l : ℝ) (hr : r ≠ 0) (hq : q ≠ 0)
    (hruv : ruv = (q ^ 2 * l ^ 2 * (1 - 0 ^ 2) ^ 2 / (2 * r ^ 2) - ru * ru - q ^ 2 / 2) / r)
    (hcons : ruu - 2 * σu * ru + 2 * Wu ^ 2 / r = 0) :
    let rt := ru + ru
    let rtt := ruu + 2 * ruv + ruu
    let σt := σu + σu
    let Ws := -Wu - Wu
    let r' := rt / (√2 * q)
    let Wl := Ws / (√2 * q)
    let r'' := (rtt - σt * rt) / (2 * q ^ 2)
    r'' = -(r' ^ 2 + 1 - l ^ 2 / r ^ 2) / (2 * r) - Wl ^ 2 / r := by
  intro rt rtt σt Ws r' Wl r''
  have hs : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hruu : ruu = 2 * σu * ru - 2 * Wu ^ 2 / r := by linarith
  simp only [r'', r', Wl, rtt, σt, rt, Ws]
  rw [hruu, hruv]
  simp only [div_pow, mul_pow, hs]
  field_simp
  ring

/-! ### α-IV.8 到着固有時 τ = ℓ gd(z/ℓ) -/

theorem arrival_time (l z : ℝ) (hl : 0 < l) :
    ∫ t in (0 : ℝ)..z, 1 / cosh (t / l) = l * CFT.AlphaIV.gd (z / l) := by
  have hd : ∀ t ∈ Set.uIcc 0 z, HasDerivAt (fun t => l * CFT.AlphaIV.gd (t / l)) (1 / cosh (t / l)) t := by
    intro t _
    have h := ((CFT.AlphaIV.gd_deriv (t / l)).comp t ((hasDerivAt_id t).div_const l)).const_mul l
    convert h using 1
    field_simp
  have hint : IntervalIntegrable (fun t => 1 / cosh (t / l)) MeasureTheory.volume 0 z := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (continuous_cosh.comp (continuous_id.div_const l))
      (fun t => (cosh_pos _).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp [CFT.AlphaIV.gd_zero]

/-! ### α-IV.5 有限時間崩壊 -/

/-- (i) エネルギー不等式の代数部分:r r′² ≥ (r₁ − r) + (2κ − ℓ²)(1/r − 1/r₁)、0 < r < r₁、
    κ ≥ ℓ²/2 なら r′² ≥ (κ − ℓ²/2)(1/r² − 1/r₁²) -/
theorem energy_ineq_alg (r r1 rp κ l : ℝ) (hr : 0 < r) (hr1 : r < r1) (hκ : l ^ 2 / 2 ≤ κ)
    (h : r * rp ^ 2 ≥ (r1 - r) + (2 * κ - l ^ 2) * (1 / r - 1 / r1)) :
    rp ^ 2 ≥ (κ - l ^ 2 / 2) * (1 / r ^ 2 - 1 / r1 ^ 2) := by
  have hr1p : 0 < r1 := lt_trans hr hr1
  have hk : 0 ≤ 2 * κ - l ^ 2 := by linarith
  have h1 : r * rp ^ 2 ≥ (2 * κ - l ^ 2) * (1 / r - 1 / r1) := by
    have : 0 ≤ r1 - r := by linarith
    linarith
  have h2 : rp ^ 2 ≥ (2 * κ - l ^ 2) * (1 / r ^ 2 - 1 / (r * r1)) := by
    have e : (2 * κ - l ^ 2) * (1 / r ^ 2 - 1 / (r * r1)) = (2 * κ - l ^ 2) * (1 / r - 1 / r1) / r := by
      field_simp; ring
    rw [e, ge_iff_le, div_le_iff hr]
    linarith
  have h3 : 2 * (1 / r ^ 2 - 1 / (r * r1)) - (1 / r ^ 2 - 1 / r1 ^ 2) = (1 / r - 1 / r1) ^ 2 := by
    field_simp; ring
  have h4 : (κ - l ^ 2 / 2) * (1 / r ^ 2 - 1 / r1 ^ 2) ≤ (2 * κ - l ^ 2) * (1 / r ^ 2 - 1 / (r * r1)) := by
    have : 0 ≤ (κ - l ^ 2 / 2) * (1 / r - 1 / r1) ^ 2 := by
      apply mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [h3]
  linarith

/-- E − 2κ/r は、崩壊中(r′ ≤ 0)かつ W²r² ≥ κ なら減らない(エネルギー不等式の単調性部分):
    (E − 2κ/r)′ = −2W²r′ + 2κr′/r² = −2r′(W² − κ/r²) ≥ 0 -/
theorem energy_monotone_integrand (W rp r κ : ℝ) (hr : 0 < r) (hrp : rp ≤ 0) (hW : κ ≤ W ^ 2 * r ^ 2) :
    0 ≤ -2 * W ^ 2 * rp + 2 * κ * rp / r ^ 2 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have h1 : κ / r ^ 2 ≤ W ^ 2 := by rw [div_le_iff hr2]; linarith
  have : -2 * W ^ 2 * rp + 2 * κ * rp / r ^ 2 = (-2 * rp) * (W ^ 2 - κ / r ^ 2) := by ring
  rw [this]
  apply mul_nonneg <;> linarith

/-- (ii) 比較定理:0 < r < r₁ で r′ ≤ −√(A(1/r² − 1/r₁²))(A > 0)が [τ₀, τ₁] で成り立つなら
    τ₁ − τ₀ ≤ r₁²/√A -/
theorem collapse_time (r rp : ℝ → ℝ) (A r1 τ0 τ1 : ℝ) (hA : 0 < A) (hτ : τ0 ≤ τ1)
    (hd : ∀ τ ∈ Set.Icc τ0 τ1, HasDerivAt r (rp τ) τ)
    (hr : ∀ τ ∈ Set.Icc τ0 τ1, 0 < r τ ∧ r τ < r1)
    (hineq : ∀ τ ∈ Set.Icc τ0 τ1, rp τ ≤ -√(A * (1 / r τ ^ 2 - 1 / r1 ^ 2))) :
    τ1 - τ0 ≤ r1 ^ 2 / √A := by
  have hsA : 0 < √A := Real.sqrt_pos.2 hA
  -- Φ(x) = (r₁/√A) √(r₁² − x²)
  let Φ : ℝ → ℝ := fun x => r1 / √A * √(r1 ^ 2 - x ^ 2)
  let g : ℝ → ℝ := fun τ => Φ (r τ) - τ
  have key : ∀ τ ∈ Set.Icc τ0 τ1,
      HasDerivAt g (r1 / √A * (-(2 * r τ * rp τ)) / (2 * √(r1 ^ 2 - r τ ^ 2)) - 1) τ := by
    intro τ hτ'
    obtain ⟨h0, h1⟩ := hr τ hτ'
    have hpos : r1 ^ 2 - r τ ^ 2 ≠ 0 := (by nlinarith : (0:ℝ) < r1 ^ 2 - r τ ^ 2).ne'
    have hs := (Real.hasDerivAt_sqrt hpos).comp τ (((hd τ hτ').pow 2).const_sub (r1 ^ 2))
    have h := (hs.const_mul (r1 / √A)).sub (hasDerivAt_id τ)
    convert h using 1
    simp only [Function.comp_def, id, Nat.cast_ofNat]
    field_simp
  have hnonneg : ∀ τ ∈ Set.Icc τ0 τ1,
      0 ≤ r1 / √A * (-(2 * r τ * rp τ)) / (2 * √(r1 ^ 2 - r τ ^ 2)) - 1 := by
    intro τ hτ'
    obtain ⟨h0, h1⟩ := hr τ hτ'
    have hr1 : 0 < r1 := lt_trans h0 h1
    have hS : 0 < √(r1 ^ 2 - r τ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
    -- √(A(1/r² − 1/r₁²)) = √A · S/(r r₁)
    have hT : √(A * (1 / r τ ^ 2 - 1 / r1 ^ 2)) = √A * √(r1 ^ 2 - r τ ^ 2) / (r τ * r1) := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by
          apply mul_nonneg hA.le
          have : r τ ^ 2 ≤ r1 ^ 2 := by nlinarith
          rw [sub_nonneg]; apply one_div_le_one_div_of_le (by positivity) this)
        (by positivity)]
      have e1 : √A * √A = A := Real.mul_self_sqrt hA.le
      have e2 : √(r1 ^ 2 - r τ ^ 2) * √(r1 ^ 2 - r τ ^ 2) = r1 ^ 2 - r τ ^ 2 :=
        Real.mul_self_sqrt (by nlinarith)
      field_simp
      rw [show √A * √(r1 ^ 2 - r τ ^ 2) * (√A * √(r1 ^ 2 - r τ ^ 2))
        = (√A * √A) * (√(r1 ^ 2 - r τ ^ 2) * √(r1 ^ 2 - r τ ^ 2)) by ring, e1, e2]
      ring
    have hi := hineq τ hτ'
    rw [hT] at hi
    -- (r₁/√A)·(−2 r rp)/(2S) ≥ (r₁/√A)·(2r)·(√A S/(r r₁))/(2S) = 1
    have hcoef : 0 ≤ r1 / √A * (2 * r τ) / (2 * √(r1 ^ 2 - r τ ^ 2)) := by positivity
    have hge : r1 / √A * (-(2 * r τ * rp τ)) / (2 * √(r1 ^ 2 - r τ ^ 2))
        ≥ r1 / √A * (2 * r τ) / (2 * √(r1 ^ 2 - r τ ^ 2)) * (√A * √(r1 ^ 2 - r τ ^ 2) / (r τ * r1)) := by
      have : r1 / √A * (-(2 * r τ * rp τ)) / (2 * √(r1 ^ 2 - r τ ^ 2))
          = r1 / √A * (2 * r τ) / (2 * √(r1 ^ 2 - r τ ^ 2)) * (-rp τ) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hcoef
    have hone : r1 / √A * (2 * r τ) / (2 * √(r1 ^ 2 - r τ ^ 2)) * (√A * √(r1 ^ 2 - r τ ^ 2) / (r τ * r1))
        = 1 := by
      field_simp
      ring
    linarith
  have hmono : MonotoneOn g (Set.Icc τ0 τ1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc τ0 τ1)
    · intro x hx; exact (key x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (key x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(key x (Set.Ioo_subset_Icc_self hx)).deriv]
      exact hnonneg x (Set.Ioo_subset_Icc_self hx)
  have h0 := Set.left_mem_Icc.2 hτ
  have h1 := Set.right_mem_Icc.2 hτ
  have hg := hmono h0 h1 hτ
  simp only [g, Φ] at hg
  have hΦ0 : 0 ≤ r1 / √A * √(r1 ^ 2 - r τ0 ^ 2) := by
    have := (hr τ0 h0); have : 0 < r1 := lt_trans this.1 this.2; positivity
  have hΦ1 : r1 / √A * √(r1 ^ 2 - r τ1 ^ 2) ≤ r1 ^ 2 / √A := by
    obtain ⟨a0, a1⟩ := hr τ1 h1
    have hr1 : 0 < r1 := lt_trans a0 a1
    have hsq : √(r1 ^ 2 - r τ1 ^ 2) ≤ r1 := by
      calc √(r1 ^ 2 - r τ1 ^ 2) ≤ √(r1 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = r1 := Real.sqrt_sq hr1.le
    calc r1 / √A * √(r1 ^ 2 - r τ1 ^ 2) ≤ r1 / √A * r1 := by
          apply mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = r1 ^ 2 / √A := by ring
  linarith

/-- (i′) エネルギー不等式そのもの:転回点 τ₁(r = r₁、r′ = 0)から崩壊中(r′ ≤ 0)、
    中心の式と W²r² ≥ κ が成り立つなら、各時刻で
    r(1 + r′²) + ℓ²/r − 2κ/r ≥ r₁ + ℓ²/r₁ − 2κ/r₁ -/
theorem energy_inequality (r rp W : ℝ → ℝ) (l κ τ1 τ2 : ℝ) (h12 : τ1 ≤ τ2)
    (hpos : ∀ τ ∈ Set.Icc τ1 τ2, 0 < r τ)
    (h1 : ∀ τ ∈ Set.Icc τ1 τ2, HasDerivAt r (rp τ) τ)
    (h2 : ∀ τ ∈ Set.Icc τ1 τ2,
      HasDerivAt rp (-(rp τ ^ 2 + 1 - l ^ 2 / r τ ^ 2) / (2 * r τ) - W τ ^ 2 / r τ) τ)
    (hdown : ∀ τ ∈ Set.Icc τ1 τ2, rp τ ≤ 0)
    (hW : ∀ τ ∈ Set.Icc τ1 τ2, κ ≤ W τ ^ 2 * r τ ^ 2) :
    ∀ τ ∈ Set.Icc τ1 τ2,
      r τ1 * (1 + rp τ1 ^ 2) + l ^ 2 / r τ1 - 2 * κ / r τ1
        ≤ r τ * (1 + rp τ ^ 2) + l ^ 2 / r τ - 2 * κ / r τ := by
  let G : ℝ → ℝ := fun τ => r τ * (1 + rp τ ^ 2) + l ^ 2 / r τ - 2 * κ / r τ
  have hG : ∀ τ ∈ Set.Icc τ1 τ2,
      HasDerivAt G (-2 * W τ ^ 2 * rp τ + 2 * κ * rp τ / r τ ^ 2) τ := by
    intro τ hτ
    have hr0 : r τ ≠ 0 := (hpos τ hτ).ne'
    have hE := CFT.AlphaIV.energy_deriv r rp W l τ hr0 (h1 τ hτ) (h2 τ hτ)
    have hk := ((h1 τ hτ).inv hr0).const_mul (2 * κ)
    have h := hE.sub hk
    have hf : G = fun τ => (r τ * (1 + rp τ ^ 2) + l ^ 2 / r τ) - 2 * κ * (r τ)⁻¹ := by
      funext τ; simp only [G]; ring
    rw [hf]
    convert h using 1
    field_simp
  have hmono : MonotoneOn G (Set.Icc τ1 τ2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc τ1 τ2)
    · intro x hx; exact (hG x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hG x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Set.Ioo_subset_Icc_self hx
      rw [(hG x hx').deriv]
      exact energy_monotone_integrand (W x) (rp x) (r x) κ (hpos x hx') (hdown x hx') (hW x hx')
  intro τ hτ
  exact hmono (Set.left_mem_Icc.2 h12) hτ hτ.1

/-- 系:転回点(r′(τ₁) = 0、r(τ₁) = r₁)からなら r r′² ≥ (r₁ − r) + (2κ − ℓ²)(1/r − 1/r₁) -/
theorem energy_inequality' (r1 r rp l κ : ℝ) (hr : 0 < r) (hr1 : 0 < r1)
    (h : r1 * (1 + 0 ^ 2) + l ^ 2 / r1 - 2 * κ / r1 ≤ r * (1 + rp ^ 2) + l ^ 2 / r - 2 * κ / r) :
    r * rp ^ 2 ≥ (r1 - r) + (2 * κ - l ^ 2) * (1 / r - 1 / r1) := by
  have e : r * (1 + rp ^ 2) + l ^ 2 / r - 2 * κ / r - (r1 * (1 + 0 ^ 2) + l ^ 2 / r1 - 2 * κ / r1)
      = r * rp ^ 2 - ((r1 - r) + (2 * κ - l ^ 2) * (1 / r - 1 / r1)) := by
    field_simp; ring
  linarith

end CFT.AlphaCompleteA
