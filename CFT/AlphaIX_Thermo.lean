/-
  α-IX.21〜IX.25、IX.27、IX.29、XI.2:ブラックホールの熱力学と統計

  * IX.21 Hawking 温度:地平線の近くで f ≈ f₁x(x = r − r_h)、固有距離 ρ で x = f₁ρ²/4 とおくと
      Euclid 計量 f dτ² + dr²/f = (f₁ρ/2)² dτ² + dρ²(`horizon_polar`)。円錐の特異点がない ⇔ 周期 β = 4π/f₁
      (`conical_period`)、T = f₁/(4π) = κ/(2π)(κ = f₁/2)。RN:f = (r − r₊)(r − r₋)/r² で f′(r₊) = (r₊ − r₋)/r₊²
      (`rn_slope`)、T = (r₊ − r₋)/(4πr₊²)、極限 r₊ = r₋ で T = 0。
  * IX.22 Euclid の首:−cosh²(x/ℓ)dt² + dx² を Euclid 化した cosh²(x/ℓ)dτ² + dx² の Gauss 曲率は
      K = −N″/N = −1/ℓ²(`euclid_neck_curvature`):双曲面 H²(半径 ℓ)。α-I の H³ と同じ定曲率負の幾何。
  * IX.23 第一法則と Smarr(G = 1、磁荷 Q):M = (r₊² + Q²)/(2r₊)、r₋ = Q²/r₊、S = πr₊²、
      T = (r₊ − r₋)/(4πr₊²)、Φ = Q/r₊ で ∂M/∂r₊ = T ∂S/∂r₊、∂M/∂Q = Φ(`first_law`)、M = 2TS + ΦQ(`smarr`)。
  * IX.24 Euclid 作用:I = β(M − ΦQ)/2(GHY 項と背景の差し引きを含む評価、Gibbons–Hawking 1977、外部)。
      Smarr と βT = 1 から I = β(M − TS − ΦQ)、S = β(M − ΦQ) − I = A/4(`euclid_action`)。
  * IX.25 Tolman–Ehrenfest:静的な輻射の静水圧平衡 dp/dr = −(ρ + p)N′/N、p = aT⁴/3、ρ = aT⁴ なら
      d(TN)/dr = 0(`tolman`)。第三法則は Israel 1986(外部)。
  * IX.27 Jüttner:E = √(m² + p²) は m + p²/2m − p⁴/8m³ ≤ E ≤ m + p²/2m(p² ≤ 8m²)(`nr_bounds`)。
      したがって e^{−βE} = e^{−βm}e^{−βp²/2m}(1 + O(p⁴)):非相対論の極限で Maxwell 分布。
      Q の座標 m/E ∈ (0, 1](`q_coordinate`)。不変測度 d³p/E と規格化(Bessel K₂)は外部。
  * IX.29 状態密度:ρ(E) ∝ e^{S₀} sinh(2π√(2CE)) の Laplace 変換(外部の標準積分)で現れる指数
      (2π√(2C))²/(4β) = 2π²C/β は IX.14 の Z と一致(`laplace_exponent`)。微視的なエントロピー
      S(E) = S₀ + 2π√(2CE) は E = 2π²CT² で S₀ + 4π²CT(`micro_macro`)、dS/dE = 1/T(`micro_temperature`)。
  * XI.2 高階補正と穏やかな WGC:L = −F²/4 + α(F²)² の磁気的な解では、エネルギー密度の補正は
      −α(F²)²(α > 0 で負)。質量関数 m(r) = M − p²/(2r) + 4πβp⁴/(5r⁵)(β > 0、`mass_function`)、
      f = 1 − 2m/r = 1 − 2M/r + p²/r² − k/r⁶(k = 8πβp⁴/5)。地平線 f(r) = 0 ⇔ M = M(r) := (r/2)(1 + p²/r² − k/r⁶)
      (`horizon_iff`)。M(p) = p − k/(2p⁵) < p(`lighter_extremal`):補正があると、古典の極限 M = p より軽い
      ブラックホールがある。極限の M/Q は 1 より小さくなり、極限ブラックホールは崩壊できる(穏やかな WGC)。
      α > 0 の符号:因果律・ユニタリ性(Adams ほか 2006)、ヘテロティック弦の F⁴ 項(外部)。
      R²(Gauss–Bonnet)の項はディラトンが一定なら 4 次元で位相的で、極限の比を変えない(外部)。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CFT.Thermo

open Real Set

/-! ### IX.21 Hawking 温度 -/

/-- 地平線の近く:x = f₁ρ²/4 なら dr/dρ = f₁ρ/2、(dr/dρ)²/f = 1、f = (f₁ρ/2)² -/
theorem horizon_polar (f1 ρ : ℝ) (hf : f1 ≠ 0) (hρ : ρ ≠ 0) :
    HasDerivAt (fun r => f1 * r ^ 2 / 4) (f1 * ρ / 2) ρ ∧
    (f1 * ρ / 2) ^ 2 / (f1 * (f1 * ρ ^ 2 / 4)) = 1 ∧ f1 * (f1 * ρ ^ 2 / 4) = (f1 * ρ / 2) ^ 2 := by
  refine ⟨?_, ?_, by ring⟩
  · have h := ((hasDerivAt_pow 2 ρ).const_mul f1).div_const 4
    convert h using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]; ring
  · field_simp <;> ring

/-- 円錐の特異点がない:角度 (f₁/2)τ が一周 2π ⇔ β = 4π/f₁、T = f₁/(4π) = κ/(2π) -/
theorem conical_period (f1 β : ℝ) (hf : 0 < f1) :
    f1 / 2 * β = 2 * π ↔ β = 4 * π / f1 := by
  have := hf.ne'
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp <;> ring

/-- RN:f = (r − r₊)(r − r₋)/r² の地平線での傾き f′(r₊) = (r₊ − r₋)/r₊² -/
theorem rn_slope (rp rm : ℝ) (hp : rp ≠ 0) :
    HasDerivAt (fun r => (r - rp) * (r - rm) / r ^ 2) ((rp - rm) / rp ^ 2) rp := by
  have h := (((hasDerivAt_id' rp).sub_const rp).mul ((hasDerivAt_id' rp).sub_const rm)).div
    (hasDerivAt_pow 2 rp) (pow_ne_zero 2 hp)
  convert h using 1
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one, sub_self, zero_mul, one_mul, mul_zero,
    sub_zero, zero_add]
  field_simp <;> ring

/-- 極限 r₊ = r₋ で T = (r₊ − r₋)/(4πr₊²) = 0 -/
theorem extremal_cold (rp : ℝ) : (rp - rp) / (4 * π * rp ^ 2) = 0 := by simp

/-! ### IX.22 Euclid の首 -/

/-- 【α-IX.22】N = cosh(x/ℓ):N″ = N/ℓ²、Gauss 曲率 −N″/N = −1/ℓ² -/
theorem euclid_neck_curvature (l x : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun y => cosh (y / l)) (sinh (x / l) * (1 / l)) x ∧
    HasDerivAt (fun y => sinh (y / l) * (1 / l)) (cosh (x / l) * (1 / l) * (1 / l)) x ∧
    -(cosh (x / l) * (1 / l) * (1 / l)) / cosh (x / l) = -1 / l ^ 2 := by
  have hd : HasDerivAt (fun y : ℝ => y / l) (1 / l) x := (hasDerivAt_id' x).div_const l
  have hc : cosh (x / l) ≠ 0 := (cosh_pos _).ne'
  refine ⟨(Real.hasDerivAt_cosh (x / l)).comp x hd, ((Real.hasDerivAt_sinh (x / l)).comp x hd).mul_const (1 / l), ?_⟩
  field_simp <;> ring

/-! ### IX.23 第一法則と Smarr -/

/-- M(r₊, Q) = (r₊² + Q²)/(2r₊)(f(r₊) = 1 − 2M/r₊ + Q²/r₊² = 0 の解) -/
noncomputable def Mrn (rp Q : ℝ) : ℝ := (rp ^ 2 + Q ^ 2) / (2 * rp)

theorem horizon_mass (rp Q M : ℝ) (hp : rp ≠ 0) :
    1 - 2 * M / rp + Q ^ 2 / rp ^ 2 = 0 ↔ M = Mrn rp Q := by
  simp only [Mrn]
  constructor
  · intro h
    have key : (1 - 2 * M / rp + Q ^ 2 / rp ^ 2) * rp ^ 2 = rp ^ 2 - 2 * M * rp + Q ^ 2 := by
      field_simp; ring
    rw [h, zero_mul] at key
    rw [eq_div_iff (mul_ne_zero two_ne_zero hp)]
    linarith
  · intro h; rw [h]; field_simp <;> ring

/-- 【α-IX.23】第一法則:∂M/∂r₊ = T ∂S/∂r₊(S = πr₊²、T = (r₊ − r₋)/(4πr₊²)、r₋ = Q²/r₊)、∂M/∂Q = Φ = Q/r₊ -/
theorem first_law (rp Q : ℝ) (hp : rp ≠ 0) :
    HasDerivAt (fun r => Mrn r Q) ((rp - Q ^ 2 / rp) / (4 * π * rp ^ 2) * (2 * π * rp)) rp ∧
    HasDerivAt (fun q => Mrn rp q) (Q / rp) Q := by
  have hπ := pi_ne_zero
  constructor
  · have h := ((hasDerivAt_pow 2 rp).add_const (Q ^ 2)).div ((hasDerivAt_id' rp).const_mul 2)
      (mul_ne_zero two_ne_zero hp)
    show HasDerivAt (fun r => (r ^ 2 + Q ^ 2) / (2 * r)) _ rp
    convert h using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp <;> ring
  · have h := ((hasDerivAt_pow 2 Q).const_add (rp ^ 2)).div_const (2 * rp)
    show HasDerivAt (fun q => (rp ^ 2 + q ^ 2) / (2 * rp)) _ Q
    convert h using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp <;> ring

/-- 【α-IX.23】Smarr:M = 2TS + ΦQ -/
theorem smarr (rp Q : ℝ) (hp : rp ≠ 0) :
    Mrn rp Q = 2 * ((rp - Q ^ 2 / rp) / (4 * π * rp ^ 2)) * (π * rp ^ 2) + Q / rp * Q := by
  have hπ := pi_ne_zero
  simp only [Mrn]; field_simp <;> ring

/-! ### IX.24 Euclid 作用 -/

/-- 【α-IX.24】I = β(M − ΦQ)/2(Gibbons–Hawking の評価)、Smarr M = 2TS + ΦQ、βT = 1 なら
I = β(M − TS − ΦQ)、S = β(M − ΦQ) − I -/
theorem euclid_action (β M T S Φ Q : ℝ) (hsm : M = 2 * T * S + Φ * Q) (hβ : β * T = 1) :
    β * (M - Φ * Q) / 2 = β * (M - T * S - Φ * Q) ∧ β * (M - Φ * Q) - β * (M - Φ * Q) / 2 = S := by
  constructor
  · rw [hsm]; ring
  · rw [hsm]; linear_combination S * hβ

/-! ### IX.25 Tolman–Ehrenfest -/

/-- 【α-IX.25】(4a/3)T³T′ = −(4a/3)T⁴N′/N(dp/dr = −(ρ + p)N′/N、p = aT⁴/3、ρ = aT⁴)なら (TN)′ = 0 -/
theorem tolman (a T N Td Nd : ℝ) (ha : a ≠ 0) (hT : T ≠ 0) (hN : N ≠ 0)
    (h : 4 * a / 3 * T ^ 3 * Td = -(4 * a / 3 * T ^ 4 * Nd / N)) : Td * N + T * Nd = 0 := by
  have h3 : 4 * a / 3 * T ^ 3 ≠ 0 := by positivity
  have hTd : Td = -(T * Nd / N) := by
    apply mul_left_cancel₀ h3
    rw [h]; field_simp <;> ring
  rw [hTd]; field_simp <;> ring

/-- (TN)′ = 0 が区間で成り立てば TN は一定 -/
theorem tolman_const (T N : ℝ → ℝ) (Td Nd : ℝ → ℝ) (r0 r1 : ℝ)
    (hT : ∀ r ∈ Icc r0 r1, HasDerivAt T (Td r) r) (hN : ∀ r ∈ Icc r0 r1, HasDerivAt N (Nd r) r)
    (h : ∀ r ∈ Icc r0 r1, Td r * N r + T r * Nd r = 0) :
    ∀ r ∈ Icc r0 r1, T r * N r = T r0 * N r0 := by
  have hd : ∀ r ∈ Icc r0 r1, HasDerivAt (fun x => T x * N x) 0 r := by
    intro r hr
    have := (hT r hr).mul (hN r hr)
    rwa [h r hr] at this
  have hcont : ContinuousOn (fun x => T x * N x) (Icc r0 r1) :=
    fun r hr => (hd r hr).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun r hr => (hd r (Ico_subset_Icc_self hr)).hasDerivWithinAt)

/-! ### IX.27 Jüttner 分布の非相対論の極限 -/

/-- 【α-IX.27】m + p²/2m − p⁴/8m³ ≤ √(m² + p²) ≤ m + p²/2m(m > 0、p² ≤ 8m²) -/
theorem nr_bounds (m p : ℝ) (hm : 0 < m) (hp : p ^ 2 ≤ 8 * m ^ 2) :
    m + p ^ 2 / (2 * m) - p ^ 4 / (8 * m ^ 3) ≤ Real.sqrt (m ^ 2 + p ^ 2) ∧
    Real.sqrt (m ^ 2 + p ^ 2) ≤ m + p ^ 2 / (2 * m) := by
  have hm0 := hm.ne'
  constructor
  · -- 左辺は m(1 + x/2 − x²/8)、x = p²/m² ∈ [0, 8]、二乗すると m²(1 + x − x³/8 + x⁴/64) ≤ m²(1 + x)
    set x := p ^ 2 / m ^ 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have hx8 : x ≤ 8 := by rw [hx, div_le_iff₀ (by positivity)]; linarith
    have e : m + p ^ 2 / (2 * m) - p ^ 4 / (8 * m ^ 3) = m * (1 + x / 2 - x ^ 2 / 8) := by
      rw [hx]; field_simp <;> ring
    rw [e]
    by_cases hneg : m * (1 + x / 2 - x ^ 2 / 8) ≤ 0
    · exact le_trans hneg (Real.sqrt_nonneg _)
    push_neg at hneg
    have ep : m ^ 2 + p ^ 2 = m ^ 2 * (1 + x) := by rw [hx]; field_simp <;> ring
    have h1 : (1 + x / 2 - x ^ 2 / 8) ^ 2 ≤ 1 + x := by
      nlinarith [sq_nonneg x, mul_nonneg hx0 (sub_nonneg.2 hx8), mul_nonneg (mul_nonneg hx0 hx0) (mul_nonneg hx0 (sub_nonneg.2 hx8))]
    have h2 : (m * (1 + x / 2 - x ^ 2 / 8)) ^ 2 ≤ m ^ 2 + p ^ 2 := by
      rw [ep]
      calc (m * (1 + x / 2 - x ^ 2 / 8)) ^ 2 = m ^ 2 * (1 + x / 2 - x ^ 2 / 8) ^ 2 := by ring
        _ ≤ m ^ 2 * (1 + x) := by gcongr
    calc m * (1 + x / 2 - x ^ 2 / 8) = Real.sqrt ((m * (1 + x / 2 - x ^ 2 / 8)) ^ 2) :=
          (Real.sqrt_sq hneg.le).symm
      _ ≤ Real.sqrt (m ^ 2 + p ^ 2) := Real.sqrt_le_sqrt h2
  · have hpos : 0 ≤ m + p ^ 2 / (2 * m) := by positivity
    have : (m + p ^ 2 / (2 * m)) ^ 2 = m ^ 2 + p ^ 2 + (p ^ 2 / (2 * m)) ^ 2 := by field_simp; ring
    calc Real.sqrt (m ^ 2 + p ^ 2) ≤ Real.sqrt ((m + p ^ 2 / (2 * m)) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [this]; nlinarith [sq_nonneg (p ^ 2 / (2 * m))])
      _ = m + p ^ 2 / (2 * m) := Real.sqrt_sq hpos

/-- Q の座標 m/E ∈ (0, 1] -/
theorem q_coordinate (m p : ℝ) (hm : 0 < m) :
    0 < m / Real.sqrt (m ^ 2 + p ^ 2) ∧ m / Real.sqrt (m ^ 2 + p ^ 2) ≤ 1 := by
  have hE : 0 < Real.sqrt (m ^ 2 + p ^ 2) := Real.sqrt_pos.2 (by positivity)
  refine ⟨div_pos hm hE, ?_⟩
  rw [div_le_one hE]
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm.le).symm
    _ ≤ Real.sqrt (m ^ 2 + p ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg p])

/-! ### IX.29 状態密度 -/

/-- 【α-IX.29】Laplace 変換の指数:a = 2π√(2C) なら a²/(4β) = 2π²C/β(IX.14 の Z と同じ) -/
theorem laplace_exponent (C β : ℝ) (hC : 0 ≤ C) (hβ : β ≠ 0) :
    (2 * π * Real.sqrt (2 * C)) ^ 2 / (4 * β) = 2 * π ^ 2 * C / β := by
  rw [mul_pow, Real.sq_sqrt (by linarith)]; field_simp <;> ring

/-- 【α-IX.29】微視的な S(E) = S₀ + 2π√(2CE) は E = 2π²CT² で S₀ + 4π²CT -/
theorem micro_macro (S0 C T : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    S0 + 2 * π * Real.sqrt (2 * C * (2 * π ^ 2 * C * T ^ 2)) = S0 + 4 * π ^ 2 * C * T := by
  have e : 2 * C * (2 * π ^ 2 * C * T ^ 2) = (2 * π * C * T) ^ 2 := by ring
  rw [e, Real.sqrt_sq (by have := pi_pos; positivity)]; ring

/-- 【α-IX.29】dS/dE = π√(2C)/√E = 1/T(E = 2π²CT²、C, T > 0) -/
theorem micro_temperature (C T : ℝ) (hC : 0 < C) (hT : 0 < T) :
    π * Real.sqrt (2 * C) / Real.sqrt (2 * π ^ 2 * C * T ^ 2) = 1 / T := by
  have e : 2 * π ^ 2 * C * T ^ 2 = (2 * C) * (π * T) ^ 2 := by ring
  have hπ := pi_pos
  rw [e, Real.sqrt_mul (show (0 : ℝ) ≤ 2 * C by linarith) ((π * T) ^ 2), Real.sqrt_sq (by positivity)]
  have hs : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.2 (by linarith)
  have hs' := hs.ne'
  have hT' := hT.ne'
  have hπ' := hπ.ne'
  field_simp

/-! ### XI.2 高階補正と穏やかな WGC -/

/-- 質量関数 m(r) = M − p²/(2r) + 4πβp⁴/(5r⁵):m′ = 4πr²ρ、ρ = p²/(8πr⁴) − βp⁴/r⁸ -/
theorem mass_function (M p β r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x => M - p ^ 2 / (2 * x) + 4 * π * β * p ^ 4 / (5 * x ^ 5))
      (4 * π * r ^ 2 * (p ^ 2 / (8 * π * r ^ 4) - β * p ^ 4 / r ^ 8)) r := by
  have hπ := pi_ne_zero
  have h1 := ((hasDerivAt_id' r).const_mul 2).inv (mul_ne_zero two_ne_zero hr)
  have h2 := ((hasDerivAt_pow 5 r).const_mul 5).inv (mul_ne_zero (by norm_num) (pow_ne_zero 5 hr))
  have h := ((h1.const_mul (p ^ 2)).const_sub M).add (h2.const_mul (4 * π * β * p ^ 4))
  convert h using 1 <;>
    first
    | (funext x; simp only [div_eq_mul_inv])
    | (simp only [Nat.cast_ofNat, show (5 : ℕ) - 1 = 4 from rfl]; field_simp; ring)

/-- M(r) = (r/2)(1 + p²/r² − k/r⁶):f(r) = 1 − 2M/r + p²/r² − k/r⁶ = 0 ⇔ M = M(r) -/
theorem horizon_iff (M p k r : ℝ) (hr : r ≠ 0) :
    1 - 2 * M / r + p ^ 2 / r ^ 2 - k / r ^ 6 = 0 ↔ M = r / 2 * (1 + p ^ 2 / r ^ 2 - k / r ^ 6) := by
  constructor
  · intro h
    have e : r / 2 * (1 + p ^ 2 / r ^ 2 - k / r ^ 6) - M = r / 2 * (1 - 2 * M / r + p ^ 2 / r ^ 2 - k / r ^ 6) := by
      field_simp <;> ring
    rw [h, mul_zero] at e; linarith
  · intro h; rw [h]; field_simp <;> ring

/-- 【α-XI.2】M(p) = p − k/(2p⁵) < p(k > 0):古典の極限 M = p より軽いブラックホールがある -/
theorem lighter_extremal (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    p / 2 * (1 + p ^ 2 / p ^ 2 - k / p ^ 6) = p - k / (2 * p ^ 5) ∧ p - k / (2 * p ^ 5) < p := by
  have hp0 := hp.ne'
  constructor
  · field_simp <;> ring
  · have : 0 < k / (2 * p ^ 5) := by positivity
    linarith

end CFT.Thermo
