/-
  未着手・部分の項目を小分けにして閉じる(2026-11-11)

  * α-X.8(閉じたダンベルの全エネルギー):Misner–Sharp 質量 m = R(1 − R′²)/(2G)。
    `rr_ms_deriv` m′ = (R′(1 − R′²) − 2RR′R″)/(2G)、`rr_ms_constraint` 時間対称な切り口のハミルトン拘束
    ³R = 16πGρ を使うと m′ = 4πR²ρR′、`rr_closed_total_zero` 両端が極(R = 0)の閉じた切り口では
    ∫ m′ = 0(全エネルギー 0)、`rr_cap_mass` 帽子 R = ℓ sin y では m = ℓ sin³y/(2G)(赤道で首の ℓ/(2G) と一致)。
  * α-XIII.4(共形平坦のままでは跳びは消えない、時間に依存する場合):`rr_extremal_rprime_deriv`、
    `rr_hessian_char` 時間対称な切り口の極値球面では r″ = Ω_ηη/Ω²(トレースの方程式から)、`rr_two_roots`
    W = r′ 型では r″ ∈ {0, −1/ℓ}、`rr_conformal_two_values` したがって Ω_ηη/Ω² ∈ {0, −1/ℓ}。
  * α-XIII.4-G(新、一般の W):`rr_general_W_rpp` 極値球面(r = ℓ、r′ = 0)でのハミルトン拘束から
    r″ = (W² − W⁴/2 − ℓ²W′²)/ℓ、`rr_general_W_any` W = 0 なら任意の r″ ≤ 0 が実現できる。
    離散的な二つの根は W = r′ に固有の性質。
  * α-X.11(帽子の線形安定性、共形平坦な部分):`rr_mode0`〜`rr_mode2` 共形 Killing ベクトルが生む三つの
    摂動は線形化方程式をみたす、`rr_dW_eta_deriv`・`rr_eta_integrability` η 方向の可積分性の恒等式、
    `rr_chi_ode` χ 方向の常微分方程式への帰着、`rr_cos_mode_excluded` 振幅の変化 f = cos η は除かれる。
  * α-XI.7(Higgs を入れた帽子):`rr_higgs_cap_residual` W = cos χ は随伴 Higgs の質量項があると解でない。
  * α-XI.5(dyon の首):`rr_dyon_bf` 電場による有効質量の負のずれ(外部の公式)を入れても BF 限界の破れは残る。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open Real Set intervalIntegral

namespace CFT.RR

/-! ### α-X.8:閉じたダンベルの全エネルギー -/

/-- Misner–Sharp 質量 m = R(1 − R′²)/(2G) -/
noncomputable def msMass (G R R1 : ℝ) : ℝ := R * (1 - R1 ^ 2) / (2 * G)

/-- m の微分(連鎖律) -/
theorem rr_ms_deriv {R R1 R2 : ℝ → ℝ} {G : ℝ} (x : ℝ) (hR : HasDerivAt R (R1 x) x)
    (hR1 : HasDerivAt R1 (R2 x) x) :
    HasDerivAt (fun x => msMass G (R x) (R1 x))
      ((R1 x * (1 - R1 x * R1 x) - 2 * R x * R1 x * R2 x) / (2 * G)) x := by
  have h := (hR.mul ((hR1.mul hR1).const_sub 1)).div_const (2 * G)
  have ef : (fun x => msMass G (R x) (R1 x)) = (fun y => R y * (1 - R1 y * R1 y) / (2 * G)) := by
    funext y; simp only [msMass]; ring
  rw [ef]
  convert h using 1
  ring

/-- ハミルトン拘束 2(1 − R′² − 2RR″)/R² = 16πGρ を使うと m′ = 4πR²ρR′ -/
theorem rr_ms_constraint (G R R1 R2 ρ : ℝ) (hG : G ≠ 0) (hR : R ≠ 0)
    (ham : 2 * (1 - R1 ^ 2 - 2 * R * R2) / R ^ 2 = 16 * π * G * ρ) :
    (R1 * (1 - R1 * R1) - 2 * R * R1 * R2) / (2 * G) = 4 * π * R ^ 2 * ρ * R1 := by
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have h : 1 - R1 ^ 2 - 2 * R * R2 = 8 * π * G * ρ * R ^ 2 := by
    rw [div_eq_iff hR2] at ham
    linarith
  rw [div_eq_iff (mul_ne_zero two_ne_zero hG)]
  linear_combination R1 * h

/-- 両端が極(R = 0)の閉じた切り口では ∫₀^L m′ dx = m(L) − m(0) = 0(全エネルギー 0) -/
theorem rr_closed_total_zero {R R1 R2 : ℝ → ℝ} {G L : ℝ}
    (hR : ∀ x, HasDerivAt R (R1 x) x) (hR1 : ∀ x, HasDerivAt R1 (R2 x) x)
    (hc : Continuous fun x => (R1 x * (1 - R1 x * R1 x) - 2 * R x * R1 x * R2 x) / (2 * G))
    (h0 : R 0 = 0) (hL : R L = 0) :
    ∫ x in (0 : ℝ)..L, (R1 x * (1 - R1 x * R1 x) - 2 * R x * R1 x * R2 x) / (2 * G) = 0 := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => rr_ms_deriv (G := G) x (hR x) (hR1 x))
    (hc.intervalIntegrable _ _)]
  simp [msMass, h0, hL]

/-- 帽子 R = ℓ sin y(y = x/ℓ)、R′ = cos y の質量は ℓ sin³y/(2G)。極 y = 0 で 0、赤道で ℓ/(2G) = 首の質量 -/
theorem rr_cap_mass (G l y : ℝ) :
    msMass G (l * sin y) (cos y) = l * sin y ^ 3 / (2 * G) ∧ msMass G l 0 = l / (2 * G) := by
  constructor
  · simp only [msMass]
    rw [show 1 - cos y ^ 2 = sin y ^ 2 by linarith [sin_sq_add_cos_sq y]]
    ring
  · simp [msMass]

/-! ### α-XIII.4:共形の枠での極値球面 -/

/-- 時間対称な切り口(η = 0)で r = Ω sin χ、ds = Ω dχ。r′ = (Ω_χ sin χ + Ω cos χ)/Ω の χ 微分は、
  χ = π/2 で Ω_χ = 0(極値球面)なら (Ω_χχ − Ω)/Ω -/
theorem rr_extremal_rprime_deriv {Ω Ωc Ωcc : ℝ → ℝ}
    (hΩ : HasDerivAt Ω (Ωc (π / 2)) (π / 2)) (hΩc : HasDerivAt Ωc (Ωcc (π / 2)) (π / 2))
    (hne : Ω (π / 2) ≠ 0) (hc0 : Ωc (π / 2) = 0) :
    HasDerivAt (fun χ => (Ωc χ * sin χ + Ω χ * cos χ) / Ω χ)
      ((Ωcc (π / 2) - Ω (π / 2)) / Ω (π / 2)) (π / 2) := by
  have h := ((hΩc.mul (hasDerivAt_sin (π / 2))).add (hΩ.mul (hasDerivAt_cos (π / 2)))).div hΩ hne
  convert h using 1
  rw [sin_pi_div_two, cos_pi_div_two, hc0]
  field_simp <;> ring

/-- r″ = (dr′/dχ)/Ω = (Ω_χχ − Ω)/Ω²。χ = π/2 では cot χ = 0 なのでトレースの方程式は −Ω_ηη + Ω_χχ = Ω、
  よって r″ = Ω_ηη/Ω² -/
theorem rr_hessian_char (Ω0 Ωcc Ωηη : ℝ) (hne : Ω0 ≠ 0) (htrace : -Ωηη + Ωcc = Ω0) :
    (Ωcc - Ω0) / Ω0 / Ω0 = Ωηη / Ω0 ^ 2 := by
  rw [show Ωcc - Ω0 = Ωηη by linarith]
  field_simp <;> ring

/-- W = r′ 型のハミルトン拘束 P(r, r′, r″) = 2ℓ²r″² + 2rr″ + ℓ²(1 − r′²)²/r² − (1 − r′²) の r = ℓ、r′ = 0 での根は
  r″ = 0 と r″ = −1/ℓ だけ -/
theorem rr_two_roots (l y : ℝ) (hl : l ≠ 0) :
    2 * l ^ 2 * y ^ 2 + 2 * l * y + l ^ 2 * (1 - 0 ^ 2) ^ 2 / l ^ 2 - (1 - 0 ^ 2) = 0
      ↔ y = 0 ∨ y = -1 / l := by
  have e : 2 * l ^ 2 * y ^ 2 + 2 * l * y + l ^ 2 * (1 - 0 ^ 2) ^ 2 / l ^ 2 - (1 - 0 ^ 2)
      = 2 * l * (y * (l * y + 1)) := by
    field_simp <;> ring
  rw [e]
  have h2l : 2 * l ≠ 0 := mul_ne_zero two_ne_zero hl
  constructor
  · intro h
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2l) with h1 | h1
    · exact Or.inl h1
    · right
      rw [eq_div_iff hl]
      linear_combination h1
  · rintro (h | h)
    · rw [h]; ring
    · have : l * y + 1 = 0 := by rw [h]; field_simp <;> ring
      rw [this]; ring

/-- したがって(W = r′ 型、共形平坦、時間対称な切り口、半径 ℓ の極値球面)Ω_ηη/Ω² ∈ {0, −1/ℓ}:
  一つの Ω の中で帽子(−1/ℓ)と首(0)を連続につなぐことはできない -/
theorem rr_conformal_two_values (l Ω0 Ωcc Ωηη : ℝ) (hl : l ≠ 0) (hne : Ω0 ≠ 0)
    (htrace : -Ωηη + Ωcc = Ω0)
    (hP : 2 * l ^ 2 * ((Ωcc - Ω0) / Ω0 / Ω0) ^ 2 + 2 * l * ((Ωcc - Ω0) / Ω0 / Ω0)
      + l ^ 2 * (1 - 0 ^ 2) ^ 2 / l ^ 2 - (1 - 0 ^ 2) = 0) :
    Ωηη / Ω0 ^ 2 = 0 ∨ Ωηη / Ω0 ^ 2 = -1 / l := by
  rw [← rr_hessian_char Ω0 Ωcc Ωηη hne htrace]
  exact (rr_two_roots l _ hl).mp hP

/-! ### α-XIII.4-G(新):一般の W では r″ は離散的でない -/

/-- 極値球面(r = ℓ、r′ = 0)でのハミルトン拘束(r² をかけた形)−4rr″ + 2(1 − r′²) = 4ℓ²(W′² + (1 − W²)²/(2r²))
  から r″ = (W² − W⁴/2 − ℓ²W′²)/ℓ -/
theorem rr_general_W_rpp (l W Wp y : ℝ) (hl : 0 < l)
    (ham : -4 * l * y + 2 * (1 - 0 ^ 2) = 4 * l ^ 2 * (Wp ^ 2 + (1 - W ^ 2) ^ 2 / (2 * l ^ 2))) :
    y = (W ^ 2 - W ^ 4 / 2 - l ^ 2 * Wp ^ 2) / l := by
  have hl0 : l ≠ 0 := hl.ne'
  have e : 4 * l ^ 2 * (Wp ^ 2 + (1 - W ^ 2) ^ 2 / (2 * l ^ 2)) = 4 * l ^ 2 * Wp ^ 2 + 2 * (1 - W ^ 2) ^ 2 := by
    field_simp <;> ring
  rw [e] at ham
  rw [eq_div_iff hl0]
  linear_combination (-1 / 4 : ℝ) * ham

/-- W = 0(首の値)のとき、任意の r″ ≤ 0 は W′ を選べば実現できる(連続的な値の帯) -/
theorem rr_general_W_any (l y : ℝ) (hl : 0 < l) (hy : y ≤ 0) :
    ∃ Wp : ℝ, (0 ^ 2 - 0 ^ 4 / 2 - l ^ 2 * Wp ^ 2) / l = y := by
  refine ⟨Real.sqrt (-y / l), ?_⟩
  have hl0 : l ≠ 0 := hl.ne'
  have hnn : 0 ≤ -y / l := div_nonneg (by linarith) hl.le
  rw [Real.sq_sqrt hnn]
  field_simp <;> ring

/-! ### α-X.11:帽子の線形摂動(共形平坦な部分) -/

/-- 線形化方程式(ℓ = 1、背景 Ω = cos η、W = cos χ)。c = cos η、s = sin η、C = cos χ、S = sin χ、
  f = δΩ とその偏微分(fe = f_η など)、W = δW、We = δW_η、Wc = δW_χ。
  (A) sin χ δN₊ + 8(δW_η + δW_χ) = 0、(B) sin χ δN₋ − 8(δW_η − δW_χ) = 0、(C) sin²χ δM + 8cos χ δW = 0、
  (T) sin χ(□̂f − f) = 0 -/
def LinSol (c s C S f fe fc fee fcc fec W We Wc : ℝ) : Prop :=
  S * (6 * c * f - 2 * c * (fee + fcc + 2 * fec) - 8 * s * (fe + fc)) + 8 * (We + Wc) = 0 ∧
  S * (6 * c * f - 2 * c * (fee + fcc - 2 * fec) - 8 * s * (fe - fc)) - 8 * (We - Wc) = 0 ∧
  S ^ 2 * (2 * c * f - 2 * c * (fee - fcc) - 4 * s * fe) + 8 * C * W = 0 ∧
  (-fee + fcc - f) * S + 2 * C * fc = 0

/-- ∂_η が生む摂動:f = −sin η、δW = 0 -/
theorem rr_mode0 (c s C S : ℝ) : LinSol c s C S (-s) (-c) 0 s 0 0 0 0 0 := by
  unfold LinSol; refine ⟨by ring, by ring, by ring, by ring⟩

/-- ξ₁ = sin η cos χ ∂_η + cos η sin χ ∂_χ が生む摂動:f = cos χ cos 2η、δW = −cos η sin²χ
  (cos 2η = c² − s²、sin 2η = 2sc) -/
theorem rr_mode1 (c s C S : ℝ) :
    LinSol c s C S (C * (c ^ 2 - s ^ 2)) (-2 * C * (2 * s * c)) (-S * (c ^ 2 - s ^ 2))
      (-4 * C * (c ^ 2 - s ^ 2)) (-C * (c ^ 2 - s ^ 2)) (2 * S * (2 * s * c))
      (-c * S ^ 2) (s * S ^ 2) (-2 * c * S * C) := by
  unfold LinSol; refine ⟨by ring, by ring, by ring, by ring⟩

/-- ξ₂ = cos η cos χ ∂_η − sin η sin χ ∂_χ が生む摂動:f = −cos χ sin 2η、δW = sin η sin²χ -/
theorem rr_mode2 (c s C S : ℝ) :
    LinSol c s C S (-C * (2 * s * c)) (-2 * C * (c ^ 2 - s ^ 2)) (S * (2 * s * c))
      (4 * C * (2 * s * c)) (C * (2 * s * c)) (2 * S * (c ^ 2 - s ^ 2))
      (s * S ^ 2) (c * S ^ 2) (2 * s * S * C) := by
  unfold LinSol; refine ⟨by ring, by ring, by ring, by ring⟩

/-- (C) と (T) から代数的に決まる δW(χ を固定した η の関数)の η 微分 -/
theorem rr_dW_eta_deriv {F Fc Fe Fec Fee : ℝ → ℝ} (C S η : ℝ) (hF : HasDerivAt F (Fe η) η)
    (hFc : HasDerivAt Fc (Fec η) η) (hFe : HasDerivAt Fe (Fee η) η) :
    HasDerivAt (fun η => -(S ^ 2 / (2 * C)) * ((F η - C / S * Fc η) * cos η - Fe η * sin η))
      (-(S ^ 2 / (2 * C)) * ((Fe η - C / S * Fec η) * cos η - (F η - C / S * Fc η) * sin η
        - Fee η * sin η - Fe η * cos η)) η := by
  have h := (((hF.sub (hFc.const_mul (C / S))).mul (hasDerivAt_cos η)).sub
    (hFe.mul (hasDerivAt_sin η))).const_mul (-(S ^ 2 / (2 * C)))
  convert h using 1
  ring

/-- η 方向の可積分性:∂_η(δW) − δW_η = (sin χ sin η/(2cos χ))·L[f]、L[f] = sin χ(f_ηη + f) − 3cos χ f_χ -/
theorem rr_eta_integrability (c s C S f fe fc fee fec : ℝ) (hC : C ≠ 0) (hS : S ≠ 0) :
    -(S ^ 2 / (2 * C)) * ((fe - C / S * fec) * c - (f - C / S * fc) * s - fee * s - fe * c)
      - S / 2 * (c * fec + 2 * s * fc)
      = S * s / (2 * C) * (S * (fee + f) - 3 * C * fc) := by
  field_simp <;> ring

/-- L[f] = 0 と (T) から χ 方向の常微分方程式 f_χχ sin χ − f_χ cos χ = 0(f_χ/sin χ が χ によらない) -/
theorem rr_chi_ode (C S f fc fee fcc : ℝ) (hL : S * (fee + f) - 3 * C * fc = 0)
    (hT : (-fee + fcc - f) * S + 2 * C * fc = 0) : fcc * S - C * fc = 0 := by
  linear_combination hT + hL

/-- 振幅の変化 f = cos η は除かれる:代数的に決まる δW = −sin²χ/(2cos χ) の χ 微分は
  −sin χ − sin³χ/(2cos²χ) で、(A)(B) が要求する δW_χ = −sin χ と一致しない -/
theorem rr_cos_mode_excluded (χ : ℝ) (hC : cos χ ≠ 0) (hS : sin χ ≠ 0) :
    HasDerivAt (fun χ => -(sin χ * sin χ / (2 * cos χ))) (-sin χ - sin χ ^ 3 / (2 * cos χ ^ 2)) χ
      ∧ -sin χ - sin χ ^ 3 / (2 * cos χ ^ 2) ≠ -sin χ := by
  constructor
  · have h := (((hasDerivAt_sin χ).mul (hasDerivAt_sin χ)).div
      ((hasDerivAt_cos χ).const_mul 2) (mul_ne_zero two_ne_zero hC)).neg
    convert h using 1
    field_simp <;> ring
  · intro h
    have h3 : sin χ ^ 3 / (2 * cos χ ^ 2) = 0 := by linarith
    have : sin χ ^ 3 ≠ 0 := pow_ne_zero 3 hS
    have : 2 * cos χ ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hC)
    exact (div_ne_zero (pow_ne_zero 3 hS) this) h3

/-- f = cos η のとき (A)(B) から δW_χ = −(sin χ/4)((3f − f_ηη − f_χχ)cos η − 4f_η sin η) = −sin χ -/
theorem rr_cos_mode_Wchi (η S : ℝ) :
    -(S / 4) * ((3 * cos η - -cos η - 0) * cos η - 4 * (-sin η) * sin η) = -S := by
  linear_combination (-S) * sin_sq_add_cos_sq η

/-! ### α-XI.7:Higgs を入れた帽子 -/

/-- 共形の枠の YM 方程式 −W_ηη + W_χχ + W(1 − W²)/sin²χ に随伴 Higgs の質量項 −Ω²m²h²W が加わる
  (Higgs は共形不変でない)。W = cos χ(W_ηη = 0、W_χχ = −cos χ)では残差は −Ω²m²h² cos χ で、
  Ω m h cos χ ≠ 0 なら 0 にならない:Higgs があると帽子の解は変わる -/
theorem rr_higgs_cap_residual (Ω m h χ : ℝ) (hS : sin χ ≠ 0) :
    -0 + -cos χ + cos χ * (1 - cos χ ^ 2) / sin χ ^ 2 - Ω ^ 2 * m ^ 2 * h ^ 2 * cos χ
      = -(Ω ^ 2 * m ^ 2 * h ^ 2 * cos χ) := by
  rw [show 1 - cos χ ^ 2 = sin χ ^ 2 by linarith [sin_sq_add_cos_sq χ]]
  field_simp <;> ring

theorem rr_higgs_cap_nonzero (Ω m h χ : ℝ) (hΩ : Ω ≠ 0) (hm : m ≠ 0) (hh : h ≠ 0) (hc : cos χ ≠ 0) :
    -(Ω ^ 2 * m ^ 2 * h ^ 2 * cos χ) ≠ 0 := by
  have : Ω ^ 2 * m ^ 2 * h ^ 2 * cos χ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hΩ) (pow_ne_zero 2 hm)) (pow_ne_zero 2 hh)) hc
  exact neg_ne_zero.mpr this

/-! ### α-XI.5:dyon の首 -/

/-- AdS₂(半径 ℓ)の一様な電場 E の中の電荷 q の場の有効質量は m²ℓ² − (qEℓ²)²(外部:Pioline–Troost 2005)。
  首の W は m²ℓ² = −1(IX.15)なので、電場を加えても BF 限界 −1/4 を下回ったまま(不安定性は消えない) -/
theorem rr_dyon_bf (x : ℝ) : (-1 : ℝ) - x ^ 2 < -1 / 4 := by
  nlinarith [sq_nonneg x]

end CFT.RR
