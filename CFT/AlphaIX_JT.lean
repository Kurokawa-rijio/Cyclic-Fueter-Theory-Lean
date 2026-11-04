/-
  α-IX.10〜IX.15:首の量子重力(球対称の縮約 → JT 重力、基底のエントロピー、Schwarzian、1 ループ)

  * IX.10 球対称の縮約(代数、AlphaS4_Curv の Levi-Civita の計算から)
      計量 −N²dt² + A²dx² + R²dΩ²、Φ = R²、√−g₄ = N A R² sinθ。4 次元のスカラー曲率 R₄(`rscD`)について
        N A R² R₄ = N A (Φ R₂ + 2 + (∇Φ)²/(2Φ)) − 2 Div、
      R₂ は 2 次元の計量 −N²dt² + A²dx² のスカラー曲率、(∇Φ)²/(2Φ) = 2(−Ṙ²/N² + R′²/A²)、
      Div = ∂_t(−(A/N)∂_tΦ) + ∂_x((N/A)∂_xΦ) は全微分(`reduction_identity`、`div_total`)。
      Yang–Mills の項(磁荷 1、W = 0):F^a_{μν}F^{aμν} = 2/R⁴。S² で積分すると(ℓ² = 4πG/g²)
        (1/16πG)·4π·2 − (1/4g²)·4π·Φ·(2/Φ²) = (1/4G)(2 − 2ℓ²/Φ)(`potential_from_YM`)。
      よって S₂ = (1/4G)∫√−g₂ [ΦR₂ + (∇Φ)²/(2Φ) + U(Φ)]、U = 2 − 2ℓ²/Φ(全微分は境界項として落とす)。
  * IX.11 首は厳密な解:定数 Φ のとき、Φ の方程式は R₂ + U′(Φ) = 0、計量の方程式は U(Φ) = 0。
      U(ℓ²) = 0、U′(ℓ²) = 2/ℓ² なので Φ = ℓ²、R₂ = −2/ℓ²(`neck_exact`)。
      計量 −dt² + cos²(t/ℓ)dx² は R₂ = 2ä/a = −2/ℓ²(`neck_metric_curvature`):半径 ℓ の AdS₂。
  * IX.12 JT への展開:Φ = ℓ²(1 + φ) で ΦR + U = ℓ²R + φ(ℓ²R + 2) − 2φ²/(1 + φ)(余りまで厳密、`jt_expansion`)。
      運動項は ℓ²(∇φ)²/(2(1 + φ)) で φ の 2 次(`jt_kinetic`)。
  * IX.13 基底のエントロピー S₀ = 4πℓ²/(4G) = πℓ²/G = 4π²/g²(G によらない)、インスタントンの作用 8π²/g² の半分
      (`ground_entropy`)。面積則は Bekenstein–Hawking(外部)。適用範囲:ディラトンを止めた切り詰め
      (VIII.3:弦理論のディラトンを入れると、磁荷だけの首はアトラクターでない)。
  * IX.14 Schwarzian の熱力学:log Z = S₀ + (3/2)log C − (3/2)log β + 2π²C/β から
      E = 3/(2β) + 2π²C/β²(`schwarzian_energy`)、S = log Z + βE = S₀ + 4π²CT + (3/2)log T + (3/2)(1 + log C)
      (`schwarzian_entropy`)、比熱 dE/dT = 3/2 + 4π²CT > 0(`schwarzian_heat_capacity`)。
      Z の 1 ループの形が厳密であること:Stanford–Witten 2017(外部)。
  * IX.15 1 ループの揺らぎ:W のモードは m²ℓ² = −1(AlphaII_EYM `neck_W_slope`)。Δ(Δ − 1) = m²ℓ² の根は
      Δ = ½ ± i√3/2(`delta_roots`)、実の根はない(BF 限界 −1/4 の下、`neck_W_unstable`)。
      負のモードの方向のガウス積分 ∫e^{+a x²}dx(a ≥ 0)は収束しない(`gaussian_negative_mode`):
      首は安定な量子の真空でなく、W の凝縮へ崩れる(Lee–Nair–Weinberg 1992 と一致。SU(2) の色磁場の
      Nielsen–Olesen の不安定性と同じ)。揺らぎの演算子の AdS₂ の質量への読み替えは標準。
-/
import CFT.AlphaS4_Curv
import CFT.AlphaII_EYM
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace CFT.JT

/-! ### IX.10 球対称の縮約(代数) -/

section Reduction

open CFT.S4
open CFT.Propagation (deriv_inv deriv_ofNat)

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S) (N A R s c : S)

/-- 2 次元の計量 −N²dt² + A²dx² のスカラー曲率 R₂ = (2/NA)(∂_t(Ȧ/N) − ∂_x(N′/A)) -/
def R2D : S :=
  2 * N⁻¹ * A⁻¹ * (d 0 (d 0 A) * N⁻¹ - d 0 A * d 0 N * N⁻¹ ^ 2 - d 1 (d 1 N) * A⁻¹ + d 1 N * d 1 A * A⁻¹ ^ 2)

/-- 全微分の項 Div = ∂_t(−(A/N)∂_tΦ) + ∂_x((N/A)∂_xΦ)、Φ = R²(展開した形) -/
def DivD : S :=
  -2 * (d 0 A * N⁻¹ * R * d 0 R - A * d 0 N * N⁻¹ ^ 2 * R * d 0 R + A * N⁻¹ * (d 0 R) ^ 2
      + A * N⁻¹ * R * d 0 (d 0 R))
    + 2 * (d 1 N * A⁻¹ * R * d 1 R - N * d 1 A * A⁻¹ ^ 2 * R * d 1 R + N * A⁻¹ * (d 1 R) ^ 2
      + N * A⁻¹ * R * d 1 (d 1 R))

set_option maxHeartbeats 0 in
/-- 【α-IX.10】N A R² R₄ = N A (Φ R₂ + 2 + (∇Φ)²/(2Φ)) − 2 Div(Φ = R²) -/
theorem reduction_identity (H : SphD d N A R s c) :
    N * A * R ^ 2 * Rsc d (giD N A R s) (GD d N A R s c)
      = N * A * (R ^ 2 * R2D d N A + 2 + 2 * (-(N⁻¹ ^ 2 * (d 0 R) ^ 2) + A⁻¹ ^ 2 * (d 1 R) ^ 2))
        - 2 * DivD d N A R := by
  rw [rscD d N A R s c H]
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  simp only [R2D, DivD]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((4 : S) * A * (d 0 A) * R ^ 2 * (d 0 R) * iA * iN * iR + (-4 : S) * A * (d 0 N) * R ^ 2 * (d 0 R) * iN ^ 2 * iR + (-4 : S) * A * (d 1 N) * R ^ 2 * (d 1 R) * iA ^ 2 * iR + (2 : S) * A * R ^ 2 * (d 0 R) ^ 2 * iN * iR ^ 2 + (4 : S) * A * R ^ 2 * (d 0 (d 0 R)) * iN * iR + (2 : S) * A * (d 0 R) ^ 2 * iN) * hiN + ((4 : S) * (d 0 A) * R ^ 2 * (d 0 R) * iN * iR + (4 : S) * (d 1 A) * N * R ^ 2 * (d 1 R) * iA ^ 2 * iR + (-2 : S) * N * R ^ 2 * (d 1 R) ^ 2 * iA * iR ^ 2 + (-4 : S) * N * R ^ 2 * (d 1 (d 1 R)) * iA * iR + (-2 : S) * N * (d 1 R) ^ 2 * iA + (-4 : S) * (d 1 N) * R ^ 2 * (d 1 R) * iA * iR) * hiA + ((2 : S) * A * N + (2 : S) * A * N * R * iR + (-4 : S) * A * (d 0 N) * R * (d 0 R) * iN ^ 2 + (2 : S) * A * R * (d 0 R) ^ 2 * iN * iR + (4 : S) * A * R * (d 0 (d 0 R)) * iN + (2 : S) * A * (d 0 R) ^ 2 * iN + (4 : S) * (d 0 A) * R * (d 0 R) * iN + (4 : S) * (d 1 A) * N * R * (d 1 R) * iA ^ 2 + (-2 : S) * N * R * (d 1 R) ^ 2 * iA * iR + (-4 : S) * N * R * (d 1 (d 1 R)) * iA + (-2 : S) * N * (d 1 R) ^ 2 * iA + (-4 : S) * (d 1 N) * R * (d 1 R) * iA) * hiR

/-- 【α-IX.10】Div は全微分:Div = ∂_t(−A N⁻¹ ∂_t(R²)) + ∂_x(N A⁻¹ ∂_x(R²)) -/
theorem div_total (hN : N ≠ 0) (hA : A ≠ 0) :
    DivD d N A R = d 0 (-(A * N⁻¹ * (2 * R * d 0 R))) + d 1 (N * A⁻¹ * (2 * R * d 1 R)) := by
  have e0 : d 0 N⁻¹ = -(N⁻¹ ^ 2 * d 0 N) := deriv_inv (d 0) N hN
  have e1 : d 1 A⁻¹ = -(A⁻¹ ^ 2 * d 1 A) := deriv_inv (d 1) A hA
  have t0 : d 0 (2 : S) = 0 := deriv_ofNat (d 0) 2
  have t1 : d 1 (2 : S) = 0 := deriv_ofNat (d 1) 2
  simp only [DivD, map_neg, Derivation.leibniz, smul_eq_mul, e0, e1, t0, t1]
  ring

end Reduction

open Real

/-- YM の項(磁荷 1、W):F^a_{μν}F^{aμν} の磁気の部分 = 2(1 − W²)²/R⁴、W = 0 で 2/R⁴ -/
theorem magnetic_F2 (W R s : ℝ) (hR : R ≠ 0) (hs : s ≠ 0) :
    2 * ((W ^ 2 - 1) * s) ^ 2 * (R⁻¹ ^ 2 * (R⁻¹ ^ 2 * s⁻¹ ^ 2)) = 2 * (1 - W ^ 2) ^ 2 / R ^ 4 := by
  field_simp <;> ring

/-- 【α-IX.10】ポテンシャル:(1/16πG)·4π·2 − (1/4g²)·4π·Φ·(2/Φ²) = (1/4G)(2 − 2ℓ²/Φ)(ℓ² = 4πG/g²) -/
theorem potential_from_YM (G g l Φ : ℝ) (hG : G ≠ 0) (hg : g ≠ 0) (hΦ : Φ ≠ 0)
    (hl : l ^ 2 = 4 * π * G / g ^ 2) :
    1 / (16 * π * G) * (4 * π) * 2 - 1 / (4 * g ^ 2) * (4 * π) * Φ * (2 / Φ ^ 2)
      = 1 / (4 * G) * (2 - 2 * l ^ 2 / Φ) := by
  have hπ := pi_ne_zero
  rw [hl]; field_simp <;> ring

/-! ### IX.11 首は厳密な解 -/

/-- 縮約したポテンシャル U(Φ) = 2 − 2ℓ²/Φ -/
noncomputable def U (l Φ : ℝ) : ℝ := 2 - 2 * l ^ 2 / Φ

theorem U_deriv (l Φ : ℝ) (hΦ : Φ ≠ 0) : HasDerivAt (U l) (2 * l ^ 2 / Φ ^ 2) Φ := by
  have h := ((hasDerivAt_inv hΦ).const_mul (2 * l ^ 2)).const_sub 2
  convert h using 1
  ring

/-- 【α-IX.11】定数の Φ:計量の方程式 U(Φ) = 0 と Φ の方程式 R₂ + U′(Φ) = 0 の解は Φ = ℓ²、R₂ = −2/ℓ² -/
theorem neck_exact (l Φ R2 : ℝ) (hl : l ≠ 0) (hΦ : Φ ≠ 0) (hU : U l Φ = 0)
    (hE : R2 + 2 * l ^ 2 / Φ ^ 2 = 0) : Φ = l ^ 2 ∧ R2 = -2 / l ^ 2 := by
  have h1 : Φ = l ^ 2 := by
    simp only [U] at hU
    field_simp at hU
    linarith
  refine ⟨h1, ?_⟩
  rw [h1] at hE
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have e : 2 * l ^ 2 / (l ^ 2) ^ 2 = 2 / l ^ 2 := by field_simp <;> ring
  have e2 : -2 / l ^ 2 = -(2 / l ^ 2) := by ring
  rw [e] at hE; rw [e2]; linarith

/-- 【α-IX.11】a = cos(t/ℓ):ä = −a/ℓ²、したがって R₂ = 2ä/a = −2/ℓ²(半径 ℓ の AdS₂) -/
theorem neck_metric_curvature (l t : ℝ) (hl : l ≠ 0) (hc : cos (t / l) ≠ 0) :
    HasDerivAt (fun τ => cos (τ / l)) (-(sin (t / l)) * (1 / l)) t ∧
    HasDerivAt (fun τ => -(sin (τ / l)) * (1 / l)) (-(cos (t / l)) * (1 / l) * (1 / l)) t ∧
    2 * (-(cos (t / l)) * (1 / l) * (1 / l)) / cos (t / l) = -2 / l ^ 2 := by
  have hd : HasDerivAt (fun τ : ℝ => τ / l) (1 / l) t := (hasDerivAt_id' t).div_const l
  refine ⟨?_, ?_, ?_⟩
  · exact (hasDerivAt_cos (t / l)).comp t hd
  · convert (((hasDerivAt_sin (t / l)).comp t hd).neg).mul_const (1 / l) using 1 <;> first | rfl | ring
  · field_simp <;> ring

/-! ### IX.12 JT への展開 -/

/-- 【α-IX.12】Φ = ℓ²(1 + φ):ΦR + U = ℓ²R + φ(ℓ²R + 2) − 2φ²/(1 + φ)(厳密) -/
theorem jt_expansion (l R φ : ℝ) (hl : l ≠ 0) (hφ : 1 + φ ≠ 0) :
    l ^ 2 * (1 + φ) * R + U l (l ^ 2 * (1 + φ)) = l ^ 2 * R + φ * (l ^ 2 * R + 2) - 2 * φ ^ 2 / (1 + φ) := by
  simp only [U]
  field_simp <;> ring

/-- 運動項:Φ = ℓ²(1 + φ)、∇Φ = ℓ²∇φ なら (∇Φ)²/(2Φ) = ℓ²(∇φ)²/(2(1 + φ))(φ の 2 次) -/
theorem jt_kinetic (l φ dφ : ℝ) (hl : l ≠ 0) (hφ : 1 + φ ≠ 0) :
    (l ^ 2 * dφ) ^ 2 / (2 * (l ^ 2 * (1 + φ))) = l ^ 2 * dφ ^ 2 / (2 * (1 + φ)) := by
  field_simp <;> ring

/-! ### IX.13 基底のエントロピー -/

/-- 【α-IX.13】S₀ = 4πℓ²/(4G) = πℓ²/G = 4π²/g² = ½·(8π²/g²) -/
theorem ground_entropy (G g l : ℝ) (hG : G ≠ 0) (hg : g ≠ 0) (hl : l ^ 2 = 4 * π * G / g ^ 2) :
    4 * π * l ^ 2 / (4 * G) = π * l ^ 2 / G ∧ π * l ^ 2 / G = 4 * π ^ 2 / g ^ 2 ∧
    4 * π ^ 2 / g ^ 2 = (1 / 2) * (8 * π ^ 2 / g ^ 2) := by
  refine ⟨by field_simp <;> ring, ?_, by ring⟩
  rw [hl]; field_simp <;> ring

/-! ### IX.14 Schwarzian の熱力学 -/

/-- log Z(β) = S₀ + (3/2)log C − (3/2)log β + 2π²C/β -/
noncomputable def logZ (S0 C β : ℝ) : ℝ := S0 + 3 / 2 * Real.log C - 3 / 2 * Real.log β + 2 * π ^ 2 * C / β

/-- 【α-IX.14】E = −∂_β log Z = 3/(2β) + 2π²C/β² -/
theorem schwarzian_energy (S0 C β : ℝ) (hβ : 0 < β) :
    HasDerivAt (logZ S0 C) (-(3 / (2 * β) + 2 * π ^ 2 * C / β ^ 2)) β := by
  have hb := hβ.ne'
  have h := (((Real.hasDerivAt_log hb).const_mul (3 / 2)).const_sub (S0 + 3 / 2 * Real.log C)).add
    ((hasDerivAt_inv hb).const_mul (2 * π ^ 2 * C))
  convert h using 1
  ring

/-- 【α-IX.14】S = log Z + βE = S₀ + 4π²CT + (3/2)log T + (3/2)(1 + log C)(T = 1/β) -/
theorem schwarzian_entropy (S0 C β : ℝ) (hβ : 0 < β) :
    logZ S0 C β + β * (3 / (2 * β) + 2 * π ^ 2 * C / β ^ 2)
      = S0 + 4 * π ^ 2 * C * (1 / β) + 3 / 2 * Real.log (1 / β) + 3 / 2 * (1 + Real.log C) := by
  have hb := hβ.ne'
  rw [one_div, Real.log_inv]
  simp only [logZ]
  field_simp <;> ring

/-- 【α-IX.14】比熱 dE/dT = 3/2 + 4π²CT > 0(E = (3/2)T + 2π²CT²、C > 0、T > 0) -/
theorem schwarzian_heat_capacity (C T : ℝ) (hC : 0 < C) (hT : 0 < T) :
    HasDerivAt (fun x => 3 / 2 * x + 2 * π ^ 2 * C * x ^ 2) (3 / 2 + 4 * π ^ 2 * C * T) T ∧
    0 < 3 / 2 + 4 * π ^ 2 * C * T := by
  constructor
  · have h := ((hasDerivAt_id' T).const_mul (3 / 2)).add ((hasDerivAt_pow 2 T).const_mul (2 * π ^ 2 * C))
    convert h using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  · have := pi_pos; positivity

/-! ### IX.15 1 ループの揺らぎ -/

/-- 【α-IX.15】Δ(Δ − 1) = m²ℓ² = −1 の根は Δ = ½ ± i√3/2(実の根はない) -/
theorem delta_roots :
    let Δp : ℂ := 1 / 2 + Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) / 2
    let Δm : ℂ := 1 / 2 - Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) / 2
    Δp * (Δp - 1) = -1 ∧ Δm * (Δm - 1) = -1 := by
  intro Δp Δm
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  constructor
  · simp only [Δp]; linear_combination (1 / 4 : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * hI + (-1 / 4 : ℂ) * h3
  · simp only [Δm]; linear_combination (1 / 4 : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * hI + (-1 / 4 : ℂ) * h3

/-- 【α-IX.15】W のモードは m²ℓ² = −1 で BF 限界 −1/4 の下(実の Δ はない) -/
theorem neck_mode_below_BF :
    HasDerivAt (fun W : ℝ => W * (1 - W ^ 2)) 1 0 ∧ -(1 : ℝ) < -(1 / 4) ∧
      ¬ ∃ α : ℝ, α ^ 2 - 1 * α - (-1) = 0 :=
  ⟨CFT.EYM.neck_W_slope, CFT.EYM.neck_W_unstable⟩

/-- 【α-IX.15】負のモードの方向のガウス積分は収束しない:e^{a x²}(a ≥ 0)は ℝ で可積分でない -/
theorem gaussian_negative_mode (a : ℝ) (ha : 0 ≤ a) :
    ¬ MeasureTheory.Integrable (fun x : ℝ => Real.exp (a * x ^ 2)) := by
  intro h
  have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ)) := by
    refine h.mono' MeasureTheory.aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_one]
    exact Real.one_le_exp (by positivity)
  rw [MeasureTheory.integrable_const_iff] at h1
  rcases h1 with h1 | h1
  · exact one_ne_zero h1
  · rw [Real.volume_univ] at h1
    exact lt_irrefl _ h1

end CFT.JT
