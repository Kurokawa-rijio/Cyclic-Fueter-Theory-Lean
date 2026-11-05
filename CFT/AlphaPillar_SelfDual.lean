/-
  新しい柱 2:自己双対接続 A = Γ + iK で帽子と首を書き直す(テスト A・B、2026-11-05)

  柱 1(AlphaPillar_Polar)では、ローレンツ群 SL(2,ℂ) = 回転 × ブーストを示した。重力の Ashtekar の
  自己双対接続 A = Γ + iK(Immirzi 係数 β = i)は、この複素化 sl(2,ℂ) = su(2) ⊕ i su(2) に住む:
  Γ(空間のスピン接続)が回転(球面)の部分、K(外曲率)がブースト(双曲面)の部分。

  外部(Ashtekar 1986):自己双対の変数でのスカラー拘束は ³R + K² − K_abK^ab = 16πGρ と同値。
  左不変な形式 dσ^i = −ε^i_jk σ^j∧σ^k(AlphaII_Action `s3_spin_connection`:Γ = σ)のもとで
  A = cσ の曲率は F = (c² − 2c)·Σ_{j<k} ε σ^j∧σ^k(Maurer–Cartan)。

  テスト A(既知の方程式の再現)
  * 帽子(閉じた輻射 FRW):K^i = ȧσ^i なので c = 1 + iȧ。曲率の係数 c² − 2c = −(1 + ȧ²) は実数で
    −|c|²(`curvature_real`、`norm_c`)。Friedmann の式 1 + ȧ² = (8πG/3)ρa² ⇔ |c|² = (8πG/3)ρa²
    (`friedmann_selfdual`)。
  * 帽子の解 a = ℓ cos η では ȧ = −tan η(`cap_hubble`)、c·cos η = e^{−iη}(`phase_lemma`):
    **自己双対接続の位相は共形時間 η そのもの**。|c| = 1/cos η = ℓ/a(`cap_modulus`)。
  * 首(同期の座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²):K^z_z = −tan(t/ℓ)/ℓ(`neck_extrinsic`)、
    S² の向きは回転だけ(単極子 cos θ dφ、`spin_is_witten` で r′ = 0)、AdS₂ の向きはブーストだけ。
    比 K/Γ = −tan(t/ℓ) で、位相は t/ℓ(`phase_lemma`)。K が一つの向きだけなので K² − K_abK^ab = 0、
    拘束は ³R = 2/ℓ² = 16πGρ ⇔ ℓ² = 4πG/g²(`neck_constraint`、IX.11 と同じ)。
    **首は「回転(S²)× ブースト(AdS₂)」で、極分解が幾何として現れたもの**。
  * 時間対称な瞬間(η = 0、t = 0)では位相 0、A = Γ は実(純粋な回転 = 頂点)。終わり(帽子の崩壊
    η = π/2、首の焦点 t = πℓ/2)では位相 π/2、e^{−iπ/2} = −i で純粋なブースト(`end_phase`)。
    帽子と首は、自己双対接続の位相という同じ時計で、同時に「回転」から「ブースト」へ回り切る。
  テスト B(仮定が帰結になるか)
  * U21′(YM 場 = スピン接続、W = r′)は「YM 場 = 自己双対接続の実部(回転の部分)」と同じ
    (`real_part`)。帽子では Γ の W = r′ = cos χ は半径 a によらない(`cap_real_part`)ので、YM の解
    W = cos χ(AlphaII_EYM `frw_exact`)と**すべての時刻で**一致する。首でも W = r′ = 0 で一致する。
    ただし「YM = 自己双対接続の実部」は新しい原理(仮定)で、厳密な領域(帽子と首)では力学と矛盾しないが、
    くさびの中の一般の時間発展で保たれるかは示していない(II.1:W = r′ は三つの相でだけ保たれる)。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp

namespace CFT.SelfDual

open Complex

/-- 【柱 2】曲率の係数 c² − 2c は c = 1 + iȧ で実数 −(1 + ȧ²) -/
theorem curvature_real (ad : ℝ) :
    (1 + I * ad) ^ 2 - 2 * (1 + I * ad) = -((1 + ad ^ 2 : ℝ) : ℂ) := by
  push_cast
  linear_combination (ad : ℂ) ^ 2 * Complex.I_sq

/-- |c|² = 1 + ȧ² -/
theorem norm_c (ad : ℝ) : Complex.normSq (1 + I * ad) = 1 + ad ^ 2 := by
  simp [Complex.normSq_apply] <;> ring

/-- 【柱 2】Friedmann の式 ⇔ −(c² − 2c) = |c|² = (8πG/3)ρa² -/
theorem friedmann_selfdual (G ρ a ad : ℝ) (h : ad ^ 2 + 1 = 8 * Real.pi * G / 3 * ρ * a ^ 2) :
    -((1 + I * ad) ^ 2 - 2 * (1 + I * ad)) = ((8 * Real.pi * G / 3 * ρ * a ^ 2 : ℝ) : ℂ) ∧
    Complex.normSq (1 + I * ad) = 8 * Real.pi * G / 3 * ρ * a ^ 2 := by
  constructor
  · rw [curvature_real, neg_neg, ← h]; push_cast; ring
  · rw [norm_c]; linarith

/-- 【柱 2】位相:(1 − i tan θ)·cos θ = e^{−iθ}(帽子では θ = η、首では θ = t/ℓ) -/
theorem phase_lemma (θ : ℝ) (hc : Real.cos θ ≠ 0) :
    (1 + I * ((-(Real.sin θ / Real.cos θ) : ℝ) : ℂ)) * (Real.cos θ : ℂ) = Complex.exp (-(θ : ℂ) * I) := by
  have hc' : Complex.cos (θ : ℂ) ≠ 0 := by rw [← Complex.ofReal_cos]; exact_mod_cast hc
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  field_simp
  ring

/-- 【柱 2】帽子 a = ℓ cos η(共形時間)の宇宙時間の膨張率 ȧ = (da/dη)/a = −tan η -/
theorem cap_hubble (l η : ℝ) (hl : l ≠ 0) (hc : Real.cos η ≠ 0) :
    HasDerivAt (fun e => l * Real.cos e) (l * -Real.sin η) η ∧
    (l * -Real.sin η) / (l * Real.cos η) = -(Real.sin η / Real.cos η) := by
  refine ⟨(Real.hasDerivAt_cos η).const_mul l, ?_⟩
  rw [mul_div_mul_left _ _ hl, neg_div]

/-- 【柱 2】帽子:|c|² = 1 + tan²η = 1/cos²η = ℓ²/a²(a = ℓ cos η) -/
theorem cap_modulus (l η : ℝ) (hl : l ≠ 0) (hc : Real.cos η ≠ 0) :
    1 + (-(Real.sin η / Real.cos η)) ^ 2 = l ^ 2 / (l * Real.cos η) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq η
  have hs : Real.sin η ^ 2 = 1 - Real.cos η ^ 2 := by linarith
  rw [neg_sq, div_pow, hs]
  field_simp <;> ring

/-- 【柱 2】帽子の Friedmann の右辺:ρ = 3/(2g²a⁴)、ℓ² = 4πG/g² なら (8πG/3)ρa² = ℓ²/a² -/
theorem cap_rhs (G g l a : ℝ) (hg : g ≠ 0) (ha : a ≠ 0) (hℓ : l ^ 2 = 4 * Real.pi * G / g ^ 2) :
    8 * Real.pi * G / 3 * (3 / (2 * g ^ 2 * a ^ 4)) * a ^ 2 = l ^ 2 / a ^ 2 := by
  rw [hℓ]
  field_simp <;> ring

/-- 【柱 2】首:g_zz = cos²(t/ℓ) の外曲率 K^z_z = ½(∂_t g_zz)/g_zz = −tan(t/ℓ)/ℓ -/
theorem neck_extrinsic (l t : ℝ) (hl : l ≠ 0) (hc : Real.cos (t / l) ≠ 0) :
    HasDerivAt (fun s => Real.cos (s / l) ^ 2) (2 * Real.cos (t / l) * (-Real.sin (t / l) * (1 / l))) t ∧
    1 / 2 * (2 * Real.cos (t / l) * (-Real.sin (t / l) * (1 / l))) / Real.cos (t / l) ^ 2
      = -(Real.sin (t / l) / Real.cos (t / l)) / l := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) t := (hasDerivAt_id' t).div_const l
  refine ⟨?_, ?_⟩
  · have h := ((Real.hasDerivAt_cos (t / l)).comp t hu).pow 2
    convert h using 1
    simp only [Function.comp_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  · field_simp <;> ring

/-- 【柱 2】首の拘束:K が一つの向き(K^z_z = k)だけなら K² − K_abK^ab = 0、拘束は ³R = 16πGρ -/
theorem neck_constraint (k R3 G ρ : ℝ) :
    R3 + k ^ 2 - k ^ 2 = 16 * Real.pi * G * ρ ↔ R3 = 16 * Real.pi * G * ρ := by
  constructor <;> intro h <;> linarith

/-- 【柱 2】始まりと終わり:位相 0 で c = 1(純粋な回転 = 頂点)、位相 π/2 で e^{−iπ/2} = −i(純粋なブースト) -/
theorem end_phase : Complex.exp (-(0 : ℂ) * I) = 1 ∧ Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * I) = -I := by
  constructor
  · simp
  · rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp

/-- 【柱 2、テスト B】YM 場 = 自己双対接続の実部(回転の部分):Re(Γ + iK) = Γ -/
theorem real_part (Γ K : ℝ) : ((Γ : ℂ) + I * K).re = Γ := by
  simp

/-- 【柱 2、テスト B】帽子:r = a sin χ、ds = a dχ のスピン接続の W = r′ = cos χ は半径 a によらない。
したがって YM の解 W = cos χ と、帽子のすべての時刻で一致する -/
theorem cap_real_part (a χ : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun x => a * Real.sin x) (a * Real.cos χ) χ ∧ a * Real.cos χ / a = Real.cos χ := by
  refine ⟨(Real.hasDerivAt_sin χ).const_mul a, ?_⟩
  exact mul_div_cancel_left₀ _ ha

/-! ### 自己双対接続は v6 の質量殻と量子半球をなぞる -/

/-- 【柱 2】ȧ = −sinh ζ と書くと:|c|² = cosh²ζ(エネルギー E/m)、c/|c| = (sech ζ, −tanh ζ) は単位円の上
(量子半球 Q = (m/E, p/E))、(|c|, Im c) = (cosh ζ, −sinh ζ) は単位双曲線の上(質量殻 (E/m, p/m))。
Re c = 1(スピン接続 Γ)が質量、Im c = ȧ(外曲率 K)が運動量の役 -/
theorem mass_shell (ζ : ℝ) :
    Complex.normSq (1 + I * ((-Real.sinh ζ : ℝ) : ℂ)) = Real.cosh ζ ^ 2 ∧
    (1 / Real.cosh ζ) ^ 2 + (-Real.sinh ζ / Real.cosh ζ) ^ 2 = 1 ∧
    Real.cosh ζ ^ 2 - (-Real.sinh ζ) ^ 2 = 1 := by
  have h := Real.cosh_sq_sub_sinh_sq ζ
  have hc := (Real.cosh_pos ζ).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_c]; nlinarith [h]
  · rw [div_pow, div_pow, neg_sq, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hc)]
    nlinarith [h]
  · rw [neg_sq]; exact h

/-- 【柱 2】位相と Gudermann:tan θ = sinh ζ、cos θ > 0 なら cos θ = 1/cosh ζ(量子半球の高さ m/E)。
帽子では θ = η、ȧ = −tan η = −sinh ζ、a/ℓ = cos η = 1/cosh ζ = m/E:
帽子の一生(a = ℓ から a → 0)は、量子半球を頂点(静止)から赤道(光速)へたどることと同じ -/
theorem gudermann_phase (θ ζ : ℝ) (hc : 0 < Real.cos θ) (ht : Real.sin θ / Real.cos θ = Real.sinh ζ) :
    Real.cos θ = 1 / Real.cosh ζ := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.cosh_sq_sub_sinh_sq ζ
  have hch := Real.cosh_pos ζ
  have hs : Real.sin θ = Real.sinh ζ * Real.cos θ := by
    rw [← ht, div_mul_cancel₀ _ hc.ne']
  rw [hs] at h1
  have hsq : Real.cos θ ^ 2 * Real.cosh ζ ^ 2 = 1 := by
    linear_combination (Real.cos θ) ^ 2 * h2 + h1
  have hprod : Real.cos θ * Real.cosh ζ = 1 := by
    have hp : 0 < Real.cos θ * Real.cosh ζ := mul_pos hc hch
    nlinarith [sq_nonneg (Real.cos θ * Real.cosh ζ - 1), hsq]
  rw [eq_div_iff hch.ne']
  exact hprod

end CFT.SelfDual
