/-
  α-VII.1 (Z24) の補強:χ と c₁ をつなぐ写像(S² の接束 = |N| = 2 の単極子の束)

  AlphaVII_Bundle は、遷移関数 e^{iNφ} の一価性 ⇔ N ∈ ℤ(`dirac_quantization`)、
  c₁ = (1/2π)∫ f = N(`chern_number`)、Gauss–Bonnet ∫K dA = 4π = 2πχ(S²)(`gauss_bonnet_round`)を示した。
  欠けていたのは「接束の c₁ = χ」という同一視の写像で、ここでそれを遷移関数の計算として与える。

  * S² を北の複素座標 z(z = ∞ を除く)と南の座標 w = 1/z で覆う。接束の局所的な枠は ∂_z と ∂_w で、
    ∂_z = (dw/dz) ∂_w、dw/dz = −z⁻²(`chart_derivative`)。
  * 赤道 z = e^{iφ} で、遷移関数は −e^{−2iφ} = e^{i(π − 2φ)}(`transition_on_equator`)。
    位相 π − 2φ は φ ↦ φ + 2π で −4π だけ回る:回転数 −2(`transition_winding`)。
    定数の位相 e^{iπ} は大域的な枠の取り替えで消せるので、接束は |N| = 2 の単極子の束と同型。
  * S² 上の複素線束は遷移関数の回転数で分類される(clutching の構成、π₁(U(1)) = ℤ。外部定理)。
    向き付けた実 2 次元束の Euler 類は、複素線束としての c₁ に等しい(Milnor–Stasheff 命題 14.? 、外部定理)。
    向きを複素構造に合わせると c₁(TS²) = 2。
  * 一方 Gauss–Bonnet から χ(S²) = (1/2π)∫K dA = 2(`euler_char_two`)。単極子の束の c₁ も N = 2 で 2
    (`tangent_chern`)。両者が一致する:c₁(TS²) = χ(S²) = 2。
  * 応用:スピン束 S⁺ は TS² の平方根なので c₁(S⁺) = χ/2、ひねりの電荷 q = c₁/2 = χ/4(α-VII.9)。
-/
import CFT.AlphaVII_Bundle

open Real

namespace CFT.Tangent

/-- 座標の取り替え w = 1/z の微分は −z⁻² -/
theorem chart_derivative (z : ℂ) (hz : z ≠ 0) : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z :=
  hasDerivAt_inv hz

/-- 【α-VII.1 Z24】赤道 z = e^{iφ} での接束の遷移関数:−(e^{iφ})⁻² = e^{i(π − 2φ)} -/
theorem transition_on_equator (φ : ℝ) :
    -((Complex.exp (φ * Complex.I)) ^ 2)⁻¹ = Complex.exp (((π - 2 * φ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  have e : (((π - 2 * φ : ℝ) : ℂ) * Complex.I)
      = -(((2 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I)) + (π : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- 位相 θ(φ) = π − 2φ は一周 φ ↦ φ + 2π で −2·(2π) 回る(回転数 −2) -/
theorem transition_winding (φ : ℝ) : (π - 2 * (φ + 2 * π)) - (π - 2 * φ) = -2 * (2 * π) := by
  ring

/-- 回転数 2 の束の遷移関数 e^{2iφ} は一価(N = 2 ∈ ℤ) -/
theorem tangent_single_valued : Complex.exp (Complex.I * ((2 : ℝ) : ℂ) * (2 * π)) = 1 :=
  (CFT.Bundle.dirac_quantization 2).mpr ⟨2, by norm_num⟩

/-- N = 2 の単極子の束の c₁ は 2 -/
theorem tangent_chern :
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (2 : ℝ) / 2 * Real.sin θ) = 2 :=
  CFT.Bundle.chern_number 2

/-- Gauss–Bonnet から χ(S²) = (1/2π)∫K dA = 2 -/
theorem euler_char_two (r : ℝ) (hr : r ≠ 0) :
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (1 / r ^ 2) * (r ^ 2 * Real.sin θ)) = 2 := by
  rw [CFT.Bundle.gauss_bonnet_round r hr]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp <;> ring

/-- 【α-VII.1 Z24】c₁(TS²) = χ(S²):|N| = 2 の単極子の束の c₁ と Gauss–Bonnet の χ が一致 -/
theorem chern_eq_euler (r : ℝ) (hr : r ≠ 0) :
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (2 : ℝ) / 2 * Real.sin θ)
      = (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (1 / r ^ 2) * (r ^ 2 * Real.sin θ)) := by
  rw [tangent_chern, euler_char_two r hr]

end CFT.Tangent
