/-
  α-IV.12 (Z13) の補強:縮約作用の境界項・規格化・Legendre 変換の正則性・超計量

  `AlphaIV_Minisuperspace` の `reduced_density` は
    √−g (R − ℓ² F̂²) = s · { 2 L₀ + 2 ∂_t(ȧ b²/N) + 4 ∂_t(a b ḃ/N) }
  を示した(L₀ = −(a ḃ² + 2 b ȧ ḃ)/N + N a (1 − ℓ²/b²))。ここでは次を加える。

  1. 境界項(Gibbons–Hawking–York):t = 一定 の面の外向きでない単位法線 n^μ = (1/N, 0, 0, 0)、
     外的曲率 K = ∇_μ n^μ = (ȧ/a + 2ḃ/b)/N(`kext_divergence`:発散の公式と一致)、
     誘導計量の体積要素 √h = a b² s。全微分の項はちょうど ∂_t(2√h K)(`ghy_boundary`)。
     したがって、空間的な境界での GHY 項 −2∮√h K(時間的な向きの規約 ε = −1)を加えた作用の密度は
       √−g (R − ℓ² F̂²) − ∂_t(2 √h K) = 2 s L₀            (`action_with_ghy`)
     で、全微分を「捨てる」のではなく、境界項で厳密に打ち消す(Gibbons–Hawking 1977、York 1972)。
  2. 規格化:作用 (1/16πG)∫√−g(…) を角度(∫₀^π sin θ dθ = 2、∫₀^{2π} dφ = 2π)と x(座標の長さ L_x)
     で積分すると、縮約 Lagrangian の係数は c = L_x/(2G)(`reduced_coefficient`)。
  3. Legendre 変換の正則性:速度から運動量への写像の行列式(速度の Hessian)は −4c²b²/N² ≠ 0
     (`legendre_hessian`、`legendre_hessian_ne`)。逆写像は
       ḃ = −N p_a/(2cb)、ȧ = (N/2c)(a p_a/b² − p_b/b)        (`legendre_inverse`、`legendre_onto`)
  4. 超計量:L の運動項 = (1/2N) G_AB q̇^A q̇^B、G = [[0, −2cb], [−2cb, −2ca]]、
     逆行列 G^{-1} = [[a/(2cb²), −1/(2cb)], [−1/(2cb), 0]](`supermetric_kinetic`、`supermetric_inverse`)、
     Hfun の運動量の項 = ½ G^{AB} p_A p_B(`hamiltonian_supermetric`)。
     Laplace–Beltrami 作用素 Δ_G f = G^{AB}∂_A∂_B f + v^A ∂_A f の 1 階の係数
     v^A = (1/√|G|)∂_B(√|G| G^{BA})(√|G| = 2cb)は v^a = 1/(2cb²)、v^b = 0
     (`lb_coeff_a`、`lb_coeff_b`)。b² · (−ħ²/2)Δ_G は AlphaIV_WKB2 の `wdwOpLB` の運動項と一致
     (`lb_operator`)。2 次元では Δ_{Ω²G} = Ω⁻² Δ_G なので、拘束を b² 倍しても Laplace–Beltrami の順序は保たれる。
  拘束の構造:L は Ṅ を含まないので p_N = 0(一次拘束)。その保存が ∂L/∂N = −Hfun = 0(二次拘束、
  `L_N`)。Hfun = 0 は一つだけの拘束なので第一類。
-/
import CFT.AlphaIV_Minisuperspace

namespace CFT.Reduction

open CFT.S4 CFT.Mini

section Boundary

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- t = 一定 の面の外的曲率 K = (ȧ/a + 2ḃ/b)/N -/
def Kext (N a b : S) : S := N⁻¹ * (d 0 a * a⁻¹ + 2 * d 0 b * b⁻¹)

/-- K は発散の公式 ∇_μ n^μ = (1/√−g) ∂_t(√−g n^t) と一致(√−g = N a b² s、n^t = 1/N、∂_t s = 0) -/
theorem kext_divergence (N a b s : S) (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hs0 : d 0 s = 0) :
    (N * a * b ^ 2 * s)⁻¹ * d 0 (N * a * b ^ 2 * s * N⁻¹) = Kext d N a b := by
  have e : N * a * b ^ 2 * s * N⁻¹ = a * b ^ 2 * s := by
    rw [show N * a * b ^ 2 * s * N⁻¹ = (a * b ^ 2 * s) * (N * N⁻¹) by ring, mul_inv_cancel₀ hN,
      mul_one]
  rw [e]
  simp only [Kext, Derivation.leibniz, Derivation.leibniz_pow, hs0, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero, zero_add, add_zero]
  field_simp <;> ring

/-- 境界項:密度の全微分の部分 = ∂_t(2 √h K)/1(√h = a b² s) -/
theorem ghy_boundary (N a b s : S) (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hs0 : d 0 s = 0) :
    s * (2 * d 0 (d 0 a * b ^ 2 * N⁻¹) + 4 * d 0 (a * b * d 0 b * N⁻¹))
      = 2 * d 0 (a * b ^ 2 * s * Kext d N a b) := by
  have e : a * b ^ 2 * s * Kext d N a b
      = s * (d 0 a * b ^ 2 * N⁻¹ + a * b * d 0 b * N⁻¹ + a * b * d 0 b * N⁻¹) := by
    simp only [Kext]
    field_simp <;> ring
  rw [e]
  conv_rhs => rw [Derivation.leibniz, hs0]
  simp only [smul_eq_mul, mul_zero, add_zero, map_add]
  ring

set_option maxHeartbeats 4000000 in
/-- 【α-IV.12】GHY の境界項を加えた作用の密度は 2 s L₀ に等しい(全微分は境界項で厳密に消える) -/
theorem action_with_ghy (N a b s c l : S) (H : SphD d N a b s c)
    (hN1 : d 1 N = 0) (ha1 : d 1 a = 0) (hb1 : d 1 b = 0) :
    N * a * b ^ 2 * s * (Rsc d (giD N a b s) (GD d N a b s c) - l ^ 2 * Fsq (giD N a b s) (FT d 0 s))
      - 2 * d 0 (a * b ^ 2 * s * Kext d N a b)
      = s * (2 * (-(a * d 0 b ^ 2 + 2 * b * d 0 a * d 0 b) * N⁻¹ + N * a * (1 - l ^ 2 * b⁻¹ ^ 2))) := by
  rw [reduced_density d N a b s c l H hN1 ha1 hb1, ← ghy_boundary d N a b s H.hN H.hA H.hR H.s0]
  ring

end Boundary

section Real

open Real

/-- ∫₀^π sin θ dθ = 2 -/
theorem angular_integral : ∫ θ in (0 : ℝ)..π, Real.sin θ = 2 := by
  rw [integral_sin, Real.cos_zero, Real.cos_pi]
  norm_num

/-- 【α-IV.12】規格化:(1/16πG) · L_x · 2π · ∫₀^π 2 sin θ dθ = L_x/(2G)。縮約 Lagrangian の係数は c = L_x/(2G) -/
theorem reduced_coefficient (G Lx : ℝ) (hG : G ≠ 0) :
    1 / (16 * π * G) * (Lx * (2 * π * ∫ θ in (0 : ℝ)..π, 2 * Real.sin θ)) = Lx / (2 * G) := by
  rw [intervalIntegral.integral_const_mul, angular_integral]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp <;> ring

/-- 速度 (ȧ, ḃ) から運動量 (p_a, p_b) への写像の行列(速度の Hessian ∂²L/∂q̇∂q̇)の行列式 -/
theorem legendre_hessian (a b N c : ℝ) :
    Matrix.det !![(0 : ℝ), -2 * c * b / N; -2 * c * b / N, -2 * c * a / N]
      = -(4 * c ^ 2 * b ^ 2 / N ^ 2) := by
  rw [Matrix.det_fin_two_of]
  ring

/-- 【α-IV.12】N b c ≠ 0 なら Hessian は正則(Legendre 変換は可逆) -/
theorem legendre_hessian_ne (a b N c : ℝ) (hN : N ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Matrix.det !![(0 : ℝ), -2 * c * b / N; -2 * c * b / N, -2 * c * a / N] ≠ 0 := by
  rw [legendre_hessian, neg_ne_zero]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero four_ne_zero (pow_ne_zero 2 hc)) (pow_ne_zero 2 hb))
    (pow_ne_zero 2 hN)

/-- 逆写像(左逆):運動量 p_a = −2cbḃ/N、p_b = −2c(aḃ + bȧ)/N から速度が戻る -/
theorem legendre_inverse (a b N c ad bd : ℝ) (hN : N ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    bd = -(N * (-2 * c * b * bd / N)) / (2 * c * b) ∧
    ad = N / (2 * c) * (a * (-2 * c * b * bd / N) / b ^ 2 - (-2 * c * (a * bd + b * ad) / N) / b) := by
  constructor <;> field_simp <;> ring

/-- 逆写像(右逆):任意の (p_a, p_b) はある速度の像(Legendre 写像は全単射) -/
theorem legendre_onto (a b N c pa pb : ℝ) (hN : N ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    -2 * c * b * (-(N * pa) / (2 * c * b)) / N = pa ∧
    -2 * c * (a * (-(N * pa) / (2 * c * b)) + b * (N / (2 * c) * (a * pa / b ^ 2 - pb / b))) / N
      = pb := by
  constructor <;> field_simp <;> ring

/-- 超計量:L の運動項 −c(aḃ² + 2bȧḃ)/N = (1/2N) G_AB q̇^A q̇^B、G = [[0, −2cb], [−2cb, −2ca]] -/
theorem supermetric_kinetic (a b c ad bd N : ℝ) (hN : N ≠ 0) :
    -c * (a * bd ^ 2 + 2 * b * ad * bd) / N
      = 1 / (2 * N) * (2 * (-2 * c * b) * ad * bd + (-2 * c * a) * bd ^ 2) := by
  field_simp <;> ring

/-- 逆超計量 G^{AB} -/
theorem supermetric_inverse (a b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    !![(0 : ℝ), -2 * c * b; -2 * c * b, -2 * c * a]
      * !![a / (2 * c * b ^ 2), -1 / (2 * c * b); -1 / (2 * c * b), 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Hfun の運動量の項 (a p_a² − 2b p_a p_b)/(4cb²) = ½ G^{AB} p_A p_B -/
theorem hamiltonian_supermetric (a b c pa pb : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    1 / 2 * (a / (2 * c * b ^ 2) * pa ^ 2 + 2 * (-1 / (2 * c * b)) * pa * pb)
      = (a * pa ^ 2 - 2 * b * pa * pb) / (4 * c * b ^ 2) := by
  field_simp <;> ring

/-- Laplace–Beltrami の 1 階の係数(a 成分):∂_a(√G G^{aa}) = ∂_a(2cb · a/(2cb²)) = 1/b、
したがって v^a = (1/b)/(2cb) = 1/(2cb²)(∂_b(√G G^{ba}) = 0 は `lb_coeff_b`) -/
theorem lb_coeff_a (a b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun x => 2 * c * b * (x / (2 * c * b ^ 2))) (1 / b) a := by
  have h := ((hasDerivAt_id a).div_const (2 * c * b ^ 2)).const_mul (2 * c * b)
  exact h.congr_deriv (by field_simp <;> ring)

/-- √G G^{ab} = 2cb · (−1/(2cb)) = −1 は b について一定:∂_b(√G G^{ab}) = 0、また G^{bb} = 0。
したがって v^b = 0 -/
theorem lb_coeff_b (b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun y => 2 * c * y * (-1 / (2 * c * y))) 0 b := by
  apply (hasDerivAt_const b (-1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hb] with y hy
  field_simp

/-- 【α-VI.4 の順序】b² · (−ħ²/2) Δ_G Ψ を展開すると、運動項は (1/4c)(−ħ²(a Ψ_aa + Ψ_a) + 2ħ² b Ψ_ab)
(Δ_G = G^{aa}∂_a² + 2G^{ab}∂_a∂_b + G^{bb}∂_b² + v^a ∂_a + v^b ∂_b、G^{bb} = v^b = 0) -/
theorem lb_operator (hb a b c : ℂ) (Ψa Ψaa Ψab Ψbb Ψb : ℂ) (hb0 : b ≠ 0) (hc : c ≠ 0) :
    b ^ 2 * (-(hb ^ 2) / 2) * (a / (2 * c * b ^ 2) * Ψaa + 2 * (-1 / (2 * c * b)) * Ψab + 0 * Ψbb
      + 1 / (2 * c * b ^ 2) * Ψa + 0 * Ψb)
      = (1 / (4 * c)) * (-hb ^ 2 * a * Ψaa + 2 * hb ^ 2 * b * Ψab) - (1 / (4 * c)) * hb ^ 2 * Ψa := by
  have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
  linear_combination (-(hb ^ 2 * c⁻¹ / 4) * ((a * Ψaa + Ψa) * (b * b⁻¹ + 1) - 2 * b * Ψab)) * hbb

end Real

end CFT.Reduction
