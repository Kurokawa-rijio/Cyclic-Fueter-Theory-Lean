/-
  球対称な部分を閉じる:Dirac 場を含む整合性と、熱力学(2026-11-12)

  ■ 球対称な EYM–Dirac 系(共形ゲージ h = −2Ω du dv、ω = ln Ω)
    フェルミオンは 2 成分 a = a₁ + i a₂(右向き)、b = b₁ + i b₂(左向き)。質量は μ = W ν、ν = g_F e^{ω/2}/r。
    ラグランジアンに i(ā a_v − a ā_v) + i(b̄ b_u − b b̄_u) − 2μ B、B = 2 Re(ā b) を足す。
    運動方程式:a_v = −iμ b、b_u = −iμ a(成分で a₁_v = μ b₂、a₂_v = −μ b₁、b₁_u = μ a₂、b₂_u = −μ a₁)。
    W、r、ω の式には B の項が加わる:
      r r_uv + r_u r_v + Ω/2 = ℓ²Ω(1 − W²)²/(2r²) + μB/4、
      W_uv = ΩW(1 − W²)/(2r²) − νB/(8ℓ²)、
      ω_uv = −2r_uv/r − ℓ²Ω(1 − W²)²/r⁴ − μB/(2r²)。
    拘束:r_uu − ω_u r_u + 2ℓ²W_u²/r + τ/r = 0、τ = ½(a₂ a₁_u − a₁ a₂_u)。
  * `sc_number`:フェルミオン数の保存 ∂_v|a|² + ∂_u|b|² = 0。
  * `sc_B_u`:B_u = 2(a₁_u b₁ + a₂_u b₂)。
  * `sc_tau_v`:τ_v = (μ_u B − μ B_u)/4。
  * `sc_conservation`:この系の源は AlphaFermion.fer_constraint_prop の保存則をみたす。
    したがって、Dirac 場を含めても拘束は時間発展で保たれる。τ の係数 ½ はこの整合性から一意に決まる。
  ■ 熱力学
  * `sc_cone`、`sc_cone_flat`:地平線の近く r − r₊ = κρ²/2(κ = F′(r₊)/2)で F dτ² + dr²/F は ρ²(κ dτ)² + dρ²。
    `sc_temperature`:これが滑らかである条件 κβ = 2π から β = 4π/F′、T = F′/(4π)(温度の規則が幾何の条件になる)。
  * `sc_second_law`:見かけの地平線(r_v = 0)の上で、エネルギーの流入 B ≥ 0、外側の条件 r_uv < 0、r_u < 0 なら、
    地平線に沿った半径の変化 (B/r_uv) r_u ≥ 0(面積は減らない)。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

namespace CFT.SC

theorem sc_number (a1 a2 b1 b2 mu : ℝ) :
    2 * (a1 * (mu * b2) + a2 * (-(mu * b1))) + 2 * (b1 * (mu * a2) + b2 * (-(mu * a1))) = 0 := by
  ring

theorem sc_B_u (a1 a2 b1 b2 a1u a2u b1u b2u mu : ℝ) (h1 : b1u = mu * a2) (h2 : b2u = -(mu * a1)) :
    2 * (a1u * b1 + a1 * b1u + a2u * b2 + a2 * b2u) = 2 * (a1u * b1 + a2u * b2) := by
  rw [h1, h2]
  ring

theorem sc_tau_v (a1 a2 b1 b2 a1u a2u a1v a2v a1uv a2uv mu muu : ℝ)
    (h1 : a1v = mu * b2) (h2 : a2v = -(mu * b1))
    (h3 : a1uv = muu * b2 - mu ^ 2 * a1) (h4 : a2uv = -(muu * b1) - mu ^ 2 * a2) :
    (a2v * a1u + a2 * a1uv - a1v * a2u - a1 * a2uv) / 2
      = (muu * (2 * (a1 * b1 + a2 * b2)) - mu * (2 * (a1u * b1 + a2u * b2))) / 4 := by
  rw [h1, h2, h3, h4]
  ring

theorem sc_conservation (r ru rv Om Omu W Wu Wuv l nu B Bu tau tv muu : ℝ)
    (hr : r ≠ 0) (hO : Om ≠ 0) (hl : l ≠ 0)
    (hmuu : muu = Wu * nu + W * (nu * (Omu / Om / 2 - ru / r)))
    (hWuv : Wuv = Om * W * (1 - W ^ 2) / (2 * r ^ 2) - nu * B / (8 * l ^ 2))
    (htv : tv = (muu * B - W * nu * Bu) / 4) :
    r * (4 * l ^ 2 * Wu * Wuv / r - 2 * l ^ 2 * Wu ^ 2 * rv / r ^ 2 + tv / r - tau * rv / r ^ 2)
      + (2 * l ^ 2 * Wu ^ 2 / r + tau / r) * rv
      + (Omu * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2) - 2 * Om * l ^ 2 * W * Wu * (1 - W ^ 2) / r ^ 2
          - Om * l ^ 2 * (1 - W ^ 2) ^ 2 * ru / r ^ 3 + (muu * B + W * nu * Bu) / 4)
      - (Omu / Om) * (Om * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2) + W * nu * B / 4)
      + r * (Om * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4 + W * nu * B / (2 * r ^ 2)) * ru = 0 := by
  rw [htv, hWuv, hmuu]
  field_simp
  ring

theorem sc_cone (k ρ : ℝ) : 2 * k * (k * ρ ^ 2 / 2) = (k * ρ) ^ 2 := by ring

theorem sc_cone_flat (k ρ : ℝ) (hk : k ≠ 0) (hρ : ρ ≠ 0) :
    (k * ρ) ^ 2 / (2 * k * (k * ρ ^ 2 / 2)) = 1 := by
  rw [sc_cone]
  exact div_self (pow_ne_zero 2 (mul_ne_zero hk hρ))

theorem sc_temperature (F' : ℝ) (hF : F' ≠ 0) : F' / 2 * (4 * π / F') = 2 * π := by
  field_simp
  ring

theorem sc_second_law (B ruv ru : ℝ) (hB : 0 ≤ B) (hruv : ruv < 0) (hru : ru < 0) :
    0 ≤ B / ruv * ru := by
  have h1 : B / ruv ≤ 0 := div_nonpos_of_nonneg_of_nonpos hB hruv.le
  nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr hru.le)]

end CFT.SC
