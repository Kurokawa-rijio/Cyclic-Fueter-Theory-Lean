/-
  Dirac 場を含める(4 項目)と、体積一定の条件(2026-11-12)

  ■ 帽子の上の Dirac 方程式(S³ = SU(2) の左不変な枠、等スピン 1/2、共形時間):
    D_λ = 2σ·(K + λT) + 3/2(λ = 0、1 は純ゲージ、λ = 1/2 が帽子 = スファレロン、f = 2λ − 1)。
    `fer_free_plus`、`fer_free_minus`:λ = 0 で 2j + 3/2 と −(2j + 1/2)(自由なスペクトル ±(n + 3/2))。
    `fer_hedgehog`:K = 0、スピンと等スピンの一重項で固有値 3/2 − 3λ = −(3/2)f。`fer_hedgehog_zero`:帽子でちょうど 0。
    `fer_triplet`:三重項では λ + 3/2。`fer_j_half`:j = 1/2、G = 1/2 の 2 × 2 の行列 [[0, √3], [√3, 0]] の固有値は x² = 3。
  ■ 2 次元に縮約した Dirac 場(質量 m = W/r、共形の枠で帽子は m = cot χ、首は m = 0):
    `fer_susy_factor`:(−∂ + m)(∂ + m) = −∂² + m² − m′。`fer_cap_partner`:m = cot χ なら m² + m′ = −1(相方は自由)。
    `fer_tower_d1`、`fer_tower_d2`、`fer_tower`:sin(kχ) は −ψ″ − ψ = (k² − 1)ψ。E² = k² − 1(k = 1 がゼロモード、k = 2 が ±√3)。
    `fer_zero_mode_cap`:ψ = sin χ は ψ′ = (cot χ)ψ。`fer_zero_mode_neck`:首では定数。
  ■ 首の上の指数:`fer_monopole_index` 電荷 q = 1/2 の単極子の最低の準位は j = q − 1/2 = 0、縮退度 2q = 1。
  ■ 反作用を含む整合性(物質の中身によらない):
    `fer_constraint_prop`:源 A、B、D が保存則 r B_v + B r_v + A_u − ω_u A + r D r_u = 0 をみたせば、拘束 C_u は保たれる。
    `fer_ym_conservation`:YM の源はこの保存則をみたす。
  ■ 体積一定:
    `vol_cap`:∫₀^π sin² = π/2(帽子の体積 2π²ℓ³)。`vol_total`、`vol_neck_length`:V = 2π²ℓ³ + 4πℓ²L、体積を決めると首の長さが決まる。
    `vol_static_cap`:体積を時間的に固定する乗数(宇宙定数 Λ と同じ形)では、静的な帽子は Λ = 3/(4ℓ²)、Ω² = 2ℓ²。
    `vol_no_neck`:その Λ では首の式 1/r² = Λ + ℓ²/r⁴(x = r²/ℓ² で 3x² − 4x + 4 = 0)に実の解がない。
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Real

namespace CFT.FER

theorem fer_free_plus (j : ℝ) :
    2 * ((j + 1 / 2) * (j + 3 / 2) - j * (j + 1) - 3 / 4) + 3 / 2 = 2 * j + 3 / 2 := by ring

theorem fer_free_minus (j : ℝ) :
    2 * ((j - 1 / 2) * (j + 1 / 2) - j * (j + 1) - 3 / 4) + 3 / 2 = -(2 * j + 1 / 2) := by ring

theorem fer_hedgehog (lam : ℝ) :
    2 * lam * (0 - 3 / 4 - 3 / 4) + 3 / 2 = -(3 / 2) * (2 * lam - 1) := by ring

theorem fer_hedgehog_zero : 2 * (1 / 2 : ℝ) * (0 - 3 / 4 - 3 / 4) + 3 / 2 = 0 := by norm_num

theorem fer_triplet (lam : ℝ) : 2 * lam * (2 - 3 / 4 - 3 / 4) + 3 / 2 = lam + 3 / 2 := by ring

theorem fer_j_half (x : ℝ) :
    (0 - x) * (0 - x) - Real.sqrt 3 * Real.sqrt 3 = x ^ 2 - 3 := by
  rw [Real.mul_self_sqrt (by norm_num)]
  ring

theorem fer_susy_factor (ψ ψ1 ψ2 m m1 : ℝ) :
    -(ψ2 + m1 * ψ + m * ψ1) + m * (ψ1 + m * ψ) = -ψ2 + (m ^ 2 - m1) * ψ := by ring

theorem fer_cap_partner (s c : ℝ) (hs : s ≠ 0) (hsc : s ^ 2 + c ^ 2 = 1) :
    c ^ 2 / s ^ 2 - 1 / s ^ 2 = -1 := by
  have h : c ^ 2 - 1 = -s ^ 2 := by linarith
  rw [← sub_div, h, neg_div, div_self (pow_ne_zero 2 hs)]

theorem fer_tower_d1 (k χ : ℝ) : HasDerivAt (fun χ => sin (k * χ)) (k * cos (k * χ)) χ := by
  have h := ((hasDerivAt_id' χ).const_mul k).sin
  convert h using 1
  ring

theorem fer_tower_d2 (k χ : ℝ) :
    HasDerivAt (fun χ => k * cos (k * χ)) (-(k ^ 2) * sin (k * χ)) χ := by
  have h := (((hasDerivAt_id' χ).const_mul k).cos).const_mul k
  convert h using 1
  ring

theorem fer_tower (k s : ℝ) : -(-(k ^ 2) * s) - s = (k ^ 2 - 1) * s := by ring

theorem fer_zero_mode_cap (χ : ℝ) (hs : sin χ ≠ 0) :
    HasDerivAt sin (cos χ / sin χ * sin χ) χ := by
  have e : cos χ / sin χ * sin χ = cos χ := by field_simp
  rw [e]
  exact Real.hasDerivAt_sin χ

theorem fer_zero_mode_neck (c x : ℝ) : HasDerivAt (fun _ : ℝ => c) (0 * c) x := by
  simpa using hasDerivAt_const x c

theorem fer_monopole_index : (1 / 2 : ℝ) - 1 / 2 = 0 ∧ 2 * (1 / 2 : ℝ) = 1 := by
  constructor <;> norm_num

theorem fer_constraint_prop (r ru rv ruu ruv ruuv Om Omu w wuv A Au B Bv D : ℝ) (hr : r ≠ 0)
    (h1 : r * ruv + ru * rv + Om / 2 = A)
    (h1u : 2 * ru * ruv + r * ruuv + ruu * rv + Omu / 2 = Au)
    (h3 : r * wuv + 2 * ruv + r * D = 0)
    (hC : ruu - w * ru + B = 0)
    (hw : w * Om = Omu)
    (hcons : r * Bv + B * rv + Au - w * A + r * D * ru = 0) :
    ruuv - wuv * ru - w * ruv + Bv = 0 := by
  have key : r * (ruuv - wuv * ru - w * ruv + Bv) = 0 := by
    linear_combination h1u - ru * h3 - rv * hC - w * h1 + (1 / 2) * hw + hcons
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hr
  · exact h

theorem fer_ym_conservation (r ru rv Om Omu W Wu Wuv l : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (hW : Wuv = Om * W * (1 - W ^ 2) / (2 * r ^ 2)) :
    r * (4 * l ^ 2 * Wu * Wuv / r - 2 * l ^ 2 * Wu ^ 2 * rv / r ^ 2) + (2 * l ^ 2 * Wu ^ 2 / r) * rv
      + (Omu * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2) - 2 * Om * l ^ 2 * W * Wu * (1 - W ^ 2) / r ^ 2
          - Om * l ^ 2 * (1 - W ^ 2) ^ 2 * ru / r ^ 3)
      - (Omu / Om) * (Om * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2))
      + r * (Om * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4) * ru = 0 := by
  rw [hW]
  field_simp
  ring

theorem vol_cap : ∫ x in (0 : ℝ)..π, sin x ^ 2 = π / 2 := by
  rw [integral_sin_sq]
  simp

theorem vol_total (l L : ℝ) :
    4 * π * l ^ 3 * (π / 2) + 4 * π * l ^ 2 * L = 2 * π ^ 2 * l ^ 3 + 4 * π * l ^ 2 * L := by ring

theorem vol_neck_length (V l : ℝ) (hl : l ≠ 0) :
    2 * π ^ 2 * l ^ 3 + 4 * π * l ^ 2 * ((V - 2 * π ^ 2 * l ^ 3) / (4 * π * l ^ 2)) = V := by
  have hp := Real.pi_ne_zero
  field_simp <;> ring

theorem vol_static_cap (l : ℝ) (hl : l ≠ 0) :
    2 * l ^ 2 = l ^ 2 + (3 / (4 * l ^ 2)) / 3 * (2 * l ^ 2) ^ 2
      ∧ (2 : ℝ) = 4 * (3 / (4 * l ^ 2)) / 3 * (2 * l ^ 2) := by
  constructor <;> field_simp <;> ring

theorem vol_no_neck (x : ℝ) : 0 < 3 * x ^ 2 - 4 * x + 4 := by
  nlinarith [sq_nonneg (3 * x - 2)]

end CFT.FER
