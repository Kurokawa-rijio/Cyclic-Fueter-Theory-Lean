/-
  球対称な EYM の理論の完成に向けて、段階 1・2(2026-11-12、G = 1 の単位)

  作用(2 次元に縮約):S = ¼∫d²x √−h { r²R_h + 2(∇r)² + 2 − 4ℓ²(∇W)² − 2ℓ²(1 − W²)²/r² }。
  共形ゲージ h = −2Ω du dv(ω = ln Ω)では、ラグランジアンは
  ¼[2r²ω_uv − 4r_u r_v + 2Ω + 8ℓ²W_u W_v − 2ℓ²Ω(1 − W²)²/r²]。
  段階 1(作用 → 運動方程式):三つの Euler–Lagrange の式は、Goursat の形の三つの方程式で 0 になる。
  * `can_el_Om_of`(ω の変分):2(r²)_uv + 2Ω − 2ℓ²Ω(1 − W²)²/r² = 0
  * `can_el_W_of`(W の変分):−16ℓ²W_uv + 8ℓ²ΩW(1 − W²)/r² = 0
  * `can_el_r_of`(r の変分):4rω_uv + 8r_uv + 4ℓ²Ω(1 − W²)²/r³ = 0
  段階 2(正準形式、h = −N²dt² + Λ²(dx + N^x dt)²):
  H = −P_r P_Λ/r + ΛP_Λ²/(2r²) + r r″/Λ − r r′Λ′/Λ² + r′²/(2Λ) − Λ/2 + H_m、H_x = P_r r′ − ΛP_Λ′ + P_W W′。
  * `can_mass_identity`:質量 M = P_Λ²/(2r) + (r/2)(1 − r′²/Λ²) は M′ = −(r′/Λ)H_g − (P_Λ/(rΛ))H_x,g をみたす。
  * `can_mass_constraint`:拘束 H = 0、H_x = 0 のもとで M′ = (r′/Λ)H_m + (P_Λ/(rΛ))P_W W′(拘束の質量の形)。
  * `can_F`:r′²/Λ² − P_Λ²/r² = 1 − 2M/r。
  * `can_ks_match`:x によらない場合、H は首の側の拘束(XV.9-K、c = ½)の 2 倍。
  Euler–Lagrange の式を作る変分の計算そのもの、正準形式の導出、拘束の代数が閉じることは外部(標準の結果)。
-/
import Mathlib.Tactic

namespace CFT.CAN

theorem can_el_Om_of (r ru rv ruv Om W l : ℝ) (hr : r ≠ 0)
    (h : ruv = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r) :
    2 * (2 * r * ruv + 2 * ru * rv) + 2 * Om - 2 * l ^ 2 * Om * (1 - W ^ 2) ^ 2 / r ^ 2 = 0 := by
  rw [h]
  field_simp
  ring

theorem can_el_W_of (r Om W Wuv l : ℝ) (h : Wuv = 2⁻¹ * Om * W * (1 - W ^ 2) / r ^ 2) :
    -16 * l ^ 2 * Wuv + 8 * l ^ 2 * Om * W * (1 - W ^ 2) / r ^ 2 = 0 := by
  rw [h]
  ring

theorem can_el_r_of (r ruv Om Omu Omv Omuv W l : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (h : Omuv = Omu * Omv / Om - 2 * Om * ruv / r - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4) :
    4 * r * (Omuv / Om - Omu * Omv / Om ^ 2) + 8 * ruv + 4 * l ^ 2 * Om * (1 - W ^ 2) ^ 2 / r ^ 3 = 0 := by
  rw [h]
  field_simp
  ring

theorem can_mass_identity (r r1 r2 L L1 PL PL1 Pr : ℝ) (hr : r ≠ 0) (hL : L ≠ 0) :
    PL * PL1 / r - PL ^ 2 * r1 / (2 * r ^ 2) + r1 / 2 * (1 - r1 ^ 2 / L ^ 2) - r * r1 * r2 / L ^ 2
        + r * r1 ^ 2 * L1 / L ^ 3
      = -(r1 / L) * (-Pr * PL / r + L * PL ^ 2 / (2 * r ^ 2) + r * r2 / L - r * r1 * L1 / L ^ 2
          + r1 ^ 2 / (2 * L) - L / 2)
        - (PL / (r * L)) * (Pr * r1 - L * PL1) := by
  field_simp
  ring

theorem can_mass_constraint (r r1 r2 L L1 PL PL1 Pr Hm PW W1 : ℝ) (hr : r ≠ 0) (hL : L ≠ 0)
    (hH : (-Pr * PL / r + L * PL ^ 2 / (2 * r ^ 2) + r * r2 / L - r * r1 * L1 / L ^ 2
          + r1 ^ 2 / (2 * L) - L / 2) + Hm = 0)
    (hHx : (Pr * r1 - L * PL1) + PW * W1 = 0) :
    PL * PL1 / r - PL ^ 2 * r1 / (2 * r ^ 2) + r1 / 2 * (1 - r1 ^ 2 / L ^ 2) - r * r1 * r2 / L ^ 2
        + r * r1 ^ 2 * L1 / L ^ 3
      = (r1 / L) * Hm + (PL / (r * L)) * (PW * W1) := by
  have idt := can_mass_identity r r1 r2 L L1 PL PL1 Pr hr hL
  linear_combination idt + (-(r1 / L)) * hH + (-(PL / (r * L))) * hHx

theorem can_F (r r1 L PL : ℝ) (hr : r ≠ 0) (hL : L ≠ 0) :
    r1 ^ 2 / L ^ 2 - PL ^ 2 / r ^ 2
      = 1 - 2 * (PL ^ 2 / (2 * r) + r / 2 * (1 - r1 ^ 2 / L ^ 2)) / r := by
  field_simp
  ring

theorem can_ks_match (a r pa pr pW W l : ℝ) (ha : a ≠ 0) (hr : r ≠ 0) (hl : l ≠ 0) :
    -pr * pa / r + a * pa ^ 2 / (2 * r ^ 2) - a / 2 + pW ^ 2 / (4 * l ^ 2 * a)
        + l ^ 2 * a * (1 - W ^ 2) ^ 2 / (2 * r ^ 2)
      = 2 * (-pa * pr / (2 * r) + a * pa ^ 2 / (4 * r ^ 2) + pW ^ 2 / (8 * l ^ 2 * a)
          - (1 / 2) ^ 2 * a * (1 - l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2)) := by
  field_simp
  ring

end CFT.CAN
