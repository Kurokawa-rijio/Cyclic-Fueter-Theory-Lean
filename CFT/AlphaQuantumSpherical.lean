/-
  理論の完成・段階 3:球対称な部分の Wheeler–DeWitt 方程式(2026-11-12、G = 1)

  量子の方程式(形式的、演算子の順序は一つ選ぶ):P → −i δ/δ(·) として Ĥ(x)Ψ[Λ, r, W] = 0、Ĥ_x(x)Ψ = 0。
  H、H_x は AlphaCanonical のもの。ここでは、この一組の拘束が既知の場合を含むことと、質量の変数での形を証明する。
  * `qs_kuchar_Lambda`、`qs_kuchar_cross`:F = r′²/Λ² − P_Λ²/r²、P_M = ΛP_Λ/(rF) とすると
    Λ² = r′²/F − F P_M²、P_Λ/(rΛ) = F P_M/Λ²。拘束の質量の形は
    M′ = [r′(P_W²/(4ℓ²) + ℓ²W′²) + F P_M P_W W′]/(r′²/F − F P_M²) + r′ℓ²(1 − W²)²/(2r²)(F ≠ 0 のところ)。
  * `qs_neck_F`:首(r′ = 0、P_Λ = 0)では F = 0。質量の変数は首の上で使えない。
  * `qs_cap_H`、`qs_cap_Hx`:帽子の形 Λ = Ω、r = Ω sin χ、W = cos χ、P_W = 0、P_Λ = −Ω_η sin²χ、P_r = −2Ω_η sin χ を
    入れると H = −(3 sin²χ/(2Ω))(Ω_η² + Ω² − ℓ²)、H_x = 0:Friedmann の拘束(Ω の振動子)になる。
    首の側は AlphaCanonical.can_ks_match。同じ一組の拘束が帽子と首の両方を含む。
  * `qs_dtheta`、`qs_dsigma`:Ψ = cos(kσ + κθ) は ∂_σ∂_θΨ = −kκΨ(kκ = 4c² で首の側の方程式の解)。
  * `qs_planewave_flat`:平面波 e^{i(kσ + κθ)} の絶対値は 1(長さの方向に一様)。
  * `qs_length_pair`:首の長さ L = a L_x と p_L = p_a/L_x は p_L L = p_a a。p_a = −2c r ṙ、c = L_x/2 なので p_L = −r ṙ。
    L と −r ṙ が共役で、ΔL·Δ(r ṙ) ≥ ħ/2(G = 1。不確定性関係そのものは外部の定理)。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

open Real

namespace CFT.QS

theorem qs_kuchar_Lambda (r r1 L PL F PM : ℝ) (hr : r ≠ 0) (hL : L ≠ 0) (hF0 : F ≠ 0)
    (hF : F = r1 ^ 2 / L ^ 2 - PL ^ 2 / r ^ 2) (hPM : PM = L * PL / (r * F)) :
    r1 ^ 2 / F - F * PM ^ 2 = L ^ 2 := by
  have h1 : r1 ^ 2 - L ^ 2 * PL ^ 2 / r ^ 2 = L ^ 2 * F := by
    rw [hF]
    field_simp
    ring
  have h2 : r1 ^ 2 / F - F * PM ^ 2 = (r1 ^ 2 - L ^ 2 * PL ^ 2 / r ^ 2) / F := by
    rw [hPM]
    field_simp
    ring
  rw [h2, h1, mul_div_assoc, div_self hF0, mul_one]

theorem qs_kuchar_cross (r L PL F PM : ℝ) (hr : r ≠ 0) (hL : L ≠ 0) (hF0 : F ≠ 0)
    (hPM : PM = L * PL / (r * F)) : PL / (r * L) = F * PM / L ^ 2 := by
  rw [hPM]
  field_simp
  ring

theorem qs_neck_F (L r : ℝ) : (0 : ℝ) ^ 2 / L ^ 2 - (0 : ℝ) ^ 2 / r ^ 2 = 0 := by simp

theorem qs_cap_H (Om Oe s l : ℝ) (hO : Om ≠ 0) (hs : s ≠ 0) (hl : l ≠ 0) :
    -(-2 * Oe * s) * (-Oe * s ^ 2) / (Om * s) + Om * (-Oe * s ^ 2) ^ 2 / (2 * (Om * s) ^ 2)
        + (Om * s) * (-(Om * s)) / Om + Om ^ 2 * (1 - s ^ 2) / (2 * Om) - Om / 2
        + l ^ 2 * s ^ 2 / Om + l ^ 2 * Om * (s ^ 2) ^ 2 / (2 * (Om * s) ^ 2)
      = -(3 * s ^ 2 / (2 * Om)) * (Oe ^ 2 + Om ^ 2 - l ^ 2) := by
  field_simp
  ring

theorem qs_cap_Hx (Om Oe s c : ℝ) :
    (-2 * Oe * s) * (Om * c) - Om * (-2 * Oe * s * c) = 0 := by ring

theorem qs_dtheta (k κ σ θ : ℝ) :
    HasDerivAt (fun θ => cos (k * σ + κ * θ)) (-κ * sin (k * σ + κ * θ)) θ := by
  have h := (((hasDerivAt_id' θ).const_mul κ).const_add (k * σ)).cos
  convert h using 1
  ring

theorem qs_dsigma (k κ σ θ : ℝ) :
    HasDerivAt (fun σ => -κ * sin (k * σ + κ * θ)) (-(k * κ) * cos (k * σ + κ * θ)) σ := by
  have h := ((((hasDerivAt_id' σ).const_mul k).add_const (κ * θ)).sin).const_mul (-κ)
  convert h using 1
  ring

theorem qs_planewave_flat (k κ σ θ : ℝ) :
    Complex.abs (Complex.exp (((k * σ + κ * θ : ℝ) : ℂ) * Complex.I)) = 1 :=
  Complex.abs_exp_ofReal_mul_I _

theorem qs_length_pair (pa a Lx : ℝ) (hLx : Lx ≠ 0) : pa / Lx * (a * Lx) = pa * a := by
  field_simp
  ring

theorem qs_length_momentum (r rd Lx : ℝ) (hLx : Lx ≠ 0) : -2 * (Lx / 2) * r * rd / Lx = -(r * rd) := by
  field_simp
  ring

end CFT.QS
