/-
  段階 2(その 1):縮約した作用の変分から、α で使ってきた方程式をすべて導く

  球対称な計量 −N²dt² + A²(dx + β dt)² + R²dΩ² と磁気的な YM 場 W(t, x)。
  縮約した作用(角度の積分と 1/16πG を除く):
    L = L₁ − 4ℓ²[N W′²/A − A ẇ²/N + NA(1 − W²)²/(2R²)]、 ℓ² = 4πG/g²
    L₁ = 2AN + (2NR′² + 4RN′R′)/A − (2A/N)u² − (4R/N)uv、 u = Ṙ − βR′、 v = Ȧ − (Aβ)′、 ẇ = Ẇ − βW′
  L₁ は EH + GHY の一階の形(段階 1 の ghy_spherical、シフトを含む版は aux/S1/shift.py)。
  YM の項は −(1/4g²)√−g F^aF^a(球対称な磁気的配位の F² の公式)。g は ℓ² を通してだけ入る。
  * first_variation:変分 δ(dt, dx と可換な導分)について
      δL = δN·E_N + δA·E_A + δR·E_R + δβ·E_β + δW·E_W + ∂_t Θ_t + ∂_x Θ_x
    E_φ は Euler–Lagrange の式(aux/S2/gen.py が生成、形式的な恒等式として Lean で確認)。
  続き(AlphaS2_Match):同期ゲージ N = 1、β = 0 で E_φ が α の方程式(H、M、発展、YM)の可逆な一次結合になる。
-/
import CFT.AlphaIV_Propagation

namespace CFT.S2

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {S : Type*} [Field S] [CharZero S]

def Lag (dt dx : Derivation ℤ S S) (N A R b W l : S) : S := (-2) * A * N * W^(4:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + 4 * A * N * W^(2:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + (-2) * A * N * l^(2:ℕ) * R⁻¹^(2:ℕ) + 2 * A * N + (-4) * A * R * (dx R) * b * (dx b) * N⁻¹ + 4 * A * R * (dt R) * (dx b) * N⁻¹ + (-2) * A * (dx R)^(2:ℕ) * b^(2:ℕ) * N⁻¹ + 4 * A * (dx R) * (dt R) * b * N⁻¹ + (-2) * A * (dt R)^(2:ℕ) * N⁻¹ + 4 * A * (dx W)^(2:ℕ) * b^(2:ℕ) * l^(2:ℕ) * N⁻¹ + (-8) * A * (dx W) * (dt W) * b * l^(2:ℕ) * N⁻¹ + 4 * A * (dt W)^(2:ℕ) * l^(2:ℕ) * N⁻¹ + (-4) * (dx A) * R * (dx R) * b^(2:ℕ) * N⁻¹ + 4 * (dx A) * R * (dt R) * b * N⁻¹ + 4 * (dt A) * R * (dx R) * b * N⁻¹ + (-4) * (dt A) * R * (dt R) * N⁻¹ + 2 * N * (dx R)^(2:ℕ) * A⁻¹ + (-4) * N * (dx W)^(2:ℕ) * A⁻¹ * l^(2:ℕ) + 4 * (dx N) * R * (dx R) * A⁻¹

def EN (dt dx : Derivation ℤ S S) (N A R b W l : S) : S := 4 * A * R * (dx R) * b * (dx b) * N⁻¹^(2:ℕ) + (-4) * A * R * (dt R) * (dx b) * N⁻¹^(2:ℕ) + 2 * A * (dx R)^(2:ℕ) * b^(2:ℕ) * N⁻¹^(2:ℕ) + (-4) * A * (dx R) * (dt R) * b * N⁻¹^(2:ℕ) + 2 * A * (dt R)^(2:ℕ) * N⁻¹^(2:ℕ) + (-2) * A * W^(4:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + 4 * A * W^(2:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + (-4) * A * (dx W)^(2:ℕ) * b^(2:ℕ) * l^(2:ℕ) * N⁻¹^(2:ℕ) + 8 * A * (dx W) * (dt W) * b * l^(2:ℕ) * N⁻¹^(2:ℕ) + (-4) * A * (dt W)^(2:ℕ) * l^(2:ℕ) * N⁻¹^(2:ℕ) + (-2) * A * l^(2:ℕ) * R⁻¹^(2:ℕ) + 2 * A + 4 * (dx A) * R * (dx R) * A⁻¹^(2:ℕ) + 4 * (dx A) * R * (dx R) * b^(2:ℕ) * N⁻¹^(2:ℕ) + (-4) * (dx A) * R * (dt R) * b * N⁻¹^(2:ℕ) + (-4) * (dt A) * R * (dx R) * b * N⁻¹^(2:ℕ) + 4 * (dt A) * R * (dt R) * N⁻¹^(2:ℕ) + (-4) * R * (dx (dx R)) * A⁻¹ + (-2) * (dx R)^(2:ℕ) * A⁻¹ + (-4) * (dx W)^(2:ℕ) * A⁻¹ * l^(2:ℕ)

def EA (dt dx : Derivation ℤ S S) (N A R b W l : S) : S := (-2) * N * (dx R)^(2:ℕ) * A⁻¹^(2:ℕ) + (-2) * N * W^(4:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + 4 * N * W^(2:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + 4 * N * (dx W)^(2:ℕ) * A⁻¹^(2:ℕ) * l^(2:ℕ) + (-2) * N * l^(2:ℕ) * R⁻¹^(2:ℕ) + 2 * N + (-4) * (dx N) * R * (dx R) * A⁻¹^(2:ℕ) + (-4) * (dx N) * R * (dx R) * b^(2:ℕ) * N⁻¹^(2:ℕ) + 4 * (dx N) * R * (dt R) * b * N⁻¹^(2:ℕ) + 4 * (dt N) * R * (dx R) * b * N⁻¹^(2:ℕ) + (-4) * (dt N) * R * (dt R) * N⁻¹^(2:ℕ) + 4 * R * (dx R) * b * (dx b) * N⁻¹ + (-4) * R * (dx R) * (dt b) * N⁻¹ + 4 * R * (dx (dx R)) * b^(2:ℕ) * N⁻¹ + (-8) * R * (dx (dt R)) * b * N⁻¹ + 4 * R * (dt (dt R)) * N⁻¹ + 2 * (dx R)^(2:ℕ) * b^(2:ℕ) * N⁻¹ + (-4) * (dx R) * (dt R) * b * N⁻¹ + 2 * (dt R)^(2:ℕ) * N⁻¹ + 4 * (dx W)^(2:ℕ) * b^(2:ℕ) * l^(2:ℕ) * N⁻¹ + (-8) * (dx W) * (dt W) * b * l^(2:ℕ) * N⁻¹ + 4 * (dt W)^(2:ℕ) * l^(2:ℕ) * N⁻¹

def ER (dt dx : Derivation ℤ S S) (N A R b W l : S) : S := 4 * A * N * W^(4:ℕ) * l^(2:ℕ) * R⁻¹^(3:ℕ) + (-8) * A * N * W^(2:ℕ) * l^(2:ℕ) * R⁻¹^(3:ℕ) + 4 * A * N * l^(2:ℕ) * R⁻¹^(3:ℕ) + (-4) * A * (dx N) * R * b * (dx b) * N⁻¹^(2:ℕ) + (-4) * A * (dx N) * (dx R) * b^(2:ℕ) * N⁻¹^(2:ℕ) + 4 * A * (dx N) * (dt R) * b * N⁻¹^(2:ℕ) + 4 * A * (dt N) * R * (dx b) * N⁻¹^(2:ℕ) + 4 * A * (dt N) * (dx R) * b * N⁻¹^(2:ℕ) + (-4) * A * (dt N) * (dt R) * N⁻¹^(2:ℕ) + 4 * A * R * b * (dx (dx b)) * N⁻¹ + 4 * A * R * (dx b)^(2:ℕ) * N⁻¹ + (-4) * A * R * (dx (dt b)) * N⁻¹ + 8 * A * (dx R) * b * (dx b) * N⁻¹ + (-4) * A * (dx R) * (dt b) * N⁻¹ + 4 * A * (dx (dx R)) * b^(2:ℕ) * N⁻¹ + (-4) * A * (dt R) * (dx b) * N⁻¹ + (-8) * A * (dx (dt R)) * b * N⁻¹ + 4 * A * (dt (dt R)) * N⁻¹ + 4 * (dx A) * N * (dx R) * A⁻¹^(2:ℕ) + 4 * (dx A) * (dx N) * R * A⁻¹^(2:ℕ) + (-4) * (dx A) * (dx N) * R * b^(2:ℕ) * N⁻¹^(2:ℕ) + 4 * (dx A) * (dt N) * R * b * N⁻¹^(2:ℕ) + 12 * (dx A) * R * b * (dx b) * N⁻¹ + (-4) * (dx A) * R * (dt b) * N⁻¹ + 4 * (dx A) * (dx R) * b^(2:ℕ) * N⁻¹ + (-4) * (dx A) * (dt R) * b * N⁻¹ + 4 * (dx (dx A)) * R * b^(2:ℕ) * N⁻¹ + 4 * (dt A) * (dx N) * R * b * N⁻¹^(2:ℕ) + (-4) * (dt A) * (dt N) * R * N⁻¹^(2:ℕ) + (-8) * (dt A) * R * (dx b) * N⁻¹ + (-4) * (dt A) * (dx R) * b * N⁻¹ + 4 * (dt A) * (dt R) * N⁻¹ + (-8) * (dx (dt A)) * R * b * N⁻¹ + 4 * (dt (dt A)) * R * N⁻¹ + (-4) * N * (dx (dx R)) * A⁻¹ + (-4) * (dx N) * (dx R) * A⁻¹ + (-4) * (dx (dx N)) * R * A⁻¹

def Eb (dt dx : Derivation ℤ S S) (N A R b W l : S) : S := (-4) * A * (dx N) * R * (dx R) * b * N⁻¹^(2:ℕ) + 4 * A * (dx N) * R * (dt R) * N⁻¹^(2:ℕ) + 4 * A * R * (dx (dx R)) * b * N⁻¹ + (-4) * A * R * (dx (dt R)) * N⁻¹ + 8 * A * (dx W)^(2:ℕ) * b * l^(2:ℕ) * N⁻¹ + (-8) * A * (dx W) * (dt W) * l^(2:ℕ) * N⁻¹ + (-4) * (dx A) * R * (dx R) * b * N⁻¹ + 4 * (dt A) * R * (dx R) * N⁻¹

def EW (dt dx : Derivation ℤ S S) (N A R b W l : S) : S := (-8) * A * N * W^(3:ℕ) * l^(2:ℕ) * R⁻¹^(2:ℕ) + 8 * A * N * W * l^(2:ℕ) * R⁻¹^(2:ℕ) + 8 * A * (dx N) * (dx W) * b^(2:ℕ) * l^(2:ℕ) * N⁻¹^(2:ℕ) + (-8) * A * (dx N) * (dt W) * b * l^(2:ℕ) * N⁻¹^(2:ℕ) + (-8) * A * (dt N) * (dx W) * b * l^(2:ℕ) * N⁻¹^(2:ℕ) + 8 * A * (dt N) * (dt W) * l^(2:ℕ) * N⁻¹^(2:ℕ) + (-16) * A * (dx W) * b * (dx b) * l^(2:ℕ) * N⁻¹ + 8 * A * (dx W) * (dt b) * l^(2:ℕ) * N⁻¹ + (-8) * A * (dx (dx W)) * b^(2:ℕ) * l^(2:ℕ) * N⁻¹ + 8 * A * (dt W) * (dx b) * l^(2:ℕ) * N⁻¹ + 16 * A * (dx (dt W)) * b * l^(2:ℕ) * N⁻¹ + (-8) * A * (dt (dt W)) * l^(2:ℕ) * N⁻¹ + (-8) * (dx A) * N * (dx W) * A⁻¹^(2:ℕ) * l^(2:ℕ) + (-8) * (dx A) * (dx W) * b^(2:ℕ) * l^(2:ℕ) * N⁻¹ + 8 * (dx A) * (dt W) * b * l^(2:ℕ) * N⁻¹ + 8 * (dt A) * (dx W) * b * l^(2:ℕ) * N⁻¹ + (-8) * (dt A) * (dt W) * l^(2:ℕ) * N⁻¹ + 8 * N * (dx (dx W)) * A⁻¹ * l^(2:ℕ) + 8 * (dx N) * (dx W) * A⁻¹ * l^(2:ℕ)

def Tht (dt dx δ : Derivation ℤ S S) (N A R b W l : S) : S := 4 * A * R * (dx b) * (δ R) * N⁻¹ + 4 * A * (dx R) * b * (δ R) * N⁻¹ + (-4) * A * (dt R) * (δ R) * N⁻¹ + (-8) * A * (dx W) * b * (δ W) * l^(2:ℕ) * N⁻¹ + 8 * A * (dt W) * (δ W) * l^(2:ℕ) * N⁻¹ + 4 * (dx A) * R * b * (δ R) * N⁻¹ + (-4) * (dt A) * R * (δ R) * N⁻¹ + 4 * R * (dx R) * b * (δ A) * N⁻¹ + (-4) * R * (dt R) * (δ A) * N⁻¹

def Thx (dt dx δ : Derivation ℤ S S) (N A R b W l : S) : S := (-4) * A * R * (dx R) * b * (δ b) * N⁻¹ + 4 * A * R * (dt R) * (δ b) * N⁻¹ + (-4) * A * R * b * (dx b) * (δ R) * N⁻¹ + (-4) * A * (dx R) * b^(2:ℕ) * (δ R) * N⁻¹ + 4 * A * (dt R) * b * (δ R) * N⁻¹ + 8 * A * (dx W) * b^(2:ℕ) * (δ W) * l^(2:ℕ) * N⁻¹ + (-8) * A * (dt W) * b * (δ W) * l^(2:ℕ) * N⁻¹ + (-4) * (dx A) * R * b^(2:ℕ) * (δ R) * N⁻¹ + 4 * (dt A) * R * b * (δ R) * N⁻¹ + 4 * N * (dx R) * A⁻¹ * (δ R) + (-8) * N * (dx W) * A⁻¹ * (δ W) * l^(2:ℕ) + 4 * (dx N) * R * A⁻¹ * (δ R) + 4 * R * (dx R) * A⁻¹ * (δ N) + (-4) * R * (dx R) * b^(2:ℕ) * (δ A) * N⁻¹ + 4 * R * (dt R) * b * (δ A) * N⁻¹

theorem first_variation (dt dx δ : Derivation ℤ S S) (N A R b W l : S)
    (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0)
    (hc : ∀ f, dt (dx f) = dx (dt f)) (hδt : ∀ f, δ (dt f) = dt (δ f)) (hδx : ∀ f, δ (dx f) = dx (δ f))
    (hlt : dt l = 0) (hlx : dx l = 0) (hld : δ l = 0) :
    δ (Lag dt dx N A R b W l) = δ N * EN dt dx N A R b W l + δ A * EA dt dx N A R b W l
      + δ R * ER dt dx N A R b W l + δ b * Eb dt dx N A R b W l + δ W * EW dt dx N A R b W l
      + dt (Tht dt dx δ N A R b W l) + dx (Thx dt dx δ N A R b W l) := by
  simp only [Lag, EN, EA, ER, Eb, EW, Tht, Thx, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, CFT.Propagation.deriv_inv _ _ hN, CFT.Propagation.deriv_inv _ _ hA,
    CFT.Propagation.deriv_inv _ _ hR, CFT.Propagation.deriv_ofNat dt 2, CFT.Propagation.deriv_ofNat dx 2,
    CFT.Propagation.deriv_ofNat δ 2, CFT.Propagation.deriv_ofNat dt 4, CFT.Propagation.deriv_ofNat dx 4,
    CFT.Propagation.deriv_ofNat δ 4, CFT.Propagation.deriv_ofNat dt 8, CFT.Propagation.deriv_ofNat dx 8,
    CFT.Propagation.deriv_ofNat δ 8, Derivation.map_one_eq_zero, hc, hδt, hδx, hlt, hlx, hld,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

end CFT.S2
