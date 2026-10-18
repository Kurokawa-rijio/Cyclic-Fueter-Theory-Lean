/-
  α-IV.1(Z1)の幾何の部分:拘束は時間発展で保たれる(拘束の伝播)

  球対称な SU(2) の Einstein–Yang–Mills、同期ゲージ(N = 1、シフト 0)。
  計量 −dt² + A²dx² + R²dΩ²、外曲率 K^x_x = Kx、K^θ_θ = KT、YM の W と P = A ∂_tW(κ = 8πG/g²)。
  関数は微分体 S の元、∂_t と ∂_x は可換な導分(滑らかな関数の芽の代数的な抽象)。D f = ∂_x f / A。
  発展方程式(入力:ADM の式と縮約した YM 方程式、AlphaII_EYM と同じ):
    ∂_t A = −A Kx、∂_t R = −R KT、∂_t W = P/A、∂_t P = ∂_x(∂_xW/A) + A W(1 − W²)/R²、
    ∂_t Kx = −2 DDR/R + K Kx − κ S_x、∂_t KT = (1 − (DR)² − R DDR)/R² + K KT − κ S_T
  拘束:
    H = ³R + 4 Kx KT + 2 KT² − 2κρ(ハミルトン拘束)
    M = 2(DR/R)(Kx − KT) − 2 D(KT) − κ j、j = −2 (P/A)(DW)/R²(運動量拘束)
  定理(sympy で見つけ、Lean で検証):
    * hamiltonian_propagation:∂_t H = 2K H − 4(DR/R) M − 2 D(M)
    * momentum_propagation:  ∂_t M = 2(Kx + KT) M − ½ D(H)
  右辺は (H, M) について線形・斉次:初期データが拘束を満たせば(H = M = 0)、この線形の系の
  解の一意性(光速で伝わる対称双曲型の系のエネルギー評価、標準)により、拘束は時間発展で保たれる。
  これは縮約 Bianchi 恒等式 ∇_μ G^{μν} = 0(幾何の半分)の球対称での具体的な形である。
  外部に残るもの:非線形な EYM 系の解の存在と一意性(Choquet-Bruhat の定理、折れ目のある初期データでは
  低い正則性の理論)と、上の線形の系の一意性のエネルギー評価。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.Propagation

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]

/-- 導分の逆元の公式 -/
theorem deriv_inv (d : Derivation ℤ S S) (a : S) (ha : a ≠ 0) : d a⁻¹ = -(a⁻¹ ^ 2 * d a) := by
  have h : d (a * a⁻¹) = 0 := by rw [mul_inv_cancel₀ ha]; exact d.map_one_eq_zero
  rw [Derivation.leibniz] at h
  simp only [smul_eq_mul] at h
  have e : d a⁻¹ = a⁻¹ * (a * d a⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [e, show a * d a⁻¹ = -(a⁻¹ * d a) by linear_combination h]
  ring

theorem deriv_ofNat (d : Derivation ℤ S S) (n : ℕ) [n.AtLeastTwo] : d (OfNat.ofNat n : S) = 0 := by
  have : (OfNat.ofNat n : S) = ((n : ℕ) : S) := (Nat.cast_eq_ofNat).symm
  rw [this]; exact d.map_natCast n

variable (dt dx : Derivation ℤ S S) (A R Kx KT W P k : S)

/-- D f = ∂_x f / A -/
def Dx (f : S) : S := A⁻¹ * dx f

def Hc : S :=
  -2 * Dx dx A (Dx dx A R) * R⁻¹ + 2 * (1 - (Dx dx A R) ^ 2 - R * Dx dx A (Dx dx A R)) * R⁻¹ ^ 2
    + 4 * Kx * KT + 2 * KT ^ 2
    - 2 * k * (((P * A⁻¹) ^ 2 + (Dx dx A W) ^ 2) * R⁻¹ ^ 2 + (1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 * 2⁻¹)

def Mc : S :=
  2 * (Dx dx A R * R⁻¹) * (Kx - KT) - 2 * Dx dx A KT - k * (-2 * (P * A⁻¹) * Dx dx A W * R⁻¹ ^ 2)

section
variable (hA : A ≠ 0) (hR : R ≠ 0)
  (hc : ∀ f, dt (dx f) = dx (dt f)) (hk1 : dt k = 0) (hk2 : dx k = 0)
  (eA : dt A = -A * Kx) (eR : dt R = -R * KT) (eW : dt W = P * A⁻¹)
  (eP : dt P = dx (dx W * A⁻¹) + A * W * (1 - W ^ 2) * R⁻¹ ^ 2)
  (eKx : dt Kx = -2 * Dx dx A (Dx dx A R) * R⁻¹ + (Kx + 2 * KT) * Kx
      - k * (((P * A⁻¹) ^ 2 + (Dx dx A W) ^ 2) * R⁻¹ ^ 2 - (1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 * 2⁻¹))
  (eKT : dt KT = (1 - (Dx dx A R) ^ 2 - R * Dx dx A (Dx dx A R)) * R⁻¹ ^ 2 + (Kx + 2 * KT) * KT
      - k * ((1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 * 2⁻¹))
include hA hR hc hk1 hk2 eA eR eW eP eKx eKT

theorem hamiltonian_propagation :
    dt (Hc dx A R Kx KT W P k) = 2 * (Kx + 2 * KT) * Hc dx A R Kx KT W P k
      - 4 * (Dx dx A R * R⁻¹) * Mc dx A R Kx KT W P k - 2 * Dx dx A (Mc dx A R Kx KT W P k) := by
  have i2 : dt (2⁻¹ : S) = 0 := by rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dt 2]; ring
  have j2 : dx (2⁻¹ : S) = 0 := by rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dx 2]; ring
  simp only [Hc, Mc, Dx, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hA, deriv_inv _ _ hR, deriv_ofNat,
    Derivation.map_one_eq_zero, hc, eA, eR, eW, eP, eKx, eKT, hk1, hk2, i2, j2,
    deriv_ofNat dt 2, deriv_ofNat dx 2, deriv_ofNat dt 4, deriv_ofNat dx 4, nsmul_eq_mul, Nat.cast_ofNat]
  have ha : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hb : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize A⁻¹ = a at ha ⊢
  generalize R⁻¹ = b at hb ⊢
  linear_combination (-4*Kx*P^2*a^2*b^2*k + 6*Kx*R*a^3*b^2*(dx (A))*(dx (R)) - 4*Kx*R*a^2*b^2*(dx (dx (R))) + 6*Kx*a^3*b*(dx (A))*(dx (R)) - 4*Kx*a^2*b^2*(dx (R))^2 - 4*Kx*a^2*b^2*(dx (W))^2*k - 4*Kx*a^2*b*(dx (dx (R))) + 4*P*W^3*a*b^4*k - 4*P*W*a*b^4*k - 2*R*a^2*b^2*(dx (Kx))*(dx (R)) - 2*a^2*b*(dx (Kx))*(dx (R))) * ha + (-4*KT*P^2*a^2*b^2*k + 4*KT*R*a^3*b^2*(dx (A))*(dx (R)) - 4*KT*R*a^2*b^2*(dx (dx (R))) - 4*KT*W^4*b^4*k + 8*KT*W^2*b^4*k - 2*KT*a^3*b*(dx (A))*(dx (R)) - 4*KT*a^2*b^2*(dx (R))^2 - 4*KT*a^2*b^2*(dx (W))^2*k + 2*KT*a^2*b*(dx (dx (R))) - 4*KT*b^4*k + 4*KT*b^2 + 4*Kx*a^3*b*(dx (A))*(dx (R)) - 4*Kx*a^2*b*(dx (dx (R))) - 2*R*a^3*b*(dx (A))*(dx (KT)) + 2*R*a^2*b*(dx (dx (KT))) - 4*a^3*(dx (A))*(dx (KT)) + 8*a^2*b*(dx (KT))*(dx (R)) - 2*a^2*b*(dx (Kx))*(dx (R)) + 4*a^2*(dx (dx (KT)))) * hb

theorem momentum_propagation :
    dt (Mc dx A R Kx KT W P k) = 2 * (Kx + KT) * Mc dx A R Kx KT W P k
      - 2⁻¹ * Dx dx A (Hc dx A R Kx KT W P k) := by
  have i2 : dt (2⁻¹ : S) = 0 := by rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dt 2]; ring
  have j2 : dx (2⁻¹ : S) = 0 := by rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dx 2]; ring
  simp only [Hc, Mc, Dx, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hA, deriv_inv _ _ hR, deriv_ofNat,
    Derivation.map_one_eq_zero, hc, eA, eR, eW, eP, eKx, eKT, hk1, hk2, i2, j2,
    deriv_ofNat dt 2, deriv_ofNat dx 2, deriv_ofNat dt 4, deriv_ofNat dx 4, nsmul_eq_mul, Nat.cast_ofNat]
  have ha : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hb : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize A⁻¹ = a at ha ⊢
  generalize R⁻¹ = b at hb ⊢
  linear_combination (-2*KT*Kx*a*b*(dx (R)) + 2*Kx^2*a*b*(dx (R)) + 4*Kx*P*a^2*b^2*(dx (W))*k - 2*Kx*a*(dx (KT)) - 2*W^3*a*b^4*(dx (W))*k + 2*W*a*b^4*(dx (W))*k) * ha + (-2*KT^2*a*b*(dx (R)) + 2*KT*Kx*a*b*(dx (R)) + 4*KT*P*a^2*b^2*(dx (W))*k + 2*KT*a*(dx (KT)) - 2*Kx*a*(dx (KT)) + 3*a^5*b*(dx (A))^2*(dx (R)) - 3*a^4*b*(dx (A))*(dx (dx (R))) - a^4*b*(dx (R))*(dx (dx (A))) + a^3*b*(dx (dx (dx (R))))) * hb

end

end CFT.Propagation
