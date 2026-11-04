/-
  独立監査(2026-11-04)の指摘を受けた補強:α-V.1(Z17、Foldy–Wouthuysen)

  監査:(i) 2 回目の変換で 1/m² までの偶の部分が変わらないことが定理になっていない、(ii) Darwin 項と
  スピン軌道項への読み替え [π_k, φ] = −i∂_kφ が形式化されていない、(iii) 静的な外場に限ることが書かれていない。
  * (i) 1 回目の後の奇の部分 X₁ = cO′(O′ は奇)に同じ Hadamard の和を当てると
        H₂ = m b + Y + c²(Y O′b − O′Y b) + c³R(`second_fw`、R は明示)。
      新しい奇の部分は c² の次数、偶の部分の変化は c³ = 1/(8m³) 以上。したがって 1/m² までの偶の部分
      β(m + O²/2m) + E − [O, [O, E]]/(8m²) は 1 回目の結果で確定する。
  * (ii) 関数の可換環 F の上の作用素 π_k f = −i∂_k f − a_k f(a_k = eA_k、i² = −1、∂_k i = 0):
        [π_k, φ] f = −i(∂_kφ) f(`comm_pi_phi`)、[π_k, [π_k, φ]] f = −(∂_k∂_kφ) f(`double_comm_pi`)、
        [π_j, π_k] f = i(∂_j a_k − ∂_k a_j) f(`comm_pi_pi`)、[[π_j, π_k], φ] = 0(`comm_comm_phi`)。
      AlphaV_FWOrder `double_comm` に入れると Σ[π_k, [π_k, φ]] = −∇²φ(Darwin 項)と
      [[π_j, π_k], φ] = 0 からスピン軌道項の形が出る。
  * (iii) 適用範囲:外場が静的(∂_tΦ = ∂_tA = 0)な場合。時間に依存する外場では −(i/8m²)[O, Ȯ] の項が加わる
      (Bjorken–Drell §4.3)。この命題はその項を含まない。
-/
import CFT.AlphaV_FWOrder
import Mathlib.RingTheory.Derivation.Basic

namespace CFT.FixFW

open CFT.FWOrder

/-! ### 2 回目の変換 -/

section Second

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable (b O Y : A) (hbb : b * b = 1) (hbO : b * O = -(O * b)) (hbY : b * Y = Y * b)

include hbb hbO hbY in
set_option maxHeartbeats 2000000 in
/-- 【α-V.1】2 回目の変換:X₁ = cO′ で H₂ = m b + Y + c²(Y O′b − O′Y b) + c³R -/
theorem second_fw (c m : ℂ) (hc : 2 * m * c = 1) :
    (m • b + c • O + Y) + ad (c • (b * (c • O))) (m • b + c • O + Y)
      + (1 / 2 : ℂ) • ad (c • (b * (c • O))) (ad (c • (b * (c • O))) (m • b + c • O + Y))
      + (1 / 6 : ℂ) • ad (c • (b * (c • O))) (ad (c • (b * (c • O)))
          (ad (c • (b * (c • O))) (m • b + c • O + Y)))
    = m • b + Y + c ^ 2 • (Y * (O * b) - O * (Y * b))
      + c ^ 3 • (O * (O * b) - (c / 2) • (O * (O * Y) - (O * (Y * O) + O * (Y * O)) + Y * (O * O))
        - (4 / 3 * c ^ 2) • (O * (O * O))
        + c ^ 3 • ((1 / 6 : ℂ) • (O * (O * (O * (Y * b)))) - (1 / 2 : ℂ) • (O * (O * (Y * (O * b))))
          + (1 / 2 : ℂ) • (O * (Y * (O * (O * b)))) - (1 / 6 : ℂ) • (Y * (O * (O * (O * b)))))
        + (-(4 / 3 : ℂ) * c ^ 4) • (O * (O * (O * (O * b))))) := by
  have hbX1 : b * (c • O) = -((c • O) * b) := by
    rw [mul_smul_comm, smul_mul_assoc, hbO, smul_neg]
  rw [fw_order2 b (c • O) Y hbb hbX1 hbY c m hc]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub, smul_add, smul_neg]
  module

end Second

/-! ### 作用素の交換子(Darwin 項とスピン軌道項) -/

section Commutators

variable {F : Type*} [CommRing F] (dd : Fin 3 → Derivation ℤ F F) (iF : F) (a : Fin 3 → F)

/-- π_k f = −i ∂_k f − a_k f -/
def piOp (k : Fin 3) (f : F) : F := -(iF * dd k f) - a k * f

/-- 【α-V.1】[π_k, φ] f = −i(∂_kφ) f -/
theorem comm_pi_phi (k : Fin 3) (φ f : F) :
    piOp dd iF a k (φ * f) - φ * piOp dd iF a k f = -(iF * dd k φ) * f := by
  simp only [piOp, Derivation.leibniz, smul_eq_mul]
  ring

/-- 【α-V.1】[π_k, [π_k, φ]] f = −(∂_k∂_kφ) f(Σ_k で −∇²φ) -/
theorem double_comm_pi (hdI : ∀ k, dd k iF = 0) (hI : iF * iF = -1) (k : Fin 3) (φ f : F) :
    piOp dd iF a k (-(iF * dd k φ) * f) - (-(iF * dd k φ)) * piOp dd iF a k f
      = -(dd k (dd k φ)) * f := by
  rw [comm_pi_phi dd iF a]
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hdI, mul_zero, add_zero]
  linear_combination (dd k (dd k φ) * f) * hI

/-- 【α-V.1】[π_j, π_k] f = i(∂_j a_k − ∂_k a_j) f(最小結合、ieB の形) -/
theorem comm_pi_pi (hdI : ∀ k, dd k iF = 0) (hcomm : ∀ j k f, dd j (dd k f) = dd k (dd j f))
    (j k : Fin 3) (f : F) :
    piOp dd iF a j (piOp dd iF a k f) - piOp dd iF a k (piOp dd iF a j f)
      = iF * (dd j (a k) - dd k (a j)) * f := by
  simp only [piOp, map_sub, map_neg, Derivation.leibniz, smul_eq_mul, hdI, mul_zero, add_zero, zero_add]
  rw [hcomm j k f]
  ring

/-- 【α-V.1】[[π_j, π_k], φ] = 0([π_j, π_k] は関数を掛けるだけ) -/
theorem comm_comm_phi (hdI : ∀ k, dd k iF = 0) (hcomm : ∀ j k f, dd j (dd k f) = dd k (dd j f))
    (j k : Fin 3) (φ f : F) :
    (piOp dd iF a j (piOp dd iF a k (φ * f)) - piOp dd iF a k (piOp dd iF a j (φ * f)))
      - φ * (piOp dd iF a j (piOp dd iF a k f) - piOp dd iF a k (piOp dd iF a j f)) = 0 := by
  rw [comm_pi_pi dd iF a hdI hcomm, comm_pi_pi dd iF a hdI hcomm]
  ring

end Commutators

end CFT.FixFW
