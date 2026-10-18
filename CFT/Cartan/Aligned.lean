/-
  α-II.6(Z4-E)⊘:整列型の C2 解は存在しない

  仮定:C2(Cartan/C2.lean)に加えて、固有値の勾配が e₀ 方向:e₁λᵢ = e₂λᵢ = 0、
  かつ e₀λ₀ は単元(固有値が U 上で実際に変化する)。
  証明の流れ:
    1. 1 段目の式(C2.pD10, pD20)から β = γ = 0(b = c = 0)、pD00 から α は単元
    2. 捩れの式 [e₁,e₂]λ₂ から α·η = 0、よって η = 0(h = 0)
    3. 曲率の式 R(e₀,e₁)e₁、R(e₀,e₂)e₂、R(e₁,e₂)e₂ から e₀α と α² を消去すると、固有値だけの関係
       g(λ) = 2λ₀³ − 5λ₀²λ₁ − 5λ₀²λ₂ + 6λ₀λ₁² + 2λ₀λ₁λ₂ + 6λ₀λ₂² − 3λ₁³ − 3λ₂³ = 0
    4. g = 0 は環の元としての等式なので e₀ を作用させてよい:e₀g = α·G₁ から G₁ = 0、同様に G₂ = 0
    5. 証明書 ((λ₀−λ₁)(λ₀−λ₂)(λ₁−λ₂))³ = c₀g + c₁G₁ + c₂G₂ で矛盾
  (z4_aligned.py, z4_aligned2.py の Gröbner 計算 {1} を、短い明示的な消去に置き換えたもの。)
-/
import CFT.Cartan.C2

namespace CFT.Cartan

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {R : Type*} [CommRing R] [Algebra ℚ R]

namespace C2

variable {F : Frame R} {lam : Fin 3 → R} (H : C2 F lam)
include H

/-- 単元の積は単元 -/
theorem unit_x : IsUnit ((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2)) :=
  (H.u01.mul H.u02).mul H.u12

/-- α-II.6(Z4-E)⊘:整列型(固有値の勾配が e₀ 方向で消えない、e₁λ = e₂λ = 0)の C2 解は存在しない -/
theorem aligned_impossible [Nontrivial R] (h1 : ∀ i, F.e 1 (lam i) = 0) (h2 : ∀ i, F.e 2 (lam i) = 0)
    (h0 : IsUnit (F.e 0 (lam 0))) : False := by
  -- 1. β = γ = 0(b = c = 0)
  have hbe : beta F lam = 0 := by
    have e := H.pD10; rw [h1 0] at e
    have e' : beta F lam * ((lam 0 - lam 1) * (lam 1 - lam 2) ^ 2) = 0 := by linear_combination e
    exact (H.u01.mul (H.u12.pow 2)).mul_left_eq_zero.mp e'
  have hga : gamma F lam = 0 := by
    have e := H.pD20; rw [h2 0] at e
    have e' : gamma F lam * ((lam 0 - lam 2) * (lam 1 - lam 2) ^ 2) = 0 := by linear_combination -e
    exact (H.u02.mul (H.u12.pow 2)).mul_left_eq_zero.mp e'
  -- 2. α は単元
  have hal : IsUnit (alpha F lam) := by
    have e : F.e 0 (lam 0) = alpha F lam * (-((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2))) := by
      rw [H.pD00]; ring
    rw [e] at h0; exact isUnit_of_mul_isUnit_left h0
  -- 3. η = 0(h = 0):捩れの式 [e₁,e₂]λ₂
  have het : eta F lam = 0 := by
    have e := H.T212
    simp only [hbe, hga, map_zero] at e
    have e' : alpha F lam * eta F lam * ((lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) * (lam 1 - lam 2) ^ 2) = 0 := by
      linear_combination -e
    have hu : IsUnit ((lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) * (lam 1 - lam 2) ^ 2) :=
      ((H.u01.pow 2).mul H.u02).mul (H.u12.pow 2)
    exact hal.mul_right_eq_zero.mp (hu.mul_left_eq_zero.mp e')
  -- 4. 固有値だけの関係 g(λ) = 0
  have hg : (((-3) * ((lam 1) * (lam 1) * (lam 1))) + ((-3) * ((lam 2) * (lam 2) * (lam 2))) + (2 * ((lam 0) * (lam 0) * (lam 0))) + ((-5) * (lam 1) * ((lam 0) * (lam 0))) + ((-5) * (lam 2) * ((lam 0) * (lam 0))) + (6 * (lam 0) * ((lam 1) * (lam 1))) + (6 * (lam 0) * ((lam 2) * (lam 2))) + (2 * (lam 0) * (lam 1) * (lam 2))) = 0 := by
    have e0 := H.S0101; have e4 := H.S0202; have e8 := H.S1212
    simp only [hbe, hga, het, map_zero] at e0 e4 e8
    have e' : ((1 : ℕ) : R) * (lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) ^ 2 * (((-3) * ((lam 1) * (lam 1) * (lam 1))) + ((-3) * ((lam 2) * (lam 2) * (lam 2))) + (2 * ((lam 0) * (lam 0) * (lam 0))) + ((-5) * (lam 1) * ((lam 0) * (lam 0))) + ((-5) * (lam 2) * ((lam 0) * (lam 0))) + (6 * (lam 0) * ((lam 1) * (lam 1))) + (6 * (lam 0) * ((lam 2) * (lam 2))) + (2 * (lam 0) * (lam 1) * (lam 2))) = 0 := by
      push_cast
      linear_combination ((((lam 0)^6) + (((lam 0)^2) * ((lam 1)^4)) + (((lam 0)^4) * ((lam 2)^2)) + (((lam 1)^4) * ((lam 2)^2)) + ((-4) * (lam 1) * ((lam 0)^5)) + ((-4) * ((lam 0)^3) * ((lam 1)^3)) + ((-2) * (lam 2) * ((lam 0)^5)) + (6 * ((lam 0)^4) * ((lam 1)^2)) + ((-12) * (lam 2) * ((lam 0)^3) * ((lam 1)^2)) + ((-4) * (lam 0) * ((lam 1)^3) * ((lam 2)^2)) + ((-4) * (lam 1) * ((lam 0)^3) * ((lam 2)^2)) + ((-2) * (lam 0) * (lam 2) * ((lam 1)^4)) + (6 * ((lam 0)^2) * ((lam 1)^2) * ((lam 2)^2)) + (8 * (lam 1) * (lam 2) * ((lam 0)^4)) + (8 * (lam 2) * ((lam 0)^2) * ((lam 1)^3)))) * e0 + ((((lam 0)^6) + (((lam 0)^2) * ((lam 2)^4)) + (((lam 0)^4) * ((lam 1)^2)) + (((lam 1)^2) * ((lam 2)^4)) + ((-4) * (lam 2) * ((lam 0)^5)) + ((-4) * ((lam 0)^3) * ((lam 2)^3)) + ((-2) * (lam 1) * ((lam 0)^5)) + (6 * ((lam 0)^4) * ((lam 2)^2)) + ((-12) * (lam 1) * ((lam 0)^3) * ((lam 2)^2)) + ((-4) * (lam 0) * ((lam 1)^2) * ((lam 2)^3)) + ((-4) * (lam 2) * ((lam 0)^3) * ((lam 1)^2)) + ((-2) * (lam 0) * (lam 1) * ((lam 2)^4)) + (6 * ((lam 0)^2) * ((lam 1)^2) * ((lam 2)^2)) + (8 * (lam 1) * (lam 2) * ((lam 0)^4)) + (8 * (lam 1) * ((lam 0)^2) * ((lam 2)^3)))) * e4 + (((6 * ((lam 0)^6)) + ((-18) * (lam 1) * ((lam 0)^5)) + ((-18) * (lam 2) * ((lam 0)^5)) + ((-16) * ((lam 0)^3) * ((lam 1)^3)) + ((-16) * ((lam 0)^3) * ((lam 2)^3)) + ((-4) * ((lam 1)^3) * ((lam 2)^3)) + (5 * ((lam 0)^2) * ((lam 1)^4)) + (5 * ((lam 0)^2) * ((lam 2)^4)) + (5 * ((lam 1)^2) * ((lam 2)^4)) + (5 * ((lam 1)^4) * ((lam 2)^2)) + (23 * ((lam 0)^4) * ((lam 1)^2)) + (23 * ((lam 0)^4) * ((lam 2)^2)) + ((-44) * (lam 1) * ((lam 0)^3) * ((lam 2)^2)) + ((-44) * (lam 2) * ((lam 0)^3) * ((lam 1)^2)) + ((-10) * (lam 0) * (lam 1) * ((lam 2)^4)) + ((-10) * (lam 0) * (lam 2) * ((lam 1)^4)) + ((-8) * (lam 0) * ((lam 1)^2) * ((lam 2)^3)) + ((-8) * (lam 0) * ((lam 1)^3) * ((lam 2)^2)) + (24 * ((lam 0)^2) * ((lam 1)^2) * ((lam 2)^2)) + (28 * (lam 1) * ((lam 0)^2) * ((lam 2)^3)) + (28 * (lam 2) * ((lam 0)^2) * ((lam 1)^3)) + (44 * (lam 1) * (lam 2) * ((lam 0)^4)))) * e8 + ((((-4) * ((lam 0)^7)) + ((-1) * ((lam 1)^3) * ((lam 2)^4)) + ((-1) * ((lam 1)^4) * ((lam 2)^3)) + ((-5) * ((lam 0)^4) * ((lam 1)^3)) + ((-5) * ((lam 0)^4) * ((lam 2)^3)) + ((-3) * ((lam 0)^2) * ((lam 1)^5)) + ((-3) * ((lam 0)^2) * ((lam 2)^5)) + ((-3) * ((lam 0)^5) * ((lam 1)^2)) + ((-3) * ((lam 0)^5) * ((lam 2)^2)) + ((-3) * ((lam 1)^2) * ((lam 2)^5)) + ((-3) * ((lam 1)^5) * ((lam 2)^2)) + (7 * ((lam 0)^3) * ((lam 1)^4)) + (7 * ((lam 0)^3) * ((lam 2)^4)) + (8 * (lam 1) * ((lam 0)^6)) + (8 * (lam 2) * ((lam 0)^6)) + ((-30) * ((lam 0)^2) * ((lam 1)^2) * ((lam 2)^3)) + ((-30) * ((lam 0)^2) * ((lam 1)^3) * ((lam 2)^2)) + ((-15) * (lam 1) * ((lam 0)^2) * ((lam 2)^4)) + ((-15) * (lam 1) * ((lam 0)^4) * ((lam 2)^2)) + ((-15) * (lam 2) * ((lam 0)^2) * ((lam 1)^4)) + ((-15) * (lam 2) * ((lam 0)^4) * ((lam 1)^2)) + ((-6) * (lam 1) * (lam 2) * ((lam 0)^5)) + (6 * (lam 0) * (lam 1) * ((lam 2)^5)) + (6 * (lam 0) * (lam 2) * ((lam 1)^5)) + (9 * (lam 0) * ((lam 1)^2) * ((lam 2)^4)) + (9 * (lam 0) * ((lam 1)^4) * ((lam 2)^2)) + (14 * (lam 0) * ((lam 1)^3) * ((lam 2)^3)) + (22 * (lam 1) * ((lam 0)^3) * ((lam 2)^3)) + (22 * (lam 2) * ((lam 0)^3) * ((lam 1)^3)) + (42 * ((lam 0)^3) * ((lam 1)^2) * ((lam 2)^2)))) * H.hhf
    exact (((natCast_isUnit 1 (by norm_num)).mul (H.u01.pow 2)).mul (H.u02.pow 2)).mul_right_eq_zero.mp e'
  -- 5. g = 0 は環の元の等式なので e₀ を作用させてよい
  have hG1 : (((lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-1) * (lam 1) * ((lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-13) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2))) + ((-9) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1))) + ((-6) * (lam 0) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-6) * (lam 2) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-4) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + (4 * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1))) + (6 * (lam 0) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + (6 * (lam 1) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + (9 * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2))) + (13 * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + ((-9) * (lam 1) * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + ((-4) * (lam 0) * (lam 2) * ((lam 1) * (lam 1) * (lam 1))) + (4 * (lam 0) * (lam 1) * ((lam 2) * (lam 2) * (lam 2))) + (9 * (lam 2) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1)))) = 0 := by
    have e := congrArg (F.e 0) hg
    simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at e
    try simp only [hbe, hga, het] at e
    have e' : alpha F lam * (((lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-1) * (lam 1) * ((lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-13) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2))) + ((-9) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1))) + ((-6) * (lam 0) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-6) * (lam 2) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-4) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + (4 * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1))) + (6 * (lam 0) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + (6 * (lam 1) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + (9 * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2))) + (13 * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + ((-9) * (lam 1) * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + ((-4) * (lam 0) * (lam 2) * ((lam 1) * (lam 1) * (lam 1))) + (4 * (lam 0) * (lam 1) * ((lam 2) * (lam 2) * (lam 2))) + (9 * (lam 2) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1)))) = 0 := by linear_combination e
    exact hal.mul_right_eq_zero.mp e'
  have hG2 : (((-2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-41) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1))) + ((-41) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + ((-32) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-32) * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-19) * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-19) * ((lam 1) * (lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2))) + ((-12) * (lam 1) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-12) * (lam 2) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-5) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-5) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + (11 * (lam 1) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + (11 * (lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + (12 * (lam 0) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + (12 * (lam 0) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + (36 * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + (36 * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + (57 * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1))) + (57 * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2))) + ((-176) * (lam 1) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2))) + ((-176) * (lam 2) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1))) + ((-127) * (lam 0) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-127) * (lam 0) * ((lam 1) * (lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + ((-38) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2))) + ((-38) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + ((-8) * (lam 1) * (lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-4) * (lam 0) * (lam 1) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-4) * (lam 0) * (lam 2) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + (38 * (lam 1) * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + (38 * (lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1))) + (132 * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + (151 * (lam 1) * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + (151 * (lam 2) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + (176 * (lam 0) * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2)))) = 0 := by
    have e := congrArg (F.e 0) hG1
    simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at e
    try simp only [hbe, hga, het] at e
    have e' : alpha F lam * (((-2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-41) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1))) + ((-41) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + ((-32) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-32) * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-19) * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-19) * ((lam 1) * (lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2))) + ((-12) * (lam 1) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-12) * (lam 2) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-5) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + ((-5) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + (11 * (lam 1) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + (11 * (lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + (12 * (lam 0) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + (12 * (lam 0) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + (36 * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + (36 * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + (57 * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1))) + (57 * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2))) + ((-176) * (lam 1) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2))) + ((-176) * (lam 2) * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1))) + ((-127) * (lam 0) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-127) * (lam 0) * ((lam 1) * (lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + ((-38) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2))) + ((-38) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + ((-8) * (lam 1) * (lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0) * (lam 0))) + ((-4) * (lam 0) * (lam 1) * ((lam 2) * (lam 2) * (lam 2) * (lam 2) * (lam 2))) + ((-4) * (lam 0) * (lam 2) * ((lam 1) * (lam 1) * (lam 1) * (lam 1) * (lam 1))) + (38 * (lam 1) * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 2) * (lam 2))) + (38 * (lam 2) * ((lam 0) * (lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1))) + (132 * ((lam 0) * (lam 0) * (lam 0)) * ((lam 1) * (lam 1)) * ((lam 2) * (lam 2))) + (151 * (lam 1) * ((lam 0) * (lam 0)) * ((lam 2) * (lam 2) * (lam 2) * (lam 2))) + (151 * (lam 2) * ((lam 0) * (lam 0)) * ((lam 1) * (lam 1) * (lam 1) * (lam 1))) + (176 * (lam 0) * ((lam 1) * (lam 1) * (lam 1)) * ((lam 2) * (lam 2) * (lam 2)))) = 0 := by linear_combination e
    exact hal.mul_right_eq_zero.mp e'
  -- 6. 証明書 ((λ₀−λ₁)(λ₀−λ₂)(λ₁−λ₂))^3 = c₀g + c₁G₁ + c₂G₂
  have hfin : ((1729 : ℕ) : R) * ((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2)) ^ 3 = 0 := by
    push_cast
    linear_combination ((((-2384) * ((lam 0)^3) * ((lam 1)^3)) + ((-2142) * ((lam 0)^2) * ((lam 2)^4)) + ((-774) * ((lam 0)^4) * ((lam 2)^2)) + ((-722) * ((lam 1)^4) * ((lam 2)^2)) + ((-336) * (lam 0) * ((lam 1)^5)) + ((-336) * (lam 1) * ((lam 2)^5)) + ((-196) * (lam 1) * ((lam 0)^5)) + (196 * (lam 2) * ((lam 0)^5)) + (336 * (lam 0) * ((lam 2)^5)) + (336 * (lam 2) * ((lam 1)^5)) + (722 * ((lam 1)^2) * ((lam 2)^4)) + (774 * ((lam 0)^4) * ((lam 1)^2)) + (2142 * ((lam 0)^2) * ((lam 1)^4)) + (2384 * ((lam 0)^3) * ((lam 2)^3)) + ((-5280) * (lam 0) * ((lam 1)^2) * ((lam 2)^3)) + ((-3784) * (lam 1) * ((lam 0)^3) * ((lam 2)^2)) + ((-2896) * (lam 2) * ((lam 0)^2) * ((lam 1)^3)) + ((-1420) * (lam 0) * (lam 2) * ((lam 1)^4)) + (1420 * (lam 0) * (lam 1) * ((lam 2)^4)) + (2896 * (lam 1) * ((lam 0)^2) * ((lam 2)^3)) + (3784 * (lam 2) * ((lam 0)^3) * ((lam 1)^2)) + (5280 * (lam 0) * ((lam 1)^3) * ((lam 2)^2)))) * hg + ((((-540) * ((lam 1)^4)) + ((-540) * ((lam 2)^4)) + ((-1461) * ((lam 0)^2) * ((lam 1)^2)) + ((-1461) * ((lam 0)^2) * ((lam 2)^2)) + (307 * (lam 1) * ((lam 2)^3)) + (307 * (lam 2) * ((lam 1)^3)) + (1330 * ((lam 1)^2) * ((lam 2)^2)) + (1981 * (lam 0) * ((lam 1)^3)) + (1981 * (lam 0) * ((lam 2)^3)) + ((-2845) * (lam 0) * (lam 1) * ((lam 2)^2)) + ((-2845) * (lam 0) * (lam 2) * ((lam 1)^2)) + (3786 * (lam 1) * (lam 2) * ((lam 0)^2)))) * hG1 + ((((-186) * ((lam 2)^2)) + (186 * ((lam 1)^2)) + ((-196) * (lam 0) * (lam 1)) + (196 * (lam 0) * (lam 2)))) * hG2
  exact ((natCast_isUnit 1729 (by norm_num)).mul (H.unit_x.pow 3)).ne_zero hfin

end C2

end CFT.Cartan
