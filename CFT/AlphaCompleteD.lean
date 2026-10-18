/-
  補強:α-VII.7(Z28-f)単位 S² 上の単極子のゼロモード

  H² = −d²/dθ² + V² ± V′、V = (m + q cos θ)/sin θ(em6.py の還元形)。
  * ゼロモードの厳密解:u(θ) = tan(θ/2)^m · sin(θ)^q は u′ = V u を満たす(0 < θ < π)
  * 端点での振る舞い:θ → 0 で θ^{m+q}、θ → π で (π − θ)^{q−m}。
    べき θ^e が端点近くで L² になる条件は e > −1/2(not_L2 系の補題と同じ判定)。
    したがって許される m は |m| < q + 1/2
  * 数え上げ:q = n(整数)なら m は半整数で 2n 個、q = n + 1/2 なら m は整数で 2n + 1 個。
    いずれも 2q 個
  * カイラリティ:もう一方の分岐(u′ = −V u)の条件 q − 1/2 < m < 1/2 − q は q ≥ 1/2 で空
  未形式化:u と θ^{m+q} の比が端点近くで有界であることを使う比較の段(標準的な実解析)
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real

namespace CFT.AlphaCompleteD

/-- ゼロモード u(θ) = tan(θ/2)^m sin(θ)^q は u′ = ((m + q cos θ)/sin θ) u を満たす -/
theorem zero_mode (m q θ : ℝ) (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt (fun θ => tan (θ / 2) ^ m * sin θ ^ q)
      ((m + q * cos θ) / sin θ * (tan (θ / 2) ^ m * sin θ ^ q)) θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 hπ
  have hh0 : 0 < θ / 2 := by linarith
  have hh1 : θ / 2 < π / 2 := by linarith
  have hc2 : 0 < cos (θ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, hh1⟩
  have hs2 : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi hh0 (by linarith)
  have ht : 0 < tan (θ / 2) := by rw [tan_eq_sin_div_cos]; positivity
  have hdt := (Real.hasDerivAt_tan (x := θ / 2) hc2.ne').comp θ ((hasDerivAt_id θ).div_const 2)
  have h1 := (Real.hasDerivAt_rpow_const (p := m) (Or.inl ht.ne')).comp θ hdt
  have h2 := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hs.ne')).comp θ (hasDerivAt_sin θ)
  have h := h1.mul h2
  convert h using 1
  simp only [Function.comp_def]
  rw [Real.rpow_sub_one ht.ne', Real.rpow_sub_one hs.ne']
  have key : tan (θ / 2) * (2 * cos (θ / 2) ^ 2) = sin θ := by
    have hsin : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
      rw [← sin_two_mul]; ring_nf
    rw [tan_eq_sin_div_cos, hsin]
    field_simp
    ring
  set T := tan (θ / 2) ^ m with hT
  set Sq := sin θ ^ q with hSq
  have e1 : m * (T / tan (θ / 2)) * (1 / cos (θ / 2) ^ 2 * (1 / 2)) = m * T / sin θ := by
    rw [← key]
    have ht0 : tan (θ / 2) ≠ 0 := ht.ne'
    have hc0 : cos (θ / 2) ≠ 0 := hc2.ne'
    ring
  rw [e1]
  field_simp
  ring

/-- もう一方の分岐 v = tan(θ/2)^{−m} sin(θ)^{−q} は v′ = −V v -/
theorem zero_mode_other (m q θ : ℝ) (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt (fun θ => tan (θ / 2) ^ (-m) * sin θ ^ (-q))
      (-((m + q * cos θ) / sin θ) * (tan (θ / 2) ^ (-m) * sin θ ^ (-q))) θ := by
  have := zero_mode (-m) (-q) θ h0 hπ
  convert this using 2
  ring

/-- q = n(正の整数):許される半整数 m = k + 1/2(|m| < n + 1/2 ⇔ −n ≤ k < n)は 2n 個 -/
theorem count_integer_charge (n : ℕ) : (Finset.Ico (-(n : ℤ)) n).card = 2 * n := by
  rw [Int.card_Ico]
  omega

/-- 半整数 m = k + 1/2 が |m| < n + 1/2 を満たす ⇔ −n ≤ k < n -/
theorem admissible_half (n : ℕ) (k : ℤ) :
    |((k : ℝ) + 1 / 2)| < n + 1 / 2 ↔ (-(n : ℤ) ≤ k ∧ k < n) := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (-(n : ℝ)) - 1 < k := by linarith
      have h3 : -(n : ℤ) - 1 < k := by exact_mod_cast this
      omega
    · have : (k : ℝ) < n := by linarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (-(n : ℝ)) ≤ k := by exact_mod_cast h1
    have h2' : (k : ℝ) ≤ n - 1 := by
      have : k ≤ (n : ℤ) - 1 := by omega
      exact_mod_cast this
    constructor <;> linarith

/-- q = n + 1/2:許される整数 m(|m| < n + 1)は 2n + 1 個 = 2q -/
theorem count_half_charge (n : ℕ) : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
  rw [Int.card_Icc]
  omega

/-- カイラリティ:q ≥ 1/2 なら他方の分岐の条件 q − 1/2 < m < 1/2 − q を満たす m はない -/
theorem other_chirality_empty (q m : ℝ) (hq : 1 / 2 ≤ q) : ¬ (q - 1 / 2 < m ∧ m < 1 / 2 - q) := by
  rintro ⟨h1, h2⟩
  linarith

/-- 端点の指数:θ → 0 で m + q、θ → π で q − m。両方 > −1/2 ⇔ |m| < q + 1/2 -/
theorem exponent_condition (m q : ℝ) :
    (-(1 / 2) < m + q ∧ -(1 / 2) < q - m) ↔ |m| < q + 1 / 2 := by
  rw [abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- α-VII.9:U(1)_F = ½ スピン接続のひねりは S² で電荷 q = χ(S²)/4 = 1/2、ゼロモードは 2q = 1 個 -/
theorem one_generation_from_twist : (2 : ℝ) * ((2 : ℝ) / 4) = 1 := by norm_num

end CFT.AlphaCompleteD
