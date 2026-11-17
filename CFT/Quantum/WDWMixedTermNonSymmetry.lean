import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 5-1（作用素の対称性）の残り：
  具体的なテスト関数による混合項の非対称性の Lean 証明。

  `WDWMixedTerm.lean` で証明済みの随伴公式
    ⟨f, b ∂_a∂_b g⟩ = ⟨b ∂_a∂_b f + ∂_a f − (b/a) ∂_b f − f/a, g⟩
  （重み 1/a の内積、矩形上のディリクレ境界）は、混合項が対称でないことを
  示唆するが、補正項が 0 でない具体例は sympy による数値確認だけだった。
  ここでは多項式テスト関数
    f(a,b) = a(a−1)(2−a)·b(1−b),
    g(a,b) = a(a−1)(2−a)·b²(1−b)²
  （矩形 [1,2]×[0,1] でディリクレ境界を満たす）に対して、重みつき内積の
  両辺を直接計算する。因子 a のおかげで重み 1/a が相殺され、被積分関数は
  多項式になる：
    ⟨f, b·g_ab⟩ = −1/12600,  ⟨b·f_ab, g⟩ = −1/25200,
  よって ⟨f, b·g_ab⟩ ≠ ⟨b·f_ab, g⟩。すなわち混合項 b·∂_a∂_b は
  重み 1/a の内積に関して対称ではない（WDW 作用素の混合項 2ħ²b ∂_a∂_b も、
  0 でない定数倍を除いて同じことである）。

  計算は因数分解 F(x)·G(y) への帰着と、FTC による単変数多項式積分で行う
  （`integral_pow` の和への分割は可積分性のサイドゴールが `simp` で
  処理できないため、原始関数を明示する FTC を使う）。
  `testFab`・`testGab` が実際に混合偏微分であることは `HasDerivAt` の
  補題（`testFab_hasDerivAt`・`testGab_hasDerivAt`）で確認してある。
-/

namespace CFT.WDWMixNonSymm

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- テスト関数 f(a,b) = a(a−1)(2−a)·b(1−b)。 -/
def testF : ℝ → ℝ → ℝ := fun a b => a * (a - 1) * (2 - a) * (b * (1 - b))

/-- テスト関数 g(a,b) = a(a−1)(2−a)·b²(1−b)²。 -/
def testG : ℝ → ℝ → ℝ := fun a b => a * (a - 1) * (2 - a) * (b ^ 2 * (1 - b) ^ 2)

/-- f の a-偏微分。 -/
def testFa : ℝ → ℝ → ℝ := fun a b => (-3*a^2 + 6*a - 2) * (b * (1 - b))

/-- f の混合偏微分 ∂_a∂_b f。 -/
def testFab : ℝ → ℝ → ℝ := fun a b => (-3*a^2 + 6*a - 2) * (1 - 2*b)

/-- g の b-偏微分。 -/
def testGb : ℝ → ℝ → ℝ := fun a b => a * (a - 1) * (2 - a) * (4*b^3 - 6*b^2 + 2*b)

/-- g の混合偏微分 ∂_a∂_b g。 -/
def testGab : ℝ → ℝ → ℝ := fun a b => (-3*a^2 + 6*a - 2) * (4*b^3 - 6*b^2 + 2*b)

/-- a(a−1)(2−a) の a-微分は −3a²+6a−2。 -/
theorem hasDerivAt_S (a : ℝ) :
    HasDerivAt (fun a' => a' * (a' - 1) * (2 - a')) (-3*a^2 + 6*a - 2) a := by
  have h1 := (hasDerivAt_id' a).mul ((hasDerivAt_id' a).sub (hasDerivAt_const a 1))
  have h2 := h1.mul ((hasDerivAt_const a 2).sub (hasDerivAt_id' a))
  convert h2 using 1
  ring

/-- b(1−b) の b-微分は 1−2b。 -/
theorem hasDerivAt_Q (b : ℝ) :
    HasDerivAt (fun b' => b' * (1 - b')) (1 - 2*b) b := by
  have h := (hasDerivAt_id' b).mul ((hasDerivAt_const b 1).sub (hasDerivAt_id' b))
  convert h using 1
  ring

/-- b²(1−b)² の b-微分は 4b³−6b²+2b。 -/
theorem hasDerivAt_R (b : ℝ) :
    HasDerivAt (fun b' => b'^2 * (1 - b')^2) (4*b^3 - 6*b^2 + 2*b) b := by
  have h2 := hasDerivAt_pow 2 b
  have hsq := ((hasDerivAt_const b 1).sub (hasDerivAt_id' b)).pow (n := 2)
  have h := h2.mul hsq
  convert h using 1
  ring

/-- `testFa` は `testF` の a-偏微分である。 -/
theorem testFa_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun a' => testF a' b) (testFa a b) a := by
  have h := (hasDerivAt_S a).mul_const (b * (1 - b))
  exact h

/-- `testFab` は `testFa` の b-偏微分、すなわち f の混合偏微分である。 -/
theorem testFab_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun b' => testFa a b') (testFab a b) b := by
  have h := (hasDerivAt_Q b).const_mul (-3*a^2 + 6*a - 2)
  exact h

/-- `testGb` は `testG` の b-偏微分である。 -/
theorem testGb_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun b' => testG a b') (testGb a b) b := by
  have h := (hasDerivAt_R b).const_mul (a * (a - 1) * (2 - a))
  exact h

/-- `testGab` は `testGb` の a-偏微分、すなわち g の混合偏微分である。 -/
theorem testGab_hasDerivAt (a b : ℝ) :
    HasDerivAt (fun a' => testGb a' b) (testGab a b) a := by
  have h := (hasDerivAt_S a).mul_const (4*b^3 - 6*b^2 + 2*b)
  exact h

/-- f は矩形 [1,2]×[0,1] でディリクレ境界を満たす。 -/
theorem testF_dirichlet (a b : ℝ) :
    testF 1 b = 0 ∧ testF 2 b = 0 ∧ testF a 0 = 0 ∧ testF a 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [testF]

/-- g は矩形 [1,2]×[0,1] でディリクレ境界を満たす。 -/
theorem testG_dirichlet (a b : ℝ) :
    testG 1 b = 0 ∧ testG 2 b = 0 ∧ testG a 0 = 0 ∧ testG a 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [testG]

/-- ∫₁² (3x⁴−15x³+26x²−18x+4) dx = 1/60。 -/
theorem integral_A :
    ∫ x in (1:ℝ)..2, (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) = 1/60 := by
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) 2,
      HasDerivAt (fun y => 3/5*y^5 - 15/4*y^4 + 26/3*y^3 - 9*y^2 + 4*y)
        (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) x := by
    intro x _
    have h5 := (hasDerivAt_pow 5 x).const_mul (3/5 : ℝ)
    have h4 := (hasDerivAt_pow 4 x).const_mul (15/4 : ℝ)
    have h3 := (hasDerivAt_pow 3 x).const_mul (26/3 : ℝ)
    have h2 := (hasDerivAt_pow 2 x).const_mul (9 : ℝ)
    have h1 := (hasDerivAt_id' x).const_mul (4 : ℝ)
    have h := (((h5.sub h4).add h3).sub h2).add h1
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun x => 3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4)
      volume 1 2 :=
    (by fun_prop : Continuous fun x : ℝ => 3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4).intervalIntegrable 1 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- ∫₀¹ (2y³−8y⁴+10y⁵−4y⁶) dy = −1/210。 -/
theorem integral_B :
    ∫ y in (0:ℝ)..1, (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6) = -1/210 := by
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun z => 1/2*z^4 - 8/5*z^5 + 5/3*z^6 - 4/7*z^7)
        (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6) y := by
    intro y _
    have h4 := (hasDerivAt_pow 4 y).const_mul (1/2 : ℝ)
    have h5 := (hasDerivAt_pow 5 y).const_mul (8/5 : ℝ)
    have h6 := (hasDerivAt_pow 6 y).const_mul (5/3 : ℝ)
    have h7 := (hasDerivAt_pow 7 y).const_mul (4/7 : ℝ)
    have h := (((h4.sub h5).add h6).sub h7)
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun y => 2*y^3 - 8*y^4 + 10*y^5 - 4*y^6)
      volume 0 1 :=
    (by fun_prop : Continuous fun y : ℝ => 2*y^3 - 8*y^4 + 10*y^5 - 4*y^6).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- ∫₀¹ (y³−4y⁴+5y⁵−2y⁶) dy = −1/420。 -/
theorem integral_C :
    ∫ y in (0:ℝ)..1, (y^3 - 4*y^4 + 5*y^5 - 2*y^6) = -1/420 := by
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun z => 1/4*z^4 - 4/5*z^5 + 5/6*z^6 - 2/7*z^7)
        (y^3 - 4*y^4 + 5*y^5 - 2*y^6) y := by
    intro y _
    have h4 := (hasDerivAt_pow 4 y).const_mul (1/4 : ℝ)
    have h5 := (hasDerivAt_pow 5 y).const_mul (4/5 : ℝ)
    have h6 := (hasDerivAt_pow 6 y).const_mul (5/6 : ℝ)
    have h7 := (hasDerivAt_pow 7 y).const_mul (2/7 : ℝ)
    have h := (((h4.sub h5).add h6).sub h7)
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun y => y^3 - 4*y^4 + 5*y^5 - 2*y^6)
      volume 0 1 :=
    (by fun_prop : Continuous fun y : ℝ => y^3 - 4*y^4 + 5*y^5 - 2*y^6).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num

/-- 点ごとの恒等式：f·(b·g_ab)/a = A(x)·B(y)（x ≠ 0）。 -/
theorem testF_mul_testGab (x y : ℝ) (hx : x ≠ 0) :
    testF x y * (y * testGab x y) * (1 / x)
      = (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6) := by
  show (x * (x - 1) * (2 - x) * (y * (1 - y)))
      * (y * ((-3*x^2 + 6*x - 2) * (4*y^3 - 6*y^2 + 2*y))) * (1 / x) = _
  field_simp
  ring

/-- 点ごとの恒等式：(b·f_ab)·g/a = A(x)·C(y)（x ≠ 0）。 -/
theorem testFab_mul_testG (x y : ℝ) (hx : x ≠ 0) :
    (y * testFab x y) * testG x y * (1 / x)
      = (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (y^3 - 4*y^4 + 5*y^5 - 2*y^6) := by
  show (y * ((-3*x^2 + 6*x - 2) * (1 - 2*y)))
      * (x * (x - 1) * (2 - x) * (y^2 * (1 - y)^2)) * (1 / x) = _
  field_simp
  ring

/-- ⟨f, b·∂_a∂_b g⟩ = −1/12600（重み 1/a の内積、[1,2]×[0,1]）。 -/
theorem weighted_inner_left :
    ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1, testF x y * (y * testGab x y) * (1 / x)
      = -1 / 12600 := by
  have e : ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1, testF x y * (y * testGab x y) * (1 / x)
      = ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1,
          (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y _
    have hx0 : x ≠ 0 := by
      have h1x : (1:ℝ) ≤ x := by
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact hx.1
      exact ne_of_gt (by linarith)
    exact testF_mul_testGab x y hx0
  have efac : ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1,
        (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6)
      = (∫ x in (1:ℝ)..2, (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4))
        * (∫ y in (0:ℝ)..1, (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6)) := by
    have e1 : ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1,
          (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6)
        = ∫ x in (1:ℝ)..2, (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4)
            * (∫ y in (0:ℝ)..1, (2*y^3 - 8*y^4 + 10*y^5 - 4*y^6)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact intervalIntegral.integral_const_mul _ _
    rw [e1]
    exact intervalIntegral.integral_mul_const _ _
  rw [e, efac, integral_A, integral_B]
  norm_num

/-- ⟨b·∂_a∂_b f, g⟩ = −1/25200（重み 1/a の内積、[1,2]×[0,1]）。 -/
theorem weighted_inner_right :
    ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1, (y * testFab x y) * testG x y * (1 / x)
      = -1 / 25200 := by
  have e : ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1, (y * testFab x y) * testG x y * (1 / x)
      = ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1,
          (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (y^3 - 4*y^4 + 5*y^5 - 2*y^6) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y _
    have hx0 : x ≠ 0 := by
      have h1x : (1:ℝ) ≤ x := by
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact hx.1
      exact ne_of_gt (by linarith)
    exact testFab_mul_testG x y hx0
  have efac : ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1,
        (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (y^3 - 4*y^4 + 5*y^5 - 2*y^6)
      = (∫ x in (1:ℝ)..2, (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4))
        * (∫ y in (0:ℝ)..1, (y^3 - 4*y^4 + 5*y^5 - 2*y^6)) := by
    have e1 : ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1,
          (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4) * (y^3 - 4*y^4 + 5*y^5 - 2*y^6)
        = ∫ x in (1:ℝ)..2, (3*x^4 - 15*x^3 + 26*x^2 - 18*x + 4)
            * (∫ y in (0:ℝ)..1, (y^3 - 4*y^4 + 5*y^5 - 2*y^6)) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact intervalIntegral.integral_const_mul _ _
    rw [e1]
    exact intervalIntegral.integral_mul_const _ _
  rw [e, efac, integral_A, integral_C]
  norm_num

/-- 【5-1】混合項 b·∂_a∂_b は重み 1/a の内積に関して対称ではない。
  具体的なテスト関数 f, g に対して ⟨f, b·g_ab⟩ ≠ ⟨b·f_ab, g⟩。
  差は −1/25200 である。これで 5-1 の残り（具体的なテスト関数による
  非対称性の Lean 証明）が閉じる。 -/
theorem mixed_term_not_symmetric :
    ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1, testF x y * (y * testGab x y) * (1 / x)
      ≠ ∫ x in (1:ℝ)..2, ∫ y in (0:ℝ)..1, (y * testFab x y) * testG x y * (1 / x) := by
  rw [weighted_inner_left, weighted_inner_right]
  norm_num

end

end CFT.WDWMixNonSymm
