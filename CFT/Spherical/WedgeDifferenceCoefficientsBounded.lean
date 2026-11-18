import CFT.Spherical.WedgeDifferenceEnergy
import CFT.Spherical.WedgeDifferenceEnergyROm
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 4-7（一意性）の第4歩：差の線形系の源項の係数の有界性。
  `WedgeDifferenceEnergy.lean`・`WedgeDifferenceEnergyROm.lean` で定義した
  14 個の係数（δW：3、δr：5、δΩ：6）について、場の値とその微分に対する点ごとの
  上界と、r・r'・Ω・Ω' に対する正の下限を仮定すれば、各係数が明示的な定数で
  上から抑えられることを証明する。純粋な代数（三角不等式と単調性）の組み立てで、
  コンパクト性は使わない。次の橋渡しは、コンパクトな矩形上の連続性から
  ここで仮定した上界・下界そのものを出すこと（連続関数の有界性と正関数の
  下限の存在）。その先はエネルギー評価と特性方向のグロンウォール（4-7 の本体）、
  拘束の差の線形系。
-/

open CFT.Wedge
open CFT.WedgeDifference
open CFT.WedgeDifferenceEnergy
open CFT.WedgeDifferenceEnergyROm

namespace CFT.WedgeDifferenceCoefficients

/-- 逆数の絶対値の上界（正の下限から）。 -/
theorem abs_inv_le_of_le {K : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ} {m : ℝ}
    (hm : 0 < m) (hf : ∀ u v, (u, v) ∈ K → m ≤ f u v) :
    ∀ u v, (u, v) ∈ K → |(f u v)⁻¹| ≤ m⁻¹ := by
  intro u v huv
  have hpos : 0 < f u v := lt_of_lt_of_le hm (hf u v huv)
  rw [abs_inv, abs_of_pos hpos]
  exact inv_anti₀ hm (hf u v huv)

/-- |1 - W²| の上界。 -/
theorem abs_one_sub_sq_le {K : Set (ℝ × ℝ)} {W : ℝ → ℝ → ℝ} {BW : ℝ}
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW) :
    ∀ u v, (u, v) ∈ K → |1 - (W u v) ^ 2| ≤ 1 + BW ^ 2 := by
  intro u v huv
  have h := hW u v huv
  calc |1 - (W u v) ^ 2| ≤ |1| + |(W u v) ^ 2| := abs_sub _ _
    _ = 1 + |W u v| ^ 2 := by simp [abs_pow]
    _ ≤ 1 + BW ^ 2 := by
        have hp := pow_le_pow_left₀ (abs_nonneg _) h 2
        linarith

/-- 差の W 方程式の δOm 係数の有界性。 -/
theorem diffWCoefOm_bound {K : Set (ℝ × ℝ)} {W r : ℝ → ℝ → ℝ} {BW mr : ℝ}
    (hmr : 0 < mr)
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K → |diffWCoefOm W r u v| ≤ 2⁻¹ * BW * (1 + BW ^ 2) * mr⁻¹ ^ 2 := by
  intro u v huv
  have hW' := hW u v huv
  have hBWnn : 0 ≤ BW := (abs_nonneg _).trans hW'
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  have hrinv2 : |(r u v)⁻¹| ^ 2 ≤ mr⁻¹ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 2
  have h1 := abs_one_sub_sq_le hW u v huv
  show |2⁻¹ * W u v * (1 - (W u v) ^ 2) * ((r u v)⁻¹) ^ 2| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  gcongr

/-- 差の W 方程式の δW 係数の有界性。 -/
theorem diffWCoefW_bound {K : Set (ℝ × ℝ)} {Om' W W' r : ℝ → ℝ → ℝ}
    {BOm' BW BW' mr : ℝ}
    (hmr : 0 < mr)
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K →
      |diffWCoefW Om' W W' r u v|
        ≤ 2⁻¹ * BOm' * (1 + BW ^ 2 + BW * BW' + BW' ^ 2) * mr⁻¹ ^ 2 := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hW'' := hW u v huv
  have hW''' := hW' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hBWnn : 0 ≤ BW := (abs_nonneg _).trans hW''
  have hBW'nn : 0 ≤ BW' := (abs_nonneg _).trans hW'''
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  have hrinv2 : |(r u v)⁻¹| ^ 2 ≤ mr⁻¹ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 2
  have h1 : |1 - (W u v) ^ 2 - W u v * W' u v - (W' u v) ^ 2|
      ≤ 1 + BW ^ 2 + BW * BW' + BW' ^ 2 := by
    calc |1 - (W u v) ^ 2 - W u v * W' u v - (W' u v) ^ 2|
        ≤ |1 - (W u v) ^ 2| + |W u v * W' u v + (W' u v) ^ 2| := by
          have hsub := abs_sub (1 - (W u v) ^ 2) (W u v * W' u v + (W' u v) ^ 2)
          convert hsub using 2
          ring
      _ ≤ (1 + BW ^ 2) + (BW * BW' + BW' ^ 2) := by
          apply add_le_add
          · exact abs_one_sub_sq_le hW u v huv
          · calc |W u v * W' u v + (W' u v) ^ 2|
                ≤ |W u v * W' u v| + |(W' u v) ^ 2| := abs_add _ _
              _ = |W u v| * |W' u v| + |W' u v| ^ 2 := by simp [abs_mul, abs_pow]
              _ ≤ BW * BW' + BW' ^ 2 := by
                  apply add_le_add
                  · exact mul_le_mul hW'' hW''' (abs_nonneg _) hBWnn
                  · exact pow_le_pow_left₀ (abs_nonneg _) hW''' 2
      _ = 1 + BW ^ 2 + BW * BW' + BW' ^ 2 := by ring
  show |2⁻¹ * Om' u v * (1 - (W u v) ^ 2 - W u v * W' u v - (W' u v) ^ 2)
        * ((r u v)⁻¹) ^ 2| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  gcongr

/-- 差の W 方程式の δr 係数の有界性。 -/
theorem diffWCoefR_bound {K : Set (ℝ × ℝ)} {Om' W' r r' : ℝ → ℝ → ℝ}
    {BOm' BW' Br Br' mr mr' : ℝ}
    (hmr : 0 < mr) (hmr' : 0 < mr')
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
    (hr : ∀ u v, (u, v) ∈ K → |r u v| ≤ Br)
    (hr' : ∀ u v, (u, v) ∈ K → |r' u v| ≤ Br')
    (hrlow : ∀ u v, (u, v) ∈ K → mr ≤ r u v)
    (hrlow' : ∀ u v, (u, v) ∈ K → mr' ≤ r' u v) :
    ∀ u v, (u, v) ∈ K →
      |diffWCoefR Om' W' r r' u v|
        ≤ 2⁻¹ * BOm' * BW' * (1 + BW' ^ 2) * (Br + Br') * mr⁻¹ ^ 2 * mr'⁻¹ ^ 2 := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hW'' := hW' u v huv
  have hr'' := hr u v huv
  have hr''' := hr' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hBW'nn : 0 ≤ BW' := (abs_nonneg _).trans hW''
  have hBrnn : 0 ≤ Br := (abs_nonneg _).trans hr''
  have hBr'nn : 0 ≤ Br' := (abs_nonneg _).trans hr'''
  have hrinv := abs_inv_le_of_le hmr hrlow u v huv
  have hrinv' := abs_inv_le_of_le hmr' hrlow' u v huv
  have hrinv2 : |(r u v)⁻¹| ^ 2 ≤ mr⁻¹ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 2
  have hrinv2' : |(r' u v)⁻¹| ^ 2 ≤ mr'⁻¹ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv' 2
  have h1 := abs_one_sub_sq_le hW' u v huv
  have hsum : |r u v + r' u v| ≤ Br + Br' := by
    calc |r u v + r' u v| ≤ |r u v| + |r' u v| := abs_add _ _
      _ ≤ Br + Br' := add_le_add hr'' hr'''
  show |-2⁻¹ * Om' u v * W' u v * (1 - (W' u v) ^ 2) * (r u v + r' u v)
        * ((r u v)⁻¹) ^ 2 * ((r' u v)⁻¹) ^ 2| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
    abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  gcongr

/-- |W + W'| の上界。 -/
theorem abs_add_le' {K : Set (ℝ × ℝ)} {W W' : ℝ → ℝ → ℝ} {BW BW' : ℝ}
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW') :
    ∀ u v, (u, v) ∈ K → |W u v + W' u v| ≤ BW + BW' := by
  intro u v huv
  calc |W u v + W' u v| ≤ |W u v| + |W' u v| := abs_add _ _
    _ ≤ BW + BW' := add_le_add (hW u v huv) (hW' u v huv)

/-- |2 - W² - W'²| の上界。 -/
theorem abs_two_sub_sq_le {K : Set (ℝ × ℝ)} {W W' : ℝ → ℝ → ℝ} {BW BW' : ℝ}
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW') :
    ∀ u v, (u, v) ∈ K → |2 - (W u v) ^ 2 - (W' u v) ^ 2| ≤ 2 + BW ^ 2 + BW' ^ 2 := by
  intro u v huv
  have h1 : |2 - (W u v) ^ 2| ≤ 2 + BW ^ 2 := by
    calc |2 - (W u v) ^ 2| ≤ |2| + |(W u v) ^ 2| := abs_sub _ _
      _ = 2 + |W u v| ^ 2 := by simp [abs_pow]
      _ ≤ 2 + BW ^ 2 := by
          have hp := pow_le_pow_left₀ (abs_nonneg _) (hW u v huv) 2
          linarith
  calc |2 - (W u v) ^ 2 - (W' u v) ^ 2|
      ≤ |2 - (W u v) ^ 2| + |(W' u v) ^ 2| := abs_sub _ _
    _ = |2 - (W u v) ^ 2| + |W' u v| ^ 2 := by simp [abs_pow]
    _ ≤ (2 + BW ^ 2) + BW' ^ 2 := by
        apply add_le_add h1
        exact pow_le_pow_left₀ (abs_nonneg _) (hW' u v huv) 2
    _ = 2 + BW ^ 2 + BW' ^ 2 := by ring

/-- |r² + r r' + r'²| の上界。 -/
theorem abs_r_quad_le {K : Set (ℝ × ℝ)} {r r' : ℝ → ℝ → ℝ} {Br Br' : ℝ}
    (hBrnn : 0 ≤ Br)
    (hr : ∀ u v, (u, v) ∈ K → |r u v| ≤ Br)
    (hr' : ∀ u v, (u, v) ∈ K → |r' u v| ≤ Br') :
    ∀ u v, (u, v) ∈ K →
      |(r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2| ≤ Br ^ 2 + Br * Br' + Br' ^ 2 := by
  intro u v huv
  have hr'' := hr u v huv
  have hr''' := hr' u v huv
  have hBr'nn : 0 ≤ Br' := (abs_nonneg _).trans hr'''
  calc |(r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2|
      ≤ |(r u v) ^ 2 + (r u v) * (r' u v)| + |(r' u v) ^ 2| := abs_add _ _
    _ ≤ (|(r u v) ^ 2| + |(r u v) * (r' u v)|) + |(r' u v) ^ 2| := by
        apply add_le_add_right (abs_add _ _) _
    _ = |r u v| ^ 2 + |r u v| * |r' u v| + |r' u v| ^ 2 := by simp [abs_mul, abs_pow]
    _ ≤ Br ^ 2 + Br * Br' + Br' ^ 2 := by
        apply add_le_add
        · apply add_le_add
          · exact pow_le_pow_left₀ (abs_nonneg _) hr'' 2
          · exact mul_le_mul hr'' hr''' (abs_nonneg _) hBrnn
        · exact pow_le_pow_left₀ (abs_nonneg _) hr''' 2

/-- |r³ + r²r' + r r'² + r'³| の上界。 -/
theorem abs_r_cubic_le {K : Set (ℝ × ℝ)} {r r' : ℝ → ℝ → ℝ} {Br Br' : ℝ}
    (hBrnn : 0 ≤ Br)
    (hr : ∀ u v, (u, v) ∈ K → |r u v| ≤ Br)
    (hr' : ∀ u v, (u, v) ∈ K → |r' u v| ≤ Br') :
    ∀ u v, (u, v) ∈ K →
      |(r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2 + (r' u v) ^ 3|
        ≤ Br ^ 3 + Br ^ 2 * Br' + Br * Br' ^ 2 + Br' ^ 3 := by
  intro u v huv
  have hr'' := hr u v huv
  have hr''' := hr' u v huv
  have hBr'nn : 0 ≤ Br' := (abs_nonneg _).trans hr'''
  have h2 : |r u v| ^ 2 ≤ Br ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hr'' 2
  have h2' : |r' u v| ^ 2 ≤ Br' ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hr''' 2
  have h3 : |r u v| ^ 3 ≤ Br ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hr'' 3
  have h3' : |r' u v| ^ 3 ≤ Br' ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hr''' 3
  have hm1 : |r u v| ^ 2 * |r' u v| ≤ Br ^ 2 * Br' :=
    mul_le_mul h2 hr''' (abs_nonneg _) (by positivity)
  have hm2 : |r u v| * |r' u v| ^ 2 ≤ Br * Br' ^ 2 :=
    mul_le_mul hr'' h2' (by positivity) hBrnn
  calc |(r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2 + (r' u v) ^ 3|
      ≤ |(r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2| + |(r' u v) ^ 3| :=
        abs_add _ _
    _ ≤ (|(r u v) ^ 3 + (r u v) ^ 2 * (r' u v)| + |(r u v) * (r' u v) ^ 2|)
        + |(r' u v) ^ 3| := by
        apply add_le_add_right (abs_add _ _) _
    _ ≤ ((|(r u v) ^ 3| + |(r u v) ^ 2 * (r' u v)|) + |(r u v) * (r' u v) ^ 2|)
        + |(r' u v) ^ 3| := by
        apply add_le_add_right (add_le_add_right (abs_add _ _) _) _
    _ = (|r u v| ^ 3 + |r u v| ^ 2 * |r' u v| + |r u v| * |r' u v| ^ 2)
        + |r' u v| ^ 3 := by simp [abs_mul, abs_pow]
    _ ≤ (Br ^ 3 + Br ^ 2 * Br' + Br * Br' ^ 2) + Br' ^ 3 := by
        apply add_le_add
        · exact add_le_add (add_le_add h3 hm1) hm2
        · exact h3'
    _ = Br ^ 3 + Br ^ 2 * Br' + Br * Br' ^ 2 + Br' ^ 3 := by ring

/-! ### δr の係数の有界性 -/

/-- 差の r 方程式の δOm 係数の有界性。 -/
theorem diffRCoefOm_bound {K : Set (ℝ × ℝ)} {W r : ℝ → ℝ → ℝ} {BW mr : ℝ}
    (hmr : 0 < mr)
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K →
      |diffRCoefOm W r u v|
        ≤ 2⁻¹ * ((1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 2 + 1) * mr⁻¹ := by
  intro u v huv
  have hW' := hW u v huv
  have hBWnn : 0 ≤ BW := (abs_nonneg _).trans hW'
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  have hrinv2 : |(r u v)⁻¹| ^ 2 ≤ mr⁻¹ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 2
  have h1 := abs_one_sub_sq_le hW u v huv
  have h2 : |(1 - (W u v) ^ 2) ^ 2| ≤ (1 + BW ^ 2) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : |(1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2| ≤ (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 2 := by
    have hrinv2' : |(r u v)⁻¹ ^ 2| ≤ mr⁻¹ ^ 2 := by
      rw [abs_pow]; exact hrinv2
    rw [abs_mul]
    exact mul_le_mul h2 hrinv2' (by positivity) (by positivity)
  have h4 : |(1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2 - 1|
      ≤ (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 2 + 1 := by
    calc |(1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2 - 1|
        ≤ |(1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2| + |1| := abs_sub _ _
      _ = |(1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2| + 1 := by simp
      _ ≤ (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 2 + 1 := add_le_add_right h3 1
  show |2⁻¹ * ((1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 2 - 1) * (r u v)⁻¹| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  gcongr

/-- 差の r 方程式の δW 係数の有界性。 -/
theorem diffRCoefW_bound {K : Set (ℝ × ℝ)} {Om' W W' r : ℝ → ℝ → ℝ}
    {BOm' BW BW' mr : ℝ}
    (hmr : 0 < mr)
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K →
      |diffRCoefW Om' W W' r u v|
        ≤ 2⁻¹ * BOm' * ((BW + BW') * (2 + BW ^ 2 + BW' ^ 2) * mr⁻¹ ^ 3) := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hW'' := hW u v huv
  have hW''' := hW' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hBWnn : 0 ≤ BW := (abs_nonneg _).trans hW''
  have hBW'nn : 0 ≤ BW' := (abs_nonneg _).trans hW'''
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  have hrinv3 : |(r u v)⁻¹| ^ 3 ≤ mr⁻¹ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 3
  have hsum := abs_add_le' hW hW' u v huv
  have htwo := abs_two_sub_sq_le hW hW' u v huv
  show |2⁻¹ * Om' u v * (-((W u v) + (W' u v)) * (2 - (W u v) ^ 2 - (W' u v) ^ 2)
        * ((r u v)⁻¹) ^ 3)| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_pow,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  gcongr

/-- 差の r 方程式の δr 係数の有界性。 -/
theorem diffRCoefR_bound {K : Set (ℝ × ℝ)} {Om' W' r r' : ℝ → ℝ → ℝ}
    {BOm' BW' Br Br' BDur' BDvr' mr mr' : ℝ}
    (hmr : 0 < mr) (hmr' : 0 < mr')
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
    (hr : ∀ u v, (u, v) ∈ K → |r u v| ≤ Br)
    (hr' : ∀ u v, (u, v) ∈ K → |r' u v| ≤ Br')
    (hDur' : ∀ u v, (u, v) ∈ K → |Du r' u v| ≤ BDur')
    (hDvr' : ∀ u v, (u, v) ∈ K → |Dv r' u v| ≤ BDvr')
    (hrlow : ∀ u v, (u, v) ∈ K → mr ≤ r u v)
    (hrlow' : ∀ u v, (u, v) ∈ K → mr' ≤ r' u v) :
    ∀ u v, (u, v) ∈ K →
      |diffRCoefR Om' W' r r' u v|
        ≤ 2⁻¹ * BOm' * ((1 + BW' ^ 2) ^ 2 * ((Br ^ 2 + Br * Br' + Br' ^ 2)
            * mr⁻¹ ^ 3 * mr'⁻¹ ^ 3) + mr⁻¹ * mr'⁻¹)
          + BDur' * BDvr' * mr⁻¹ * mr'⁻¹ := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hW'' := hW' u v huv
  have hr'' := hr u v huv
  have hr''' := hr' u v huv
  have hDur'' := hDur' u v huv
  have hDvr'' := hDvr' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hBW'nn : 0 ≤ BW' := (abs_nonneg _).trans hW''
  have hBrnn : 0 ≤ Br := (abs_nonneg _).trans hr''
  have hBr'nn : 0 ≤ Br' := (abs_nonneg _).trans hr'''
  have hBDur'nn : 0 ≤ BDur' := (abs_nonneg _).trans hDur''
  have hBDvr'nn : 0 ≤ BDvr' := (abs_nonneg _).trans hDvr''
  have hmrnn : 0 ≤ mr⁻¹ := inv_nonneg.mpr hmr.le
  have hmr'nn : 0 ≤ mr'⁻¹ := inv_nonneg.mpr hmr'.le
  have hrinv := abs_inv_le_of_le hmr hrlow u v huv
  have hrinv' := abs_inv_le_of_le hmr' hrlow' u v huv
  have hrinv3 : |(r u v)⁻¹| ^ 3 ≤ mr⁻¹ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 3
  have hrinv3' : |(r' u v)⁻¹| ^ 3 ≤ mr'⁻¹ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv' 3
  have h1 := abs_one_sub_sq_le hW' u v huv
  have h1sq : |(1 - (W' u v) ^ 2) ^ 2| ≤ (1 + BW' ^ 2) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h1sq' : |1 - (W' u v) ^ 2| ^ 2 ≤ (1 + BW' ^ 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hquad := abs_r_quad_le hBrnn hr hr' u v huv
  have hA : |(1 - (W' u v) ^ 2) ^ 2
        * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
          * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3)|
      ≤ (1 + BW' ^ 2) ^ 2 * ((Br ^ 2 + Br * Br' + Br' ^ 2) * mr⁻¹ ^ 3 * mr'⁻¹ ^ 3) := by
    simp only [abs_mul, abs_neg, abs_pow]
    gcongr
  have hB : |(1 - (W' u v) ^ 2) ^ 2
        * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
          * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3) + (r u v)⁻¹ * (r' u v)⁻¹|
      ≤ (1 + BW' ^ 2) ^ 2 * ((Br ^ 2 + Br * Br' + Br' ^ 2) * mr⁻¹ ^ 3 * mr'⁻¹ ^ 3)
          + mr⁻¹ * mr'⁻¹ := by
    calc |_|
        ≤ |(1 - (W' u v) ^ 2) ^ 2
            * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
              * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3)|
            + |(r u v)⁻¹ * (r' u v)⁻¹| := abs_add _ _
      _ ≤ (1 + BW' ^ 2) ^ 2 * ((Br ^ 2 + Br * Br' + Br' ^ 2) * mr⁻¹ ^ 3 * mr'⁻¹ ^ 3)
            + mr⁻¹ * mr'⁻¹ := by
          apply add_le_add hA
          rw [abs_mul]
          exact mul_le_mul hrinv hrinv' (abs_nonneg _) hmrnn
  show |2⁻¹ * Om' u v * ((1 - (W' u v) ^ 2) ^ 2
        * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
          * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3)
      + (r u v)⁻¹ * (r' u v)⁻¹)
      + (Du r' u v) * (Dv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹| ≤ _
  calc |2⁻¹ * Om' u v * ((1 - (W' u v) ^ 2) ^ 2
          * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
            * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3)
        + (r u v)⁻¹ * (r' u v)⁻¹)
        + (Du r' u v) * (Dv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹|
      ≤ |2⁻¹ * Om' u v * ((1 - (W' u v) ^ 2) ^ 2
            * (-((r u v) ^ 2 + (r u v) * (r' u v) + (r' u v) ^ 2)
              * ((r u v)⁻¹) ^ 3 * ((r' u v)⁻¹) ^ 3)
          + (r u v)⁻¹ * (r' u v)⁻¹)|
          + |(Du r' u v) * (Dv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹| := abs_add _ _
    _ ≤ 2⁻¹ * BOm' * ((1 + BW' ^ 2) ^ 2 * ((Br ^ 2 + Br * Br' + Br' ^ 2)
            * mr⁻¹ ^ 3 * mr'⁻¹ ^ 3) + mr⁻¹ * mr'⁻¹)
          + BDur' * BDvr' * mr⁻¹ * mr'⁻¹ := by
        apply add_le_add
        · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
          gcongr
        · rw [abs_mul, abs_mul, abs_mul]
          gcongr

/-- 差の r 方程式の δru 係数の有界性。 -/
theorem diffRCoefRu_bound {K : Set (ℝ × ℝ)} {r : ℝ → ℝ → ℝ} {BDvr mr : ℝ}
    (hmr : 0 < mr)
    (hDvr : ∀ u v, (u, v) ∈ K → |Dv r u v| ≤ BDvr)
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K → |diffRCoefRu r u v| ≤ BDvr * mr⁻¹ := by
  intro u v huv
  have hDvr' := hDvr u v huv
  have hBDvrnn : 0 ≤ BDvr := (abs_nonneg _).trans hDvr'
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  show |-(Dv r u v) * (r u v)⁻¹| ≤ _
  rw [abs_mul, abs_neg]
  exact mul_le_mul hDvr' hrinv (abs_nonneg _) hBDvrnn

/-- 差の r 方程式の δrv 係数の有界性。 -/
theorem diffRCoefRv_bound {K : Set (ℝ × ℝ)} {r r' : ℝ → ℝ → ℝ} {BDur' mr : ℝ}
    (hmr : 0 < mr)
    (hDur' : ∀ u v, (u, v) ∈ K → |Du r' u v| ≤ BDur')
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K → |diffRCoefRv r r' u v| ≤ BDur' * mr⁻¹ := by
  intro u v huv
  have hDur'' := hDur' u v huv
  have hBDur'nn : 0 ≤ BDur' := (abs_nonneg _).trans hDur''
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  show |-(Du r' u v) * (r u v)⁻¹| ≤ _
  rw [abs_mul, abs_neg]
  exact mul_le_mul hDur'' hrinv (abs_nonneg _) hBDur'nn

/-! ### δΩ の係数の有界性 -/

/-- 差の Ω 方程式の δOu 係数の有界性。 -/
theorem diffOmCoefOu_bound {K : Set (ℝ × ℝ)} {Om : ℝ → ℝ → ℝ} {BDvOm mOm : ℝ}
    (hmOm : 0 < mOm)
    (hDvOm : ∀ u v, (u, v) ∈ K → |Dv Om u v| ≤ BDvOm)
    (hOm : ∀ u v, (u, v) ∈ K → mOm ≤ Om u v) :
    ∀ u v, (u, v) ∈ K → |diffOmCoefOu Om u v| ≤ BDvOm * mOm⁻¹ := by
  intro u v huv
  have hDvOm' := hDvOm u v huv
  have hBDvOmnn : 0 ≤ BDvOm := (abs_nonneg _).trans hDvOm'
  have hOminv := abs_inv_le_of_le hmOm hOm u v huv
  show |(Dv Om u v) * (Om u v)⁻¹| ≤ _
  rw [abs_mul]
  exact mul_le_mul hDvOm' hOminv (abs_nonneg _) hBDvOmnn

/-- 差の Ω 方程式の δOv 係数の有界性。 -/
theorem diffOmCoefOv_bound {K : Set (ℝ × ℝ)} {Om Om' : ℝ → ℝ → ℝ} {BDuOm' mOm : ℝ}
    (hmOm : 0 < mOm)
    (hDuOm' : ∀ u v, (u, v) ∈ K → |Du Om' u v| ≤ BDuOm')
    (hOm : ∀ u v, (u, v) ∈ K → mOm ≤ Om u v) :
    ∀ u v, (u, v) ∈ K → |diffOmCoefOv Om Om' u v| ≤ BDuOm' * mOm⁻¹ := by
  intro u v huv
  have hDuOm'' := hDuOm' u v huv
  have hBDuOm'nn : 0 ≤ BDuOm' := (abs_nonneg _).trans hDuOm''
  have hOminv := abs_inv_le_of_le hmOm hOm u v huv
  show |(Du Om' u v) * (Om u v)⁻¹| ≤ _
  rw [abs_mul]
  exact mul_le_mul hDuOm'' hOminv (abs_nonneg _) hBDuOm'nn

/-- 差の Ω 方程式の δOm 係数の有界性。 -/
theorem diffOmCoefOm_bound {K : Set (ℝ × ℝ)} {Om Om' W r : ℝ → ℝ → ℝ}
    {BDuOm' BDvOm' BDuvr BOm BOm' BW mOm mOm' mr : ℝ}
    (hmOm : 0 < mOm) (hmOm' : 0 < mOm') (hmr : 0 < mr)
    (hDuOm' : ∀ u v, (u, v) ∈ K → |Du Om' u v| ≤ BDuOm')
    (hDvOm' : ∀ u v, (u, v) ∈ K → |Dv Om' u v| ≤ BDvOm')
    (hDuvr : ∀ u v, (u, v) ∈ K → |Duv r u v| ≤ BDuvr)
    (hOm : ∀ u v, (u, v) ∈ K → |Om u v| ≤ BOm)
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hOmlow : ∀ u v, (u, v) ∈ K → mOm ≤ Om u v)
    (hOm'low : ∀ u v, (u, v) ∈ K → mOm' ≤ Om' u v)
    (hrlow : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K →
      |diffOmCoefOm Om Om' W r u v|
        ≤ BDuOm' * BDvOm' * mOm⁻¹ * mOm'⁻¹ + 2 * BDuvr * mr⁻¹
            + (BOm + BOm') * (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 4 := by
  intro u v huv
  have hDuOm'' := hDuOm' u v huv
  have hDvOm'' := hDvOm' u v huv
  have hDuvr' := hDuvr u v huv
  have hOm'' := hOm u v huv
  have hOm''' := hOm' u v huv
  have hW' := hW u v huv
  have hBDuOm'nn : 0 ≤ BDuOm' := (abs_nonneg _).trans hDuOm''
  have hBDvOm'nn : 0 ≤ BDvOm' := (abs_nonneg _).trans hDvOm''
  have hBDuvrnn : 0 ≤ BDuvr := (abs_nonneg _).trans hDuvr'
  have hBOmnn : 0 ≤ BOm := (abs_nonneg _).trans hOm''
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm'''
  have hBWnn : 0 ≤ BW := (abs_nonneg _).trans hW'
  have hmOmnn : 0 ≤ mOm⁻¹ := inv_nonneg.mpr hmOm.le
  have hmOm'nn : 0 ≤ mOm'⁻¹ := inv_nonneg.mpr hmOm'.le
  have hmrnn : 0 ≤ mr⁻¹ := inv_nonneg.mpr hmr.le
  have hOminv := abs_inv_le_of_le hmOm hOmlow u v huv
  have hOminv' := abs_inv_le_of_le hmOm' hOm'low u v huv
  have hrinv := abs_inv_le_of_le hmr hrlow u v huv
  have hrinv4 : |(r u v)⁻¹| ^ 4 ≤ mr⁻¹ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 4
  have h1 := abs_one_sub_sq_le hW u v huv
  have h1sq : |(1 - (W u v) ^ 2) ^ 2| ≤ (1 + BW ^ 2) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h1sq' : |1 - (W u v) ^ 2| ^ 2 ≤ (1 + BW ^ 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hX : |-(Du Om' u v) * (Dv Om' u v) * (Om u v)⁻¹ * (Om' u v)⁻¹|
      ≤ BDuOm' * BDvOm' * mOm⁻¹ * mOm'⁻¹ := by
    simp only [abs_mul, abs_neg]
    gcongr
  have hY : |2 * (Duv r u v) * (r u v)⁻¹| ≤ 2 * BDuvr * mr⁻¹ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    gcongr
  have hZ : |((Om u v) + (Om' u v)) * (1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 4|
      ≤ (BOm + BOm') * (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 4 := by
    simp only [abs_mul, abs_pow]
    gcongr
    · calc |Om u v + Om' u v| ≤ |Om u v| + |Om' u v| := abs_add _ _
        _ ≤ BOm + BOm' := add_le_add hOm'' hOm'''
  show |-(Du Om' u v) * (Dv Om' u v) * (Om u v)⁻¹ * (Om' u v)⁻¹
        - 2 * (Duv r u v) * (r u v)⁻¹
        - ((Om u v) + (Om' u v)) * (1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 4| ≤ _
  calc |-(Du Om' u v) * (Dv Om' u v) * (Om u v)⁻¹ * (Om' u v)⁻¹
        - 2 * (Duv r u v) * (r u v)⁻¹
        - ((Om u v) + (Om' u v)) * (1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 4|
      ≤ |-(Du Om' u v) * (Dv Om' u v) * (Om u v)⁻¹ * (Om' u v)⁻¹
            - 2 * (Duv r u v) * (r u v)⁻¹|
          + |((Om u v) + (Om' u v)) * (1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 4| :=
        abs_sub _ _
    _ ≤ (|-(Du Om' u v) * (Dv Om' u v) * (Om u v)⁻¹ * (Om' u v)⁻¹|
            + |2 * (Duv r u v) * (r u v)⁻¹|)
          + |((Om u v) + (Om' u v)) * (1 - (W u v) ^ 2) ^ 2 * ((r u v)⁻¹) ^ 4| := by
        apply add_le_add_right (abs_sub _ _) _
    _ ≤ (BDuOm' * BDvOm' * mOm⁻¹ * mOm'⁻¹ + 2 * BDuvr * mr⁻¹)
          + (BOm + BOm') * (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 4 := by
        apply add_le_add (add_le_add hX hY) hZ
    _ = BDuOm' * BDvOm' * mOm⁻¹ * mOm'⁻¹ + 2 * BDuvr * mr⁻¹
          + (BOm + BOm') * (1 + BW ^ 2) ^ 2 * mr⁻¹ ^ 4 := by ring

/-- 差の Ω 方程式の δruv 係数の有界性。 -/
theorem diffOmCoefRuv_bound {K : Set (ℝ × ℝ)} {Om' r : ℝ → ℝ → ℝ} {BOm' mr : ℝ}
    (hmr : 0 < mr)
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K → |diffOmCoefRuv Om' r u v| ≤ 2 * BOm' * mr⁻¹ := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  show |-2 * Om' u v * (r u v)⁻¹| ≤ _
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  gcongr

/-- 差の Ω 方程式の δr 係数の有界性。 -/
theorem diffOmCoefR_bound {K : Set (ℝ × ℝ)} {Om' W' r r' : ℝ → ℝ → ℝ}
    {BOm' BW' Br Br' BDuvr' mr mr' : ℝ}
    (hmr : 0 < mr) (hmr' : 0 < mr')
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
    (hr : ∀ u v, (u, v) ∈ K → |r u v| ≤ Br)
    (hr' : ∀ u v, (u, v) ∈ K → |r' u v| ≤ Br')
    (hDuvr' : ∀ u v, (u, v) ∈ K → |Duv r' u v| ≤ BDuvr')
    (hrlow : ∀ u v, (u, v) ∈ K → mr ≤ r u v)
    (hrlow' : ∀ u v, (u, v) ∈ K → mr' ≤ r' u v) :
    ∀ u v, (u, v) ∈ K →
      |diffOmCoefR Om' W' r r' u v|
        ≤ 2 * BOm' * BDuvr' * mr⁻¹ * mr'⁻¹
            + BOm' ^ 2 * (1 + BW' ^ 2) ^ 2
              * (Br ^ 3 + Br ^ 2 * Br' + Br * Br' ^ 2 + Br' ^ 3)
              * mr⁻¹ ^ 4 * mr'⁻¹ ^ 4 := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hW'' := hW' u v huv
  have hr'' := hr u v huv
  have hr''' := hr' u v huv
  have hDuvr'' := hDuvr' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hBW'nn : 0 ≤ BW' := (abs_nonneg _).trans hW''
  have hBrnn : 0 ≤ Br := (abs_nonneg _).trans hr''
  have hBr'nn : 0 ≤ Br' := (abs_nonneg _).trans hr'''
  have hBDuvr'nn : 0 ≤ BDuvr' := (abs_nonneg _).trans hDuvr''
  have hmrnn : 0 ≤ mr⁻¹ := inv_nonneg.mpr hmr.le
  have hmr'nn : 0 ≤ mr'⁻¹ := inv_nonneg.mpr hmr'.le
  have hrinv := abs_inv_le_of_le hmr hrlow u v huv
  have hrinv' := abs_inv_le_of_le hmr' hrlow' u v huv
  have hrinv4 : |(r u v)⁻¹| ^ 4 ≤ mr⁻¹ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 4
  have hrinv4' : |(r' u v)⁻¹| ^ 4 ≤ mr'⁻¹ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv' 4
  have h1 := abs_one_sub_sq_le hW' u v huv
  have h1sq : |(1 - (W' u v) ^ 2) ^ 2| ≤ (1 + BW' ^ 2) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h1sq' : |1 - (W' u v) ^ 2| ^ 2 ≤ (1 + BW' ^ 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hOm'sq : |Om' u v| ^ 2 ≤ BOm' ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hOm'' 2
  have hcubic := abs_r_cubic_le hBrnn hr hr' u v huv
  have hP : |2 * Om' u v * (Duv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹|
      ≤ 2 * BOm' * BDuvr' * mr⁻¹ * mr'⁻¹ := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    gcongr
  have hQ : |(Om' u v) ^ 2 * (1 - (W' u v) ^ 2) ^ 2
        * ((r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2 + (r' u v) ^ 3)
        * ((r u v)⁻¹) ^ 4 * ((r' u v)⁻¹) ^ 4|
      ≤ BOm' ^ 2 * (1 + BW' ^ 2) ^ 2
          * (Br ^ 3 + Br ^ 2 * Br' + Br * Br' ^ 2 + Br' ^ 3)
          * mr⁻¹ ^ 4 * mr'⁻¹ ^ 4 := by
    simp only [abs_mul, abs_pow]
    gcongr
  show |2 * Om' u v * (Duv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹
        + (Om' u v) ^ 2 * (1 - (W' u v) ^ 2) ^ 2
          * ((r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2
            + (r' u v) ^ 3) * ((r u v)⁻¹) ^ 4 * ((r' u v)⁻¹) ^ 4| ≤ _
  calc |2 * Om' u v * (Duv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹
        + (Om' u v) ^ 2 * (1 - (W' u v) ^ 2) ^ 2
          * ((r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2
            + (r' u v) ^ 3) * ((r u v)⁻¹) ^ 4 * ((r' u v)⁻¹) ^ 4|
      ≤ |2 * Om' u v * (Duv r' u v) * (r u v)⁻¹ * (r' u v)⁻¹|
          + |(Om' u v) ^ 2 * (1 - (W' u v) ^ 2) ^ 2
            * ((r u v) ^ 3 + (r u v) ^ 2 * (r' u v) + (r u v) * (r' u v) ^ 2
              + (r' u v) ^ 3) * ((r u v)⁻¹) ^ 4 * ((r' u v)⁻¹) ^ 4| := abs_add _ _
    _ ≤ 2 * BOm' * BDuvr' * mr⁻¹ * mr'⁻¹
          + BOm' ^ 2 * (1 + BW' ^ 2) ^ 2
            * (Br ^ 3 + Br ^ 2 * Br' + Br * Br' ^ 2 + Br' ^ 3)
            * mr⁻¹ ^ 4 * mr'⁻¹ ^ 4 := add_le_add hP hQ

/-- 差の Ω 方程式の δW 係数の有界性。 -/
theorem diffOmCoefW_bound {K : Set (ℝ × ℝ)} {Om' W W' r : ℝ → ℝ → ℝ}
    {BOm' BW BW' mr : ℝ}
    (hmr : 0 < mr)
    (hOm' : ∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
    (hW : ∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
    (hW' : ∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
    (hr : ∀ u v, (u, v) ∈ K → mr ≤ r u v) :
    ∀ u v, (u, v) ∈ K →
      |diffOmCoefW Om' W W' r u v|
        ≤ BOm' ^ 2 * (BW + BW') * (2 + BW ^ 2 + BW' ^ 2) * mr⁻¹ ^ 4 := by
  intro u v huv
  have hOm'' := hOm' u v huv
  have hW'' := hW u v huv
  have hW''' := hW' u v huv
  have hBOm'nn : 0 ≤ BOm' := (abs_nonneg _).trans hOm''
  have hBWnn : 0 ≤ BW := (abs_nonneg _).trans hW''
  have hBW'nn : 0 ≤ BW' := (abs_nonneg _).trans hW'''
  have hrinv := abs_inv_le_of_le hmr hr u v huv
  have hrinv4 : |(r u v)⁻¹| ^ 4 ≤ mr⁻¹ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hrinv 4
  have hOm'sq : |Om' u v| ^ 2 ≤ BOm' ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hOm'' 2
  have hsum := abs_add_le' hW hW' u v huv
  have htwo := abs_two_sub_sq_le hW hW' u v huv
  show |(Om' u v) ^ 2 * ((W u v) + (W' u v)) * (2 - (W u v) ^ 2 - (W' u v) ^ 2)
        * ((r u v)⁻¹) ^ 4| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
  gcongr

end CFT.WedgeDifferenceCoefficients
