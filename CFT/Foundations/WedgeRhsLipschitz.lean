import CFT.Foundations.WaveCharacteristicIntegralEquation

/-!
  命題集 `LEAN_GAP_TREES.md` 4-17（準線形系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上）
  の第3層 (c)：矩形の小ささによる C¹ ノルムでの縮小評価 — の第1段。
  凍結した右辺 wedgeRhsR/Om/W の差を、2つの場のジェット（値と1階微分、
  Ω 方程式では r の混合微分も）の差で抑えるリプシッツ評価（明示定数つき）と、
  二重積分の差の評価（矩形の面積 × 上限）を証明する。

  右辺は r と Ω による割り算を含む有理関数なので、評価は r ≥ r₀ > 0
  （1/r 特異性の回避）と Ω ≥ Om₀ > 0（Ω 方程式の割り算）のもとで行う。
  定数はすべて明示的で、矩形のサイズには依存しない（縮小因子は
  積分表示の二重積分から来る面積因子 (u - u₀)(v - v₀) である）。

  残り（4-17 の第3層 (c) の組み立て）：C¹ ノルムの定義と、反復写像の
  像の C¹ ノルムの差が矩形の小ささで縮小することの証明。
  キャップ（r = 0）を含む版は 4-16 に残る。
-/

namespace CFT.WedgeRhsLip

open CFT.Wedge
open CFT.WaveIntegralEq

noncomputable section

/-- 積の差の評価（2因子）。 -/
theorem abs_mul_sub_mul_le {a a' b b' M_a M_b' : ℝ}
    (ha : |a| ≤ M_a) (hb' : |b'| ≤ M_b') :
    |a * b - a' * b'| ≤ |a - a'| * M_b' + M_a * |b - b'| := by
  have h : a * b - a' * b' = (a - a') * b' + a * (b - b') := by ring
  calc |a * b - a' * b'| = |(a - a') * b' + a * (b - b')| := by rw [h]
    _ ≤ |(a - a') * b'| + |a * (b - b')| := abs_add _ _
    _ = |a - a'| * |b'| + |a| * |b - b'| := by rw [abs_mul, abs_mul]
    _ ≤ |a - a'| * M_b' + M_a * |b - b'| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hb' (abs_nonneg _))
          (mul_le_mul_of_nonneg_right ha (abs_nonneg _))

/-- 逆数の差の評価（下から r₀ で抑えられた正の数同士）。 -/
theorem abs_inv_sub_le {x y r₀ : ℝ} (hr₀ : 0 < r₀) (hx : r₀ ≤ x) (hy : r₀ ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| / r₀ ^ 2 := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₀ hx)
  have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₀ hy)
  have hxy : r₀ ^ 2 ≤ x * y := by
    calc r₀ ^ 2 = r₀ * r₀ := by ring
      _ ≤ x * y := mul_le_mul hx hy (le_of_lt hr₀) (le_of_lt (lt_of_lt_of_le hr₀ hx))
  have hax : |x| = x := abs_of_pos (lt_of_lt_of_le hr₀ hx)
  have hay : |y| = y := abs_of_pos (lt_of_lt_of_le hr₀ hy)
  rw [inv_sub_inv hx0 hy0, abs_div, abs_mul, hax, hay, abs_sub_comm]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hxy

/-- 平方の差の評価。 -/
theorem abs_sq_sub_le {x y M : ℝ} (hxM : |x| ≤ M) (hyM : |y| ≤ M) :
    |x ^ 2 - y ^ 2| ≤ 2 * M * |x - y| := by
  have hfac : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  calc |x ^ 2 - y ^ 2| = |(x - y) * (x + y)| := by rw [hfac]
    _ = |x - y| * |x + y| := abs_mul _ _
    _ ≤ |x - y| * (2 * M) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |x + y| ≤ |x| + |y| := abs_add _ _
          _ ≤ M + M := add_le_add hxM hyM
          _ = 2 * M := by ring
    _ = 2 * M * |x - y| := by ring

/-- 逆二乗の差の評価。 -/
theorem abs_inv_sq_sub_le {x y r₀ M : ℝ} (hr₀ : 0 < r₀)
    (hx : r₀ ≤ x) (hy : r₀ ≤ y) (hxM : |x| ≤ M) (hyM : |y| ≤ M) :
    |(x ^ 2)⁻¹ - (y ^ 2)⁻¹| ≤ 2 * M * |x - y| / r₀ ^ 4 := by
  have h1 : |(x ^ 2)⁻¹ - (y ^ 2)⁻¹| ≤ |x ^ 2 - y ^ 2| / (r₀ ^ 2) ^ 2 :=
    abs_inv_sub_le (show (0:ℝ) < r₀ ^ 2 by positivity)
      (pow_le_pow_left₀ (le_of_lt hr₀) hx 2) (pow_le_pow_left₀ (le_of_lt hr₀) hy 2)
  have h2 : |x ^ 2 - y ^ 2| ≤ 2 * M * |x - y| := abs_sq_sub_le hxM hyM
  calc |(x ^ 2)⁻¹ - (y ^ 2)⁻¹| ≤ |x ^ 2 - y ^ 2| / (r₀ ^ 2) ^ 2 := h1
    _ ≤ (2 * M * |x - y|) / (r₀ ^ 2) ^ 2 := by
        apply div_le_div_of_nonneg_right h2 (by positivity)
    _ = 2 * M * |x - y| / r₀ ^ 4 := by ring

/-- 4乗の差の評価。 -/
theorem abs_pow4_sub_le {x y M : ℝ} (hxM : |x| ≤ M) (hyM : |y| ≤ M) :
    |x ^ 4 - y ^ 4| ≤ 4 * M ^ 3 * |x - y| := by
  have hfac : x ^ 4 - y ^ 4 = (x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2) := by ring
  have hsq : |x ^ 2 - y ^ 2| ≤ 2 * M * |x - y| := abs_sq_sub_le hxM hyM
  have hsum : |x ^ 2 + y ^ 2| ≤ 2 * M ^ 2 := by
    calc |x ^ 2 + y ^ 2| ≤ |x ^ 2| + |y ^ 2| := abs_add _ _
      _ = |x| ^ 2 + |y| ^ 2 := by rw [abs_pow, abs_pow]
      _ ≤ M ^ 2 + M ^ 2 := add_le_add (pow_le_pow_left₀ (abs_nonneg _) hxM 2)
          (pow_le_pow_left₀ (abs_nonneg _) hyM 2)
      _ = 2 * M ^ 2 := by ring
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hxM
  calc |x ^ 4 - y ^ 4| = |(x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2)| := by rw [hfac]
    _ = |x ^ 2 - y ^ 2| * |x ^ 2 + y ^ 2| := abs_mul _ _
    _ ≤ (2 * M * |x - y|) * (2 * M ^ 2) :=
        mul_le_mul hsq hsum (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hM) (abs_nonneg _))
    _ = 4 * M ^ 3 * |x - y| := by ring

/-- 逆4乗の差の評価。 -/
theorem abs_inv_pow4_sub_le {x y r₀ M : ℝ} (hr₀ : 0 < r₀)
    (hx : r₀ ≤ x) (hy : r₀ ≤ y) (hxM : |x| ≤ M) (hyM : |y| ≤ M) :
    |(x ^ 4)⁻¹ - (y ^ 4)⁻¹| ≤ 4 * M ^ 3 * |x - y| / r₀ ^ 8 := by
  have h1 : |(x ^ 4)⁻¹ - (y ^ 4)⁻¹| ≤ |x ^ 4 - y ^ 4| / (r₀ ^ 4) ^ 2 :=
    abs_inv_sub_le (show (0:ℝ) < r₀ ^ 4 by positivity)
      (pow_le_pow_left₀ (le_of_lt hr₀) hx 4) (pow_le_pow_left₀ (le_of_lt hr₀) hy 4)
  have h2 : |x ^ 4 - y ^ 4| ≤ 4 * M ^ 3 * |x - y| := abs_pow4_sub_le hxM hyM
  calc |(x ^ 4)⁻¹ - (y ^ 4)⁻¹| ≤ |x ^ 4 - y ^ 4| / (r₀ ^ 4) ^ 2 := h1
    _ ≤ (4 * M ^ 3 * |x - y|) / (r₀ ^ 4) ^ 2 := by
        apply div_le_div_of_nonneg_right h2 (by positivity)
    _ = 4 * M ^ 3 * |x - y| / r₀ ^ 8 := by ring

/-- W * (1 - W²) のリプシッツ評価。 -/
theorem abs_polyW_sub_le {W W' M_W : ℝ} (hW : |W| ≤ M_W) (hW' : |W'| ≤ M_W) :
    |W * (1 - W ^ 2) - W' * (1 - W' ^ 2)| ≤ (1 + 3 * M_W ^ 2) * |W - W'| := by
  have hM : 0 ≤ M_W := le_trans (abs_nonneg _) hW
  have h3 : |W ^ 3 - W' ^ 3| ≤ 3 * M_W ^ 2 * |W - W'| := by
    have hfac : W ^ 3 - W' ^ 3 = (W - W') * (W ^ 2 + W * W' + W' ^ 2) := by ring
    have hsum : |W ^ 2 + W * W' + W' ^ 2| ≤ 3 * M_W ^ 2 := by
      calc |W ^ 2 + W * W' + W' ^ 2|
          ≤ |W ^ 2| + |W * W'| + |W' ^ 2| :=
            (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
        _ = |W| ^ 2 + |W| * |W'| + |W'| ^ 2 := by rw [abs_pow, abs_mul, abs_pow]
        _ ≤ M_W ^ 2 + M_W * M_W + M_W ^ 2 := by
            apply add_le_add
            · apply add_le_add
              · exact pow_le_pow_left₀ (abs_nonneg _) hW 2
              · exact mul_le_mul hW hW' (abs_nonneg _) hM
            · exact pow_le_pow_left₀ (abs_nonneg _) hW' 2
        _ = 3 * M_W ^ 2 := by ring
    calc |W ^ 3 - W' ^ 3| = |(W - W') * (W ^ 2 + W * W' + W' ^ 2)| := by rw [hfac]
      _ = |W - W'| * |W ^ 2 + W * W' + W' ^ 2| := abs_mul _ _
      _ ≤ |W - W'| * (3 * M_W ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = 3 * M_W ^ 2 * |W - W'| := by ring
  have heq : W * (1 - W ^ 2) - W' * (1 - W' ^ 2)
      = (W - W') - (W ^ 3 - W' ^ 3) := by ring
  calc |W * (1 - W ^ 2) - W' * (1 - W' ^ 2)|
      = |(W - W') - (W ^ 3 - W' ^ 3)| := by rw [heq]
    _ ≤ |W - W'| + |W ^ 3 - W' ^ 3| := abs_sub _ _
    _ ≤ |W - W'| + 3 * M_W ^ 2 * |W - W'| := add_le_add_left h3 _
    _ = (1 + 3 * M_W ^ 2) * |W - W'| := by ring

/-- W * (1 - W²) の上限。 -/
theorem abs_polyW_bound {W M_W : ℝ} (hW : |W| ≤ M_W) :
    |W * (1 - W ^ 2)| ≤ M_W * (1 + M_W ^ 2) := by
  have hM : 0 ≤ M_W := le_trans (abs_nonneg _) hW
  have h1 : |1 - W ^ 2| ≤ 1 + M_W ^ 2 := by
    calc |1 - W ^ 2| ≤ |1| + |W ^ 2| := abs_sub _ _
      _ = 1 + |W| ^ 2 := by rw [abs_one, abs_pow]
      _ ≤ 1 + M_W ^ 2 := add_le_add_left (pow_le_pow_left₀ (abs_nonneg _) hW 2) 1
  calc |W * (1 - W ^ 2)| = |W| * |1 - W ^ 2| := abs_mul _ _
    _ ≤ M_W * (1 + M_W ^ 2) :=
        mul_le_mul hW h1 (abs_nonneg _) hM

/-- (1 - W²)² のリプシッツ評価。 -/
theorem abs_polyQ_sub_le {W W' M_W : ℝ} (hW : |W| ≤ M_W) (hW' : |W'| ≤ M_W) :
    |(1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2| ≤ (4 * M_W + 4 * M_W ^ 3) * |W - W'| := by
  have hM : 0 ≤ M_W := le_trans (abs_nonneg _) hW
  have h2 : |W ^ 2 - W' ^ 2| ≤ 2 * M_W * |W - W'| := abs_sq_sub_le hW hW'
  have h4 : |W ^ 4 - W' ^ 4| ≤ 4 * M_W ^ 3 * |W - W'| := abs_pow4_sub_le hW hW'
  have heq : (1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2
      = -2 * (W ^ 2 - W' ^ 2) + (W ^ 4 - W' ^ 4) := by ring
  calc |(1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2|
      = |-2 * (W ^ 2 - W' ^ 2) + (W ^ 4 - W' ^ 4)| := by rw [heq]
    _ ≤ |-2 * (W ^ 2 - W' ^ 2)| + |W ^ 4 - W' ^ 4| := abs_add _ _
    _ = 2 * |W ^ 2 - W' ^ 2| + |W ^ 4 - W' ^ 4| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * (2 * M_W * |W - W'|) + 4 * M_W ^ 3 * |W - W'| := by
        apply add_le_add _ h4
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = (4 * M_W + 4 * M_W ^ 3) * |W - W'| := by ring

/-- (1 - W²)² の上限。 -/
theorem abs_polyQ_bound {W M_W : ℝ} (hW : |W| ≤ M_W) :
    |(1 - W ^ 2) ^ 2| ≤ (1 + M_W ^ 2) ^ 2 := by
  have h1 : |1 - W ^ 2| ≤ 1 + M_W ^ 2 := by
    calc |1 - W ^ 2| ≤ |1| + |W ^ 2| := abs_sub _ _
      _ = 1 + |W| ^ 2 := by rw [abs_one, abs_pow]
      _ ≤ 1 + M_W ^ 2 := add_le_add_left (pow_le_pow_left₀ (abs_nonneg _) hW 2) 1
  calc |(1 - W ^ 2) ^ 2| = |1 - W ^ 2| ^ 2 := by rw [abs_pow]
    _ ≤ (1 + M_W ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- W 方程式の右辺のリプシッツ評価（明示定数つき）。
    rhsW Om W r = (1/2) * Om * W * (1 - W²) / r²。 -/
theorem rhsW_sub_le {Om Om' W W' r r' M_Om M_W M_r r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (hMr : |r| ≤ M_r) (hMr' : |r'| ≤ M_r)
    (hOm : |Om| ≤ M_Om)
    (hW : |W| ≤ M_W) (hW' : |W'| ≤ M_W) :
    |rhsW Om W r - rhsW Om' W' r'|
      ≤ (M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2)) * |Om - Om'|
        + (M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2)) * |W - W'|
        + (M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4) * |r - r'| := by
  have hMOm : 0 ≤ M_Om := le_trans (abs_nonneg _) hOm
  have hMW : 0 ≤ M_W := le_trans (abs_nonneg _) hW
  have hK1 : 0 ≤ M_W * (1 + M_W ^ 2) := mul_nonneg hMW (by positivity)
  have hK2 : 0 ≤ 1 + 3 * M_W ^ 2 := by positivity
  have heq : rhsW Om W r = ((1 / 2) * Om * (W * (1 - W ^ 2))) * (r ^ 2)⁻¹ := by
    unfold rhsW; ring
  have heq' : rhsW Om' W' r' = ((1 / 2) * Om' * (W' * (1 - W' ^ 2))) * (r' ^ 2)⁻¹ := by
    unfold rhsW; ring
  rw [heq, heq']
  have hP : |W * (1 - W ^ 2) - W' * (1 - W' ^ 2)| ≤ (1 + 3 * M_W ^ 2) * |W - W'| :=
    abs_polyW_sub_le hW hW'
  have hPb : |W' * (1 - W' ^ 2)| ≤ M_W * (1 + M_W ^ 2) := abs_polyW_bound hW'
  have hPab : |W * (1 - W ^ 2)| ≤ M_W * (1 + M_W ^ 2) := abs_polyW_bound hW
  have hA : |(1 / 2) * Om * (W * (1 - W ^ 2)) - (1 / 2) * Om' * (W' * (1 - W' ^ 2))|
      ≤ (1 / 2) * |Om - Om'| * (M_W * (1 + M_W ^ 2))
        + (1 / 2) * M_Om * ((1 + 3 * M_W ^ 2) * |W - W'|) := by
    have h := abs_mul_sub_mul_le (a := (1 / 2) * Om) (a' := (1 / 2) * Om')
      (b := W * (1 - W ^ 2)) (b' := W' * (1 - W' ^ 2))
      (M_a := (1 / 2) * M_Om) (M_b' := M_W * (1 + M_W ^ 2)) ?_ hPb
    · have haa : |(1 / 2) * Om - (1 / 2) * Om'| = (1 / 2) * |Om - Om'| := by
        rw [← mul_sub, abs_mul]
        norm_num
      rw [haa] at h
      refine h.trans ?_
      apply add_le_add_left _ _
      exact mul_le_mul_of_nonneg_left hP (mul_nonneg (by norm_num) hMOm)
    · rw [abs_mul]
      have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left hOm (by norm_num)
  have hAb : |(1 / 2) * Om * (W * (1 - W ^ 2))|
      ≤ (1 / 2) * M_Om * (M_W * (1 + M_W ^ 2)) := by
    calc |(1 / 2) * Om * (W * (1 - W ^ 2))|
        = |(1 / 2) * Om| * |W * (1 - W ^ 2)| := abs_mul _ _
      _ ≤ ((1 / 2) * M_Om) * (M_W * (1 + M_W ^ 2)) := by
          apply mul_le_mul _ hPab (abs_nonneg _)
            (mul_nonneg (by norm_num) hMOm)
          rw [abs_mul]
          have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
          rw [hhalf]
          exact mul_le_mul_of_nonneg_left hOm (by norm_num)
      _ = (1 / 2) * M_Om * (M_W * (1 + M_W ^ 2)) := by ring
  have hinv : |(r ^ 2)⁻¹ - (r' ^ 2)⁻¹| ≤ 2 * M_r * |r - r'| / r₀ ^ 4 :=
    abs_inv_sq_sub_le hr₀ hr hr' hMr hMr'
  have hinvb : |(r' ^ 2)⁻¹| ≤ 1 / r₀ ^ 2 := by
    have hr2 : r₀ ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ (le_of_lt hr₀) hr' 2
    have hpos : (0:ℝ) < r' ^ 2 := lt_of_lt_of_le (by positivity) hr2
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hr2
  calc |((1 / 2) * Om * (W * (1 - W ^ 2))) * (r ^ 2)⁻¹
        - ((1 / 2) * Om' * (W' * (1 - W' ^ 2))) * (r' ^ 2)⁻¹|
      ≤ |((1 / 2) * Om * (W * (1 - W ^ 2))) - ((1 / 2) * Om' * (W' * (1 - W' ^ 2)))|
          * (1 / r₀ ^ 2)
        + (1 / 2) * M_Om * (M_W * (1 + M_W ^ 2))
          * (2 * M_r * |r - r'| / r₀ ^ 4) := by
        refine (abs_mul_sub_mul_le hAb hinvb).trans ?_
        apply add_le_add
        · exact le_refl _
        · exact mul_le_mul_of_nonneg_left hinv
            (mul_nonneg (mul_nonneg (by norm_num) hMOm) hK1)
    _ ≤ ((1 / 2) * |Om - Om'| * (M_W * (1 + M_W ^ 2))
          + (1 / 2) * M_Om * ((1 + 3 * M_W ^ 2) * |W - W'|)) * (1 / r₀ ^ 2)
        + (1 / 2) * M_Om * (M_W * (1 + M_W ^ 2))
          * (2 * M_r * |r - r'| / r₀ ^ 4) := by
        apply add_le_add _ (le_refl _)
        exact mul_le_mul_of_nonneg_right hA (by positivity)
    _ = (M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2)) * |Om - Om'|
        + (M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2)) * |W - W'|
        + (M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4) * |r - r'| := by ring

/-- r 方程式の右辺のリプシッツ評価（明示定数つき）。
    rhsR Om W ru rv r = (1/2) * Om * ((1 - W²)² / r² - 1) / r - ru * rv / r。
    S = (1 - W²)² / r² - 1 の上限を KS = (1 + M_W²)² / r₀² + 1 と書く。 -/
theorem rhsR_sub_le {Om Om' W W' ru ru' rv rv' r r' M_Om M_W M_u M_v M_r r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (hMr : |r| ≤ M_r) (hMr' : |r'| ≤ M_r)
    (hOm : |Om| ≤ M_Om)
    (hW : |W| ≤ M_W) (hW' : |W'| ≤ M_W)
    (hu : |ru| ≤ M_u)
    (hv : |rv| ≤ M_v) (hv' : |rv'| ≤ M_v) :
    |rhsR Om W ru rv r - rhsR Om' W' ru' rv' r'|
      ≤ ((1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀)) * |Om - Om'|
        + ((1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3) * |W - W'|
        + (M_v / r₀) * |ru - ru'|
        + (M_u / r₀) * |rv - rv'|
        + (M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
           + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
           + M_u * M_v / r₀ ^ 2) * |r - r'| := by
  have hMOm : 0 ≤ M_Om := le_trans (abs_nonneg _) hOm
  have hMW : 0 ≤ M_W := le_trans (abs_nonneg _) hW
  have hMu : 0 ≤ M_u := le_trans (abs_nonneg _) hu
  have hMv : 0 ≤ M_v := le_trans (abs_nonneg _) hv
  have hKS : 0 ≤ (1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1 := by positivity
  have heq : rhsR Om W ru rv r
      = ((1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)) * r⁻¹
        - (ru * rv) * r⁻¹ := by
    unfold rhsR; ring
  have heq' : rhsR Om' W' ru' rv' r'
      = ((1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)) * r'⁻¹
        - (ru' * rv') * r'⁻¹ := by
    unfold rhsR; ring
  have hinv2 : |(r ^ 2)⁻¹ - (r' ^ 2)⁻¹| ≤ 2 * M_r * |r - r'| / r₀ ^ 4 :=
    abs_inv_sq_sub_le hr₀ hr hr' hMr hMr'
  have hinv1 : |r⁻¹ - r'⁻¹| ≤ |r - r'| / r₀ ^ 2 := abs_inv_sub_le hr₀ hr hr'
  have hinvb2 : |(r' ^ 2)⁻¹| ≤ 1 / r₀ ^ 2 := by
    have hr2 : r₀ ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ (le_of_lt hr₀) hr' 2
    have hpos : (0:ℝ) < r' ^ 2 := lt_of_lt_of_le (by positivity) hr2
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hr2
  have hinvb1 : |(r ^ 2)⁻¹| ≤ 1 / r₀ ^ 2 := by
    have hr2 : r₀ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (le_of_lt hr₀) hr 2
    have hpos : (0:ℝ) < r ^ 2 := lt_of_lt_of_le (by positivity) hr2
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hr2
  have hinvrb : |r'⁻¹| ≤ 1 / r₀ := by
    have hpos : (0:ℝ) < r' := lt_of_lt_of_le hr₀ hr'
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le hr₀ hr'
  have hQ : |(1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2|
      ≤ (4 * M_W + 4 * M_W ^ 3) * |W - W'| := abs_polyQ_sub_le hW hW'
  have hQb : |(1 - W' ^ 2) ^ 2| ≤ (1 + M_W ^ 2) ^ 2 := abs_polyQ_bound hW'
  have hQab : |(1 - W ^ 2) ^ 2| ≤ (1 + M_W ^ 2) ^ 2 := abs_polyQ_bound hW
  -- S = Q * (r²)⁻¹ - 1 の差と上限
  have hS : |(1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1
        - ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)|
      ≤ (4 * M_W + 4 * M_W ^ 3) * |W - W'| * (1 / r₀ ^ 2)
        + (1 + M_W ^ 2) ^ 2 * (2 * M_r * |r - r'| / r₀ ^ 4) := by
    have hsub : (1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1
        - ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)
        = (1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - (1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ := by ring
    rw [hsub]
    refine (abs_mul_sub_mul_le hQab hinvb2).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hQ (by positivity)
    · exact mul_le_mul_of_nonneg_left hinv2 (by positivity)
  have hSb : |(1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1|
      ≤ (1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1 := by
    calc |(1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1|
        ≤ |(1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹| + |1| := abs_sub _ _
      _ = |(1 - W ^ 2) ^ 2| * |(r ^ 2)⁻¹| + 1 := by rw [abs_mul, abs_one]
      _ ≤ (1 + M_W ^ 2) ^ 2 * (1 / r₀ ^ 2) + 1 := by
          apply add_le_add_right _ 1
          exact mul_le_mul hQab hinvb1 (abs_nonneg _) (by positivity)
      _ = (1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1 := by ring
  have hSb' : |(1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1|
      ≤ (1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1 := by
    calc |(1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1|
        ≤ |(1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹| + |1| := abs_sub _ _
      _ = |(1 - W' ^ 2) ^ 2| * |(r' ^ 2)⁻¹| + 1 := by rw [abs_mul, abs_one]
      _ ≤ (1 + M_W ^ 2) ^ 2 * (1 / r₀ ^ 2) + 1 := by
          apply add_le_add_right _ 1
          exact mul_le_mul hQb hinvb2 (abs_nonneg _) (by positivity)
      _ = (1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1 := by ring
  -- 第1項 A = ((1/2) * Om * S) * r⁻¹ の差
  have hA1 : |(1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)
        - (1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)|
      ≤ (1 / 2) * |Om - Om'| * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)
        + (1 / 2) * M_Om * ((4 * M_W + 4 * M_W ^ 3) * |W - W'| * (1 / r₀ ^ 2)
          + (1 + M_W ^ 2) ^ 2 * (2 * M_r * |r - r'| / r₀ ^ 4)) := by
    have h := abs_mul_sub_mul_le (a := (1 / 2) * Om) (a' := (1 / 2) * Om')
      (b := (1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)
      (b' := (1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)
      (M_a := (1 / 2) * M_Om) (M_b' := (1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) ?_ hSb'
    · have haa : |(1 / 2) * Om - (1 / 2) * Om'| = (1 / 2) * |Om - Om'| := by
        rw [← mul_sub, abs_mul]
        norm_num
      rw [haa] at h
      refine h.trans ?_
      apply add_le_add_left _ _
      exact mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num) hMOm)
    · rw [abs_mul]
      have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left hOm (by norm_num)
  have hAb1 : |(1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)|
      ≤ (1 / 2) * M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) := by
    calc |(1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)|
        = |(1 / 2) * Om| * |(1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1| := abs_mul _ _
      _ ≤ ((1 / 2) * M_Om) * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) := by
          apply mul_le_mul _ hSb (abs_nonneg _) (mul_nonneg (by norm_num) hMOm)
          rw [abs_mul]
          have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
          rw [hhalf]
          exact mul_le_mul_of_nonneg_left hOm (by norm_num)
      _ = (1 / 2) * M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) := by ring
  have hA : |((1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)) * r⁻¹
        - ((1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)) * r'⁻¹|
      ≤ ((1 / 2) * |Om - Om'| * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)
          + (1 / 2) * M_Om * ((4 * M_W + 4 * M_W ^ 3) * |W - W'| * (1 / r₀ ^ 2)
            + (1 + M_W ^ 2) ^ 2 * (2 * M_r * |r - r'| / r₀ ^ 4))) * (1 / r₀)
        + (1 / 2) * M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) * (|r - r'| / r₀ ^ 2) := by
    refine (abs_mul_sub_mul_le hAb1 hinvrb).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hA1 (by positivity)
    · exact mul_le_mul_of_nonneg_left hinv1
        (mul_nonneg (mul_nonneg (by norm_num) hMOm) hKS)
  -- 第2項 B = (ru * rv) * r⁻¹ の差
  have hB1 : |ru * rv - ru' * rv'| ≤ |ru - ru'| * M_v + M_u * |rv - rv'| :=
    abs_mul_sub_mul_le hu hv'
  have hBb : |ru * rv| ≤ M_u * M_v := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hMu
  have hB : |(ru * rv) * r⁻¹ - (ru' * rv') * r'⁻¹|
      ≤ (|ru - ru'| * M_v + M_u * |rv - rv'|) * (1 / r₀)
        + M_u * M_v * (|r - r'| / r₀ ^ 2) := by
    refine (abs_mul_sub_mul_le hBb hinvrb).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hB1 (by positivity)
    · exact mul_le_mul_of_nonneg_left hinv1 (mul_nonneg hMu hMv)
  -- 組み立て
  have hdecomp : |rhsR Om W ru rv r - rhsR Om' W' ru' rv' r'|
      ≤ |((1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)) * r⁻¹
          - ((1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)) * r'⁻¹|
        + |(ru * rv) * r⁻¹ - (ru' * rv') * r'⁻¹| := by
    rw [heq, heq']
    have hsub : (((1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)) * r⁻¹
          - (ru * rv) * r⁻¹)
        - (((1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)) * r'⁻¹
          - (ru' * rv') * r'⁻¹)
        = (((1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)) * r⁻¹
          - ((1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)) * r'⁻¹)
        - ((ru * rv) * r⁻¹ - (ru' * rv') * r'⁻¹) := by ring
    rw [hsub]
    exact abs_sub _ _
  refine hdecomp.trans ?_
  calc |((1 / 2) * Om * ((1 - W ^ 2) ^ 2 * (r ^ 2)⁻¹ - 1)) * r⁻¹
        - ((1 / 2) * Om' * ((1 - W' ^ 2) ^ 2 * (r' ^ 2)⁻¹ - 1)) * r'⁻¹|
      + |(ru * rv) * r⁻¹ - (ru' * rv') * r'⁻¹|
      ≤ (((1 / 2) * |Om - Om'| * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)
          + (1 / 2) * M_Om * ((4 * M_W + 4 * M_W ^ 3) * |W - W'| * (1 / r₀ ^ 2)
            + (1 + M_W ^ 2) ^ 2 * (2 * M_r * |r - r'| / r₀ ^ 4))) * (1 / r₀)
        + (1 / 2) * M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) * (|r - r'| / r₀ ^ 2))
      + ((|ru - ru'| * M_v + M_u * |rv - rv'|) * (1 / r₀)
        + M_u * M_v * (|r - r'| / r₀ ^ 2)) := add_le_add hA hB
    _ = ((1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀)) * |Om - Om'|
        + ((1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3) * |W - W'|
        + (M_v / r₀) * |ru - ru'|
        + (M_u / r₀) * |rv - rv'|
        + (M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
           + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
           + M_u * M_v / r₀ ^ 2) * |r - r'| := by ring

/-- Ω 方程式の右辺のリプシッツ評価（明示定数つき）。
    rhsOm Om Ou Ov ruv r W = Ou * Ov / Om - 2 * Om * ruv / r
      - Om² * (1 - W²)² / r⁴。Ω は Om₀ > 0 で下から抑える。 -/
theorem rhsOm_sub_le {Om Om' Ou Ou' Ov Ov' ruv ruv' r r' W W'
    M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ : ℝ}
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (hMr : |r| ≤ M_r) (hMr' : |r'| ≤ M_r)
    (hOm : Om₀ ≤ Om) (hOm' : Om₀ ≤ Om')
    (hOmM : |Om| ≤ M_Om) (hOmM' : |Om'| ≤ M_Om)
    (hOu : |Ou| ≤ M_Ou)
    (hOv : |Ov| ≤ M_Ov) (hOv' : |Ov'| ≤ M_Ov)
    (huv : |ruv| ≤ M_uv) (huv' : |ruv'| ≤ M_uv)
    (hW : |W| ≤ M_W) (hW' : |W'| ≤ M_W) :
    |rhsOm Om Ou Ov ruv r W - rhsOm Om' Ou' Ov' ruv' r' W'|
      ≤ (M_Ov / Om₀) * |Ou - Ou'|
        + (M_Ou / Om₀) * |Ov - Ov'|
        + (M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
           + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4) * |Om - Om'|
        + (2 * M_Om / r₀) * |ruv - ruv'|
        + (2 * M_Om * M_uv / r₀ ^ 2
           + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8) * |r - r'|
        + (M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4) * |W - W'| := by
  have hMOm : 0 ≤ M_Om := le_trans (abs_nonneg _) hOmM
  have hMOu : 0 ≤ M_Ou := le_trans (abs_nonneg _) hOu
  have hMOv : 0 ≤ M_Ov := le_trans (abs_nonneg _) hOv
  have hMuv : 0 ≤ M_uv := le_trans (abs_nonneg _) huv
  have hMW : 0 ≤ M_W := le_trans (abs_nonneg _) hW
  have heq : rhsOm Om Ou Ov ruv r W
      = (Ou * Ov) * Om⁻¹ - (2 * Om * ruv) * r⁻¹
        - (Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹ := by
    unfold rhsOm; ring
  have heq' : rhsOm Om' Ou' Ov' ruv' r' W'
      = (Ou' * Ov') * Om'⁻¹ - (2 * Om' * ruv') * r'⁻¹
        - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹ := by
    unfold rhsOm; ring
  have hinvOm : |Om⁻¹ - Om'⁻¹| ≤ |Om - Om'| / Om₀ ^ 2 :=
    abs_inv_sub_le hOm₀ hOm hOm'
  have hinvOmb : |Om'⁻¹| ≤ 1 / Om₀ := by
    have hpos : (0:ℝ) < Om' := lt_of_lt_of_le hOm₀ hOm'
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le hOm₀ hOm'
  have hinv1 : |r⁻¹ - r'⁻¹| ≤ |r - r'| / r₀ ^ 2 := abs_inv_sub_le hr₀ hr hr'
  have hinvrb : |r'⁻¹| ≤ 1 / r₀ := by
    have hpos : (0:ℝ) < r' := lt_of_lt_of_le hr₀ hr'
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le hr₀ hr'
  have hinv4 : |(r ^ 4)⁻¹ - (r' ^ 4)⁻¹| ≤ 4 * M_r ^ 3 * |r - r'| / r₀ ^ 8 :=
    abs_inv_pow4_sub_le hr₀ hr hr' hMr hMr'
  have hinvb4 : |(r' ^ 4)⁻¹| ≤ 1 / r₀ ^ 4 := by
    have hr4 : r₀ ^ 4 ≤ r' ^ 4 := pow_le_pow_left₀ (le_of_lt hr₀) hr' 4
    have hpos : (0:ℝ) < r' ^ 4 := lt_of_lt_of_le (by positivity) hr4
    rw [abs_inv, abs_of_pos hpos, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hr4
  have hQ : |(1 - W ^ 2) ^ 2 - (1 - W' ^ 2) ^ 2|
      ≤ (4 * M_W + 4 * M_W ^ 3) * |W - W'| := abs_polyQ_sub_le hW hW'
  have hQb : |(1 - W' ^ 2) ^ 2| ≤ (1 + M_W ^ 2) ^ 2 := abs_polyQ_bound hW'
  have hQab : |(1 - W ^ 2) ^ 2| ≤ (1 + M_W ^ 2) ^ 2 := abs_polyQ_bound hW
  -- 第1項 T1 = (Ou * Ov) * Om⁻¹
  have hOv1 : |Ou * Ov - Ou' * Ov'| ≤ |Ou - Ou'| * M_Ov + M_Ou * |Ov - Ov'| :=
    abs_mul_sub_mul_le hOu hOv'
  have hOvB : |Ou * Ov| ≤ M_Ou * M_Ov := by
    rw [abs_mul]
    exact mul_le_mul hOu hOv (abs_nonneg _) hMOu
  have hT1 : |(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹|
      ≤ (|Ou - Ou'| * M_Ov + M_Ou * |Ov - Ov'|) * (1 / Om₀)
        + M_Ou * M_Ov * (|Om - Om'| / Om₀ ^ 2) := by
    refine (abs_mul_sub_mul_le hOvB hinvOmb).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hOv1 (by positivity)
    · exact mul_le_mul_of_nonneg_left hinvOm (mul_nonneg hMOu hMOv)
  -- 第2項 T2 = (2 * Om * ruv) * r⁻¹
  have hruv1 : |2 * Om * ruv - 2 * Om' * ruv'|
      ≤ 2 * |Om - Om'| * M_uv + 2 * M_Om * |ruv - ruv'| := by
    have h := abs_mul_sub_mul_le (a := Om) (a' := Om') (b := ruv) (b' := ruv')
      (M_a := M_Om) (M_b' := M_uv) hOmM huv'
    have h2 : |2 * Om * ruv - 2 * Om' * ruv'|
        = 2 * |Om * ruv - Om' * ruv'| := by
      have he : 2 * Om * ruv - 2 * Om' * ruv' = 2 * (Om * ruv - Om' * ruv') := by ring
      rw [he, abs_mul]
      norm_num
    rw [h2]
    calc 2 * |Om * ruv - Om' * ruv'|
        ≤ 2 * (|Om - Om'| * M_uv + M_Om * |ruv - ruv'|) := by
          apply mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 2 * |Om - Om'| * M_uv + 2 * M_Om * |ruv - ruv'| := by ring
  have hruvB : |2 * Om * ruv| ≤ 2 * M_Om * M_uv := by
    calc |2 * Om * ruv| = 2 * (|Om| * |ruv|) := by
          have h2 : |(2 : ℝ)| = 2 := by norm_num
          rw [abs_mul, abs_mul, h2]
          ring
      _ ≤ 2 * (M_Om * M_uv) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hOmM huv (abs_nonneg _) hMOm
      _ = 2 * M_Om * M_uv := by ring
  have hT2 : |(2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹|
      ≤ (2 * |Om - Om'| * M_uv + 2 * M_Om * |ruv - ruv'|) * (1 / r₀)
        + 2 * M_Om * M_uv * (|r - r'| / r₀ ^ 2) := by
    refine (abs_mul_sub_mul_le hruvB hinvrb).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hruv1 (by positivity)
    · exact mul_le_mul_of_nonneg_left hinv1 (mul_nonneg (mul_nonneg (by norm_num) hMOm) hMuv)
  -- 第3項 T3 = (Om² * Q) * (r⁴)⁻¹
  have hOm2 : |Om ^ 2 - Om' ^ 2| ≤ 2 * M_Om * |Om - Om'| :=
    abs_sq_sub_le hOmM hOmM'
  have hOm2b : |Om ^ 2| ≤ M_Om ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hOmM 2
  have hQOm : |Om ^ 2 * (1 - W ^ 2) ^ 2 - Om' ^ 2 * (1 - W' ^ 2) ^ 2|
      ≤ (2 * M_Om * |Om - Om'|) * (1 + M_W ^ 2) ^ 2
        + M_Om ^ 2 * ((4 * M_W + 4 * M_W ^ 3) * |W - W'|) := by
    refine (abs_mul_sub_mul_le hOm2b hQb).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hOm2 (by positivity)
    · exact mul_le_mul_of_nonneg_left hQ (by positivity)
  have hQOmB : |Om ^ 2 * (1 - W ^ 2) ^ 2| ≤ M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul hOm2b hQab (abs_nonneg _) (by positivity)
  have hT3 : |(Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
        - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹|
      ≤ ((2 * M_Om * |Om - Om'|) * (1 + M_W ^ 2) ^ 2
          + M_Om ^ 2 * ((4 * M_W + 4 * M_W ^ 3) * |W - W'|)) * (1 / r₀ ^ 4)
        + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * (4 * M_r ^ 3 * |r - r'| / r₀ ^ 8) := by
    refine (abs_mul_sub_mul_le hQOmB hinvb4).trans ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hQOm (by positivity)
    · exact mul_le_mul_of_nonneg_left hinv4
        (mul_nonneg (by positivity) (by positivity))
  -- 組み立て
  have hdecomp : |rhsOm Om Ou Ov ruv r W - rhsOm Om' Ou' Ov' ruv' r' W'|
      ≤ |(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹|
        + |(2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹|
        + |(Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
          - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹| := by
    rw [heq, heq']
    have hsub : ((Ou * Ov) * Om⁻¹ - (2 * Om * ruv) * r⁻¹
          - (Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹)
        - ((Ou' * Ov') * Om'⁻¹ - (2 * Om' * ruv') * r'⁻¹
          - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹)
        = ((Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹)
        - ((2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹)
        - ((Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
          - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹) := by ring
    rw [hsub]
    calc |(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹
          - ((2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹)
          - ((Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
            - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹)|
        ≤ |(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹
          - ((2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹)|
          + |(Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
            - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹| := abs_sub _ _
      _ ≤ (|(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹|
          + |(2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹|)
          + |(Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
            - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹| := by
          apply add_le_add_right _ _
          exact abs_sub _ _
      _ = |(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹|
          + |(2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹|
          + |(Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
            - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹| := by ring
  refine hdecomp.trans ?_
  calc |(Ou * Ov) * Om⁻¹ - (Ou' * Ov') * Om'⁻¹|
      + |(2 * Om * ruv) * r⁻¹ - (2 * Om' * ruv') * r'⁻¹|
      + |(Om ^ 2 * (1 - W ^ 2) ^ 2) * (r ^ 4)⁻¹
        - (Om' ^ 2 * (1 - W' ^ 2) ^ 2) * (r' ^ 4)⁻¹|
      ≤ ((|Ou - Ou'| * M_Ov + M_Ou * |Ov - Ov'|) * (1 / Om₀)
          + M_Ou * M_Ov * (|Om - Om'| / Om₀ ^ 2))
        + ((2 * |Om - Om'| * M_uv + 2 * M_Om * |ruv - ruv'|) * (1 / r₀)
          + 2 * M_Om * M_uv * (|r - r'| / r₀ ^ 2))
        + (((2 * M_Om * |Om - Om'|) * (1 + M_W ^ 2) ^ 2
            + M_Om ^ 2 * ((4 * M_W + 4 * M_W ^ 3) * |W - W'|)) * (1 / r₀ ^ 4)
          + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * (4 * M_r ^ 3 * |r - r'| / r₀ ^ 8)) :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = (M_Ov / Om₀) * |Ou - Ou'|
        + (M_Ou / Om₀) * |Ov - Ov'|
        + (M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
           + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4) * |Om - Om'|
        + (2 * M_Om / r₀) * |ruv - ruv'|
        + (2 * M_Om * M_uv / r₀ ^ 2
           + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8) * |r - r'|
        + (M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4) * |W - W'| := by ring

/-- 凍結右辺の差の評価（W 方程式）：2つの場のジェットの差で抑える。 -/
theorem wedgeRhsW_sub_le {F G : WedgeFields} {s t M_Om M_W M_r r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hrF : r₀ ≤ F.r s t) (hrG : r₀ ≤ G.r s t)
    (hMrF : |F.r s t| ≤ M_r) (hMrG : |G.r s t| ≤ M_r)
    (hOmF : |F.Om s t| ≤ M_Om)
    (hWF : |F.W s t| ≤ M_W) (hWG : |G.W s t| ≤ M_W) :
    |wedgeRhsW F s t - wedgeRhsW G s t|
      ≤ (M_W * (1 + M_W ^ 2) / (2 * r₀ ^ 2)) * |F.Om s t - G.Om s t|
        + (M_Om * (1 + 3 * M_W ^ 2) / (2 * r₀ ^ 2)) * |F.W s t - G.W s t|
        + (M_Om * M_W * (1 + M_W ^ 2) * M_r / r₀ ^ 4) * |F.r s t - G.r s t| :=
  rhsW_sub_le hr₀ hrF hrG hMrF hMrG hOmF hWF hWG

/-- 凍結右辺の差の評価（r 方程式）：2つの場のジェットの差で抑える。 -/
theorem wedgeRhsR_sub_le {F G : WedgeFields} {s t M_Om M_W M_u M_v M_r r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hrF : r₀ ≤ F.r s t) (hrG : r₀ ≤ G.r s t)
    (hMrF : |F.r s t| ≤ M_r) (hMrG : |G.r s t| ≤ M_r)
    (hOmF : |F.Om s t| ≤ M_Om)
    (hWF : |F.W s t| ≤ M_W) (hWG : |G.W s t| ≤ M_W)
    (huF : |Du F.r s t| ≤ M_u)
    (hvF : |Dv F.r s t| ≤ M_v) (hvG : |Dv G.r s t| ≤ M_v) :
    |wedgeRhsR F s t - wedgeRhsR G s t|
      ≤ ((1 / 2) * (((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1) / r₀)) * |F.Om s t - G.Om s t|
        + ((1 / 2) * M_Om * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 3) * |F.W s t - G.W s t|
        + (M_v / r₀) * |Du F.r s t - Du G.r s t|
        + (M_u / r₀) * |Dv F.r s t - Dv G.r s t|
        + (M_Om * (1 + M_W ^ 2) ^ 2 * M_r / r₀ ^ 5
           + (M_Om * ((1 + M_W ^ 2) ^ 2 / r₀ ^ 2 + 1)) / (2 * r₀ ^ 2)
           + M_u * M_v / r₀ ^ 2) * |F.r s t - G.r s t| :=
  rhsR_sub_le hr₀ hrF hrG hMrF hMrG hOmF hWF hWG huF hvF hvG

/-- 凍結右辺の差の評価（Ω 方程式）：2つの場のジェットの差で抑える。
    Ω 方程式の右辺は Duv F.r（r の混合微分）にも依存する。 -/
theorem wedgeRhsOm_sub_le {F G : WedgeFields} {s t M_Om M_Ou M_Ov M_uv M_W M_r r₀ Om₀ : ℝ}
    (hr₀ : 0 < r₀) (hOm₀ : 0 < Om₀)
    (hrF : r₀ ≤ F.r s t) (hrG : r₀ ≤ G.r s t)
    (hMrF : |F.r s t| ≤ M_r) (hMrG : |G.r s t| ≤ M_r)
    (hOmF : Om₀ ≤ F.Om s t) (hOmG : Om₀ ≤ G.Om s t)
    (hOmMF : |F.Om s t| ≤ M_Om) (hOmMG : |G.Om s t| ≤ M_Om)
    (hOuF : |Du F.Om s t| ≤ M_Ou)
    (hOvF : |Dv F.Om s t| ≤ M_Ov) (hOvG : |Dv G.Om s t| ≤ M_Ov)
    (huvF : |Duv F.r s t| ≤ M_uv) (huvG : |Duv G.r s t| ≤ M_uv)
    (hWF : |F.W s t| ≤ M_W) (hWG : |G.W s t| ≤ M_W) :
    |wedgeRhsOm F s t - wedgeRhsOm G s t|
      ≤ (M_Ov / Om₀) * |Du F.Om s t - Du G.Om s t|
        + (M_Ou / Om₀) * |Dv F.Om s t - Dv G.Om s t|
        + (M_Ou * M_Ov / Om₀ ^ 2 + 2 * M_uv / r₀
           + 2 * M_Om * (1 + M_W ^ 2) ^ 2 / r₀ ^ 4) * |F.Om s t - G.Om s t|
        + (2 * M_Om / r₀) * |Duv F.r s t - Duv G.r s t|
        + (2 * M_Om * M_uv / r₀ ^ 2
           + M_Om ^ 2 * (1 + M_W ^ 2) ^ 2 * 4 * M_r ^ 3 / r₀ ^ 8)
          * |F.r s t - G.r s t|
        + (M_Om ^ 2 * (4 * M_W + 4 * M_W ^ 3) / r₀ ^ 4) * |F.W s t - G.W s t| :=
  rhsOm_sub_le hr₀ hOm₀ hrF hrG hMrF hMrG hOmF hOmG hOmMF hOmMG hOuF hOvF hOvG
    huvF huvG hWF hWG

/-- 二重積分の差の評価：矩形上で右辺の差が M で抑えられれば、
    二重積分の差は矩形の面積 × M で抑えられる。
    第1層 (a) の積分表示と合わせると、反復写像の像の差が矩形の
    大きさで制御できることになる（第3層 (c) の組み立ての部品）。 -/
theorem double_integral_sub_le {F G : ℝ → ℝ → ℝ} {u₀ u v₀ v M : ℝ}
    (hu : u₀ ≤ u) (hv : v₀ ≤ v)
    (hFG : ∀ s ∈ Set.Icc u₀ u, ∀ t ∈ Set.Icc v₀ v, |F s t - G s t| ≤ M) :
    |∫ s in u₀..u, ∫ t in v₀..v, (F s t - G s t)|
      ≤ (u - u₀) * (v - v₀) * M := by
  have hmem : ∀ {a b : ℝ} (h : a ≤ b) {x : ℝ}, x ∈ Ι a b → x ∈ Set.Icc a b := by
    intro a b h x hx
    have h1 : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    rwa [Set.uIcc_of_le h] at h1
  have hinner : ∀ s ∈ Set.Icc u₀ u,
      |∫ t in v₀..v, (F s t - G s t)| ≤ M * (v - v₀) := by
    intro s hs
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := v₀) (b := v)
      (f := fun t => F s t - G s t) (C := M) (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hFG s hs t (hmem hv ht))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hv)] at h
    exact h
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const (a := u₀) (b := u)
    (f := fun s => ∫ t in v₀..v, (F s t - G s t)) (C := M * (v - v₀))
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact hinner s (hmem hu hs))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu)] at houter
  calc |∫ s in u₀..u, ∫ t in v₀..v, (F s t - G s t)|
      = ‖∫ s in u₀..u, ∫ t in v₀..v, (F s t - G s t)‖ := by rw [Real.norm_eq_abs]
    _ ≤ (M * (v - v₀)) * (u - u₀) := houter
    _ = (u - u₀) * (v - v₀) * M := by ring

end

end CFT.WedgeRhsLip
