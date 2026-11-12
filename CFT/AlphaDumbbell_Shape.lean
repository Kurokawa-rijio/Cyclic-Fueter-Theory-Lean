/-
  ダンベルの形:(r, W) の平面での円と、その包絡線(2026-11-12)

  * Weyl 曲率 = 質量 − 磁気の自己エネルギー:
    `ds_weyl_mass`:Weyl の不変量 1 + r²Q_uv/Ω は 3(2m/r − ℓ²(1 − W²)²/r²)(2m/r = 1 + 2r_u r_v/Ω は Misner–Sharp の質量)。
    共形平坦 ⇔ 2mr = ℓ²(1 − W²)²。
    `ds_mass_u`:拘束 C_u = 0 と r_uv の式から m_u = −2ℓ²W_u² r_v/Ω + r_u ℓ²(1 − W²)²/(2r²)。
    `ds_N_u`:N = 2mr − ℓ²(1 − W²)² の輸送の式 N_u − (r_u/r)N = Σ_u。
  * 形:
    `ds_circle_of_flat`:時間対称・W = r′・共形平坦(1 − W² = ℓ²(1 − W²)²/r²)で W² ≠ 1 なら r² + ℓ²W² = ℓ²。
    `ds_cap_on_circle`、`ds_neck_on_circle`:帽子 r = ℓ sin(x/ℓ)、W = cos(x/ℓ) は円を一周し、首は円の上の一点 (ℓ, 0)。
    `ds_cap_disc`:帽子の全体は円板 r² + ℓ²W² ≤ ℓ² の中(等号は時間対称な瞬間か極)。
    `ds_slope_disc`、`ds_slope_real`:共形平坦な解のヌル方向の傾き dW/dr の二次方程式の判別式は
    4(1 − W²)³(ℓ²(1 − W²) − r²)/r²。実の傾きがあるのは円板の中だけで、円の上で二つの根が重なる。
    `ds_branch`:r² + ℓ²r′² = ℓ² の 2 回微分できる解は各点で r′ = 0(首、包絡線)か r″ = −r/ℓ²(帽子)。
    首は帽子の族の包絡線(特異解)で、ダンベルは正則な解と特異解を C¹ でつないだもの。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

open Real

namespace CFT.DS

theorem ds_weyl_mass (r ru rv Om W l : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0) :
    r ^ 2 / Om * (6 * ru * rv / r ^ 2 - 3 * Om * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4 + 2 * Om / r ^ 2) + 1
      = 3 * ((1 + 2 * ru * rv / Om) - l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2) := by
  field_simp
  ring

theorem ds_mass_u (r ru rv ruu ruv Om Omu W Wu l : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (hC : ruu = Omu / Om * ru - 2 * l ^ 2 * Wu ^ 2 / r)
    (h1 : ruv = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r) :
    ru / 2 * (1 + 2 * ru * rv / Om) + r * (ruu * rv + ru * ruv) / Om - r * ru * rv * Omu / Om ^ 2
      = -2 * l ^ 2 * Wu ^ 2 * rv / Om + ru * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2) := by
  rw [hC, h1]
  field_simp
  ring

theorem ds_N_u (r ru rv Om W Wu l m mu N : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (hmu : mu = -2 * l ^ 2 * Wu ^ 2 * rv / Om + ru * l ^ 2 * (1 - W ^ 2) ^ 2 / (2 * r ^ 2))
    (hN : N = 2 * m * r - l ^ 2 * (1 - W ^ 2) ^ 2) :
    2 * mu * r + 2 * m * ru + 4 * l ^ 2 * W * Wu * (1 - W ^ 2) - ru / r * N
      = 2 * ru * l ^ 2 * (1 - W ^ 2) ^ 2 / r + 4 * l ^ 2 * W * Wu * (1 - W ^ 2)
        - 4 * l ^ 2 * r * rv * Wu ^ 2 / Om := by
  rw [hmu, hN]
  field_simp
  ring

theorem ds_circle_of_flat (r W l : ℝ) (hr : r ≠ 0) (hW : 1 - W ^ 2 ≠ 0)
    (h : 1 - W ^ 2 = l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2) : r ^ 2 + l ^ 2 * W ^ 2 = l ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hr)] at h
  have h2 : r ^ 2 = l ^ 2 * (1 - W ^ 2) :=
    mul_left_cancel₀ hW (by linear_combination h)
  linear_combination h2

theorem ds_cap_on_circle (l x : ℝ) : (l * sin (x / l)) ^ 2 + l ^ 2 * cos (x / l) ^ 2 = l ^ 2 := by
  linear_combination l ^ 2 * sin_sq_add_cos_sq (x / l)

theorem ds_neck_on_circle (l : ℝ) : l ^ 2 + l ^ 2 * (0 : ℝ) ^ 2 = l ^ 2 := by ring

theorem ds_cap_disc (l η χ : ℝ) :
    (l * cos η * sin χ) ^ 2 + l ^ 2 * cos χ ^ 2 = l ^ 2 - l ^ 2 * sin η ^ 2 * sin χ ^ 2 := by
  linear_combination l ^ 2 * sin χ ^ 2 * sin_sq_add_cos_sq η + l ^ 2 * sin_sq_add_cos_sq χ

theorem ds_slope_disc (r W l : ℝ) (hr : r ≠ 0) :
    (2 * W * (1 - W ^ 2)) ^ 2 - 4 * ((1 - W ^ 2) ^ 2 / r) * ((r ^ 2 - l ^ 2 * (1 - W ^ 2) ^ 2) / r)
      = 4 * (1 - W ^ 2) ^ 3 / r ^ 2 * (l ^ 2 * (1 - W ^ 2) - r ^ 2) := by
  field_simp
  ring

theorem ds_slope_real (r W l : ℝ) (hr : r ≠ 0) (hW : 0 < 1 - W ^ 2) :
    0 ≤ (2 * W * (1 - W ^ 2)) ^ 2 - 4 * ((1 - W ^ 2) ^ 2 / r) * ((r ^ 2 - l ^ 2 * (1 - W ^ 2) ^ 2) / r)
      ↔ r ^ 2 + l ^ 2 * W ^ 2 ≤ l ^ 2 := by
  rw [ds_slope_disc r W l hr]
  have hr2 : 0 < r ^ 2 := lt_of_le_of_ne (sq_nonneg r) (Ne.symm (pow_ne_zero 2 hr))
  have hk : 0 < 4 * (1 - W ^ 2) ^ 3 / r ^ 2 := div_pos (mul_pos (by norm_num) (pow_pos hW 3)) hr2
  have e : l ^ 2 * (1 - W ^ 2) - r ^ 2 = l ^ 2 - (r ^ 2 + l ^ 2 * W ^ 2) := by ring
  rw [mul_nonneg_iff_of_pos_left hk, e, sub_nonneg]

theorem ds_branch {r r' : ℝ → ℝ} {l x r'' : ℝ} (hl : l ≠ 0)
    (h : ∀ y, r y ^ 2 + l ^ 2 * r' y ^ 2 = l ^ 2)
    (hr : HasDerivAt r (r' x) x) (hr' : HasDerivAt r' r'' x) :
    r' x = 0 ∨ r'' = -(r x) / l ^ 2 := by
  have hd : HasDerivAt (fun y => r y * r y + l ^ 2 * (r' y * r' y))
      (r' x * r x + r x * r' x + l ^ 2 * (r'' * r' x + r' x * r'')) x :=
    (hr.mul hr).add ((hr'.mul hr').const_mul (l ^ 2))
  have e : (fun y => r y * r y + l ^ 2 * (r' y * r' y)) = fun _ => l ^ 2 := by
    funext y
    linear_combination h y
  rw [e] at hd
  have k := hd.unique (hasDerivAt_const x (l ^ 2))
  have k2 : r' x * (r x + l ^ 2 * r'') = 0 := by linear_combination k / 2
  rcases mul_eq_zero.mp k2 with h1 | h1
  · exact Or.inl h1
  · right
    rw [eq_div_iff (pow_ne_zero 2 hl)]
    linarith

end CFT.DS
