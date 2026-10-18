/-
  α-III 接合とダンベルの必然性(Z0, Z0′, Z6, Z7, Z0-f, Z0-m)

  形式化した内容
  * α-III.1 (Z6)   時間対称な赤道での Israel 条件:[T_nn] = −ρ_B − p_c = −1/(4πGℓ²) ≠ 0
  * α-III.2 (Z7)   null な弱不連続 [F] = k∧α(k null、α·k = 0)では k^μ[T_μν] = 0
                    (ファイル AlphaIII_P1.lean)
  * α-III.3 (Z0)   球対称 Penrose 型定理:DEC(|J| ≤ ρ)、外側が捕捉されない(|rK_T| ≤ r′)、
                    出発球面が境界(r′² = r²K_T²)なら、M₂ ≥ r₀。
                    質量恒等式 dM₂/ds = r²(ρr′ − J r K_T) は仮定(Einstein の拘束式から導出)
  * α-III.4 (Z0′)  M₂ の値:Q の赤道 = a、首 = ℓ、平坦 = 0。連続性から a = ℓ、
                    首から平坦へは開けない
  * α-III.5 (Z0′)  空間的 Schwarzschild 断面(Ricci 固有値 −2μ, μ, μ)は (I) を満たさない
  * α-III.6 (Z0-f) 平坦極限:キャップ質量 = (4π/3)ρr³、恒等式は dm/dr = 4πr²ρ に退化
  * α-III.7 (Z0-m) ℓ*/(2G) = √π M_Pl/g(M_Pl = 1/√G)
-/
import CFT.Basic

open Real

namespace CFT.AlphaIII

/-! ### α-III.1 Israel 接合 -/

/-- キャップ(輻射 FRW)の ρ_c = 3/(8πGℓ²)、p_c = ρ_c/3、首の ρ_B = 2/(16πGℓ²) のとき
    [T_nn] = −ρ_B − p_c = −1/(4πGℓ²) -/
theorem israel_jump (G l : ℝ) (hG : G ≠ 0) (hl : l ≠ 0) :
    -(2 / (16 * π * G * l ^ 2)) - (3 / (8 * π * G * l ^ 2)) / 3 = -(1 / (4 * π * G * l ^ 2)) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- したがって [T_nn] ≠ 0 で、時間対称な Israel 接合(σ = 0 には [T_nn] = 0 が必要)は不可能 -/
theorem israel_impossible (G l : ℝ) (hG : 0 < G) (hl : l ≠ 0) :
    -(2 / (16 * π * G * l ^ 2)) - (3 / (8 * π * G * l ^ 2)) / 3 ≠ 0 := by
  rw [israel_jump G l hG.ne' hl]
  have : 0 < 4 * π * G * l ^ 2 := by positivity
  have : 0 < 1 / (4 * π * G * l ^ 2) := by positivity
  linarith

/-! ### α-III.3 球対称 Penrose 型定理 -/

/-- 点ごとの評価:|J| ≤ ρ、|rK| ≤ r′ なら ρ r′ − J (r K) ≥ 0 -/
theorem integrand_nonneg (ρ J rp rK : ℝ) (hJ : |J| ≤ ρ) (hu : |rK| ≤ rp) :
    0 ≤ ρ * rp - J * rK := by
  have h1 : J * rK ≤ |J| * |rK| := by
    rw [← abs_mul]; exact le_abs_self _
  have hρ : 0 ≤ ρ := le_trans (abs_nonneg _) hJ
  have h2 : |J| * |rK| ≤ ρ * rp := mul_le_mul hJ hu (abs_nonneg _) hρ
  linarith

/-- 定理 Z0:境界球面から捕捉されない外側へ進むと M₂ ≥ r₀ -/
theorem penrose_spherical (r rp KT ρ J M : ℝ → ℝ) (s0 s1 : ℝ)
    (hM : ∀ s, M s = r s * (1 - rp s ^ 2 + r s ^ 2 * KT s ^ 2))
    (hD : ∀ s ∈ Set.Icc s0 s1, HasDerivAt M (r s ^ 2 * (ρ s * rp s - J s * (r s * KT s))) s)
    (hunt : ∀ s ∈ Set.Icc s0 s1, |r s * KT s| ≤ rp s)
    (hdec : ∀ s ∈ Set.Icc s0 s1, |J s| ≤ ρ s)
    (hmarg : rp s0 ^ 2 = r s0 ^ 2 * KT s0 ^ 2) :
    ∀ s ∈ Set.Icc s0 s1, r s0 ≤ M s := by
  have hM0 : M s0 = r s0 := by rw [hM, hmarg]; ring
  have hmono : MonotoneOn M (Set.Icc s0 s1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc s0 s1)
    · intro x hx; exact (hD x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hD x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Set.Ioo_subset_Icc_self hx
      rw [(hD x hx').deriv]
      exact mul_nonneg (sq_nonneg _) (integrand_nonneg _ _ _ _ (hdec x hx') (hunt x hx'))
  intro s hs
  by_cases h : s0 ≤ s1
  · rw [← hM0]
    exact hmono (Set.left_mem_Icc.2 h) hs hs.1
  · exact absurd (le_trans hs.1 hs.2) h

/-- 系:r₀ > 0 なら、その外側に M₂ = 0(平坦)の点はない -/
theorem no_flat_exterior (r rp KT ρ J M : ℝ → ℝ) (s0 s1 : ℝ)
    (hM : ∀ s, M s = r s * (1 - rp s ^ 2 + r s ^ 2 * KT s ^ 2))
    (hD : ∀ s ∈ Set.Icc s0 s1, HasDerivAt M (r s ^ 2 * (ρ s * rp s - J s * (r s * KT s))) s)
    (hunt : ∀ s ∈ Set.Icc s0 s1, |r s * KT s| ≤ rp s)
    (hdec : ∀ s ∈ Set.Icc s0 s1, |J s| ≤ ρ s)
    (hmarg : rp s0 ^ 2 = r s0 ^ 2 * KT s0 ^ 2) (hr0 : 0 < r s0) :
    ∀ s ∈ Set.Icc s0 s1, M s ≠ 0 := by
  intro s hs h0
  have := penrose_spherical r rp KT ρ J M s0 s1 hM hD hunt hdec hmarg s hs
  linarith

/-! ### α-III.4 M₂ の値と a = ℓ -/

/-- Q のキャップ(半径 a、r = a sin χ、r′ = cos χ、K = 0):M₂ = a sin³χ -/
theorem M2_cap (a χ : ℝ) :
    a * sin χ * (1 - cos χ ^ 2 + (a * sin χ) ^ 2 * 0 ^ 2) = a * sin χ ^ 3 := by
  have := sin_sq_add_cos_sq χ
  linear_combination (-(a * sin χ)) * this

/-- 赤道 χ = π/2 では M₂ = a(しかも r′ = 0、K = 0 なので境界球面) -/
theorem M2_equator (a : ℝ) : a * sin (π / 2) ^ 3 = a := by simp

/-- 首(r = ℓ、r′ = 0、K = 0):M₂ = ℓ で、すべての球面が境界球面 -/
theorem M2_neck (l : ℝ) : l * (1 - 0 ^ 2 + l ^ 2 * 0 ^ 2) = l := by ring

theorem neck_marginal (l : ℝ) : (0 : ℝ) ^ 2 = l ^ 2 * 0 ^ 2 := by ring

/-- 平坦(r = s、r′ = 1、K = 0):M₂ = 0 -/
theorem M2_flat (s : ℝ) : s * (1 - 1 ^ 2 + s ^ 2 * 0 ^ 2) = 0 := by ring

/-- 接合で M₂ が連続なら、キャップの半径は a = ℓ -/
theorem a_eq_l (a l : ℝ) (hcont : a * sin (π / 2) ^ 3 = l * (1 - 0 ^ 2 + l ^ 2 * 0 ^ 2)) :
    a = l := by
  rw [M2_equator, M2_neck] at hcont
  exact hcont

/-! ### α-III.5 Schwarzschild は公理 (C) と両立しない -/

/-- 空間的 Schwarzschild 断面:Ricci 固有値 (−2μ, μ, μ)。断面曲率は
    K₁₂ = K₁₃ = −μ、K₂₃ = 2μ で、R = 0、|Rm|² = 24μ² -/
theorem schw_R (μ : ℝ) : (-2 * μ) + μ + μ = 0 := by ring

theorem schw_Rm2 (μ : ℝ) : 4 * ((-μ) ^ 2 + (-μ) ^ 2 + (2 * μ) ^ 2) = 24 * μ ^ 2 := by ring

/-- 断面曲率と Ricci 固有値の関係の確認:λ₁ = K₁₂ + K₁₃ = −2μ、λ₂ = K₁₂ + K₂₃ = μ -/
theorem schw_consistent (μ : ℝ) : (-μ) + (-μ) = -2 * μ ∧ (-μ) + 2 * μ = μ := by
  constructor <;> ring

/-- μ ≠ 0、ℓ ≠ 0 なら (I) R = (ℓ²/2)|Rm|² は成り立たない -/
theorem schw_not_I (μ l : ℝ) (hμ : μ ≠ 0) (hl : l ≠ 0) :
    ¬ ((-2 * μ) + μ + μ = l ^ 2 / 2 * (4 * ((-μ) ^ 2 + (-μ) ^ 2 + (2 * μ) ^ 2))) := by
  rw [schw_R, schw_Rm2]
  intro h
  have : 0 < l ^ 2 / 2 * (24 * μ ^ 2) := by positivity
  linarith

/-! ### α-III.6 平坦極限との整合 -/

/-- R = 6/a² = 16πGρ から ρ = 3/(8πGa²)。このとき (4π/3)ρ(a sin χ)³ = a sin³χ/(2G) = M₂/(2G) -/
theorem cap_newton (G a χ : ℝ) (hG : G ≠ 0) (ha : a ≠ 0) :
    (4 * π / 3) * (3 / (8 * π * G * a ^ 2)) * (a * sin χ) ^ 3 = a * sin χ ^ 3 / (2 * G) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- dM₂/ds = r²ρ̃ r′(K = 0、ρ̃ = 8πGρ)と M₂ = 2Gm から dm/ds = 4πr²ρ r′ -/
theorem flat_mass_rate (G r ρ rp : ℝ) (hG : G ≠ 0) :
    r ^ 2 * (8 * π * G * ρ) * rp / (2 * G) = 4 * π * r ^ 2 * ρ * rp := by
  field_simp
  ring

/-! ### α-III.7 平坦側から見た最小質量 -/

private lemma eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  have h2 : (a - b) * (a + b) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · nlinarith

/-- ℓ* = √(4πG/g²) のとき ℓ*/(2G) = √π · (1/√G) / g -/
theorem min_mass (G g : ℝ) (hG : 0 < G) (hg : 0 < g) :
    √(4 * π * G / g ^ 2) / (2 * G) = √π * (1 / √G) / g := by
  apply eq_of_sq_eq (by positivity) (by positivity)
  have hr : (√π * (1 / √G)) ^ 2 = π / G := by
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt pi_pos.le, Real.sq_sqrt hG.le]
    ring
  rw [div_pow, Real.sq_sqrt (by positivity), div_pow, hr]
  field_simp
  ring

end CFT.AlphaIII
