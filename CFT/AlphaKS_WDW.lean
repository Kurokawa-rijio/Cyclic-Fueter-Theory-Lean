/-
  首の側の量子重力の方程式:Kantowski–Sachs 型のミニ超空間(2026-11-12)

  計量 −N²dt² + a(t)²dx² + r(t)²dΩ² と磁気的な W(t)。縮約した作用(c = L/(2G)、L は x の長さ)は
  c∫dt{[−a ṙ² − 2r ȧ ṙ + 2ℓ² a Ẇ²]/N + N a[1 − ℓ²(1 − W²)²/r²]}。
  首(r = ℓ、W = 0)と、W = 0 の Reissner–Nordström の内部を含む。
  * `ks_hamiltonian`:運動量 p_a = −2c r ṙ、p_r = −2c(a ṙ + r ȧ)、p_W = 4cℓ² a Ẇ で、
    −p_a p_r/(2r) + a p_a²/(4r²) + p_W²/(8ℓ²a) = c²(−a ṙ² − 2r ȧ ṙ + 2ℓ² a Ẇ²)。p_r について 1 次(r が時計)。
  * `ks_rn`:RN の内部 f = 1 − 2M/r + ℓ²/r² は拘束 f + r f′ = 1 − ℓ²/r² をみたす。
  * `ks_hj`、`ks_hj_solves`:W = 0 の部分で、σ = a² r/2、θ = −(r + ℓ²/r)/2 とすると
    S = kσ + κθ は kκ = 4c² のとき Hamilton–Jacobi 方程式の解(WDW は ∂_σ∂_θ Ψ = −4c² Ψ の形)。
  * `ks_inversion_theta`、`ks_inversion_sigma`:r → ℓ²/r、a → a r/ℓ で σ、θ は不変(反転の対称性)。
  * `ks_fold_le`、`ks_fold_eq`:θ ≤ −ℓ、等号は r = ℓ(首)だけ。首はミニ超空間の折り目。
  * `ks_inverted`:ポテンシャルの W についての展開 ℓ²(1 − W²)² = ℓ² − 2ℓ²W² + ℓ²W⁴(W = 0 で逆さの振動子)。
-/
import Mathlib.Tactic

namespace CFT.KS

theorem ks_hamiltonian (a r ad rd Wd c l : ℝ) (hr : r ≠ 0) (ha : a ≠ 0) (hl : l ≠ 0) :
    -(-2 * c * r * rd) * (-2 * c * (a * rd + r * ad)) / (2 * r)
      + a * (-2 * c * r * rd) ^ 2 / (4 * r ^ 2) + (4 * c * l ^ 2 * a * Wd) ^ 2 / (8 * l ^ 2 * a)
      = c ^ 2 * (-a * rd ^ 2 - 2 * r * ad * rd + 2 * l ^ 2 * a * Wd ^ 2) := by
  field_simp
  ring

theorem ks_rn (r M l : ℝ) (hr : r ≠ 0) :
    (1 - 2 * M / r + l ^ 2 / r ^ 2) + r * (2 * M / r ^ 2 - 2 * l ^ 2 / r ^ 3) = 1 - l ^ 2 / r ^ 2 := by
  field_simp
  ring

theorem ks_hj (a r k κ l : ℝ) (hr : r ≠ 0) :
    -(k * a * r) * (k * a ^ 2 / 2 - κ * (1 - l ^ 2 / r ^ 2) / 2) / (2 * r)
      + a * (k * a * r) ^ 2 / (4 * r ^ 2) = k * κ * a * (1 - l ^ 2 / r ^ 2) / 4 := by
  field_simp
  ring

theorem ks_hj_solves (a r k κ l c : ℝ) (hr : r ≠ 0) (h : k * κ = 4 * c ^ 2) :
    -(k * a * r) * (k * a ^ 2 / 2 - κ * (1 - l ^ 2 / r ^ 2) / 2) / (2 * r)
      + a * (k * a * r) ^ 2 / (4 * r ^ 2) = c ^ 2 * a * (1 - l ^ 2 / r ^ 2) := by
  rw [ks_hj a r k κ l hr]
  linear_combination (a * (1 - l ^ 2 / r ^ 2) / 4) * h

theorem ks_inversion_theta (r l : ℝ) (hr : r ≠ 0) (hl : l ≠ 0) :
    -(l ^ 2 / r + l ^ 2 / (l ^ 2 / r)) / 2 = -(r + l ^ 2 / r) / 2 := by
  field_simp
  ring

theorem ks_inversion_sigma (a r l : ℝ) (hr : r ≠ 0) (hl : l ≠ 0) :
    (a * r / l) ^ 2 * (l ^ 2 / r) / 2 = a ^ 2 * r / 2 := by
  field_simp
  ring

theorem ks_fold_id (r l : ℝ) (hr : r ≠ 0) : r + l ^ 2 / r - 2 * l = (r - l) ^ 2 / r := by
  field_simp
  ring

theorem ks_fold_le (r l : ℝ) (hr : 0 < r) : -(r + l ^ 2 / r) / 2 ≤ -l := by
  have e := ks_fold_id r l hr.ne'
  have h : 0 ≤ (r - l) ^ 2 / r := div_nonneg (sq_nonneg _) hr.le
  linarith

theorem ks_fold_eq (r l : ℝ) (hr : 0 < r) (h : -(r + l ^ 2 / r) / 2 = -l) : r = l := by
  have e := ks_fold_id r l hr.ne'
  have h0 : (r - l) ^ 2 / r = 0 := by linarith
  rcases div_eq_zero_iff.mp h0 with h1 | h1
  · have h2 := (pow_eq_zero_iff two_ne_zero).mp h1
    linarith
  · exact absurd h1 hr.ne'

theorem ks_inverted (W l : ℝ) : l ^ 2 * (1 - W ^ 2) ^ 2 = l ^ 2 - 2 * l ^ 2 * W ^ 2 + l ^ 2 * W ^ 4 := by
  ring

end CFT.KS
