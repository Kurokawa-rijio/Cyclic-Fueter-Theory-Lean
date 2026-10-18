/-
  α-VIII.5(Z38、Z42):ℓ*² と α′ の関係、SU(2)_k WZW のレベルの障害

  理論の側:ℓ*² = 4πG/g²(α-II.1、AlphaII の ham)。
  弦の側(外部の結果):ヘテロティック弦の木の近似の次元縮約で G_N = c·α_GUT·α′、α_GUT = g²/(4π)。
  係数 c は規約による:Witten(1996、hep-th/9602070)の規約では c = 1/4、
  台帳の ℓ*² = α′/8 は c = 1/8 の規約(g² = 4κ²/α′、κ² = 8πG)に当たる。
  採用(2026-10-16):Witten の規約 c = 1/4、ℓ*² = α′/4。
    * ell_sq_eq:ℓ*² = c·α′(c は G_N = c α_GUT α′ の係数そのもの)
    * ell_ledger:c = 1/8 なら ℓ*² = α′/8(台帳)、ell_witten:c = 1/4 なら α′/4
    * kaplunovsky:g² = 4κ²/α′、κ² = 8πG なら c = 1/8
  Z42:S³ の半径 R の SU(2)_k WZW では R² = kα′。R = ℓ* なら k = c。
    * wzw_level:k = c、wzw_obstruction:0 < c < 1 なら k は正の整数でない(c = 1/8 でも 1/4 でも障害)
-/
import CFT.Basic

open Real

namespace CFT.Z38

/-- ℓ*² = 4πG/g² に G = c (g²/4π) α′ を入れると ℓ*² = c α′ -/
theorem ell_sq_eq (G g c α' : ℝ) (hg : g ≠ 0) (hG : G = c * (g ^ 2 / (4 * π)) * α') :
    4 * π * G / g ^ 2 = c * α' := by
  have hπ : π ≠ 0 := pi_ne_zero
  rw [hG]; field_simp; ring

theorem ell_ledger (G g α' : ℝ) (hg : g ≠ 0) (hG : G = (1 / 8) * (g ^ 2 / (4 * π)) * α') :
    4 * π * G / g ^ 2 = α' / 8 := by
  rw [ell_sq_eq G g (1 / 8) α' hg hG]; ring

theorem ell_witten (G g α' : ℝ) (hg : g ≠ 0) (hG : G = (1 / 4) * (g ^ 2 / (4 * π)) * α') :
    4 * π * G / g ^ 2 = α' / 4 := by
  rw [ell_sq_eq G g (1 / 4) α' hg hG]; ring

/-- g² = 4κ²/α′、κ² = 8πG ⇒ G = (1/8)(g²/4π)α′ -/
theorem kaplunovsky (G g κ α' : ℝ) (hα : α' ≠ 0) (hκ : κ ^ 2 = 8 * π * G)
    (hgk : g ^ 2 = 4 * κ ^ 2 / α') : G = (1 / 8) * (g ^ 2 / (4 * π)) * α' := by
  have hπ : π ≠ 0 := pi_ne_zero
  rw [hgk, hκ]; field_simp; ring

/-- R² = kα′ と R = ℓ*(R² = c α′)から k = c -/
theorem wzw_level (k c α' : ℝ) (hα : α' ≠ 0) (h : k * α' = c * α') : k = c :=
  mul_right_cancel₀ hα h

/-- 0 < c < 1 なら k = c は正の整数でない -/
theorem wzw_obstruction (c : ℝ) (h0 : 0 < c) (h1 : c < 1) : ¬ ∃ m : ℕ, 0 < m ∧ (m : ℝ) = c := by
  rintro ⟨m, hm, hmc⟩
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem wzw_obstruction_values :
    (¬ ∃ m : ℕ, 0 < m ∧ (m : ℝ) = 1 / 8) ∧ (¬ ∃ m : ℕ, 0 < m ∧ (m : ℝ) = 1 / 4) :=
  ⟨wzw_obstruction _ (by norm_num) (by norm_num), wzw_obstruction _ (by norm_num) (by norm_num)⟩

end CFT.Z38
