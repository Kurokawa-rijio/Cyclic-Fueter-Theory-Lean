/-
  α-III.4(Z0′)の作り直し:帽子の半径 a = ℓ と「首は平坦へ開けない」を、仮定を結論にせずに示す

  監査の指摘:旧 a_eq_l は「M₂ が連続」を仮定にしていて、それがほぼ結論そのものだった。
  ここでは二つの独立な道で a = ℓ を出す。
    * glue_C1:帽子 r = a sin(s/a) と首 r = ℓ を C¹ で貼る([r] = [r′] = 0)。首では r′ = 0 なので
      接合点で cos(s_j/a) = 0、そこで r = a sin(s_j/a) = ℓ。a, ℓ > 0 から sin = 1、a = ℓ
    * glue_EYM:EYM のハミルトン拘束は帽子で a² = 4πG/g²、首で ℓ² = 4πG/g²(AlphaII_EYM の
      ell_cap、ell_neck)を要求するので、a = ℓ
  首は平坦へ開けない:
    * no_flat_from_constraints:接合の球面は周縁的捕捉面(r′ = rK_T = 0)。そこから外へ、捕捉されず
      (|rK_T| ≤ r′)優勢エネルギー条件(|J| ≤ ρ)が成り立つ限り、拘束方程式から M₂ ≥ r₀ > 0
      (AlphaIII_Shape の penrose_from_constraints)。よって M₂ = 0(平坦)の点には到達しない
-/
import CFT.AlphaIII_Shape
import CFT.AlphaII_EYM

open Real Set

namespace CFT.Glue

/-- C¹ の貼り合わせから a = ℓ -/
theorem glue_C1 (a l sj : ℝ) (ha : 0 < a) (hl : 0 < l)
    (hr1 : cos (sj / a) = 0) (hr : a * sin (sj / a) = l) : a = l := by
  have hs : sin (sj / a) ^ 2 = 1 := by have := sin_sq_add_cos_sq (sj / a); rw [hr1] at this; linarith
  have hpos : 0 < sin (sj / a) := by
    by_contra h; push_neg at h
    have : a * sin (sj / a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le h
    linarith
  have h1 : sin (sj / a) = 1 := by nlinarith [hs, hpos]
  rw [h1, mul_one] at hr; exact hr

/-- EYM の拘束から a = ℓ(帽子と首がそれぞれ半径² = 4πG/g² を要求) -/
theorem glue_EYM (G g a l : ℝ) (hg : g ≠ 0) (ha : 0 < a) (hl : 0 < l) (hG : G ≠ 0)
    (hcap : 16 * π * G * (3 / (2 * g ^ 2 * a ^ 4)) = 6 / a ^ 2)
    (hneck : 16 * π * G * (1 / (2 * g ^ 2 * l ^ 4)) = 2 / l ^ 2) : a = l := by
  have h1 := (CFT.EYM.ell_cap G g a hg ha.ne' hG).1 hcap
  have h2 := (CFT.EYM.ell_neck G g l hg hl.ne' hG).1 hneck
  have : a ^ 2 = l ^ 2 := by rw [h1, h2]
  nlinarith [sq_nonneg (a - l), sq_nonneg (a + l)]

/-- 首は平坦へ開けない(拘束方程式から) -/
theorem no_flat_from_constraints (r rp rpp a KT KTp ρ J M : ℝ → ℝ) (s0 s1 : ℝ)
    (hM : ∀ s, M s = r s * (1 - rp s ^ 2 + r s ^ 2 * KT s ^ 2))
    (hr0 : ∀ s ∈ Icc s0 s1, r s ≠ 0)
    (d1 : ∀ s ∈ Icc s0 s1, HasDerivAt r (rp s) s)
    (d2 : ∀ s ∈ Icc s0 s1, HasDerivAt rp (rpp s) s)
    (d3 : ∀ s ∈ Icc s0 s1, HasDerivAt KT (KTp s) s)
    (hH : ∀ s ∈ Icc s0 s1, 2 * (1 - rp s ^ 2 - 2 * r s * rpp s) / r s ^ 2
      + 4 * a s * KT s + 2 * KT s ^ 2 = 2 * ρ s)
    (hMom : ∀ s ∈ Icc s0 s1, 2 * (rp s / r s) * (a s - KT s) - 2 * KTp s = J s)
    (hunt : ∀ s ∈ Icc s0 s1, |r s * KT s| ≤ rp s)
    (hdec : ∀ s ∈ Icc s0 s1, |J s| ≤ ρ s)
    (hmarg : rp s0 ^ 2 = r s0 ^ 2 * KT s0 ^ 2) (hpos : 0 < r s0) :
    ∀ s ∈ Icc s0 s1, M s ≠ 0 := by
  intro s hs h0
  have := CFT.Shape.penrose_from_constraints r rp rpp a KT KTp ρ J M s0 s1 hM hr0 d1 d2 d3 hH hMom
    hunt hdec hmarg s hs
  linarith

/-- 接合の球面は周縁的捕捉面:r′ = 0、K_T = 0 で hmarg が成り立つ -/
theorem junction_marginal (l : ℝ) : (0 : ℝ) ^ 2 = l ^ 2 * 0 ^ 2 := by ring

end CFT.Glue
