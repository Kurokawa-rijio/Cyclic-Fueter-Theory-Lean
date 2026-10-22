/-
  α-III.7 の合成(2026-10-21 の評価基準 3-G:質量の下限を定義の書き換えでなく条件から導く)

  旧 min_mass は数の恒等式 ℓ*/(2G) = √π M_Pl/g だけだった。ここでは
  * min_mass_from_constraints:ハミルトン拘束・運動量拘束(場の方程式)、未捕捉(|rK_T| ≤ r′)、
    優勢エネルギー条件(|J| ≤ ρ)、出発点が周縁的捕捉面(首の喉)で r(s₀)=ℓ、首の EYM
    ハミルトン拘束を仮定する。ell_neck から ℓ²=4πG/g²、従って r₀²=4πG/g² を導き、
    外側のすべての点で物理質量 m=M₂/(2G) ≥ √π M_Pl/g を示す(penrose_from_constraints と min_mass を合成)。
-/
import CFT.AlphaIII_Shape
import CFT.AlphaII_EYM

open Real Set

namespace CFT.S3M

theorem min_mass_from_constraints (r rp rpp a KT KTp ρ J M : ℝ → ℝ) (s0 s1 G g l : ℝ)
    (hG : 0 < G) (hg : 0 < g) (hlpos : 0 < l)
    (hneckR : r s0 = l)
    (hneckEYM : 16 * π * G * (1 / (2 * g ^ 2 * l ^ 4)) = 2 / l ^ 2)
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
    (hmarg : rp s0 ^ 2 = r s0 ^ 2 * KT s0 ^ 2) :
    ∀ s ∈ Icc s0 s1, √π * (1 / √G) / g ≤ M s / (2 * G) := by
  have hEll : l ^ 2 = 4 * π * G / g ^ 2 :=
    (CFT.EYM.ell_neck G g l (ne_of_gt hg) (ne_of_gt hlpos) (ne_of_gt hG)).1 hneckEYM
  have hneck : r s0 ^ 2 = 4 * π * G / g ^ 2 := by
    rw [hneckR, hEll]
  have hpos : 0 < r s0 := by rw [hneckR]; exact hlpos
  intro s hs
  have hp := CFT.Shape.penrose_from_constraints r rp rpp a KT KTp ρ J M s0 s1 hM hr0 d1 d2 d3 hH hMom hunt hdec
    hmarg s hs
  have hr : r s0 = √(4 * π * G / g ^ 2) := by
    rw [← hneck, Real.sqrt_sq hpos.le]
  rw [← CFT.AlphaIII.min_mass G g hG hg, ← hr]
  exact div_le_div_of_nonneg_right hp (by positivity)

end CFT.S3M
