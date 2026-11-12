/-
  Weak Gravity Conjecture(WGC)のまわりで、この理論の中で閉じる部分(2026-11-12)

  ℓ² = 4πG/g²。電荷 g q、質量 m の粒子に対する WGC は m ≤ g q/√(4πG) = q/ℓ(極限 RN の質量と電荷の比、外部の予想)。
  随伴 Higgs の真空の値 v で W ボソンは m_W = g v、電荷 1。BPS 単極子は質量 4πv/g、磁荷 4π/g。
  * `wgc_W`:(m_W ℓ)² = 4πG v²(g によらない)。
  * `wgc_monopole`:(単極子の質量/極限の質量)² = 4πG v²。W ボソンの電気的な WGC と単極子の磁気的な WGC は同じ条件 4πG v² ≤ 1。
  * `wgc_window`:首の安定の条件 (m_W ℓ)² ≥ 3/4(XI.4)と WGC (m_W ℓ)² ≤ 1 を合わせると 3/(16πG) ≤ v² ≤ 1/(4πG)。
    `wgc_window_nonempty`:この窓は空でない(幅は 3/4 から 1)。
  * `wgc_lambda`、`wgc_lambda_eq`:首が存在する宇宙定数の上限。1/R² − ℓ²/R⁴ ≤ 1/(4ℓ²)、等号は R² = 2ℓ²。
    `wgc_lambda_g`:1/(4ℓ²) = g²/(16πG)。Λ ≤ g²/(16πG)。
  * `wgc_fl`:Festina Lente の下限(外部の予想)は W ボソンについて (m_W ℓ)² ≥ √(Λℓ²)。
    首が存在し(Λℓ² ≤ 1/4)安定((m_W ℓ)² ≥ 3/4)なら、この下限は自動的に成り立つ。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Real

namespace CFT.WGC

theorem wgc_W (G g v l : ℝ) (hg : g ≠ 0) (hl : l ^ 2 = 4 * π * G / g ^ 2) :
    (g * v) ^ 2 * l ^ 2 = 4 * π * G * v ^ 2 := by
  rw [hl]
  field_simp
  ring

theorem wgc_monopole (G g v : ℝ) (hg : g ≠ 0) (hG : G ≠ 0) :
    (4 * π * v / g) ^ 2 / ((4 * π / g) ^ 2 / (4 * π * G)) = 4 * π * G * v ^ 2 := by
  have hp := Real.pi_ne_zero
  field_simp
  ring

theorem wgc_window (k v : ℝ) (hk : 0 < k) :
    (3 / (4 * k) ≤ v ^ 2 ∧ v ^ 2 ≤ 1 / k) ↔ (3 / 4 ≤ k * v ^ 2 ∧ k * v ^ 2 ≤ 1) := by
  have h4k : 0 < 4 * k := by linarith
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff h4k] at h1
    rw [le_div_iff hk] at h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor
    · rw [div_le_iff h4k]
      linarith
    · rw [le_div_iff hk]
      linarith

theorem wgc_window_nonempty : ∃ x : ℝ, 3 / 4 ≤ x ∧ x ≤ 1 := ⟨7 / 8, by norm_num, by norm_num⟩

theorem wgc_lambda_id (R l : ℝ) (hR : R ≠ 0) (hl : l ≠ 0) :
    1 / (4 * l ^ 2) - (1 / R ^ 2 - l ^ 2 / R ^ 4) = (l / R ^ 2 - 1 / (2 * l)) ^ 2 := by
  field_simp
  ring

theorem wgc_lambda (R l : ℝ) (hR : R ≠ 0) (hl : l ≠ 0) :
    1 / R ^ 2 - l ^ 2 / R ^ 4 ≤ 1 / (4 * l ^ 2) := by
  have e := wgc_lambda_id R l hR hl
  have h := sq_nonneg (l / R ^ 2 - 1 / (2 * l))
  linarith

theorem wgc_lambda_eq (l : ℝ) (hl : l ≠ 0) (R : ℝ) (hR : R ^ 2 = 2 * l ^ 2) :
    1 / R ^ 2 - l ^ 2 / R ^ 4 = 1 / (4 * l ^ 2) := by
  rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, hR]
  field_simp
  ring

theorem wgc_lambda_g (G g l : ℝ) (hg : g ≠ 0) (hG : G ≠ 0) (hl : l ^ 2 = 4 * π * G / g ^ 2) :
    1 / (4 * l ^ 2) = g ^ 2 / (16 * π * G) := by
  have hp := Real.pi_ne_zero
  rw [hl]
  field_simp
  ring

theorem wgc_fl (x lam : ℝ) (hlam : lam ≤ 1 / 4) (hx : 3 / 4 ≤ x) : Real.sqrt lam ≤ x := by
  have h : Real.sqrt lam ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · have : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
      linarith
  linarith

end CFT.WGC
