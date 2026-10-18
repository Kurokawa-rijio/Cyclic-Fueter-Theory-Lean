/-
  α-III.9(Z23):Gauss–Codazzi 分解と接合の統一(球対称での定式化)

  空間の切り口 ds² + r(s)² dΩ²(時間対称、K_ij = 0)。Gauss の式によるハミルトン拘束
    ³R = 2(1 − r′² − 2 r r″)/r² = 16πG ρ
  (α-II.9 の ham と同じ形。帽子と首の各領域での拘束は AlphaIntegrals の cap_constraint, neck_constraint)。

  接合面 s = s₀ の三つの型:
    * 空間的な切り口の中の 2 球面(この節):r は連続、r′ が跳ぶと r″ は δ 関数を含む。
      弱い意味で r″ = r″_正則 + [r′] δ_{s₀}(weak_second_derivative。部分積分を両側で行う)。
      拘束の δ の係数を比べると、表面密度 σ = −[r′]/(4πG r₀)(shell_density)。
      したがって [r′] = 0 ⇔ 殻なし(no_shell_iff)。Z1 の帽子と首の接合は [r] = [r′] = 0 なので殻なし。
    * 時間的な面:Israel の条件 [K_ij] − h_ij[K] = −8πG S_ij(α-III.1 の israel_jump, israel_impossible)
    * ヌルな面:k^μ[T_μν] = 0(α-III.2 の null_front)
  面の型は法線 n の長さの符号で決まる(classify)。
  未形式化:非球対称な接合、一般の超曲面上の分布としての Einstein 方程式。
-/
import CFT.Basic
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open Real intervalIntegral Set

namespace CFT.Junction

/-- 面の型:法線 n の長さ g(n,n) の符号 -/
inductive Kind | timelike | spacelike | null

/-- g(n,n) > 0 なら時間的な面、< 0 なら空間的な面、= 0 ならヌルな面(符号 (−,+,+,+)) -/
noncomputable def classify (nn : ℝ) : Kind :=
  if 0 < nn then Kind.timelike else if nn < 0 then Kind.spacelike else Kind.null

theorem classify_null : classify 0 = Kind.null := by simp [classify]

/-- 球対称な切り口のスカラー曲率(Gauss の式) -/
noncomputable def scalR (r rp rpp : ℝ) : ℝ := 2 * (1 - rp ^ 2 - 2 * r * rpp) / r ^ 2

/-- r″ の弱い形:両側で部分積分すると −∫ r′φ′ = ∫ r″_正則 φ + [r′] φ(s₀) -/
theorem weak_second_derivative {a s₀ b : ℝ} (has : a ≤ s₀) (hsb : s₀ ≤ b)
    {pm pp rm rp φ φ' : ℝ → ℝ}
    (hpm : ∀ x ∈ Icc a s₀, HasDerivWithinAt pm (rm x) (Icc a s₀) x)
    (hpp : ∀ x ∈ Icc s₀ b, HasDerivWithinAt pp (rp x) (Icc s₀ b) x)
    (hφm : ∀ x ∈ Icc a s₀, HasDerivWithinAt φ (φ' x) (Icc a s₀) x)
    (hφp : ∀ x ∈ Icc s₀ b, HasDerivWithinAt φ (φ' x) (Icc s₀ b) x)
    (hrm : IntervalIntegrable rm MeasureTheory.volume a s₀)
    (hrp : IntervalIntegrable rp MeasureTheory.volume s₀ b)
    (hφ'm : IntervalIntegrable φ' MeasureTheory.volume a s₀)
    (hφ'p : IntervalIntegrable φ' MeasureTheory.volume s₀ b)
    (ha : φ a = 0) (hb : φ b = 0) :
    -((∫ x in a..s₀, pm x * φ' x) + ∫ x in s₀..b, pp x * φ' x)
      = (∫ x in a..s₀, rm x * φ x) + (∫ x in s₀..b, rp x * φ x) + (pp s₀ - pm s₀) * φ s₀ := by
  have e1 := integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := pm) (v := φ) (u' := rm) (v' := φ') (a := a) (b := s₀)
    (by rw [uIcc_of_le has]; exact hpm) (by rw [uIcc_of_le has]; exact hφm) hrm hφ'm
  have e2 := integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := pp) (v := φ) (u' := rp) (v' := φ') (a := s₀) (b := b)
    (by rw [uIcc_of_le hsb]; exact hpp) (by rw [uIcc_of_le hsb]; exact hφp) hrp hφ'p
  rw [e1, e2, ha, hb]
  ring

/-- 拘束 ³R = 16πG(ρ_正則 + σ δ) の δ の係数:−4[r′]/r₀ = 16πG σ ⇒ σ = −[r′]/(4πG r₀) -/
theorem shell_density (G r₀ jump σ : ℝ) (hG : G ≠ 0) (hr : r₀ ≠ 0)
    (h : 2 * (-(2 * r₀ * jump)) / r₀ ^ 2 = 16 * π * G * σ) :
    σ = -jump / (4 * π * G * r₀) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp at h ⊢
  have h2 : r₀ * (σ * (4 * π * G * r₀) + jump) = 0 := by linear_combination (-1 / 4 : ℝ) * h
  have h3 := (mul_eq_zero.mp h2).resolve_left hr
  linarith

/-- 殻がない ⇔ [r′] = 0 -/
theorem no_shell_iff (G r₀ jump : ℝ) (hG : G ≠ 0) (hr : r₀ ≠ 0) :
    -jump / (4 * π * G * r₀) = 0 ↔ jump = 0 := by
  have hπ : π ≠ 0 := pi_ne_zero
  constructor
  · intro h
    have : (4 * π * G * r₀) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG) hr
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · exact absurd h this
  · intro h; rw [h]; simp

/-- 時間対称な切り口の拘束は ρ = ³R/(16πG) で、Z5 のハミルトン拘束(ham)と同じ形 -/
theorem constraint_form (r rp rpp : ℝ) (hr : r ≠ 0) :
    scalR r rp rpp / 2 = (1 - rp ^ 2 - 2 * r * rpp) / r ^ 2 := by
  unfold scalR; field_simp; ring

end CFT.Junction
