/-
  α-VIII.7(Z44):崩壊するダンベルは BPS(超対称)でない

  論理(合意した再構成):
    (1) 外部定理:Killing スピノル ε ≠ 0 があれば、双線形 K^μ = ε̄γ^με は Killing ベクトル
        (Tod、Gauntlett–Gutowski らの標準的な結果。ここでは仮定 hKilling)。
        時間成分は K^t = ε†ε > 0(killing_time_pos、ここで証明)。
    (2) 球対称な時空の等長変換は面積半径 r を保つ:K(r) = K^t ∂_t r + K^s ∂_s r = 0(仮定 hiso)。
    (3) 首の中心(喉)では ∂_s r = 0(r の極小)。よって K^t ∂_t r = 0、K^t ≠ 0 から ∂_t r = 0。
    (4) Z9(大域的な崩壊):首の半径 r(t) は r(0) > 0 から有限時間 T で 0 になる。
  (3) と (4) は両立しない:no_killing_spinor。
    * causal_time_ne_zero:0 でない因果的なベクトル(−K_t² + |K_x|² ≤ 0)は K^t ≠ 0
  BF 境界の側(AlphaVIII_BPS):超対称なら揺らぎの演算子は Q†Q + QQ† の形で負のモードがない。
-/
import CFT.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace CFT.Z44

/-- K^t = ε†ε = Σ|ε_a|² > 0(ε ≠ 0、成分を実部・虚部の組で書く) -/
theorem killing_time_pos (ε : Fin 4 → ℝ × ℝ) (hε : ε ≠ 0) :
    0 < ∑ a, ((ε a).1 ^ 2 + (ε a).2 ^ 2) := by
  obtain ⟨a, ha⟩ : ∃ a, ε a ≠ 0 := by
    by_contra h; push_neg at h; exact hε (funext h)
  have hpos : 0 < (ε a).1 ^ 2 + (ε a).2 ^ 2 := by
    by_cases h1 : (ε a).1 = 0
    · have h2 : (ε a).2 ≠ 0 := fun h2 => ha (Prod.ext h1 h2)
      positivity
    · positivity
  calc 0 < (ε a).1 ^ 2 + (ε a).2 ^ 2 := hpos
    _ ≤ ∑ b, ((ε b).1 ^ 2 + (ε b).2 ^ 2) :=
      Finset.single_le_sum (f := fun b => (ε b).1 ^ 2 + (ε b).2 ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ a)

/-- 0 でない因果的なベクトルの時間成分は 0 でない -/
theorem causal_time_ne_zero (Kt : ℝ) (Kx : Fin 3 → ℝ) (hK : (Kt, Kx) ≠ (0, 0))
    (hcausal : -Kt ^ 2 + (Kx 0 ^ 2 + Kx 1 ^ 2 + Kx 2 ^ 2) ≤ 0) : Kt ≠ 0 := by
  intro h0
  subst h0
  have h0' : Kx 0 = 0 := by nlinarith [sq_nonneg (Kx 0), sq_nonneg (Kx 1), sq_nonneg (Kx 2)]
  have h1' : Kx 1 = 0 := by nlinarith [sq_nonneg (Kx 0), sq_nonneg (Kx 1), sq_nonneg (Kx 2)]
  have h2' : Kx 2 = 0 := by nlinarith [sq_nonneg (Kx 0), sq_nonneg (Kx 1), sq_nonneg (Kx 2)]
  apply hK
  have : Kx = 0 := by funext i; fin_cases i <;> simp [h0', h1', h2']
  rw [this]

/-- 首の喉で Killing ベクトルがあれば半径は時間によらない -/
theorem throat_static (r r' Kt Ks : ℝ → ℝ) (hr : ∀ t, HasDerivAt r (r' t) t)
    (hKt : ∀ t, Kt t ≠ 0) (hiso : ∀ t, Kt t * r' t + Ks t * 0 = 0) : ∀ t, r t = r 0 := by
  have hz : ∀ t, r' t = 0 := fun t => by
    have := hiso t; rw [mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (hKt t)
  intro t
  have hd : ∀ x, HasDerivAt r 0 x := fun x => by simpa [hz x] using hr x
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0

/-- 崩壊するダンベル(Z9)には Killing スピノルがない -/
theorem no_killing_spinor (r r' : ℝ → ℝ) (hr : ∀ t, HasDerivAt r (r' t) t)
    (hcollapse : 0 < r 0 ∧ ∃ T, r T = 0)
    (ε : ℝ → Fin 4 → ℝ × ℝ) (hε : ∀ t, ε t ≠ 0)
    (Ks : ℝ → ℝ)
    (hiso : ∀ t, (∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) * r' t + Ks t * 0 = 0) : False := by
  have hKt : ∀ t, (∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) ≠ 0 :=
    fun t => (killing_time_pos (ε t) (hε t)).ne'
  have hs := throat_static r r' (fun t => ∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) Ks hr hKt hiso
  obtain ⟨h0, T, hT⟩ := hcollapse
  have := hs T
  linarith

end CFT.Z44
