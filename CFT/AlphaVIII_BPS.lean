/-
  α-VIII.7(Z44):BPS の no-go の代数的な核心(超対称なハミルトニアンの正値性)

  超対称代数 H = Q†Q + QQ†(有限次元の状態空間 ℂⁿ での形)について:
    * susy_posSemidef:H は半正定値
    * susy_energy_nonneg:H の固有値はすべて ≥ 0(負のエネルギーのモードはない)
    * bps_iff:⟨ψ, Hψ⟩ = 0 ⇔ Qψ = 0 かつ Q†ψ = 0(BPS 状態 = 超対称性を保つ状態)
    * no_bf_violating_mode:負の固有値を持つモード(BF 境界を破るモードのエネルギー)は存在しない
  したがって、超対称な(BPS)背景のゆらぎの演算子が H の形なら、AlphaVIII_BF の振動解
  (BF 境界の下のモード)は現れない。
  未形式化:Z44 の作用と超対称変換則から、ゆらぎの演算子が実際にこの形になること
  (Bergshoeff–de Roo のヘテロティック超重力の全作用が必要)。
-/
import CFT.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix ComplexOrder

namespace CFT.BPS

variable {n : Type*} [Fintype n]

/-- 超対称なハミルトニアン H = Q†Q + QQ† -/
noncomputable def susyH (Q : Matrix n n ℂ) : Matrix n n ℂ := Qᴴ * Q + Q * Qᴴ

theorem susy_posSemidef (Q : Matrix n n ℂ) : (susyH Q).PosSemidef :=
  (posSemidef_conjTranspose_mul_self Q).add (posSemidef_self_mul_conjTranspose Q)

/-- ⟨ψ, Hψ⟩ = ‖Qψ‖² + ‖Q†ψ‖² -/
theorem energy_split (Q : Matrix n n ℂ) (ψ : n → ℂ) :
    star ψ ⬝ᵥ (susyH Q *ᵥ ψ) = star (Q *ᵥ ψ) ⬝ᵥ (Q *ᵥ ψ) + star (Qᴴ *ᵥ ψ) ⬝ᵥ (Qᴴ *ᵥ ψ) := by
  simp only [susyH, add_mulVec, dotProduct_add, ← mulVec_mulVec]
  rw [dotProduct_mulVec, dotProduct_mulVec (star ψ) Q, star_mulVec, star_mulVec, conjTranspose_conjTranspose]

/-- BPS ⇔ 超対称性を保つ -/
theorem bps_iff (Q : Matrix n n ℂ) (ψ : n → ℂ) :
    star ψ ⬝ᵥ (susyH Q *ᵥ ψ) = 0 ↔ Q *ᵥ ψ = 0 ∧ Qᴴ *ᵥ ψ = 0 := by
  rw [energy_split]
  constructor
  · intro h
    have a := dotProduct_star_self_nonneg (Q *ᵥ ψ)
    have b := dotProduct_star_self_nonneg (Qᴴ *ᵥ ψ)
    have := (add_eq_zero_iff_of_nonneg a b).mp h
    exact ⟨dotProduct_star_self_eq_zero.mp this.1, dotProduct_star_self_eq_zero.mp this.2⟩
  · rintro ⟨h1, h2⟩; simp [h1, h2]

/-- 固有値は非負:Hψ = Eψ、ψ ≠ 0 なら 0 ≤ E -/
theorem susy_energy_nonneg (Q : Matrix n n ℂ) (ψ : n → ℂ) (E : ℂ) (hψ : ψ ≠ 0)
    (hE : susyH Q *ᵥ ψ = E • ψ) : 0 ≤ E := by
  have hpos : 0 ≤ star ψ ⬝ᵥ (susyH Q *ᵥ ψ) := (susy_posSemidef Q).2 ψ
  rw [hE, dotProduct_smul, smul_eq_mul] at hpos
  have hn : 0 < star ψ ⬝ᵥ ψ := dotProduct_star_self_pos_iff.mpr hψ
  obtain ⟨hr, hi⟩ := Complex.lt_def.mp hn
  rw [Complex.le_def] at hpos ⊢
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im] at hpos hr hi ⊢
  rw [← hi] at hpos
  simp only [mul_zero, sub_zero, add_zero] at hpos
  constructor
  · exact nonneg_of_mul_nonneg_left (by linarith [hpos.1]) hr
  · have := hpos.2; rw [zero_add] at this; rcases mul_eq_zero.mp this.symm with h | h
    · exact h.symm
    · linarith

/-- BF 境界を破るモード(負のエネルギー E < 0 の固有状態)は存在しない -/
theorem no_bf_violating_mode (Q : Matrix n n ℂ) (ψ : n → ℂ) (E : ℂ) (hψ : ψ ≠ 0)
    (hE : susyH Q *ᵥ ψ = E • ψ) : ¬ E < 0 :=
  fun h => (lt_irrefl (0 : ℂ)) (lt_of_le_of_lt (susy_energy_nonneg Q ψ E hψ hE) h)

end CFT.BPS
