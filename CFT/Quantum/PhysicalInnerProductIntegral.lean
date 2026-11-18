/-
  5-6 物理的内積の正定値性（積分表示）

  `PhysicalInnerProductStates.lean` では物理的内積を L² の抽象的な内積として
  扱い、非負性 (`phys_inner_nonneg`) と非退化性 (`phys_inner_eq_zero`) を
  証明した。ここではその内積が実際に C 表示の積分
    ⟨f, g⟩ = ∫ f̄(C) g(C) dC   (C > 8c²ℓ)
  であることを定理として固定し、ノルム二乗の積分表示と、非零状態に対する
  厳密な正値性を積分の形で示す。これで 5-6「物理状態の内積が実際に正定値
  であること」が、抽象形と積分形の両方で確認されたことになる。
  双線形性（共役対称性・加法性・スカラー倍）も物理的記法で固定する。
-/
import CFT.Quantum.PhysicalInnerProductStates

open MeasureTheory ComplexConjugate

namespace CFT.PhysInner

/-- 【5-6】物理的内積の積分表示：⟨f, g⟩ = ∫ f̄(C) g(C) dC -/
theorem phys_inner_eq_integral (c l : ℝ) (f g : CFT.Phys.Hphys c l) :
    inner f g = ∫ x, conj (f x) * g x ∂(volume.restrict (Set.Ioi (8 * c ^ 2 * l))) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => RCLike.inner_apply (f x) (g x)

/-- 【5-6】ノルム二乗の積分表示：‖f‖² = ∫ |f(C)|² dC -/
theorem phys_normSq_eq_integral (c l : ℝ) (f : CFT.Phys.Hphys c l) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(volume.restrict (Set.Ioi (8 * c ^ 2 * l))) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (E := CFT.Phys.Hphys c l) f,
    MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  apply integral_congr_ae
  filter_upwards with x
  exact inner_self_eq_norm_sq (f x)

/-- 【5-6】非零状態の厳密な正値性：⟨f, f⟩ の実部は正 -/
theorem phys_inner_pos_of_ne_zero (c l : ℝ) (f : CFT.Phys.Hphys c l) (hf0 : f ≠ 0) :
    0 < RCLike.re (inner f f : ℂ) := by
  rw [inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hf0) 2

/-- 【5-6】非零状態の厳密な正値性（積分形）：∫ |f(C)|² dC > 0 -/
theorem phys_inner_pos_integral (c l : ℝ) (f : CFT.Phys.Hphys c l) (hf0 : f ≠ 0) :
    0 < ∫ x, ‖f x‖ ^ 2 ∂(volume.restrict (Set.Ioi (8 * c ^ 2 * l))) := by
  rw [← phys_normSq_eq_integral c l f]
  exact pow_pos (norm_pos_iff.mpr hf0) 2

/-- 【5-6】共役対称性：⟨f, g⟩ の共役は ⟨g, f⟩ -/
theorem phys_inner_conj_symm (c l : ℝ) (f g : CFT.Phys.Hphys c l) :
    star (inner f g : ℂ) = (inner g f : ℂ) := inner_conj_symm g f

/-- 【5-6】第 2 引数についての加法性 -/
theorem phys_inner_add_right (c l : ℝ) (f g h : CFT.Phys.Hphys c l) :
    (inner f (g + h) : ℂ) = (inner f g : ℂ) + (inner f h : ℂ) := inner_add_right f g h

/-- 【5-6】第 2 引数についてのスカラー倍 -/
theorem phys_inner_smul_right (c l : ℝ) (r : ℂ) (f g : CFT.Phys.Hphys c l) :
    (inner f (r • g) : ℂ) = r * (inner f g : ℂ) := inner_smul_right f g r

end CFT.PhysInner
