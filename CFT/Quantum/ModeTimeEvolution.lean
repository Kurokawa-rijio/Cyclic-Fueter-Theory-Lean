import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 7-3（摂動の時間発展）の単一モード核：
  固有値 −ω²（安定）に対応するモード A cos ωt + B sin ωt は ψ'' = −ω²ψ を満たし有界、
  固有値 +μ²（不安定）に対応するモード A cosh μt + B sinh μt は ψ'' = +μ²ψ を満たし、
  cosh モードは 1 以上に留まり続ける。固有値の符号 ↔ 成長/有界の対応の最小モデル。
-/

namespace CFT.ModeEvolution

open Real

/-- 安定モードの1階微分。 -/
theorem stableMode_hasDerivAt (ω A B t : ℝ) :
    HasDerivAt (fun s => A * cos (ω * s) + B * sin (ω * s))
      (ω * (-A * sin (ω * t) + B * cos (ω * t))) t := by
  have hcos : HasDerivAt (fun s => cos (ω * s)) (-sin (ω * t) * ω) t :=
    (hasDerivAt_cos (ω * t)).comp t (by simpa using (hasDerivAt_id t).const_mul ω)
  have hsin : HasDerivAt (fun s => sin (ω * s)) (cos (ω * t) * ω) t :=
    (hasDerivAt_sin (ω * t)).comp t (by simpa using (hasDerivAt_id t).const_mul ω)
  have h := (hcos.const_mul A).add (hsin.const_mul B)
  convert h using 1
  ring

/-- 安定モードの導関数の微分。 -/
theorem stableMode_deriv_hasDerivAt (ω A B t : ℝ) :
    HasDerivAt (fun s => ω * (-A * sin (ω * s) + B * cos (ω * s)))
      (-ω ^ 2 * (A * cos (ω * t) + B * sin (ω * t))) t := by
  have hcos : HasDerivAt (fun s => cos (ω * s)) (-sin (ω * t) * ω) t :=
    (hasDerivAt_cos (ω * t)).comp t (by simpa using (hasDerivAt_id t).const_mul ω)
  have hsin : HasDerivAt (fun s => sin (ω * s)) (cos (ω * t) * ω) t :=
    (hasDerivAt_sin (ω * t)).comp t (by simpa using (hasDerivAt_id t).const_mul ω)
  have h := ((hsin.const_mul (-A)).add (hcos.const_mul B)).const_mul ω
  convert h using 1 <;> ring

/-- 安定モードは ψ'' = −ω²ψ を満たす。 -/
theorem stableMode_secondDeriv (ω A B t : ℝ) :
    deriv (deriv (fun s => A * cos (ω * s) + B * sin (ω * s))) t
      = -ω ^ 2 * (A * cos (ω * t) + B * sin (ω * t)) := by
  have hderiv : deriv (fun s => A * cos (ω * s) + B * sin (ω * s))
      = fun s => ω * (-A * sin (ω * s) + B * cos (ω * s)) :=
    funext fun s => (stableMode_hasDerivAt ω A B s).deriv
  rw [hderiv]
  exact (stableMode_deriv_hasDerivAt ω A B t).deriv

/-- 安定モードは有界：|ψ(t)| ≤ |A| + |B|。 -/
theorem stableMode_bounded (ω A B t : ℝ) :
    |A * cos (ω * t) + B * sin (ω * t)| ≤ |A| + |B| := by
  refine (abs_add _ _).trans ?_
  have h1 : |A * cos (ω * t)| ≤ |A| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg A) (abs_cos_le_one _)
  have h2 : |B * sin (ω * t)| ≤ |B| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg B) (abs_sin_le_one _)
  exact add_le_add h1 h2

/-- 不安定モードの1階微分。 -/
theorem unstableMode_hasDerivAt (μ A B t : ℝ) :
    HasDerivAt (fun s => A * cosh (μ * s) + B * sinh (μ * s))
      (μ * (A * sinh (μ * t) + B * cosh (μ * t))) t := by
  have hcosh : HasDerivAt (fun s => cosh (μ * s)) (sinh (μ * t) * μ) t :=
    (hasDerivAt_cosh (μ * t)).comp t (by simpa using (hasDerivAt_id t).const_mul μ)
  have hsinh : HasDerivAt (fun s => sinh (μ * s)) (cosh (μ * t) * μ) t :=
    (hasDerivAt_sinh (μ * t)).comp t (by simpa using (hasDerivAt_id t).const_mul μ)
  have h := (hcosh.const_mul A).add (hsinh.const_mul B)
  convert h using 1
  ring

/-- 不安定モードの導関数の微分。 -/
theorem unstableMode_deriv_hasDerivAt (μ A B t : ℝ) :
    HasDerivAt (fun s => μ * (A * sinh (μ * s) + B * cosh (μ * s)))
      (μ ^ 2 * (A * cosh (μ * t) + B * sinh (μ * t))) t := by
  have hcosh : HasDerivAt (fun s => cosh (μ * s)) (sinh (μ * t) * μ) t :=
    (hasDerivAt_cosh (μ * t)).comp t (by simpa using (hasDerivAt_id t).const_mul μ)
  have hsinh : HasDerivAt (fun s => sinh (μ * s)) (cosh (μ * t) * μ) t :=
    (hasDerivAt_sinh (μ * t)).comp t (by simpa using (hasDerivAt_id t).const_mul μ)
  have h := ((hsinh.const_mul A).add (hcosh.const_mul B)).const_mul μ
  convert h using 1 <;> ring

/-- 不安定モードは ψ'' = +μ²ψ を満たす。 -/
theorem unstableMode_secondDeriv (μ A B t : ℝ) :
    deriv (deriv (fun s => A * cosh (μ * s) + B * sinh (μ * s))) t
      = μ ^ 2 * (A * cosh (μ * t) + B * sinh (μ * t)) := by
  have hderiv : deriv (fun s => A * cosh (μ * s) + B * sinh (μ * s))
      = fun s => μ * (A * sinh (μ * s) + B * cosh (μ * s)) :=
    funext fun s => (unstableMode_hasDerivAt μ A B s).deriv
  rw [hderiv]
  exact (unstableMode_deriv_hasDerivAt μ A B t).deriv

/-- cosh モードは 1 を下回らない（初期値 1 から離れる一方）。 -/
theorem coshMode_ge_one (μ t : ℝ) : 1 ≤ cosh (μ * t) := one_le_cosh _

end CFT.ModeEvolution
