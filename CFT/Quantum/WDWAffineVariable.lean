import Mathlib
import CFT.Quantum.WDWSymmetry

/-!
  命題集 `LEAN_GAP_TREES.md` 5-1（作用素の対称性）の残り：a 変数から
  アフィン変数への変数変換。

  WDW 作用素の a-部分は重み 1/a の内積 ⟨f, g⟩ = ∫ f̄ g (da/a) に関して
  対称であることが `WDWSymmetry`・`WDWComplexSymmetry` で証明済み。
  一方アフィン量子化（`AffineQuantizationInnerProduct.lean`）の物理的内積は
  ⟨f, g⟩ = ∫₀^∞ f̄ g dk（k = K − K₀）という平坦な dk 内積である。
  このモジュールは両者をつなぐ変数変換 k = log a を形式化する：

  * 置換公式（`log_integral_subst`・`log_integral_subst_complex`）：
    ∫_{log A}^{log B} F(e^k) dk = ∫_A^B F(a) (da/a)。
    すなわち a = K − K₀ と同一視すれば、WDW の重み付き内積はまさに
    アフィン量子化の L²((0, ∞), dk) 内積になる
    （`weighted_inner_subst`・`weighted_inner_subst_complex`）。
  * 連鎖律（`hasDerivAt_comp_exp`・`hasDerivAt_comp_exp_complex`・
    `hasDerivAt_comp_exp_second`）：∂_k = a ∂_a、
    ∂_k² ψ̃ = a² ψ'' + a ψ'。ただし ψ̃(k) = ψ(e^k)。
  * 作用素の表示（`wdwAPart_affine`）：a ∂_a² = (∂_k² − ∂_k)/a により、
    WDW a-部分は k 変数で
    Ĥ_a = (1/4c)(−ħ²(∂_k² − ∂_k)/a) − c a (b² − ℓ²)
    と書ける。1 階の項 −∂_k が残るのは、混合項と同様に順序づけの
    問題がここにも現れることの反映である。

  残り（5-1）：具体的なテスト関数による非対称性の Lean 証明
  （多項式テスト関数による評価）。
-/

namespace CFT.WDWAffine

open MeasureTheory intervalIntegral
open scoped Interval

/-- アフィン変数 k = log a への置換（実関数版）。
  ∫_{log A}^{log B} F(e^k) dk = ∫_A^B F(a) (da/a)。 -/
theorem log_integral_subst {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (F : ℝ → ℝ)
    (hF : ContinuousOn F [[A, B]]) :
    ∫ x in Real.log A..Real.log B, F (Real.exp x) = ∫ x in A..B, F x / x := by
  have hlog : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
  have himg : Real.exp '' [[Real.log A, Real.log B]] ⊆ [[A, B]] := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Set.uIcc_of_le hlog, Set.mem_Icc] at hx
    rw [Set.uIcc_of_le hAB, Set.mem_Icc]
    constructor
    · rw [← Real.exp_log hA]; exact Real.exp_le_exp.mpr hx.1
    · rw [← Real.exp_log (lt_of_lt_of_le hA hAB)]; exact Real.exp_le_exp.mpr hx.2
  have hne : ∀ x ∈ [[A, B]], (x : ℝ) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hAB, Set.mem_Icc] at hx
    exact (lt_of_lt_of_le hA hx.1).ne'
  have hg' : ContinuousOn (fun x => F x / x) (Real.exp '' [[Real.log A, Real.log B]]) :=
    (hF.div continuousOn_id hne).mono himg
  have hexp : ∀ x ∈ [[Real.log A, Real.log B]], HasDerivAt Real.exp (Real.exp x) x :=
    fun x _ => Real.hasDerivAt_exp x
  have hcont : ContinuousOn Real.exp [[Real.log A, Real.log B]] :=
    Real.continuous_exp.continuousOn
  have key := integral_comp_mul_deriv' (f := Real.exp) (f' := Real.exp)
    (g := fun x => F x / x) hexp hcont hg'
  rw [Real.exp_log hA, Real.exp_log (lt_of_lt_of_le hA hAB)] at key
  rw [← key]
  apply integral_congr
  intro x _
  simp only [Function.comp_apply]
  rw [div_mul_cancel₀ _ (Real.exp_ne_zero x)]

/-- アフィン変数への置換（複素関数版）。 -/
theorem log_integral_subst_complex {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (F : ℝ → ℂ)
    (hF : ContinuousOn F [[A, B]]) :
    ∫ x in Real.log A..Real.log B, F (Real.exp x) = ∫ x in A..B, F x / x := by
  have hlog : Real.log A ≤ Real.log B := Real.log_le_log hA hAB
  have himg : Real.exp '' [[Real.log A, Real.log B]] ⊆ [[A, B]] := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Set.uIcc_of_le hlog, Set.mem_Icc] at hx
    rw [Set.uIcc_of_le hAB, Set.mem_Icc]
    constructor
    · rw [← Real.exp_log hA]; exact Real.exp_le_exp.mpr hx.1
    · rw [← Real.exp_log (lt_of_lt_of_le hA hAB)]; exact Real.exp_le_exp.mpr hx.2
  have hne : ∀ x ∈ [[A, B]], ((x : ℂ)) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hAB, Set.mem_Icc] at hx
    exact_mod_cast (lt_of_lt_of_le hA hx.1).ne'
  have hg' : ContinuousOn (fun x => F x / x) (Real.exp '' [[Real.log A, Real.log B]]) :=
    (hF.div Complex.continuous_ofReal.continuousOn hne).mono himg
  have hexp : ∀ x ∈ [[Real.log A, Real.log B]], HasDerivAt Real.exp (Real.exp x) x :=
    fun x _ => Real.hasDerivAt_exp x
  have hcont : ContinuousOn Real.exp [[Real.log A, Real.log B]] :=
    Real.continuous_exp.continuousOn
  have key := integral_comp_smul_deriv' (f := Real.exp) (f' := Real.exp)
    (g := fun x => F x / x) hexp hcont hg'
  rw [Real.exp_log hA, Real.exp_log (lt_of_lt_of_le hA hAB)] at key
  rw [← key]
  apply integral_congr
  intro x _
  simp only [Function.comp_apply, Complex.real_smul]
  rw [mul_div_cancel₀ _ (by exact_mod_cast Real.exp_ne_zero x)]

/-- 【5-1】重み 1/a の内積はアフィン変数では平坦な dk 内積になる（実関数版）。 -/
theorem weighted_inner_subst {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {f g : ℝ → ℝ} (hf : ContinuousOn f [[A, B]]) (hg : ContinuousOn g [[A, B]]) :
    ∫ x in Real.log A..Real.log B, f (Real.exp x) * g (Real.exp x)
      = ∫ x in A..B, f x * g x / x :=
  log_integral_subst hA hAB (fun x => f x * g x) (hf.mul hg)

/-- 【5-1】重み 1/a の内積はアフィン変数では平坦な dk 内積になる（複素版）。
  a = K − K₀ と同一視すれば、これはまさにアフィン量子化の内積
  ⟨f, g⟩ = ∫ f̄ g dk である。 -/
theorem weighted_inner_subst_complex {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {f g : ℝ → ℂ} (hf : ContinuousOn f [[A, B]]) (hg : ContinuousOn g [[A, B]]) :
    ∫ x in Real.log A..Real.log B, star (f (Real.exp x)) * g (Real.exp x)
      = ∫ x in A..B, star (f x) * g x / x :=
  log_integral_subst_complex hA hAB (fun x => star (f x) * g x) (hf.star.mul hg)

/-- 【5-1】連鎖律：∂_k = a ∂_a（実関数版）。ψ̃(k) = ψ(e^k) の微分は a ψ'(a)。 -/
theorem hasDerivAt_comp_exp {ψ ψ' : ℝ → ℝ} {k : ℝ}
    (hψ : HasDerivAt ψ (ψ' (Real.exp k)) (Real.exp k)) :
    HasDerivAt (fun k => ψ (Real.exp k)) (Real.exp k * ψ' (Real.exp k)) k := by
  have h : HasDerivAt (ψ ∘ Real.exp) (Real.exp k * ψ' (Real.exp k)) k :=
    HasDerivAt.scomp k hψ (Real.hasDerivAt_exp k)
  exact h

/-- 【5-1】連鎖律：∂_k = a ∂_a（複素関数版）。 -/
theorem hasDerivAt_comp_exp_complex {ψ : ℝ → ℂ} {ψ' : ℂ} {k : ℝ}
    (hψ : HasDerivAt ψ ψ' (Real.exp k)) :
    HasDerivAt (fun k => ψ (Real.exp k)) ((Real.exp k : ℂ) * ψ') k := by
  have h : HasDerivAt (ψ ∘ Real.exp) ((Real.exp k : ℂ) * ψ') k :=
    HasDerivAt.scomp k hψ (Real.hasDerivAt_exp k)
  exact h

/-- 【5-1】2 階の連鎖律：∂_k² ψ̃ = a² ψ'' + a ψ'（実関数版）。 -/
theorem hasDerivAt_comp_exp_second {ψ' ψ'' : ℝ → ℝ} {k : ℝ}
    (hψ' : ∀ x, HasDerivAt ψ' (ψ'' x) x) :
    HasDerivAt (fun k => Real.exp k * ψ' (Real.exp k))
      (Real.exp k * ψ' (Real.exp k) + Real.exp k ^ 2 * ψ'' (Real.exp k)) k := by
  have h1 : HasDerivAt (fun k => ψ' (Real.exp k)) (Real.exp k * ψ'' (Real.exp k)) k := by
    have h : HasDerivAt (ψ' ∘ Real.exp) (Real.exp k * ψ'' (Real.exp k)) k :=
      HasDerivAt.scomp k (hψ' (Real.exp k)) (Real.hasDerivAt_exp k)
    exact h
  have h2 : HasDerivAt (fun k => Real.exp k * ψ' (Real.exp k))
      (Real.exp k * ψ' (Real.exp k) + Real.exp k * (Real.exp k * ψ'' (Real.exp k))) k :=
    (Real.hasDerivAt_exp k).mul h1
  have e : Real.exp k * ψ' (Real.exp k) + Real.exp k * (Real.exp k * ψ'' (Real.exp k))
      = Real.exp k * ψ' (Real.exp k) + Real.exp k ^ 2 * ψ'' (Real.exp k) := by ring
  rw [e] at h2
  exact h2

/-- 【5-1】WDW a-部分作用素のアフィン変数表示：a ∂_a² = (∂_k² − ∂_k)/a。
  すなわち Ĥ_a = (1/4c)(−ħ²(∂_k² − ∂_k)/a) − c a (b² − ℓ²)。 -/
theorem wdwAPart_affine (c l hb b k : ℝ) (Ψ Ψ' Ψ'' : ℝ) :
    CFT.WDWSymm.wdwAPart c l hb b (Real.exp k) Ψ Ψ''
      = (1 / (4 * c)) * (-hb ^ 2 * ((Real.exp k ^ 2 * Ψ'' + Real.exp k * Ψ')
          - Real.exp k * Ψ') / Real.exp k)
        - c * Real.exp k * (b ^ 2 - l ^ 2) * Ψ := by
  have hne : Real.exp k ≠ 0 := Real.exp_ne_zero k
  have key : (Real.exp k ^ 2 * Ψ'' + Real.exp k * Ψ') - Real.exp k * Ψ'
      = Real.exp k ^ 2 * Ψ'' := by ring
  have e2 : Real.exp k ^ 2 * Ψ'' / Real.exp k = Real.exp k * Ψ'' := by
    rw [pow_two, mul_assoc]
    exact mul_div_cancel_left₀ _ hne
  rw [key, mul_div_assoc, e2]
  simp only [CFT.WDWSymm.wdwAPart]
  ring

end CFT.WDWAffine
