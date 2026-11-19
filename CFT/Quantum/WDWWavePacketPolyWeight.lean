/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  一般の重み g への拡張（第十七段）。

  第十六段では、反対称部分が w_anti(C) = (C − m)·u(C)（u は連続・非負で、区間内の
  どこかで正）と書ける重みでは、小さな θ > 0 でサイン積分が正になり、位相つき波束は
  0 にならないことを示した。残っていたのは「単調な重みからこの因数分解を導くこと」
  （差商の連続性）である。ここではその一段として、多項式重み w(C) = C^k に対する
  因数分解を証明する：等比数列の和の恒等式により
  antiPart (C ↦ C^k) = (C − m) · Σ_{i<k} C^i (C₁+C₂−C)^{k−1−i} と書け、
  因子は C の多項式関数として連続である。二次重みでは因子は定数 C₁+C₂
  （すなわち u = 2m）、三次重みでは因子は (C−m)² + 3m² で、m > 0 の範囲では
  第十六段の仮定（u ≥ 0、区間内で正）を満たす。したがって二次・三次の重みでも
  小さな T₀ で波束は 0 にならない（具体例 c = ℓ = 1、C ∈ [9, 10] を含む）。
  一般の C¹ 重みに対する差商の連続性による因数分解は次の段に残る。

  残り：単調な一般の重みからの因数分解の導出（差商の連続性）、およびサイン積分の
  零点の具体的な構造（大きな θ での符号変化、零点の列挙など）。
-/
import CFT.Quantum.WDWWavePacketSineZero

namespace CFT.WDWWavePacketPolyWeight

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketDecayExplicit CFT.WDWWavePacketSymmW CFT.WDWWavePacketAsymW
  CFT.WDWWavePacketSineZero
  MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 単項式重み C ↦ C^k の反対称部分は (C − m) と有限和の積に因数分解できる
    （等比数列の和の恒等式 `geom_sum₂_mul` による）。-/
theorem antiPart_pow_eq (k : ℕ) (C₁ C₂ C : ℝ) :
    antiPart (fun C => C ^ k) C₁ C₂ C
      = (C - (C₁ + C₂) / 2) *
        ∑ i ∈ Finset.range k, C ^ i * (C₁ + C₂ - C) ^ (k - 1 - i) := by
  have h := geom_sum₂_mul C (C₁ + C₂ - C) k
  have hC : C - (C₁ + C₂ - C) = 2 * (C - (C₁ + C₂) / 2) := by ring
  rw [hC] at h
  unfold antiPart
  show (C ^ k - (C₁ + C₂ - C) ^ k) / 2
      = (C - (C₁ + C₂) / 2) *
        ∑ i ∈ Finset.range k, C ^ i * (C₁ + C₂ - C) ^ (k - 1 - i)
  rw [← h]
  ring

/-- 因数分解の因子は C の連続関数である（有限和の各項は冪の積）。-/
theorem antiPart_pow_factor_continuousOn (k : ℕ) (C₁ C₂ : ℝ) :
    ContinuousOn
      (fun C => ∑ i ∈ Finset.range k, C ^ i * (C₁ + C₂ - C) ^ (k - 1 - i))
      (Set.uIcc C₁ C₂) := by
  apply (continuous_finset_sum _ (fun i _ => by fun_prop)).continuousOn

/-- 二次重み w(C) = C² の反対称部分は (C − m)·(C₁ + C₂)（すなわち u = 2m）。-/
theorem antiPart_sq_eq (C₁ C₂ C : ℝ) :
    antiPart (fun C => C ^ 2) C₁ C₂ C = (C - (C₁ + C₂) / 2) * (C₁ + C₂) := by
  unfold antiPart
  show (C ^ 2 - (C₁ + C₂ - C) ^ 2) / 2 = (C - (C₁ + C₂) / 2) * (C₁ + C₂)
  ring

/-- 三次重み w(C) = C³ の反対称部分は (C − m)·((C − m)² + 3m²)。-/
theorem antiPart_cube_eq (C₁ C₂ C : ℝ) :
    antiPart (fun C => C ^ 3) C₁ C₂ C
      = (C - (C₁ + C₂) / 2) *
        ((C - (C₁ + C₂) / 2) ^ 2 + 3 * ((C₁ + C₂) / 2) ^ 2) := by
  unfold antiPart
  show (C ^ 3 - (C₁ + C₂ - C) ^ 3) / 2
      = (C - (C₁ + C₂) / 2) *
        ((C - (C₁ + C₂) / 2) ^ 2 + 3 * ((C₁ + C₂) / 2) ^ 2)
  ring

/-- 二次重みでは、m = (C₁+C₂)/2 > 0 なら小さな θ > 0 でサイン積分は正である。-/
theorem integral_sin_sq_pos {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (hC₁ : 0 < C₁) :
    0 < ∫ C in C₁..C₂, antiPart (fun C => C ^ 2) C₁ C₂ C
      * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  apply integral_sin_antiPart_pos hlt hθ0 hθ (fun C => C ^ 2) (continuous_pow 2).continuousOn
    (u := fun _ => C₁ + C₂) (hu_cont := continuousOn_const)
    (hu_nonneg := fun _ => by show (0 : ℝ) ≤ C₁ + C₂; linarith)
    (hfact := fun C => antiPart_sq_eq C₁ C₂ C)
    (c₀ := (C₁ + C₂) / 2) (hc₀ := ⟨by linarith, by linarith⟩)
    (hu0 := by show (0 : ℝ) < C₁ + C₂; linarith)

/-- 三次重みでは、m = (C₁+C₂)/2 > 0 なら小さな θ > 0 でサイン積分は正である。-/
theorem integral_sin_cube_pos {C₁ C₂ θ : ℝ} (hlt : C₁ < C₂) (hθ0 : 0 < θ)
    (hθ : θ < 2 * Real.pi / (C₂ - C₁)) (hC₁ : 0 < C₁) :
    0 < ∫ C in C₁..C₂, antiPart (fun C => C ^ 3) C₁ C₂ C
      * Real.sin ((C - (C₁ + C₂) / 2) * θ) := by
  apply integral_sin_antiPart_pos hlt hθ0 hθ (fun C => C ^ 3) (continuous_pow 3).continuousOn
    (u := fun C => (C - (C₁ + C₂) / 2) ^ 2 + 3 * ((C₁ + C₂) / 2) ^ 2)
    (hu_cont := by fun_prop)
    (hu_nonneg := fun C => by
      show (0 : ℝ) ≤ (C - (C₁ + C₂) / 2) ^ 2 + 3 * ((C₁ + C₂) / 2) ^ 2
      positivity)
    (hfact := fun C => antiPart_cube_eq C₁ C₂ C)
    (c₀ := (C₁ + C₂) / 2) (hc₀ := ⟨by linarith, by linarith⟩)
    (hu0 := by
      have hm : 0 < (C₁ + C₂) / 2 := by linarith
      have h0 : ((C₁ + C₂) / 2 - (C₁ + C₂) / 2) ^ 2 = 0 := by simp
      show (0 : ℝ) < ((C₁ + C₂) / 2 - (C₁ + C₂) / 2) ^ 2 + 3 * ((C₁ + C₂) / 2) ^ 2
      rw [h0, zero_add]
      exact mul_pos (by norm_num) (pow_pos hm 2))

/-- 具体例：c = ℓ = 1、C ∈ [9, 10]、二次重みでは、0 < T₀ < 2π の範囲で位相つき波束は
    0 にならない。-/
theorem packetPhase_ne_sq_example {T₀ : ℝ} (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi) :
    packetPhase 1 1 9 10 T₀ 1 (fun C => C ^ 2 * Real.sqrt (Q 1 1 C 1)) ≠ 0 := by
  refine packetPhase_ne_of_small_pos (c := 1) (l := 1) one_pos (by norm_num) (by norm_num)
    one_pos (w := fun C => C ^ 2) (hw_cont := (continuous_pow 2).continuousOn)
    (g := fun C => C ^ 2 * Real.sqrt (Q 1 1 C 1)) (hg := fun C _ => rfl)
    (u := fun _ => (9 + 10 : ℝ)) (hu_cont := continuousOn_const)
    (hu_nonneg := fun _ => by show (0 : ℝ) ≤ (9 + 10 : ℝ); norm_num)
    (hfact := fun C => antiPart_sq_eq 9 10 C)
    (c₀ := (9 + 10 : ℝ) / 2) (hc₀ := ⟨by norm_num, by norm_num⟩)
    (hu0 := by show (0 : ℝ) < (9 + 10 : ℝ); norm_num)
    hT0 ?_
  have heq : (2 : ℝ) * Real.pi * (1 : ℝ) / ((10 : ℝ) - 9) = 2 * Real.pi := by
    rw [show ((10 : ℝ) - 9) = 1 by norm_num, div_one, mul_one]
  rw [heq]
  exact hT

/-- 具体例：c = ℓ = 1、C ∈ [9, 10]、三次重みでは、0 < T₀ < 2π の範囲で位相つき波束は
    0 にならない。-/
theorem packetPhase_ne_cube_example {T₀ : ℝ} (hT0 : 0 < T₀) (hT : T₀ < 2 * Real.pi) :
    packetPhase 1 1 9 10 T₀ 1 (fun C => C ^ 3 * Real.sqrt (Q 1 1 C 1)) ≠ 0 := by
  refine packetPhase_ne_of_small_pos (c := 1) (l := 1) one_pos (by norm_num) (by norm_num)
    one_pos (w := fun C => C ^ 3) (hw_cont := (continuous_pow 3).continuousOn)
    (g := fun C => C ^ 3 * Real.sqrt (Q 1 1 C 1)) (hg := fun C _ => rfl)
    (u := fun C => (C - (9 + 10 : ℝ) / 2) ^ 2 + 3 * ((9 + 10 : ℝ) / 2) ^ 2)
    (hu_cont := by fun_prop)
    (hu_nonneg := fun C => by
      show (0 : ℝ) ≤ (C - (9 + 10 : ℝ) / 2) ^ 2 + 3 * ((9 + 10 : ℝ) / 2) ^ 2
      positivity)
    (hfact := fun C => antiPart_cube_eq 9 10 C)
    (c₀ := (9 + 10 : ℝ) / 2) (hc₀ := ⟨by norm_num, by norm_num⟩)
    (hu0 := by
      show (0 : ℝ) < ((9 + 10 : ℝ) / 2 - (9 + 10 : ℝ) / 2) ^ 2 + 3 * ((9 + 10 : ℝ) / 2) ^ 2
      rw [show ((9 + 10 : ℝ) / 2 - (9 + 10 : ℝ) / 2) ^ 2 = 0 by simp, zero_add]
      norm_num)
    hT0 ?_
  have heq : (2 : ℝ) * Real.pi * (1 : ℝ) / ((10 : ℝ) - 9) = 2 * Real.pi := by
    rw [show ((10 : ℝ) - 9) = 1 by norm_num, div_one, mul_one]
  rw [heq]
  exact hT

end

end CFT.WDWWavePacketPolyWeight
