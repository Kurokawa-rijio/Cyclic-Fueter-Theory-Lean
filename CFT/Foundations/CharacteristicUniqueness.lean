/-
  命題集 `LEAN_GAP_TREES.md` 4-7(一意性)の組み立て 第 1 段:半線形の特性初期値問題の一意性(2026-11-18)

  未知関数の差 δ_i(i = 1..n)が、2 つのヌル面(u = 0 と v = 0)の上で 0 で、
  混合微分が値と 1 階微分でリプシッツ的に抑えられる
    |∂_u∂_v δ_i| ≤ L Σ_j (|δ_j| + |∂_u δ_j| + |∂_v δ_j|)
  なら、長方形 [0,a]×[0,b] の上で δ_i ≡ 0。くさびの 2 つの解の差がこの形をみたすことは
  第 2 段(係数の有界性、`WedgeDifferenceSystem` の解析版)で示す。

  偏微分は `CFT.Wedge` の Du、Dv、Duv(スライスの `deriv`)。正則性の仮定:
  * 各点で v 方向に微分可能(微分は Dv)。
  * t ↦ Dv δ(t, v) が u 方向に微分可能で微分が Duv(Duv の定義そのもの)。
  * s ↦ Du δ(u, s) が v 方向に微分可能で微分が Duv(混合偏微分の可換性。C² なら成り立つ。4-5 の解析版と同じ仮定)。
  * δ、Du δ、Dv δ、Duv δ が連続。

  * `abs_le_integral_abs`:g(0) = 0 なら |g(v)| ≤ ∫_0^v |g′|(微積分学の基本定理)。
  * `char_uniqueness`:主定理。f = Σ_j (|δ_j| + |∂_u δ_j| + |∂_v δ_j|) が
    f ≤ n(1+L)(∫_0^v f + ∫_0^u f) をみたすことを示し、`CharacteristicGronwall.char_gronwall` に入れる。
-/
import CFT.Foundations.CharacteristicGronwall
import CFT.Spherical.WedgeEYMSystem

open Real Set CFT.Wedge

namespace CFT.CharUniqueness

/-- g(0) = 0 なら |g(v)| ≤ ∫_0^v |g′| -/
theorem abs_le_integral_abs {g g' : ℝ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : g 0 = 0)
    (hd : ∀ s ∈ Icc (0:ℝ) v, HasDerivAt g (g' s) s) (hc : Continuous g') :
    |g v| ≤ ∫ s in (0:ℝ)..v, |g' s| := by
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by rwa [uIcc_of_le hv] at hs)) (hc.intervalIntegrable 0 v)
  rw [h0, sub_zero] at e
  rw [← e]
  exact intervalIntegral.abs_integral_le_integral_abs hv

theorem slice1 {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (x : ℝ) :
    Continuous (fun s => F x s) :=
  hF.comp (continuous_const.prod_mk continuous_id)

theorem slice2 {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (y : ℝ) :
    Continuous (fun t => F t y) :=
  hF.comp (continuous_id.prod_mk continuous_const)

/-- 半線形の特性初期値問題の一意性 -/
theorem char_uniqueness {n : ℕ} {a b L : ℝ} (hL : 0 ≤ L) (d : Fin n → ℝ → ℝ → ℝ)
    (hu0 : ∀ i u, d i u 0 = 0) (hv0 : ∀ i v, d i 0 v = 0)
    (hcd : ∀ i, Continuous (Function.uncurry (d i)))
    (hcu : ∀ i, Continuous (Function.uncurry (Du (d i))))
    (hcv : ∀ i, Continuous (Function.uncurry (Dv (d i))))
    (hcuv : ∀ i, Continuous (Function.uncurry (Duv (d i))))
    (hdv : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      HasDerivAt (fun s => d i u s) (Dv (d i) u v) v)
    (hduv_u : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      HasDerivAt (fun t => Dv (d i) t v) (Duv (d i) u v) u)
    (hduv_v : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      HasDerivAt (fun s => Du (d i) u s) (Duv (d i) u v) v)
    (hlip : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      |Duv (d i) u v| ≤ L * ∑ j, (|d j u v| + |Du (d j) u v| + |Dv (d j) u v|)) :
    ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, d i u v = 0 := by
  -- ヌル面上で 1 階微分も 0
  have hDu0 : ∀ i u, Du (d i) u 0 = 0 := fun i u => by simp [Du, hu0]
  have hDv0 : ∀ i v, Dv (d i) 0 v = 0 := fun i v => by simp [Dv, hv0]
  let A : Fin n → ℝ → ℝ → ℝ := fun j u v => |d j u v| + |Du (d j) u v| + |Dv (d j) u v|
  let f : ℝ → ℝ → ℝ := fun u v => ∑ j, A j u v
  have hA : ∀ j, Continuous (Function.uncurry (A j)) := fun j =>
    ((hcd j).abs.add (hcu j).abs).add (hcv j).abs
  have hf : Continuous (Function.uncurry f) := by
    have : Function.uncurry f = fun p => ∑ j, Function.uncurry (A j) p := rfl
    rw [this]
    exact continuous_finset_sum _ (fun j _ => hA j)
  have hAnn : ∀ j u v, 0 ≤ A j u v := fun j u v => by
    show 0 ≤ |d j u v| + |Du (d j) u v| + |Dv (d j) u v|
    positivity
  have hfnn : ∀ u v, 0 ≤ f u v := fun u v => Finset.sum_nonneg (fun j _ => hAnn j u v)
  have hAf : ∀ j u v, A j u v ≤ f u v := fun j u v =>
    Finset.single_le_sum (fun k _ => hAnn k u v) (Finset.mem_univ j)
  have hK : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      f u v ≤ (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
    intro u hu v hv
    have I1nn : 0 ≤ ∫ s in (0:ℝ)..v, f u s :=
      intervalIntegral.integral_nonneg hv.1 (fun s _ => hfnn u s)
    have I2nn : 0 ≤ ∫ t in (0:ℝ)..u, f t v :=
      intervalIntegral.integral_nonneg hu.1 (fun t _ => hfnn t v)
    have hfs : Continuous (fun s => f u s) := slice1 hf u
    have hft : Continuous (fun t => f t v) := slice2 hf v
    have hj : ∀ j, A j u v ≤ (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
      intro j
      have hsv : ∀ s ∈ Icc (0:ℝ) v, s ∈ Icc (0:ℝ) b := fun s hs => ⟨hs.1, hs.2.trans hv.2⟩
      have htu : ∀ t ∈ Icc (0:ℝ) u, t ∈ Icc (0:ℝ) a := fun t ht => ⟨ht.1, ht.2.trans hu.2⟩
      -- |δ_j| ≤ ∫_0^v |∂_v δ_j| ≤ ∫_0^v f
      have b1 : |d j u v| ≤ ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_integral_abs hv.1 (hu0 j u) (fun s hs => hdv j u hu s (hsv s hs))
          (slice1 (hcv j) u)).trans ?_
        exact intervalIntegral.integral_mono_on hv.1 ((slice1 (hcv j) u).abs.intervalIntegrable _ _)
          (hfs.intervalIntegrable _ _)
          (fun s _ => by
            have h1 : |Dv (d j) u s| ≤ A j u s := by
              show |Dv (d j) u s| ≤ |d j u s| + |Du (d j) u s| + |Dv (d j) u s|
              have := abs_nonneg (d j u s); have := abs_nonneg (Du (d j) u s); linarith
            exact h1.trans (hAf j u s))
      -- |∂_u δ_j| ≤ ∫_0^v |∂_u∂_v δ_j| ≤ L ∫_0^v f
      have b2 : |Du (d j) u v| ≤ L * ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_integral_abs hv.1 (hDu0 j u) (fun s hs => hduv_v j u hu s (hsv s hs))
          (slice1 (hcuv j) u)).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hv.1
          ((slice1 (hcuv j) u).abs.intervalIntegrable _ _)
          ((continuous_const.mul hfs).intervalIntegrable _ _)
          (fun s hs => hlip j u hu s (hsv s hs))
      -- |∂_v δ_j| ≤ ∫_0^u |∂_u∂_v δ_j| ≤ L ∫_0^u f
      have b3 : |Dv (d j) u v| ≤ L * ∫ t in (0:ℝ)..u, f t v := by
        refine (abs_le_integral_abs hu.1 (hDv0 j v) (fun t ht => hduv_u j t (htu t ht) v hv)
          (slice2 (hcuv j) v)).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hu.1
          ((slice2 (hcuv j) v).abs.intervalIntegrable _ _)
          ((continuous_const.mul hft).intervalIntegrable _ _)
          (fun t ht => hlip j t (htu t ht) v hv)
      show |d j u v| + |Du (d j) u v| + |Dv (d j) u v|
        ≤ (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)
      nlinarith [mul_nonneg hL I1nn, mul_nonneg hL I2nn]
    calc f u v = ∑ j, A j u v := rfl
      _ ≤ ∑ _j : Fin n, (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) :=
          Finset.sum_le_sum (fun j _ => hj j)
      _ = (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hzero := CFT.CharGronwall.char_gronwall hf (fun u _ v _ => hfnn u v) hK
  intro i u hu v hv
  have h0 : f u v = 0 := hzero u hu v hv
  have hAi : A i u v = 0 := le_antisymm (h0 ▸ hAf i u v) (hAnn i u v)
  have : |d i u v| + |Du (d i) u v| + |Dv (d i) u v| = 0 := hAi
  have h1 := abs_nonneg (Du (d i) u v)
  have h2 := abs_nonneg (Dv (d i) u v)
  exact abs_eq_zero.mp (by linarith [abs_nonneg (d i u v)])

end CFT.CharUniqueness
