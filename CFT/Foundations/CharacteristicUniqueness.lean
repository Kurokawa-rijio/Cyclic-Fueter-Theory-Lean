/-
  命題集 `LEAN_GAP_TREES.md` 4-7(一意性)の組み立て 第 1 段:半線形の特性初期値問題の一意性(2026-11-18)

  長方形 R = [0,a]×[0,b] の上の未知関数 δ_i(i = 1..n)が、2 つのヌル面の辺(u = 0 と v = 0)の上で 0 で、
  混合微分が値と 1 階微分でリプシッツ的に抑えられる
    |∂_u∂_v δ_i| ≤ L Σ_j (|δ_j| + |∂_u δ_j| + |∂_v δ_j|)
  なら、R の上で δ_i ≡ 0。

  方程式とデータの仮定は R の上だけで置く(R の外で方程式は課さない)。ただし下の `C2Data` は R の辺の点でも
  両側の HasDerivAt を仮定するので、辺の点での微分を通して R のすぐ外の値には依存する。
  * `C2Data a b d du dv duv`:R の上での「混合 C² 級」。d、du、dv、duv は R 上で連続、R の各点で
    ∂_u d = du、∂_v d = dv、∂_u dv = duv、∂_v du = duv(混合偏微分の可換性を含む)。
    ∂_u² d、∂_v² d の存在は含まない(通常の C² より弱い。方程式に出るのは ∂_u∂_v だけなので、この弱い形で足りる)。
    微分は関数そのものとして渡す(`deriv` で書かない)ので、差 d − d′ の微分は du − du′ になるだけで済む。
    R の辺の点でも HasDerivAt を仮定するので、解は R より少し広い範囲で C¹ に延びているとしている。
  * `abs_le_integral_abs`:g(0) = 0 なら |g(v)| ≤ ∫_0^v |g′|(微積分学の基本定理)。
  * `edge_deriv_zero`:辺の上で 0 の関数は、辺の方向の微分も辺の上で 0(区間の上での微分の一意性)。
  * `char_uniqueness`:主定理。a、b > 0 のときは f = Σ_j (|δ_j| + |∂_u δ_j| + |∂_v δ_j|) が
    f ≤ n(1+L)(∫_0^v f + ∫_0^u f) をみたすことを示して `CharacteristicGronwall.char_gronwall_on` に入れる。
    a ≤ 0 または b ≤ 0 なら R は辺に含まれ、データから直接従う。
-/
import CFT.Foundations.CharacteristicGronwall

open Real Set

namespace CFT.CharUniqueness

/-- 長方形 [0,a]×[0,b] の上での混合 C² 級(値・∂_u・∂_v・∂_u∂_v が連続。∂_u²、∂_v² は含まない。
微分は関数として渡す) -/
structure C2Data (a b : ℝ) (d du dv duv : ℝ → ℝ → ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry d) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  cont_u : ContinuousOn (Function.uncurry du) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  cont_v : ContinuousOn (Function.uncurry dv) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  cont_uv : ContinuousOn (Function.uncurry duv) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)
  deriv_u : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun t => d t v) (du u v) u
  deriv_v : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun s => d u s) (dv u v) v
  deriv_uv_u : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun t => dv t v) (duv u v) u
  deriv_uv_v : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, HasDerivAt (fun s => du u s) (duv u v) v

/-- 2 つの C² 関数の差も C²(微分は微分の差) -/
theorem C2Data.sub {a b : ℝ} {d du dv duv d' du' dv' duv' : ℝ → ℝ → ℝ}
    (h : C2Data a b d du dv duv) (h' : C2Data a b d' du' dv' duv') :
    C2Data a b (fun s t => d s t - d' s t) (fun s t => du s t - du' s t)
      (fun s t => dv s t - dv' s t) (fun s t => duv s t - duv' s t) where
  cont := h.cont.sub h'.cont
  cont_u := h.cont_u.sub h'.cont_u
  cont_v := h.cont_v.sub h'.cont_v
  cont_uv := h.cont_uv.sub h'.cont_uv
  deriv_u := fun u hu v hv => (h.deriv_u u hu v hv).sub (h'.deriv_u u hu v hv)
  deriv_v := fun u hu v hv => (h.deriv_v u hu v hv).sub (h'.deriv_v u hu v hv)
  deriv_uv_u := fun u hu v hv => (h.deriv_uv_u u hu v hv).sub (h'.deriv_uv_u u hu v hv)
  deriv_uv_v := fun u hu v hv => (h.deriv_uv_v u hu v hv).sub (h'.deriv_uv_v u hu v hv)

/-- g(0) = 0 なら |g(v)| ≤ ∫_0^v |g′| -/
theorem abs_le_integral_abs {g g' : ℝ → ℝ} {v : ℝ} (hv : 0 ≤ v) (h0 : g 0 = 0)
    (hd : ∀ s ∈ Icc (0:ℝ) v, HasDerivAt g (g' s) s) (hc : ContinuousOn g' (Icc (0:ℝ) v)) :
    |g v| ≤ ∫ s in (0:ℝ)..v, |g' s| := by
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by rwa [uIcc_of_le hv] at hs)) (hc.intervalIntegrable_of_Icc hv)
  rw [h0, sub_zero] at e
  rw [← e]
  exact intervalIntegral.abs_integral_le_integral_abs hv

theorem sliceOn1 {F : ℝ → ℝ → ℝ} {a b x : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)) (hx : x ∈ Icc (0:ℝ) a) :
    ContinuousOn (fun s => F x s) (Icc (0:ℝ) b) :=
  hF.comp (continuousOn_const.prod continuousOn_id) (fun _ hs => Set.mk_mem_prod hx hs)

theorem sliceOn2 {F : ℝ → ℝ → ℝ} {a b y : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b)) (hy : y ∈ Icc (0:ℝ) b) :
    ContinuousOn (fun t => F t y) (Icc (0:ℝ) a) :=
  hF.comp (continuousOn_id.prod continuousOn_const) (fun _ ht => Set.mk_mem_prod ht hy)

/-- 区間 [0,a](a > 0)の上で 0 の関数は、[0,a] の各点で(両側の)微分も 0 -/
theorem edge_deriv_zero {g : ℝ → ℝ} {g' a x : ℝ} (ha : 0 < a) (hx : x ∈ Icc (0:ℝ) a)
    (h0 : ∀ t ∈ Icc (0:ℝ) a, g t = 0) (hd : HasDerivAt g g' x) : g' = 0 := by
  have h2 : HasDerivWithinAt g 0 (Icc (0:ℝ) a) x :=
    (hasDerivWithinAt_const x (Icc (0:ℝ) a) (0:ℝ)).congr (fun t ht => h0 t ht) (h0 x hx)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc ha x hx) hd.hasDerivWithinAt h2

/-- 半線形の特性初期値問題の一意性(仮定は長方形の上だけ) -/
theorem char_uniqueness {n : ℕ} {a b L : ℝ} (hL : 0 ≤ L) (d du dv duv : Fin n → ℝ → ℝ → ℝ)
    (hC : ∀ i, C2Data a b (d i) (du i) (dv i) (duv i))
    (hu0 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, d i u 0 = 0) (hv0 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, d i 0 v = 0)
    (hlip : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      |duv i u v| ≤ L * ∑ j, (|d j u v| + |du j u v| + |dv j u v|)) :
    ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, d i u v = 0 := by
  -- 退化した長方形(辺に含まれる)はデータから直接
  rcases lt_or_le 0 a with ha | ha
  swap
  · intro i u hu v hv
    have : u = 0 := le_antisymm (hu.2.trans ha) hu.1
    subst this
    exact hv0 i v hv
  rcases lt_or_le 0 b with hb | hb
  swap
  · intro i u hu v hv
    have : v = 0 := le_antisymm (hv.2.trans hb) hv.1
    subst this
    exact hu0 i u hu
  have hb0 : (0:ℝ) ∈ Icc (0:ℝ) b := ⟨le_rfl, hb.le⟩
  have ha0 : (0:ℝ) ∈ Icc (0:ℝ) a := ⟨le_rfl, ha.le⟩
  -- 辺の上で 1 階微分も 0
  have hDu0 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, du i u 0 = 0 := fun i u hu =>
    edge_deriv_zero ha hu (hu0 i) ((hC i).deriv_u u hu 0 hb0)
  have hDv0 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, dv i 0 v = 0 := fun i v hv =>
    edge_deriv_zero hb hv (hv0 i) ((hC i).deriv_v 0 ha0 v hv)
  let A : Fin n → ℝ → ℝ → ℝ := fun j u v => |d j u v| + |du j u v| + |dv j u v|
  let f : ℝ → ℝ → ℝ := fun u v => ∑ j, A j u v
  have hA : ∀ j, ContinuousOn (Function.uncurry (A j)) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := fun j =>
    (((hC j).cont.abs).add ((hC j).cont_u.abs)).add ((hC j).cont_v.abs)
  have hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := by
    have : Function.uncurry f = fun p => ∑ j, Function.uncurry (A j) p := rfl
    rw [this]
    exact continuousOn_finset_sum _ (fun j _ => hA j)
  have hAnn : ∀ j u v, 0 ≤ A j u v := fun j u v => by
    show 0 ≤ |d j u v| + |du j u v| + |dv j u v|
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
    have subv : Icc (0:ℝ) v ⊆ Icc (0:ℝ) b := Icc_subset_Icc le_rfl hv.2
    have subu : Icc (0:ℝ) u ⊆ Icc (0:ℝ) a := Icc_subset_Icc le_rfl hu.2
    have hfs : ContinuousOn (fun s => f u s) (Icc (0:ℝ) v) := (sliceOn1 hf hu).mono subv
    have hft : ContinuousOn (fun t => f t v) (Icc (0:ℝ) u) := (sliceOn2 hf hv).mono subu
    have hj : ∀ j, A j u v ≤ (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
      intro j
      -- |δ_j| ≤ ∫_0^v |∂_v δ_j| ≤ ∫_0^v f
      have c1 : ContinuousOn (fun s => dv j u s) (Icc (0:ℝ) v) :=
        (sliceOn1 (hC j).cont_v hu).mono subv
      have b1 : |d j u v| ≤ ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_integral_abs hv.1 (hu0 j u hu)
          (fun s hs => (hC j).deriv_v u hu s (subv hs)) c1).trans ?_
        exact intervalIntegral.integral_mono_on hv.1 (c1.abs.intervalIntegrable_of_Icc hv.1)
          (hfs.intervalIntegrable_of_Icc hv.1)
          (fun s _ => by
            have h1 : |dv j u s| ≤ A j u s := by
              show |dv j u s| ≤ |d j u s| + |du j u s| + |dv j u s|
              have := abs_nonneg (d j u s); have := abs_nonneg (du j u s); linarith
            exact h1.trans (hAf j u s))
      -- |∂_u δ_j| ≤ ∫_0^v |∂_u∂_v δ_j| ≤ L ∫_0^v f
      have c2 : ContinuousOn (fun s => duv j u s) (Icc (0:ℝ) v) :=
        (sliceOn1 (hC j).cont_uv hu).mono subv
      have b2 : |du j u v| ≤ L * ∫ s in (0:ℝ)..v, f u s := by
        refine (abs_le_integral_abs hv.1 (hDu0 j u hu)
          (fun s hs => (hC j).deriv_uv_v u hu s (subv hs)) c2).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hv.1 (c2.abs.intervalIntegrable_of_Icc hv.1)
          ((continuousOn_const.mul hfs).intervalIntegrable_of_Icc hv.1)
          (fun s hs => hlip j u hu s (subv hs))
      -- |∂_v δ_j| ≤ ∫_0^u |∂_u∂_v δ_j| ≤ L ∫_0^u f
      have c3 : ContinuousOn (fun t => duv j t v) (Icc (0:ℝ) u) :=
        (sliceOn2 (hC j).cont_uv hv).mono subu
      have b3 : |dv j u v| ≤ L * ∫ t in (0:ℝ)..u, f t v := by
        refine (abs_le_integral_abs hu.1 (hDv0 j v hv)
          (fun t ht => (hC j).deriv_uv_u t (subu ht) v hv) c3).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hu.1 (c3.abs.intervalIntegrable_of_Icc hu.1)
          ((continuousOn_const.mul hft).intervalIntegrable_of_Icc hu.1)
          (fun t ht => hlip j t (subu ht) v hv)
      show |d j u v| + |du j u v| + |dv j u v|
        ≤ (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)
      nlinarith [mul_nonneg hL I1nn, mul_nonneg hL I2nn]
    calc f u v = ∑ j, A j u v := rfl
      _ ≤ ∑ _j : Fin n, (1 + L) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) :=
          Finset.sum_le_sum (fun j _ => hj j)
      _ = (n * (1 + L)) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hzero := CFT.CharGronwall.char_gronwall_on hf (fun u _ v _ => hfnn u v) hK
  intro i u hu v hv
  have h0 : f u v = 0 := hzero u hu v hv
  have hAi : A i u v = 0 := le_antisymm (h0 ▸ hAf i u v) (hAnn i u v)
  have : |d i u v| + |du i u v| + |dv i u v| = 0 := hAi
  have h1 := abs_nonneg (du i u v)
  have h2 := abs_nonneg (dv i u v)
  exact abs_eq_zero.mp (by linarith [abs_nonneg (d i u v)])

end CFT.CharUniqueness
