/-
  命題集 `LEAN_GAP_TREES.md` 4-7(一意性)の本体の解析部品:特性方向の 2 変数グロンウォール(2026-11-18)

  くさび(1+1 次元、二重ヌル座標)の差の線形系は、1 階の形 (δ, δ_u, δ_v) に直すと
    δ_u(u,v) = ∫_0^v δ_uv(u,s) ds、 δ_v(u,v) = ∫_0^u δ_uv(t,v) dt、 δ(u,v) = ∫_0^u δ_u(t,v) dt
  と書ける(2 つの解は同じ特性データを持つので、両方のヌル面上で差は 0)。
  係数が有界なら、f = |δ| + |δ_u| + |δ_v| は
    f(u,v) ≤ K (∫_0^v f(u,s) ds + ∫_0^u f(t,v) dt)
  をみたす。この不等式だけから f ≡ 0 が従う、というのがこのモジュールの主定理。
  エネルギー法(Mathlib に無い、原子核 4-16)を使わずに一意性を取る道具になる。

  * `exp_int_le`:∫_0^v e^{λ(u+s)} ds ≤ e^{λ(u+v)}/λ(λ > 0)。
  * `char_gronwall_on`:長方形 [0,a]×[0,b] 上で連続かつ非負な f が上の積分不等式をみたせば、f は長方形上で 0。
    証明:重み e^{−λ(u+v)} をつけた g の最大値 N を取る(コンパクト性)。λ = 4K とすると N ≤ N/2 になり N = 0。
    連続性は長方形の上だけで仮定する。`char_gronwall` は全平面で連続な場合の系。
  * `char_gronwall_triple`:1 階の系 (X, Y, Z) の形。
    |Y(u,v)| ≤ L ∫_0^v |X(u,s)| ds、|Z(u,v)| ≤ L ∫_0^u |X(t,v)| dt、|X(u,v)| ≤ ∫_0^u |Y(t,v)| dt
    なら X, Y, Z はすべて 0(4-7 の組み立てで使う形)。
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open Real Set

namespace CFT.CharGronwall

/-- ∫_0^v e^{λ(u+s)} ds ≤ e^{λ(u+v)}/λ -/
theorem exp_int_le (lam u v : ℝ) (hl : 0 < lam) :
    ∫ s in (0:ℝ)..v, exp (lam * (u + s)) ≤ exp (lam * (u + v)) / lam := by
  have h1 : (fun s => exp (lam * (u + s))) = fun s => exp (lam * u) * exp (lam * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.exp hl.ne', integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  have e : exp (lam * (u + v)) = exp (lam * u) * exp (lam * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  have hu := Real.exp_pos (lam * u)
  have hi : 0 < lam⁻¹ := inv_pos.mpr hl
  rw [div_eq_mul_inv]
  nlinarith [mul_pos hu hi]

/-- 特性方向の 2 変数グロンウォール(連続性は長方形の上だけで仮定) -/
theorem char_gronwall_on {a b K : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b))
    (hnn : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, 0 ≤ f u v)
    (hK : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      f u v ≤ K * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, f u v = 0 := by
  intro u hu v hv
  have hc1 : ∀ x ∈ Icc (0:ℝ) a, ContinuousOn (fun s => f x s) (Icc (0:ℝ) b) := fun x hx =>
    hf.comp (continuousOn_const.prod continuousOn_id) (fun s hs => Set.mk_mem_prod hx hs)
  have hc2 : ∀ y ∈ Icc (0:ℝ) b, ContinuousOn (fun t => f t y) (Icc (0:ℝ) a) := fun y hy =>
    hf.comp (continuousOn_id.prod continuousOn_const) (fun t ht => Set.mk_mem_prod ht hy)
  -- K を正の定数 K' = max K 1 に取り替える
  have hint1 : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b, 0 ≤ ∫ s in (0:ℝ)..y, f x s :=
    fun x hx y hy => intervalIntegral.integral_nonneg hy.1
      (fun s hs => hnn x hx s ⟨hs.1, hs.2.trans hy.2⟩)
  have hint2 : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b, 0 ≤ ∫ t in (0:ℝ)..x, f t y :=
    fun x hx y hy => intervalIntegral.integral_nonneg hx.1
      (fun t ht => hnn t ⟨ht.1, ht.2.trans hx.2⟩ y hy)
  have hK'pos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK2 : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b,
      f x y ≤ max K 1 * ((∫ s in (0:ℝ)..y, f x s) + ∫ t in (0:ℝ)..x, f t y) :=
    fun x hx y hy => (hK x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (hint1 x hx y hy) (hint2 x hx y hy)))
  -- 重み e^{−λ(u+v)} をつけた関数の最大値
  have hlpos : 0 < 4 * max K 1 := by positivity
  let g : ℝ × ℝ → ℝ := fun p => exp (-((4 * max K 1) * (p.1 + p.2))) * Function.uncurry f p
  have hg : ContinuousOn g (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.add continuous_snd)).neg).continuousOn.mul hf
  have hR : IsCompact (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b).Nonempty := ⟨(u, v), hu, hv⟩
  obtain ⟨p, hp, hmax⟩ := hR.exists_isMaxOn hne hg
  have hmax' : ∀ q ∈ Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b, g q ≤ g p := fun q hq => isMaxOn_iff.mp hmax q hq
  obtain ⟨hp1, hp2⟩ := hp
  have hgq : ∀ x y, g (x, y) = exp (-((4 * max K 1) * (x + y))) * f x y := fun x y => rfl
  have hN0 : 0 ≤ g p := by
    have h0 : 0 ≤ g (u, v) := by
      rw [hgq]
      exact mul_nonneg (Real.exp_pos _).le (hnn u hu v hv)
    exact h0.trans (hmax' (u, v) ⟨hu, hv⟩)
  -- 各点の評価 f(x,y) ≤ N e^{λ(x+y)}
  have hbound : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b,
      f x y ≤ g p * exp ((4 * max K 1) * (x + y)) := by
    intro x hx y hy
    have h := hmax' (x, y) ⟨hx, hy⟩
    rw [hgq] at h
    have hE := Real.exp_pos ((4 * max K 1) * (x + y))
    have hinv : exp (-((4 * max K 1) * (x + y))) * exp ((4 * max K 1) * (x + y)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc f x y = (exp (-((4 * max K 1) * (x + y))) * f x y) * exp ((4 * max K 1) * (x + y)) := by
          rw [mul_comm (exp _) (f x y), mul_assoc, hinv, mul_one]
      _ ≤ g p * exp ((4 * max K 1) * (x + y)) := mul_le_mul_of_nonneg_right h hE.le
  have hcont_e : ∀ c : ℝ, Continuous (fun s => g p * exp ((4 * max K 1) * (c + s))) := fun c =>
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.add continuous_id)))
  -- 2 つの積分の評価
  have hI1 : ∫ s in (0:ℝ)..p.2, f p.1 s
      ≤ g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) := by
    calc ∫ s in (0:ℝ)..p.2, f p.1 s
        ≤ ∫ s in (0:ℝ)..p.2, g p * exp ((4 * max K 1) * (p.1 + s)) :=
          intervalIntegral.integral_mono_on hp2.1 (((hc1 p.1 hp1).mono (Icc_subset_Icc le_rfl hp2.2)).intervalIntegrable_of_Icc hp2.1)
            ((hcont_e p.1).intervalIntegrable _ _)
            (fun s hs => hbound p.1 hp1 s ⟨hs.1, hs.2.trans hp2.2⟩)
      _ = g p * ∫ s in (0:ℝ)..p.2, exp ((4 * max K 1) * (p.1 + s)) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) :=
          mul_le_mul_of_nonneg_left (exp_int_le _ p.1 p.2 hlpos) hN0
  have hI2 : ∫ t in (0:ℝ)..p.1, f t p.2
      ≤ g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) := by
    calc ∫ t in (0:ℝ)..p.1, f t p.2
        ≤ ∫ t in (0:ℝ)..p.1, g p * exp ((4 * max K 1) * (p.2 + t)) :=
          intervalIntegral.integral_mono_on hp1.1 (((hc2 p.2 hp2).mono (Icc_subset_Icc le_rfl hp1.2)).intervalIntegrable_of_Icc hp1.1)
            ((hcont_e p.2).intervalIntegrable _ _)
            (fun t ht => by
              have h := hbound t ⟨ht.1, ht.2.trans hp1.2⟩ p.2 hp2
              rwa [add_comm t p.2] at h)
      _ = g p * ∫ t in (0:ℝ)..p.1, exp ((4 * max K 1) * (p.2 + t)) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ g p * (exp ((4 * max K 1) * (p.2 + p.1)) / (4 * max K 1)) :=
          mul_le_mul_of_nonneg_left (exp_int_le _ p.2 p.1 hlpos) hN0
      _ = g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)) := by rw [add_comm p.2 p.1]
  -- 最大点での値:N e^{λ(p1+p2)} ≤ N e^{λ(p1+p2)}/2
  have hfp : f p.1 p.2 = g p * exp ((4 * max K 1) * (p.1 + p.2)) := by
    have hinv : exp (-((4 * max K 1) * (p.1 + p.2))) * exp ((4 * max K 1) * (p.1 + p.2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hgp : g p = exp (-((4 * max K 1) * (p.1 + p.2))) * f p.1 p.2 := rfl
    rw [hgp, mul_comm (exp _) (f p.1 p.2), mul_assoc, hinv, mul_one]
  have hmain : g p * exp ((4 * max K 1) * (p.1 + p.2))
      ≤ max K 1 * (g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1))
        + g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1))) := by
    rw [← hfp]
    exact (hK2 p.1 hp1 p.2 hp2).trans
      (mul_le_mul_of_nonneg_left (add_le_add hI1 hI2) hK'pos.le)
  have hsimp : max K 1 * (g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1))
        + g p * (exp ((4 * max K 1) * (p.1 + p.2)) / (4 * max K 1)))
      = g p * exp ((4 * max K 1) * (p.1 + p.2)) / 2 := by
    have hne' : max K 1 ≠ 0 := hK'pos.ne'
    field_simp
    ring
  have hNE : g p * exp ((4 * max K 1) * (p.1 + p.2)) ≤ 0 := by linarith
  have hNp : g p ≤ 0 := by
    by_contra h
    push_neg at h
    have := mul_pos h (Real.exp_pos ((4 * max K 1) * (p.1 + p.2)))
    linarith
  -- 結論
  have hguv : g (u, v) ≤ 0 := (hmax' (u, v) ⟨hu, hv⟩).trans hNp
  rw [hgq] at hguv
  have hf0 : f u v ≤ 0 := by
    by_contra h
    push_neg at h
    have := mul_pos (Real.exp_pos (-((4 * max K 1) * (u + v)))) h
    linarith
  exact le_antisymm hf0 (hnn u hu v hv)

/-- 特性方向の 2 変数グロンウォール(全平面で連続な場合) -/
theorem char_gronwall {a b K : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f))
    (hnn : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, 0 ≤ f u v)
    (hK : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      f u v ≤ K * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, f u v = 0 :=
  char_gronwall_on hf.continuousOn hnn hK

/-- 1 階の系 (X, Y, Z) の形:
|Y(u,v)| ≤ L ∫_0^v |X(u,s)| ds、|Z(u,v)| ≤ L ∫_0^u |X(t,v)| dt、|X(u,v)| ≤ ∫_0^u |Y(t,v)| dt
なら X, Y, Z はすべて長方形上で 0 -/
theorem char_gronwall_triple {a b L : ℝ} {X Y Z : ℝ → ℝ → ℝ}
    (hX : Continuous (Function.uncurry X)) (hY : Continuous (Function.uncurry Y))
    (hZ : Continuous (Function.uncurry Z)) (hL : 0 ≤ L)
    (hYb : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, |Y u v| ≤ L * ∫ s in (0:ℝ)..v, |X u s|)
    (hZb : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, |Z u v| ≤ L * ∫ t in (0:ℝ)..u, |X t v|)
    (hXb : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, |X u v| ≤ ∫ t in (0:ℝ)..u, |Y t v|) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, X u v = 0 ∧ Y u v = 0 ∧ Z u v = 0 := by
  let f : ℝ → ℝ → ℝ := fun u v => |X u v| + |Y u v| + |Z u v|
  have hf : Continuous (Function.uncurry f) :=
    (hX.abs.add hY.abs).add hZ.abs
  have hc : ∀ (W : ℝ → ℝ → ℝ), Continuous (Function.uncurry W) →
      (∀ x, Continuous (fun s => |W x s|)) ∧ (∀ y, Continuous (fun t => |W t y|)) :=
    fun W hW => ⟨fun x => (hW.comp (continuous_const.prod_mk continuous_id)).abs,
      fun y => (hW.comp (continuous_id.prod_mk continuous_const)).abs⟩
  have hfc1 : ∀ x, Continuous (fun s => f x s) := fun x =>
    (((hc X hX).1 x).add ((hc Y hY).1 x)).add ((hc Z hZ).1 x)
  have hfc2 : ∀ y, Continuous (fun t => f t y) := fun y =>
    (((hc X hX).2 y).add ((hc Y hY).2 y)).add ((hc Z hZ).2 y)
  have hnn : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, 0 ≤ f u v := fun u _ v _ => by
    show 0 ≤ |X u v| + |Y u v| + |Z u v|
    positivity
  have hK : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      f u v ≤ (L + 1) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v) := by
    intro u hu v hv
    have m1 : ∫ s in (0:ℝ)..v, |X u s| ≤ ∫ s in (0:ℝ)..v, f u s :=
      intervalIntegral.integral_mono_on hv.1 (((hc X hX).1 u).intervalIntegrable _ _)
        ((hfc1 u).intervalIntegrable _ _)
        (fun s _ => by
          show |X u s| ≤ |X u s| + |Y u s| + |Z u s|
          have := abs_nonneg (Y u s); have := abs_nonneg (Z u s); linarith)
    have m2 : ∫ t in (0:ℝ)..u, |X t v| ≤ ∫ t in (0:ℝ)..u, f t v :=
      intervalIntegral.integral_mono_on hu.1 (((hc X hX).2 v).intervalIntegrable _ _)
        ((hfc2 v).intervalIntegrable _ _)
        (fun t _ => by
          show |X t v| ≤ |X t v| + |Y t v| + |Z t v|
          have := abs_nonneg (Y t v); have := abs_nonneg (Z t v); linarith)
    have m3 : ∫ t in (0:ℝ)..u, |Y t v| ≤ ∫ t in (0:ℝ)..u, f t v :=
      intervalIntegral.integral_mono_on hu.1 (((hc Y hY).2 v).intervalIntegrable _ _)
        ((hfc2 v).intervalIntegrable _ _)
        (fun t _ => by
          show |Y t v| ≤ |X t v| + |Y t v| + |Z t v|
          have := abs_nonneg (X t v); have := abs_nonneg (Z t v); linarith)
    have i1 : 0 ≤ ∫ s in (0:ℝ)..v, f u s := intervalIntegral.integral_nonneg hv.1
      (fun s hs => hnn u hu s ⟨hs.1, hs.2.trans hv.2⟩)
    have i2 : 0 ≤ ∫ t in (0:ℝ)..u, f t v := intervalIntegral.integral_nonneg hu.1
      (fun t ht => hnn t ⟨ht.1, ht.2.trans hu.2⟩ v hv)
    have e1 := hYb u hu v hv
    have e2 := hZb u hu v hv
    have e3 := hXb u hu v hv
    show |X u v| + |Y u v| + |Z u v|
      ≤ (L + 1) * ((∫ s in (0:ℝ)..v, f u s) + ∫ t in (0:ℝ)..u, f t v)
    nlinarith [mul_le_mul_of_nonneg_left m1 hL, mul_le_mul_of_nonneg_left m2 hL]
  intro u hu v hv
  have h0 := char_gronwall hf hnn hK u hu v hv
  have hx := abs_nonneg (X u v)
  have hy := abs_nonneg (Y u v)
  have hz := abs_nonneg (Z u v)
  have h0' : |X u v| + |Y u v| + |Z u v| = 0 := h0
  refine ⟨abs_eq_zero.mp (by linarith), abs_eq_zero.mp (by linarith), abs_eq_zero.mp (by linarith)⟩

end CFT.CharGronwall
