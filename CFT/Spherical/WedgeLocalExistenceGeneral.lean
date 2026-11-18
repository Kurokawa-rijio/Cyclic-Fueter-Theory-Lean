/-
  命題集 `LEAN_GAP_TREES.md` 4-17(くさび系の局所存在、r ≥ r₀ > 0 の小さい特性矩形上)の完成(2026-11-18)

  任意の C¹ 級の特性データ φ(v = 0 の辺、添字 0 = r、1 = Ω、2 = W)と ψ(u = 0 の辺)について、
  角で一致し(φ i 0 = ψ i 0)、角で r > 0、Ω > 0 なら、
  * `wedge_local_existence_gen`:角の近くの正方形 [0,ε]×[0,ε] の上で、くさびの 3 本の発展方程式をみたし、
    データを再現し、C² 級で、r ≥ r₀、Ω ≥ r₀(r₀ > 0)の解がある。
  * `wedge_local_wellposed_gen`:その正方形の上で、同じデータをもち r > 0、Ω > 0 の C² 解はこれしかない。

  方法は `WedgeExistence`(帽子と首のデータの場合)と同じ:右辺を切り落として大域的にリプシッツにし、
  `GoursatExistence.goursat_exists`(重みつき sup ノルムでの Banach の不動点定理)で解き、
  角の近くでは切り落としが効かないことを使う。r₀ は角での r、Ω の小さいほうの半分。
  一意性は `WedgeUniqueness.wedge_uniqueness_of_pos_same`(データは任意)。

  範囲の注意:
  * データ φ i、ψ i は ℝ 全体で C¹(`ContDiff ℝ 1`)と仮定する。辺の上だけで与えられたデータを ℝ 全体の
    C¹ 関数に延ばす補題は入れていない(解が使うのは辺 [0,ε] の上の値だけ)。
  * ε は存在するというだけで、明示していない(角での連続性から取る)。r₀ は角での r、Ω の小さいほうの半分で明示的。
  * 角は (0,0) に置いている。一般の角 (u₀,v₀) は平行移動で移るが、その書き換えは形式化していない。
  * 「解」は 3 本の発展方程式の解で、拘束 C_u、C_v をみたすことは含まない。
  * Muse の路線(`WedgeC1Contraction` までの C¹ ノルムでの縮小評価)とは別の道で、存在そのものを閉じている。
    あちらは評価までで、Banach の不動点定理の適用はしていない。
    キャップ(r = 0)を含む版は 4-16 に残る。
-/
import CFT.Spherical.WedgeExistence

open Real Set Filter Topology CFT.Wedge CFT.CharUniqueness CFT.Goursat CFT.WedgeUniq CFT.WedgeExist

namespace CFT.WedgeExistGen

/-- 一般の特性データを長方形の 2 辺の上で課したもの -/
def GenDataOn (a b : ℝ) (φ ψ : Fin 3 → ℝ → ℝ) (F : WedgeFields) : Prop :=
  (∀ u ∈ Icc (0:ℝ) a, F.r u 0 = φ 0 u ∧ F.Om u 0 = φ 1 u ∧ F.W u 0 = φ 2 u)
    ∧ (∀ v ∈ Icc (0:ℝ) b, F.r 0 v = ψ 0 v ∧ F.Om 0 v = ψ 1 v ∧ F.W 0 v = ψ 2 v)

theorem sameDataOn_of_gen {a b : ℝ} {φ ψ : Fin 3 → ℝ → ℝ} {F G : WedgeFields}
    (dF : GenDataOn a b φ ψ F) (dG : GenDataOn a b φ ψ G) : SameDataOn a b F G :=
  ⟨fun u hu => ⟨(dF.1 u hu).1.trans (dG.1 u hu).1.symm, (dF.1 u hu).2.1.trans (dG.1 u hu).2.1.symm,
      (dF.1 u hu).2.2.trans (dG.1 u hu).2.2.symm⟩,
    fun v hv => ⟨(dF.2 v hv).1.trans (dG.2 v hv).1.symm, (dF.2 v hv).2.1.trans (dG.2 v hv).2.1.symm,
      (dF.2 v hv).2.2.trans (dG.2 v hv).2.2.symm⟩⟩

theorem abs_le_of_near {x c η : ℝ} (h : |x - c| < η) (hη : η ≤ 1) : |x| ≤ |c| + 1 := by
  have := abs_sub_abs_le_abs_sub x c
  linarith

/-- くさびの局所存在(データは任意):角で r > 0、Ω > 0 の C¹ データに対し、角の近くの正方形の上で
発展方程式・データ・C² 級をみたし、r、Ω が正の定数 r₀ 以上の解がある。 -/
theorem wedge_local_existence_gen (φ ψ : Fin 3 → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h00 : ∀ i, φ i 0 = ψ i 0)
    (hr : 0 < φ 0 0) (hO : 0 < φ 1 0) :
    ∃ ε > 0, ∃ r₀ > 0, ∃ F : WedgeFields, WedgeEqsOn ε ε F ∧ GenDataOn ε ε φ ψ F
      ∧ C2On ε ε F.r ∧ C2On ε ε F.Om ∧ C2On ε ε F.W
      ∧ ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, r₀ ≤ F.r u v ∧ r₀ ≤ F.Om u v := by
  -- 角での値
  set c0 := φ 0 0
  set c1 := φ 1 0
  set c2 := φ 2 0
  set p0 := deriv (φ 0) 0
  set q0 := deriv (ψ 0) 0
  set p1 := deriv (φ 1) 0
  set q1 := deriv (ψ 1) 0
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = min c0 c1 / 2 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact half_pos (lt_min hr hO)
  have hm0 : 2 * m ≤ c0 := by rw [hmdef]; linarith [min_le_left c0 c1]
  have hm1 : 2 * m ≤ c1 := by rw [hmdef]; linarith [min_le_right c0 c1]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = 1 + |c0| + |c1| + |c2| + |p0| + |q0| + |p1| + |q1| := ⟨_, rfl⟩
  have a0 := abs_nonneg c0
  have a1 := abs_nonneg c1
  have a2 := abs_nonneg c2
  have a3 := abs_nonneg p0
  have a4 := abs_nonneg q0
  have a5 := abs_nonneg p1
  have a6 := abs_nonneg q1
  have hc0 : c0 ≤ |c0| := le_abs_self c0
  have hc1 : c1 ≤ |c1| := le_abs_self c1
  have hmB : m ≤ B := by rw [hBdef]; linarith
  obtain ⟨L, hL, hF⟩ := Fw_lip hm hmB
  obtain ⟨U, Uu, Uv, Uuv, hC, hd1, hd2, heq⟩ := goursat_exists (a := 1) (b := 1)
    zero_le_one zero_le_one hL (Fw B m) hF φ ψ (fun i => deriv (φ i)) (fun i => deriv (ψ i))
    (fun i x => ((hφ i).differentiable le_rfl x).hasDerivAt)
    (fun i x => ((hψ i).differentiable le_rfl x).hasDerivAt)
    (fun i => (hφ i).continuous_deriv le_rfl)
    (fun i => (hψ i).continuous_deriv le_rfl)
    h00
  -- 偏微分は Goursat 解の微分
  have eDu : ∀ i, Du (U i) = Uu i := fun i => funext fun u => funext fun v =>
    ((hC i).deriv_u u v).deriv
  have eDv : ∀ i, Dv (U i) = Uv i := fun i => funext fun u => funext fun v =>
    ((hC i).deriv_v u v).deriv
  have eDuv : ∀ i, Duv (U i) = Uuv i := fun i => funext fun u => funext fun v => by
    show deriv (fun t => deriv (fun s => U i t s) v) u = Uuv i u v
    have h : (fun t => deriv (fun s => U i t s) v) = fun t => Uv i t v :=
      funext fun t => ((hC i).deriv_v t v).deriv
    rw [h]
    exact ((hC i).deriv_uv_u u v).deriv
  -- 角での値はデータで決まる
  have cu : ∀ i u, Uu i u 0 = deriv (φ i) u := fun i u => by
    rw [← eDu]
    show deriv (fun t => U i t 0) u = _
    rw [show (fun t => U i t 0) = φ i from funext (hd1 i)]
  have cv : ∀ i v, Uv i 0 v = deriv (ψ i) v := fun i v => by
    rw [← eDv]
    show deriv (fun s => U i 0 s) v = _
    rw [show (fun s => U i 0 s) = ψ i from funext (hd2 i)]
  have k0 : U 0 0 0 = c0 := hd1 0 0
  have k1 : U 1 0 0 = c1 := hd1 1 0
  have k2 : U 2 0 0 = c2 := hd1 2 0
  have k3 : Uu 0 0 0 = p0 := cu 0 0
  have k4 : Uv 0 0 0 = q0 := cv 0 0
  have k5 : Uu 1 0 0 = p1 := cu 1 0
  have k6 : Uv 1 0 0 = q1 := cv 1 0
  -- 角の近くでは切り落としが効かない
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min m 1 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min hm one_pos
  have hηm : η ≤ m := by rw [hηdef]; exact min_le_left _ _
  have hη1 : η ≤ 1 := by rw [hηdef]; exact min_le_right _ _
  let S : ℝ × ℝ → ℝ := fun q =>
    |U 0 q.1 q.2 - c0| + |U 1 q.1 q.2 - c1| + |U 2 q.1 q.2 - c2| + |Uu 0 q.1 q.2 - p0|
      + |Uv 0 q.1 q.2 - q0| + |Uu 1 q.1 q.2 - p1| + |Uv 1 q.1 q.2 - q1|
  have hS : Continuous S :=
    (((((((hC 0).cont.sub continuous_const).abs.add ((hC 1).cont.sub continuous_const).abs).add
      ((hC 2).cont.sub continuous_const).abs).add ((hC 0).cont_u.sub continuous_const).abs).add
      ((hC 0).cont_v.sub continuous_const).abs).add
      ((hC 1).cont_u.sub continuous_const).abs).add ((hC 1).cont_v.sub continuous_const).abs
  have hS0 : S (0, 0) = 0 := by
    show |U 0 0 0 - c0| + |U 1 0 0 - c1| + |U 2 0 0 - c2| + |Uu 0 0 0 - p0|
      + |Uv 0 0 0 - q0| + |Uu 1 0 0 - p1| + |Uv 1 0 0 - q1| = 0
    rw [k0, k1, k2, k3, k4, k5, k6]
    simp
  obtain ⟨δ, hδ, hδS⟩ := Metric.continuous_iff.mp hS (0, 0) η hη
  refine ⟨min (δ / 2) 1, lt_min (by linarith) one_pos, m, hm, ⟨U 0, U 1, U 2⟩, ?_⟩
  have hsmall : ∀ u ∈ Icc (0:ℝ) (min (δ / 2) 1), ∀ v ∈ Icc (0:ℝ) (min (δ / 2) 1), S (u, v) < η := by
    intro u hu v hv
    have hu2 : u ≤ δ / 2 := hu.2.trans (min_le_left _ _)
    have hv2 : v ≤ δ / 2 := hv.2.trans (min_le_left _ _)
    have hd : dist (u, v) ((0:ℝ), (0:ℝ)) < δ := by
      simp only [Prod.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hu.1, abs_of_nonneg hv.1]
      exact max_lt (by linarith) (by linarith)
    have := hδS (u, v) hd
    rw [hS0, Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hsub : ∀ x ∈ Icc (0:ℝ) (min (δ / 2) 1), x ∈ Icc (0:ℝ) 1 := fun x hx =>
    ⟨hx.1, hx.2.trans (min_le_right _ _)⟩
  -- 各点での評価
  have hpt : ∀ u ∈ Icc (0:ℝ) (min (δ / 2) 1), ∀ v ∈ Icc (0:ℝ) (min (δ / 2) 1),
      trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))
        = toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v)
      ∧ m ≤ U 0 u v ∧ m ≤ U 1 u v := by
    intro u hu v hv
    have hs : |U 0 u v - c0| + |U 1 u v - c1| + |U 2 u v - c2| + |Uu 0 u v - p0|
        + |Uv 0 u v - q0| + |Uu 1 u v - p1| + |Uv 1 u v - q1| < η := hsmall u hu v hv
    have e1 := abs_nonneg (U 0 u v - c0)
    have e2 := abs_nonneg (U 1 u v - c1)
    have e3 := abs_nonneg (U 2 u v - c2)
    have e4 := abs_nonneg (Uu 0 u v - p0)
    have e5 := abs_nonneg (Uv 0 u v - q0)
    have e6 := abs_nonneg (Uu 1 u v - p1)
    have e7 := abs_nonneg (Uv 1 u v - q1)
    have b1 : |U 0 u v - c0| < η := by linarith
    have b2 : |U 1 u v - c1| < η := by linarith
    have b3 : |U 2 u v - c2| < η := by linarith
    have b4 : |Uu 0 u v - p0| < η := by linarith
    have b5 : |Uv 0 u v - q0| < η := by linarith
    have b6 : |Uu 1 u v - p1| < η := by linarith
    have b7 : |Uv 1 u v - q1| < η := by linarith
    have t3 := abs_le_of_near b3 hη1
    have t4 := abs_le_of_near b4 hη1
    have t5 := abs_le_of_near b5 hη1
    have t6 := abs_le_of_near b6 hη1
    have t7 := abs_le_of_near b7 hη1
    rw [abs_lt] at b1 b2
    have l0 : m ≤ U 0 u v := by linarith [b1.1]
    have l1 : m ≤ U 1 u v := by linarith [b2.1]
    refine ⟨trunc_of (p := toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, l0, l1⟩
    · exact l1
    · show U 1 u v ≤ B
      rw [hBdef]; linarith [b2.2]
    · show |U 2 u v| ≤ B
      rw [hBdef]; linarith
    · show |Uu 0 u v| ≤ B
      rw [hBdef]; linarith
    · show |Uv 0 u v| ≤ B
      rw [hBdef]; linarith
    · exact l0
    · show U 0 u v ≤ B
      rw [hBdef]; linarith [b1.2]
    · show |Uu 1 u v| ≤ B
      rw [hBdef]; linarith
    · show |Uv 1 u v| ≤ B
      rw [hBdef]; linarith
  refine ⟨fun u hu v hv => ?_, ⟨fun u _ => ?_, fun v _ => ?_⟩, ?_, ?_, ?_, fun u hu v hv => ?_⟩
  · -- 発展方程式
    obtain ⟨hp, _, _⟩ := hpt u hu v hv
    have e0 : Uuv 0 u v = rhsR (U 1 u v) (U 2 u v) (Uu 0 u v) (Uv 0 u v) (U 0 u v) := by
      rw [heq 0 u (hsub u hu) v (hsub v hv)]
      show eR (trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))) = _
      exact (congrArg eR hp).trans rfl
    have e1 : Uuv 1 u v = rhsOm (U 1 u v) (Uu 1 u v) (Uv 1 u v)
        (rhsR (U 1 u v) (U 2 u v) (Uu 0 u v) (Uv 0 u v) (U 0 u v)) (U 0 u v) (U 2 u v) := by
      rw [heq 1 u (hsub u hu) v (hsub v hv)]
      show eOm (trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))) = _
      exact (congrArg eOm hp).trans rfl
    have e2 : Uuv 2 u v = rhsW (U 1 u v) (U 2 u v) (U 0 u v) := by
      rw [heq 2 u (hsub u hu) v (hsub v hv)]
      show eW (trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))) = _
      exact (congrArg eW hp).trans rfl
    show Duv (U 0) u v = rhsR (U 1 u v) (U 2 u v) (Du (U 0) u v) (Dv (U 0) u v) (U 0 u v)
      ∧ Duv (U 1) u v
          = rhsOm (U 1 u v) (Du (U 1) u v) (Dv (U 1) u v) (Duv (U 0) u v) (U 0 u v) (U 2 u v)
      ∧ Duv (U 2) u v = rhsW (U 1 u v) (U 2 u v) (U 0 u v)
    rw [eDuv, eDuv, eDuv, eDu, eDu, eDv, eDv]
    exact ⟨e0, by rw [e1, e0], e2⟩
  · exact ⟨hd1 0 u, hd1 1 u, hd1 2 u⟩
  · exact ⟨hd2 0 v, hd2 1 v, hd2 2 v⟩
  · show C2Data _ _ (U 0) (Du (U 0)) (Dv (U 0)) (Duv (U 0))
    rw [eDu, eDv, eDuv]
    exact (hC 0).toC2Data _ _
  · show C2Data _ _ (U 1) (Du (U 1)) (Dv (U 1)) (Duv (U 1))
    rw [eDu, eDv, eDuv]
    exact (hC 1).toC2Data _ _
  · show C2Data _ _ (U 2) (Du (U 2)) (Dv (U 2)) (Duv (U 2))
    rw [eDu, eDv, eDuv]
    exact (hC 2).toC2Data _ _
  · obtain ⟨_, h1, h2⟩ := hpt u hu v hv
    exact ⟨h1, h2⟩

/-- くさびの局所適切性(データは任意):角の近くの正方形の上で、同じデータをもち r > 0、Ω > 0 の
C² 解はちょうど一つあり、その解は r、Ω ≥ r₀ > 0 をみたす。 -/
theorem wedge_local_wellposed_gen (φ ψ : Fin 3 → ℝ → ℝ)
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h00 : ∀ i, φ i 0 = ψ i 0)
    (hr : 0 < φ 0 0) (hO : 0 < φ 1 0) :
    ∃ ε > 0, ∃ r₀ > 0, ∃ F : WedgeFields, (WedgeEqsOn ε ε F ∧ GenDataOn ε ε φ ψ F
      ∧ C2On ε ε F.r ∧ C2On ε ε F.Om ∧ C2On ε ε F.W
      ∧ ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, r₀ ≤ F.r u v ∧ r₀ ≤ F.Om u v)
      ∧ ∀ G : WedgeFields, WedgeEqsOn ε ε G → GenDataOn ε ε φ ψ G
        → C2On ε ε G.r → C2On ε ε G.Om → C2On ε ε G.W
        → (∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, 0 < G.r u v ∧ 0 < G.Om u v)
        → ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε,
          G.r u v = F.r u v ∧ G.Om u v = F.Om u v ∧ G.W u v = F.W u v := by
  obtain ⟨ε, hε, r₀, hr₀, F, eF, dF, rFr, rFO, rFW, pF⟩ :=
    wedge_local_existence_gen φ ψ hφ hψ h00 hr hO
  refine ⟨ε, hε, r₀, hr₀, F, ⟨eF, dF, rFr, rFO, rFW, pF⟩, fun G eG dG rGr rGO rGW pG => ?_⟩
  exact wedge_uniqueness_of_pos_same G F eG eF (sameDataOn_of_gen dG dF) rGr rGO rGW rFr rFO rFW
    (fun u hu v hv => ⟨(pG u hu v hv).1, (pG u hu v hv).2,
      lt_of_lt_of_le hr₀ (pF u hu v hv).1, lt_of_lt_of_le hr₀ (pF u hu v hv).2⟩)

end CFT.WedgeExistGen
