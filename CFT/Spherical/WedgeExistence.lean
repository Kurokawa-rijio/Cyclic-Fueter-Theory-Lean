/-
  命題集 `LEAN_GAP_TREES.md` 4-9(くさびの局所存在)と局所適切性(2026-11-18)

  くさびの球対称 EYM 系(`CFT.Wedge` の 3 本の発展方程式、帽子と首の特性データ)は、
  角 (0,0) の近くの小さな正方形 [0,ε]×[0,ε] の上で C² 級の解を持ち、そこで r > 0、Ω > 0。
  さらに、その正方形の上で r > 0、Ω > 0 をみたす解はこれしかない(4-7 と合わせた局所適切性)。
  ここでの「解」は 3 本の発展方程式の解で、拘束 C_u、C_v をみたすことは含まない(未証明)。

  方法:
  * 右辺を切り落とす(`trunc`:Ω、r を [m,B] に、W、r_u、r_v、Ω_u、Ω_v を [−B,B] に射影)と、
    `WedgeUniqueness` の UL 評価から大域的にリプシッツな右辺 `Fw` になる。
  * `GoursatExistence.goursat_exists` で切り落とした系を [0,1]×[0,1] の上で解く。
  * 角での値はデータだけで決まる(r = Ω = 1、W = 0、r_u = capR′(0)、r_v = 0、Ω_u = capOm′(0)、
    Ω_v = neckOm′(0))。B をこれらより大きく取っておくと、解の連続性から角の近くでは切り落としが効かず、
    元の方程式の解になる。
-/
import CFT.Foundations.GoursatExistence
import CFT.Spherical.WedgeUniqueness

open Real Set Filter Topology CFT.Wedge CFT.CharUniqueness CFT.Goursat CFT.WedgeUniq

namespace CFT.WedgeExist

/-! ### 切り落とし -/

/-- 区間 [lo, hi] への射影 -/
noncomputable def clampIcc (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clampIcc_lip (lo hi x y : ℝ) : |clampIcc lo hi x - clampIcc lo hi y| ≤ |x - y| := by
  unfold clampIcc
  have h1 := abs_max_sub_max_le_max lo (min hi x) lo (min hi y)
  have h2 := abs_min_sub_min_le_max hi x hi y
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min hi x - min hi y))] at h1
  rw [max_eq_right (abs_nonneg (x - y))] at h2
  exact h1.trans h2

theorem clampIcc_ge (lo hi x : ℝ) : lo ≤ clampIcc lo hi x := le_max_left _ _

theorem clampIcc_le {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clampIcc lo hi x ≤ hi :=
  max_le h (min_le_left _ _)

theorem clampIcc_of {lo hi x : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) : clampIcc lo hi x = x := by
  unfold clampIcc
  rw [min_eq_right h2, max_eq_right h1]

/-- 7 個の量の切り落とし -/
noncomputable def trunc (B m : ℝ) (p : Pt) : Pt :=
  ⟨clampIcc m B p.Om, clampIcc (-B) B p.W, clampIcc (-B) B p.ru, clampIcc (-B) B p.rv,
    clampIcc m B p.r, clampIcc (-B) B p.Ou, clampIcc (-B) B p.Ov⟩

theorem trunc_good {B m : ℝ} (hm : 0 < m) (hmB : m ≤ B) (p : Pt) : Good B m (trunc B m p) := by
  have a1 : ∀ x, |clampIcc (-B) B x| ≤ B := fun x =>
    abs_le.mpr ⟨clampIcc_ge _ _ _, clampIcc_le (by linarith) x⟩
  have a2 : ∀ x, |clampIcc m B x| ≤ B := fun x =>
    abs_le.mpr ⟨by linarith [clampIcc_ge m B x], clampIcc_le hmB x⟩
  exact ⟨a2 _, a1 _, a1 _, a1 _, a1 _, a1 _, clampIcc_ge _ _ _, clampIcc_ge _ _ _⟩

theorem trunc_pdist (B m : ℝ) (p q : Pt) : pdist (trunc B m p) (trunc B m q) ≤ pdist p q := by
  simp only [pdist, trunc]
  have := clampIcc_lip m B p.Om q.Om
  have := clampIcc_lip (-B) B p.W q.W
  have := clampIcc_lip (-B) B p.ru q.ru
  have := clampIcc_lip (-B) B p.rv q.rv
  have := clampIcc_lip m B p.r q.r
  have := clampIcc_lip (-B) B p.Ou q.Ou
  have := clampIcc_lip (-B) B p.Ov q.Ov
  linarith

theorem trunc_of {B m : ℝ} {p : Pt} (h1 : m ≤ p.Om) (h2 : p.Om ≤ B) (hW : |p.W| ≤ B)
    (hru : |p.ru| ≤ B) (hrv : |p.rv| ≤ B) (h6 : m ≤ p.r) (h7 : p.r ≤ B) (hOu : |p.Ou| ≤ B)
    (hOv : |p.Ov| ≤ B) : trunc B m p = p := by
  have c : ∀ x, |x| ≤ B → clampIcc (-B) B x = x := fun x hx =>
    clampIcc_of (abs_le.mp hx).1 (abs_le.mp hx).2
  unfold trunc
  (rw [clampIcc_of h1 h2, c _ hW, c _ hru, c _ hrv, clampIcc_of h6 h7, c _ hOu, c _ hOv]) <;> rfl

/-- 切り落とした式は大域的にリプシッツ -/
theorem lip_trunc {B m : ℝ} {e : Pt → ℝ} (hm : 0 < m) (hmB : m ≤ B) (h : UL B m e) :
    ∃ Λ, 0 ≤ Λ ∧ ∀ p q, |e (trunc B m p) - e (trunc B m q)| ≤ Λ * pdist p q := by
  obtain ⟨Λ, hΛ, hl⟩ := h
  exact ⟨Λ, hΛ, fun p q => ((hl _ _ (trunc_good hm hmB p) (trunc_good hm hmB q)).2.2).trans
    (mul_le_mul_of_nonneg_left (trunc_pdist B m p q) hΛ)⟩

/-! ### 3 成分の系としての右辺(添字 0 = r、1 = Ω、2 = W) -/

/-- 値 x、u 微分 y、v 微分 z から 7 個の量へ -/
def toPt (x y z : Fin 3 → ℝ) : Pt := ⟨x 1, x 2, y 0, z 0, x 0, y 1, z 1⟩

theorem toPt_pdist (x1 y1 z1 x2 y2 z2 : Fin 3 → ℝ) :
    pdist (toPt x1 y1 z1) (toPt x2 y2 z2)
      ≤ ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|) := by
  rw [Fin.sum_univ_three]
  simp only [pdist, toPt]
  linarith [abs_nonneg (y1 2 - y2 2), abs_nonneg (z1 2 - z2 2)]

/-- 3 本の右辺 -/
noncomputable def eVec : Fin 3 → Pt → ℝ := ![eR, eOm, eW]

/-- 切り落とした右辺 -/
noncomputable def Fw (B m : ℝ) (i : Fin 3) (x y z : Fin 3 → ℝ) : ℝ :=
  eVec i (trunc B m (toPt x y z))

theorem Fw_lip {B m : ℝ} (hm : 0 < m) (hmB : m ≤ B) :
    ∃ L, 0 ≤ L ∧ ∀ i x1 y1 z1 x2 y2 z2, |Fw B m i x1 y1 z1 - Fw B m i x2 y2 z2|
      ≤ L * ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|) := by
  obtain ⟨Λ0, h0n, h0⟩ := lip_trunc hm hmB (UL_rhsR (B := B) hm)
  obtain ⟨Λ1, h1n, h1⟩ := lip_trunc hm hmB (UL_rhsOm (B := B) hm)
  obtain ⟨Λ2, h2n, h2⟩ := lip_trunc hm hmB (UL_rhsW (B := B) hm)
  refine ⟨Λ0 + Λ1 + Λ2, by linarith, fun i x1 y1 z1 x2 y2 z2 => ?_⟩
  have hp := toPt_pdist x1 y1 z1 x2 y2 z2
  have hpn := pdist_nonneg (toPt x1 y1 z1) (toPt x2 y2 z2)
  have lift : ∀ Λ : ℝ, 0 ≤ Λ → Λ ≤ Λ0 + Λ1 + Λ2 →
      Λ * pdist (toPt x1 y1 z1) (toPt x2 y2 z2)
        ≤ (Λ0 + Λ1 + Λ2) * ∑ j, (|x1 j - x2 j| + |y1 j - y2 j| + |z1 j - z2 j|) :=
    fun Λ ha hb => mul_le_mul hb hp hpn (by linarith)
  fin_cases i
  · show |eR (trunc B m (toPt x1 y1 z1)) - eR (trunc B m (toPt x2 y2 z2))| ≤ _
    exact (h0 _ _).trans (lift Λ0 h0n (by linarith))
  · show |eOm (trunc B m (toPt x1 y1 z1)) - eOm (trunc B m (toPt x2 y2 z2))| ≤ _
    exact (h1 _ _).trans (lift Λ1 h1n (by linarith))
  · show |eW (trunc B m (toPt x1 y1 z1)) - eW (trunc B m (toPt x2 y2 z2))| ≤ _
    exact (h2 _ _).trans (lift Λ2 h2n (by linarith))

/-! ### 特性データ -/

/-- 帽子(v = 0)のデータ -/
noncomputable def phiW : Fin 3 → ℝ → ℝ := ![capR, capOm, capW]

/-- 首(u = 0)のデータ -/
noncomputable def psiW : Fin 3 → ℝ → ℝ := ![fun _ => 1, neckOm, fun _ => 0]

theorem capR_cd : ContDiff ℝ 1 capR :=
  (Real.contDiff_cos.comp (contDiff_id.div_const _)).pow 2

theorem capOm_cd : ContDiff ℝ 1 capOm :=
  (Real.contDiff_cos.comp (contDiff_id.div_const _)).pow 2

theorem capW_cd : ContDiff ℝ 1 capW :=
  Real.contDiff_sin.comp (contDiff_id.div_const _)

theorem neckOm_cd : ContDiff ℝ 1 neckOm :=
  ((Real.contDiff_cosh.comp (contDiff_id.div_const _)).pow 2).inv
    (fun _ => pow_ne_zero 2 (Real.cosh_pos _).ne')

theorem phiW_cd : ∀ i, ContDiff ℝ 1 (phiW i) := by
  intro i
  fin_cases i
  · exact capR_cd
  · exact capOm_cd
  · exact capW_cd

theorem psiW_cd : ∀ i, ContDiff ℝ 1 (psiW i) := by
  intro i
  fin_cases i
  · exact contDiff_const
  · exact neckOm_cd
  · exact contDiff_const

theorem phiW_psiW_corner : ∀ i, phiW i 0 = psiW i 0 := by
  intro i
  fin_cases i
  · show capR 0 = 1
    exact corner_values.1
  · show capOm 0 = neckOm 0
    rw [corner_values.2.1, corner_values.2.2.2]
  · show capW 0 = 0
    exact corner_values.2.2.1

/-! ### 主定理 -/

/-- くさびの局所存在:角の近くの正方形 [0,ε]×[0,ε] の上で、発展方程式・特性データ・C² 級をみたし、
r > 0、Ω > 0 の解がある。 -/
theorem wedge_local_existence :
    ∃ ε > 0, ∃ F : WedgeFields, WedgeEqsOn ε ε F ∧ WedgeDataOn ε ε F
      ∧ C2On ε ε F.r ∧ C2On ε ε F.Om ∧ C2On ε ε F.W
      ∧ ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, 0 < F.r u v ∧ 0 < F.Om u v := by
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 + |deriv capR 0| + |deriv capOm 0| + |deriv neckOm 0| :=
    ⟨_, rfl⟩
  have hB1 := abs_nonneg (deriv capR 0)
  have hB2 := abs_nonneg (deriv capOm 0)
  have hB3 := abs_nonneg (deriv neckOm 0)
  have hm : (0:ℝ) < 1 / 2 := by norm_num
  have hmB : (1:ℝ) / 2 ≤ B := by rw [hBdef]; linarith
  obtain ⟨L, hL, hF⟩ := Fw_lip hm hmB
  obtain ⟨U, Uu, Uv, Uuv, hC, hd1, hd2, heq⟩ := goursat_exists (a := 1) (b := 1)
    zero_le_one zero_le_one hL (Fw B (1 / 2)) hF phiW psiW (fun i => deriv (phiW i))
    (fun i => deriv (psiW i))
    (fun i x => ((phiW_cd i).differentiable le_rfl x).hasDerivAt)
    (fun i x => ((psiW_cd i).differentiable le_rfl x).hasDerivAt)
    (fun i => (phiW_cd i).continuous_deriv le_rfl)
    (fun i => (psiW_cd i).continuous_deriv le_rfl)
    phiW_psiW_corner
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
  have cu : ∀ i u, Uu i u 0 = deriv (phiW i) u := fun i u => by
    rw [← eDu]
    show deriv (fun t => U i t 0) u = _
    rw [show (fun t => U i t 0) = phiW i from funext (hd1 i)]
  have cv : ∀ i v, Uv i 0 v = deriv (psiW i) v := fun i v => by
    rw [← eDv]
    show deriv (fun s => U i 0 s) v = _
    rw [show (fun s => U i 0 s) = psiW i from funext (hd2 i)]
  have k0 : U 0 0 0 = 1 := (hd1 0 0).trans corner_values.1
  have k1 : U 1 0 0 = 1 := (hd1 1 0).trans corner_values.2.1
  have k2 : U 2 0 0 = 0 := (hd1 2 0).trans corner_values.2.2.1
  have k3 : Uu 0 0 0 = deriv capR 0 := cu 0 0
  have k4 : Uv 0 0 0 = 0 := by rw [cv 0 0]; exact deriv_const 0 (1:ℝ)
  have k5 : Uu 1 0 0 = deriv capOm 0 := cu 1 0
  have k6 : Uv 1 0 0 = deriv neckOm 0 := cv 1 0
  -- 角の近くでは切り落としが効かない
  let S : ℝ × ℝ → ℝ := fun q =>
    |U 0 q.1 q.2 - 1| + |U 1 q.1 q.2 - 1| + |U 2 q.1 q.2| + |Uu 0 q.1 q.2 - deriv capR 0|
      + |Uv 0 q.1 q.2| + |Uu 1 q.1 q.2 - deriv capOm 0| + |Uv 1 q.1 q.2 - deriv neckOm 0|
  have hS : Continuous S :=
    (((((((hC 0).cont.sub continuous_const).abs.add ((hC 1).cont.sub continuous_const).abs).add
      (hC 2).cont.abs).add ((hC 0).cont_u.sub continuous_const).abs).add (hC 0).cont_v.abs).add
      ((hC 1).cont_u.sub continuous_const).abs).add ((hC 1).cont_v.sub continuous_const).abs
  have hS0 : S (0, 0) = 0 := by
    show |U 0 0 0 - 1| + |U 1 0 0 - 1| + |U 2 0 0| + |Uu 0 0 0 - deriv capR 0|
      + |Uv 0 0 0| + |Uu 1 0 0 - deriv capOm 0| + |Uv 1 0 0 - deriv neckOm 0| = 0
    rw [k0, k1, k2, k3, k4, k5, k6]
    simp
  obtain ⟨δ, hδ, hδS⟩ := Metric.continuous_iff.mp hS (0, 0) (1 / 2) (by norm_num)
  refine ⟨min (δ / 2) 1, lt_min (by linarith) one_pos, ⟨U 0, U 1, U 2⟩, ?_⟩
  have hsmall : ∀ u ∈ Icc (0:ℝ) (min (δ / 2) 1), ∀ v ∈ Icc (0:ℝ) (min (δ / 2) 1), S (u, v) < 1 / 2 := by
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
      trunc B (1 / 2) (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))
        = toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v)
      ∧ 1 / 2 < U 0 u v ∧ 1 / 2 < U 1 u v := by
    intro u hu v hv
    have hs := hsmall u hu v hv
    have a1 := abs_nonneg (U 0 u v - 1)
    have a2 := abs_nonneg (U 1 u v - 1)
    have a3 := abs_nonneg (U 2 u v)
    have a4 := abs_nonneg (Uu 0 u v - deriv capR 0)
    have a5 := abs_nonneg (Uv 0 u v)
    have a6 := abs_nonneg (Uu 1 u v - deriv capOm 0)
    have a7 := abs_nonneg (Uv 1 u v - deriv neckOm 0)
    have s : |U 0 u v - 1| + |U 1 u v - 1| + |U 2 u v| + |Uu 0 u v - deriv capR 0|
        + |Uv 0 u v| + |Uu 1 u v - deriv capOm 0| + |Uv 1 u v - deriv neckOm 0| < 1 / 2 := hs
    have b1 : |U 0 u v - 1| < 1 / 2 := by linarith
    have b2 : |U 1 u v - 1| < 1 / 2 := by linarith
    have b3 : |U 2 u v| < 1 / 2 := by linarith
    have b4 : |Uu 0 u v - deriv capR 0| < 1 / 2 := by linarith
    have b5 : |Uv 0 u v| < 1 / 2 := by linarith
    have b6 : |Uu 1 u v - deriv capOm 0| < 1 / 2 := by linarith
    have b7 : |Uv 1 u v - deriv neckOm 0| < 1 / 2 := by linarith
    rw [abs_lt] at b1 b2
    have t4 : |Uu 0 u v| ≤ B := by
      have := abs_sub_abs_le_abs_sub (Uu 0 u v) (deriv capR 0)
      rw [hBdef]; linarith
    have t6 : |Uu 1 u v| ≤ B := by
      have := abs_sub_abs_le_abs_sub (Uu 1 u v) (deriv capOm 0)
      rw [hBdef]; linarith
    have t7 : |Uv 1 u v| ≤ B := by
      have := abs_sub_abs_le_abs_sub (Uv 1 u v) (deriv neckOm 0)
      rw [hBdef]; linarith
    have hB2' : 2 ≤ B := by rw [hBdef]; linarith
    refine ⟨trunc_of (p := toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, by linarith [b1.1], by linarith [b2.1]⟩
    · show 1 / 2 ≤ U 1 u v
      linarith [b2.1]
    · show U 1 u v ≤ B
      linarith [b2.2]
    · show |U 2 u v| ≤ B
      linarith
    · exact t4
    · show |Uv 0 u v| ≤ B
      linarith
    · show 1 / 2 ≤ U 0 u v
      linarith [b1.1]
    · show U 0 u v ≤ B
      linarith [b1.2]
    · exact t6
    · exact t7
  refine ⟨fun u hu v hv => ?_, ⟨fun u _ => ?_, fun v _ => ?_⟩, ?_, ?_, ?_, fun u hu v hv => ?_⟩
  · -- 発展方程式
    obtain ⟨hp, _, _⟩ := hpt u hu v hv
    have q0 : Uuv 0 u v = rhsR (U 1 u v) (U 2 u v) (Uu 0 u v) (Uv 0 u v) (U 0 u v) := by
      rw [heq 0 u (hsub u hu) v (hsub v hv)]
      show eR (trunc B (1 / 2) (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v)))
        = _
      exact (congrArg eR hp).trans rfl
    have q1 : Uuv 1 u v = rhsOm (U 1 u v) (Uu 1 u v) (Uv 1 u v)
        (rhsR (U 1 u v) (U 2 u v) (Uu 0 u v) (Uv 0 u v) (U 0 u v)) (U 0 u v) (U 2 u v) := by
      rw [heq 1 u (hsub u hu) v (hsub v hv)]
      show eOm (trunc B (1 / 2) (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v)))
        = _
      exact (congrArg eOm hp).trans rfl
    have q2 : Uuv 2 u v = rhsW (U 1 u v) (U 2 u v) (U 0 u v) := by
      rw [heq 2 u (hsub u hu) v (hsub v hv)]
      show eW (trunc B (1 / 2) (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v)))
        = _
      exact (congrArg eW hp).trans rfl
    show Duv (U 0) u v = rhsR (U 1 u v) (U 2 u v) (Du (U 0) u v) (Dv (U 0) u v) (U 0 u v)
      ∧ Duv (U 1) u v
          = rhsOm (U 1 u v) (Du (U 1) u v) (Dv (U 1) u v) (Duv (U 0) u v) (U 0 u v) (U 2 u v)
      ∧ Duv (U 2) u v = rhsW (U 1 u v) (U 2 u v) (U 0 u v)
    rw [eDuv, eDuv, eDuv, eDu, eDu, eDv, eDv]
    exact ⟨q0, by rw [q1, q0], q2⟩
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
    exact ⟨by linarith, by linarith⟩

/-- くさびの局所適切性(存在と一意性):角の近くの正方形の上で、r > 0、Ω > 0 の C² 解がちょうど一つある。 -/
theorem wedge_local_wellposed :
    ∃ ε > 0, ∃ F : WedgeFields, (WedgeEqsOn ε ε F ∧ WedgeDataOn ε ε F
      ∧ C2On ε ε F.r ∧ C2On ε ε F.Om ∧ C2On ε ε F.W
      ∧ ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, 0 < F.r u v ∧ 0 < F.Om u v)
      ∧ ∀ G : WedgeFields, WedgeEqsOn ε ε G → WedgeDataOn ε ε G
        → C2On ε ε G.r → C2On ε ε G.Om → C2On ε ε G.W
        → (∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε, 0 < G.r u v ∧ 0 < G.Om u v)
        → ∀ u ∈ Icc (0:ℝ) ε, ∀ v ∈ Icc (0:ℝ) ε,
          G.r u v = F.r u v ∧ G.Om u v = F.Om u v ∧ G.W u v = F.W u v := by
  obtain ⟨ε, hε, F, eF, dF, rFr, rFO, rFW, pF⟩ := wedge_local_existence
  refine ⟨ε, hε, F, ⟨eF, dF, rFr, rFO, rFW, pF⟩, fun G eG dG rGr rGO rGW pG => ?_⟩
  exact wedge_uniqueness_of_pos G F eG eF dG dF rGr rGO rGW rFr rFO rFW
    (fun u hu v hv => ⟨(pG u hu v hv).1, (pG u hu v hv).2, (pF u hu v hv).1, (pF u hu v hv).2⟩)

end CFT.WedgeExist
