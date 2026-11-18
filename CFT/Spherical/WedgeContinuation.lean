/-
  命題集 `LEAN_GAP_TREES.md` 4-15(大域拡張の障害)の同定(2026-11-18)

  任意の長方形 [0,a]×[0,b] と定数 0 < m ≤ B について、帽子と首のデータをもつ C² 級の場 F が
  長方形全体にあり、各点 (u,v) で 7 個の量 (Ω, W, r_u, r_v, r, Ω_u, Ω_v) が箱
    m ≤ Ω ≤ B、m ≤ r ≤ B、|W|, |r_u|, |r_v|, |Ω_u|, |Ω_v| ≤ B
  の中にあれば、その点でくさびの 3 本の発展方程式をみたす(`wedge_continuation`)。
  4-7 の一意性と合わせると、くさびの解を延ばすことを妨げるのは「この箱から出ること」、
  つまり r → 0、Ω → 0、または場と 1 階微分の発散だけである。
  証明は 4-9 と同じく、切り落とした系を長方形全体で解き(`goursat_exists`)、箱の中では切り落としが効かないことを使う。
-/
import CFT.Spherical.WedgeExistence

open Real Set CFT.Wedge CFT.CharUniqueness CFT.Goursat CFT.WedgeUniq CFT.WedgeExist

namespace CFT.WedgeCont

/-- 切り落としの箱の中 -/
def Inside (B m : ℝ) (p : Pt) : Prop :=
  m ≤ p.Om ∧ p.Om ≤ B ∧ |p.W| ≤ B ∧ |p.ru| ≤ B ∧ |p.rv| ≤ B ∧ m ≤ p.r ∧ p.r ≤ B
    ∧ |p.Ou| ≤ B ∧ |p.Ov| ≤ B

theorem trunc_of_inside {B m : ℝ} {p : Pt} (h : Inside B m p) : trunc B m p = p :=
  trunc_of h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

/-- 大域拡張の障害の同定:長方形全体に C² の場があり、箱の中の点では発展方程式をみたす -/
theorem wedge_continuation {a b B m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 < m) (hmB : m ≤ B) :
    ∃ F : WedgeFields, WedgeDataOn a b F ∧ C2On a b F.r ∧ C2On a b F.Om ∧ C2On a b F.W
      ∧ ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, Inside B m (ptOf F u v) →
        Duv F.r u v = rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v)
        ∧ Duv F.Om u v
            = rhsOm (F.Om u v) (Du F.Om u v) (Dv F.Om u v) (Duv F.r u v) (F.r u v) (F.W u v)
        ∧ Duv F.W u v = rhsW (F.Om u v) (F.W u v) (F.r u v) := by
  obtain ⟨L, hL, hF⟩ := Fw_lip hm hmB
  obtain ⟨U, Uu, Uv, Uuv, hC, hd1, hd2, heq⟩ := goursat_exists (a := a) (b := b)
    ha hb hL (Fw B m) hF phiW psiW (fun i => deriv (phiW i)) (fun i => deriv (psiW i))
    (fun i x => ((phiW_cd i).differentiable le_rfl x).hasDerivAt)
    (fun i x => ((psiW_cd i).differentiable le_rfl x).hasDerivAt)
    (fun i => (phiW_cd i).continuous_deriv le_rfl)
    (fun i => (psiW_cd i).continuous_deriv le_rfl)
    phiW_psiW_corner
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
  refine ⟨⟨U 0, U 1, U 2⟩, ⟨fun u _ => ⟨hd1 0 u, hd1 1 u, hd1 2 u⟩,
    fun v _ => ⟨hd2 0 v, hd2 1 v, hd2 2 v⟩⟩, ?_, ?_, ?_, fun u hu v hv hin => ?_⟩
  · show C2Data _ _ (U 0) (Du (U 0)) (Dv (U 0)) (Duv (U 0))
    rw [eDu, eDv, eDuv]
    exact (hC 0).toC2Data _ _
  · show C2Data _ _ (U 1) (Du (U 1)) (Dv (U 1)) (Duv (U 1))
    rw [eDu, eDv, eDuv]
    exact (hC 1).toC2Data _ _
  · show C2Data _ _ (U 2) (Du (U 2)) (Dv (U 2)) (Duv (U 2))
    rw [eDu, eDv, eDuv]
    exact (hC 2).toC2Data _ _
  · have hp : trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))
        = toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v) := by
      apply trunc_of_inside
      have e : ptOf ⟨U 0, U 1, U 2⟩ u v
          = toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v) := by
        show (⟨U 1 u v, U 2 u v, Du (U 0) u v, Dv (U 0) u v, U 0 u v, Du (U 1) u v,
          Dv (U 1) u v⟩ : Pt) = _
        (rw [eDu, eDv]) <;> rfl
      rw [← e]
      exact hin
    have q0 : Uuv 0 u v = rhsR (U 1 u v) (U 2 u v) (Uu 0 u v) (Uv 0 u v) (U 0 u v) := by
      rw [heq 0 u hu v hv]
      show eR (trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))) = _
      exact (congrArg eR hp).trans rfl
    have q1 : Uuv 1 u v = rhsOm (U 1 u v) (Uu 1 u v) (Uv 1 u v)
        (rhsR (U 1 u v) (U 2 u v) (Uu 0 u v) (Uv 0 u v) (U 0 u v)) (U 0 u v) (U 2 u v) := by
      rw [heq 1 u hu v hv]
      show eOm (trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))) = _
      exact (congrArg eOm hp).trans rfl
    have q2 : Uuv 2 u v = rhsW (U 1 u v) (U 2 u v) (U 0 u v) := by
      rw [heq 2 u hu v hv]
      show eW (trunc B m (toPt (fun j => U j u v) (fun j => Uu j u v) (fun j => Uv j u v))) = _
      exact (congrArg eW hp).trans rfl
    show Duv (U 0) u v = rhsR (U 1 u v) (U 2 u v) (Du (U 0) u v) (Dv (U 0) u v) (U 0 u v)
      ∧ Duv (U 1) u v
          = rhsOm (U 1 u v) (Du (U 1) u v) (Dv (U 1) u v) (Duv (U 0) u v) (U 0 u v) (U 2 u v)
      ∧ Duv (U 2) u v = rhsW (U 1 u v) (U 2 u v) (U 0 u v)
    rw [eDuv, eDuv, eDuv, eDu, eDu, eDv, eDv]
    exact ⟨q0, by rw [q1, q0], q2⟩

end CFT.WedgeCont
