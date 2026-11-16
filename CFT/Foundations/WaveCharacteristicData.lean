import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 4-3（線形波動の特性初期値問題）の存在半分：
  2本の特性面上のデータ p（v = v₀ 上）、q（u = u₀ 上）が角で両立すれば
  （q v₀ = p u₀）、φ(u, v) = p u + q v − p u₀ は波動方程式 φ_uv = 0 を満たし、
  両方のデータを再現する。一意性は 4-3 の残り（平均値定理による定数性）。
-/

namespace CFT.WaveData

/-- 特性データから作った候補関数。 -/
noncomputable def waveFromData (p q : ℝ → ℝ) (u₀ : ℝ) (u v : ℝ) : ℝ :=
  p u + q v - p u₀

/-- 候補は波動方程式 φ_uv = 0 を満たす（q の微分可能性だけでよい）。 -/
theorem waveFromData_mixedDeriv_zero {p q : ℝ → ℝ} (hq : Differentiable ℝ q)
    (u₀ u v : ℝ) :
    deriv (fun u' => deriv (fun v' => waveFromData p q u₀ u' v') v) u = 0 := by
  have hconst : (fun u' => deriv (fun v' => waveFromData p q u₀ u' v') v)
      = fun _ => deriv q v := by
    funext u'
    have hderiv : HasDerivAt (fun v' => waveFromData p q u₀ u' v') (deriv q v) v := by
      have hsum := ((hasDerivAt_const v (p u')).add (hq v).hasDerivAt).sub_const (p u₀)
      simpa only [waveFromData, zero_add] using hsum
    rw [hderiv.deriv]
  rw [hconst]
  exact deriv_const u (deriv q v)

/-- v = v₀ 上でデータを再現する（角の両立条件 q v₀ = p u₀ を使う）。 -/
theorem waveFromData_on_v {p q : ℝ → ℝ} {u₀ v₀ : ℝ} (hcorner : q v₀ = p u₀)
    (u : ℝ) :
    waveFromData p q u₀ u v₀ = p u := by
  simp only [waveFromData, hcorner]
  ring

/-- u = u₀ 上でデータを再現する。 -/
theorem waveFromData_on_u {p q : ℝ → ℝ} (u₀ : ℝ) (v : ℝ) :
    waveFromData p q u₀ u₀ v = q v := by
  simp only [waveFromData]
  ring

end CFT.WaveData
