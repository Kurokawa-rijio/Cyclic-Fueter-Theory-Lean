import CFT.Foundations.WaveCharacteristicData

/-!
  命題集 `LEAN_GAP_TREES.md` 4-3（線形波動方程式の特性初期値問題）の一意性半分：
  混合微分 φ_uv = 0（と v 方向の微分可能性）だけから、任意の解は特性データで
  決まる：φ(u, v) = φ(u₀, v) + φ(u, v₀) − φ(u₀, v₀)。両特性面上でデータが
  0 なら解は恒等的に 0。Clairaut（混合偏微分の交換）は使わない：
  固定した v に対し u ↦ ∂_v φ(u, v) は微分 0 なので平均値定理で定数、
  固定した u に対し v ↦ φ(u, v) − φ(u₀, v) も微分 0 なので定数。
  存在半分は `CFT.Foundations.WaveCharacteristicData`（明示解 φ = p u + q v − p u₀）。
  これで 4-3 は存在・一意性ともに閉じる。
-/

namespace CFT.WaveUniqueness

open CFT.WaveData

/-- 混合微分が 0 なら、v 方向の微分 ∂_v φ(u, v) は u に依らない
    （平均値定理 `is_const_of_deriv_eq_zero`）。 -/
theorem vderiv_const_of_mixedDeriv_zero {φ : ℝ → ℝ → ℝ}
    (hk : ∀ v, Differentiable ℝ (fun u' => deriv (fun v' => φ u' v') v))
    (hmix : ∀ u v, deriv (fun u' => deriv (fun v' => φ u' v') v) u = 0)
    (u₀ u v : ℝ) :
    deriv (fun v' => φ u v') v = deriv (fun v' => φ u₀ v') v :=
  is_const_of_deriv_eq_zero (hk v) (fun u' => hmix u' v) u u₀

/-- 一意性の核：混合微分 0 の関数は、2 本の特性面上の値の和から角の値を
    引いたものに等しい。 -/
theorem wave_decomposition {φ : ℝ → ℝ → ℝ}
    (hφv : ∀ u, Differentiable ℝ (fun v' => φ u v'))
    (hk : ∀ v, Differentiable ℝ (fun u' => deriv (fun v' => φ u' v') v))
    (hmix : ∀ u v, deriv (fun u' => deriv (fun v' => φ u' v') v) u = 0)
    (u₀ v₀ u v : ℝ) :
    φ u v = φ u₀ v + φ u v₀ - φ u₀ v₀ := by
  have hF : ∀ t, deriv (fun t' => φ u t' - φ u₀ t') t = 0 := by
    intro t
    rw [deriv_sub ((hφv u) t) ((hφv u₀) t),
      vderiv_const_of_mixedDeriv_zero hk hmix u₀ u t]
    exact sub_self _
  have hconst := is_const_of_deriv_eq_zero ((hφv u).sub (hφv u₀)) hF v v₀
  linarith

/-- 両特性面上でデータが 0 なら解は恒等的に 0（一意性）。 -/
theorem wave_eq_zero_of_data_zero {φ : ℝ → ℝ → ℝ} (u₀ v₀ : ℝ)
    (hφv : ∀ u, Differentiable ℝ (fun v' => φ u v'))
    (hk : ∀ v, Differentiable ℝ (fun u' => deriv (fun v' => φ u' v') v))
    (hmix : ∀ u v, deriv (fun u' => deriv (fun v' => φ u' v') v) u = 0)
    (hdata_v : ∀ u, φ u v₀ = 0) (hdata_u : ∀ v, φ u₀ v = 0)
    (u v : ℝ) : φ u v = 0 := by
  have h := wave_decomposition hφv hk hmix u₀ v₀ u v
  rw [hdata_v u, hdata_u v, hdata_u v₀] at h
  simpa using h

/-- 任意の解は、自分の特性データから作った明示解 `waveFromData` に等しい
    （存在半分との接続：4-3 の解は一意）。 -/
theorem wave_eq_waveFromData {φ : ℝ → ℝ → ℝ}
    (hφv : ∀ u, Differentiable ℝ (fun v' => φ u v'))
    (hk : ∀ v, Differentiable ℝ (fun u' => deriv (fun v' => φ u' v') v))
    (hmix : ∀ u v, deriv (fun u' => deriv (fun v' => φ u' v') v) u = 0)
    (u₀ v₀ u v : ℝ) :
    φ u v = waveFromData (fun t => φ t v₀) (fun t => φ u₀ t) u₀ u v := by
  have h := wave_decomposition hφv hk hmix u₀ v₀ u v
  simp only [waveFromData]
  linarith

end CFT.WaveUniqueness
