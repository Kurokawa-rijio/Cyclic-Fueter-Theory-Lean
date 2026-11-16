import CFT.Quantum.MinisuperspaceNeckAction

/-!
  命題集 `LEAN_GAP_TREES.md` 1-2a（2026-11-16、demos/Gap12a.lean から取り込み）：
  ミニスーパースペース Lagrangian `CFT.Mini.Lfun` の残り2つの偏微分 ∂L/∂a、∂L/∂b。
  ツリー内には既に `L_ad`（∂L/∂ȧ）、`L_bd`（∂L/∂ḃ）、`L_N`（∂L/∂N = −Hfun）があり、
  本モジュールで a・b 方向が揃う。Euler–Lagrange 方程式の組み立ては
  `CFT/Quantum/MinisuperspaceEulerLagrange.lean`。
-/

open CFT.Mini

namespace CFT.Mini

/-- ∂L/∂a = −cḃ²/N + cN(1 − ℓ²/b²) -/
theorem L_a (a b ad bd N c l : ℝ) :
    HasDerivAt (fun x => Lfun x b ad bd N c l)
      (-(c * bd ^ 2) / N + c * N * (1 - l ^ 2 / b ^ 2)) a := by
  have hf : (fun x => Lfun x b ad bd N c l) =
      fun x => (-(c * bd ^ 2) / N + c * N * (1 - l ^ 2 / b ^ 2)) * x
        + c * (-(2 * b * ad * bd) / N) := by
    funext x; simp only [Lfun]; ring
  rw [hf]
  simpa using ((hasDerivAt_id a).const_mul (-(c * bd ^ 2) / N + c * N * (1 - l ^ 2 / b ^ 2))).add_const
    (c * (-(2 * b * ad * bd) / N))

/-- ∂L/∂b = −2cȧḃ/N + 2cNaℓ²/b³ -/
theorem L_b (a b ad bd N c l : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun y => Lfun a y ad bd N c l)
      (-2 * c * ad * bd / N + 2 * c * N * a * l ^ 2 / b ^ 3) b := by
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(b ^ 2)⁻¹) b := hasDerivAt_inv hb
  have hinv2 : HasDerivAt (fun y : ℝ => (y⁻¹) ^ 2) (2 * b⁻¹ * (-(b ^ 2)⁻¹)) b := by
    simpa using hinv.pow 2
  have h := (((hasDerivAt_id b).const_mul (-(2 * c * ad * bd) / N)).add
    (hinv2.const_mul (-(c * N * a * l ^ 2)))).add_const (c * (-(a * bd ^ 2) / N + N * a))
  have hf : (fun y => Lfun a y ad bd N c l) =
      fun y => (-(2 * c * ad * bd) / N) * id y + (-(c * N * a * l ^ 2)) * (id y⁻¹) ^ 2
        + c * (-(a * bd ^ 2) / N + N * a) := by
    funext y; simp only [Lfun, id]; ring
  rw [hf]
  convert h using 1
  field_simp
  ring

end CFT.Mini
