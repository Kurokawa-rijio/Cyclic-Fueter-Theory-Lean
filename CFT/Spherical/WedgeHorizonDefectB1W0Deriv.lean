/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **B1|_{W=0} の四次式 P の導関数による零点位置の精密化**。
  前段（`WedgeHorizonDefectB1W0Zero`）で四次式
    P(r) = −3r⁴ + r²r₊² + 9r² − 10r·r₊ + 3r₊²
  の端点値と中間値の定理による零点の存在が閉じた。ここでは導関数
    P′(r) = −12r³ + 2r·r₊² + 18r − 10r₊ = −2·g(r),
    g(r) = 6r³ − (r₊²+9)r + 5r₊
  を導入する。g′(r) = 18r² − (r₊²+9) は臨界点
    r* = √((r₊²+9)/18)
  で符号が変わり、g は (0, r*] 上で狭義単調減少、[r*, ∞) 上で狭義
  単調増加する。臨界点での値は
    g(r*) = 5r₊ − (2/3)(r₊²+9)·r*
  で、g(r₊) = r₊(5r₊²−4) とあわせて、P′ の符号変化の位置を絞る
  材料になる。g(r*) = 0 の閾値は r₊ ≈ 0.9912（方程式
  2(r₊²+9)³ = 2025r₊² の解）で、きれいな数ではないため、この段では
  臨界点の値の公式までとし、閾値の確定は次の段に残す。式の確認は
  sympy による明示計算でも照合済み（`/tmp/check_b1deriv.py`）。
-/
import CFT.Spherical.WedgeHorizonDefectB1W0Zero

open Real Set Filter Topology
open CFT.WedgeDefectB1W0Zero

namespace CFT.WedgeDefectB1W0Deriv

/-- P′(r) = −2g(r) の三次式 g(r) = 6r³ − (r₊²+9)r + 5r₊。 -/
noncomputable def defectCubicB1W0Deriv (r rp : ℝ) : ℝ :=
  6 * r ^ 3 - (rp ^ 2 + 9) * r + 5 * rp

/-- g の臨界点 r* = √((r₊²+9)/18)。g′(r*) = 0。 -/
noncomputable def defectQuarticCritPoint (rp : ℝ) : ℝ :=
  Real.sqrt ((rp ^ 2 + 9) / 18)

/-- 四次式 P の導関数（`HasDerivAt` 版）。 -/
theorem defectQuarticB1W0_hasDerivAt {r rp : ℝ} :
    HasDerivAt (fun r => defectQuarticB1W0 r rp)
      (-12 * r ^ 3 + 2 * r * rp ^ 2 + 18 * r - 10 * rp) r := by
  have heq : (fun r => defectQuarticB1W0 r rp)
      = (fun x => -3 * x ^ 4 + x ^ 2 * rp ^ 2 + 9 * x ^ 2 - (10 * rp) * x
        + 3 * rp ^ 2) := by
    funext x
    rw [defectQuarticB1W0_eq]
    ring
  rw [heq]
  have h1 := (hasDerivAt_pow 4 r).const_mul (-3)
  have h2 := (hasDerivAt_pow 2 r).mul_const (rp ^ 2)
  have h3 := (hasDerivAt_pow 2 r).const_mul (9 : ℝ)
  have h4 := (hasDerivAt_id r).const_mul (10 * rp)
  have h5 := hasDerivAt_const r (3 * rp ^ 2)
  have h := (((h1.add h2).add h3).sub h4).add h5
  convert h using 1
  ring

/-- 四次式 P の導関数は −2g。 -/
theorem defectQuarticB1W0_deriv_eq {r rp : ℝ} :
    deriv (fun r => defectQuarticB1W0 r rp) r
      = -2 * defectCubicB1W0Deriv r rp := by
  rw [defectQuarticB1W0_hasDerivAt.deriv]
  unfold defectCubicB1W0Deriv
  ring

/-- 三次式 g の導関数（`HasDerivAt` 版）。 -/
theorem defectCubicB1W0Deriv_hasDerivAt {r rp : ℝ} :
    HasDerivAt (fun r => defectCubicB1W0Deriv r rp)
      (18 * r ^ 2 - (rp ^ 2 + 9)) r := by
  have heq : (fun r => defectCubicB1W0Deriv r rp)
      = (fun x => 6 * x ^ 3 - (rp ^ 2 + 9) * x + 5 * rp) := by
    funext x
    rfl
  rw [heq]
  have h1 := (hasDerivAt_pow 3 r).const_mul (6 : ℝ)
  have h2 := (hasDerivAt_id r).const_mul (rp ^ 2 + 9)
  have h3 := hasDerivAt_const r (5 * rp)
  have h := (h1.sub h2).add h3
  convert h using 1
  ring

/-- 三次式 g の導関数は 18r² − (r₊²+9)。 -/
theorem defectCubicB1W0Deriv_deriv_eq {r rp : ℝ} :
    deriv (fun r => defectCubicB1W0Deriv r rp) r
      = 18 * r ^ 2 - (rp ^ 2 + 9) :=
  defectCubicB1W0Deriv_hasDerivAt.deriv

/-- 三次式 g は連続。 -/
theorem defectCubicB1W0Deriv_continuous {rp : ℝ} :
    Continuous fun r => defectCubicB1W0Deriv r rp := by
  unfold defectCubicB1W0Deriv
  continuity

/-- 臨界点の二乗：r*² = (r₊²+9)/18。 -/
theorem defectQuarticCritPoint_sq {rp : ℝ} :
    (defectQuarticCritPoint rp) ^ 2 = (rp ^ 2 + 9) / 18 := by
  unfold defectQuarticCritPoint
  rw [Real.sq_sqrt]
  positivity

/-- 臨界点は正。 -/
theorem defectQuarticCritPoint_pos {rp : ℝ} :
    0 < defectQuarticCritPoint rp := by
  unfold defectQuarticCritPoint
  apply Real.sqrt_pos.mpr
  positivity

/-- g(0) = 5r₊。 -/
theorem defectCubicB1W0Deriv_at_zero {rp : ℝ} :
    defectCubicB1W0Deriv 0 rp = 5 * rp := by
  unfold defectCubicB1W0Deriv
  ring

/-- g(r₊) = r₊(5r₊²−4)。符号は r₊ と 2/√5 の大小で決まる。 -/
theorem defectCubicB1W0Deriv_at_rp {rp : ℝ} :
    defectCubicB1W0Deriv rp rp = rp * (5 * rp ^ 2 - 4) := by
  unfold defectCubicB1W0Deriv
  ring

/-- P′(r₊) = −2r₊(5r₊²−4)。 -/
theorem defectQuarticB1W0_deriv_at_rp {rp : ℝ} :
    deriv (fun r => defectQuarticB1W0 r rp) rp
      = -2 * rp * (5 * rp ^ 2 - 4) := by
  rw [defectQuarticB1W0_deriv_eq, defectCubicB1W0Deriv_at_rp]
  ring

/-- 臨界点での g の値：g(r*) = 5r₊ − (2/3)(r₊²+9)·r*。 -/
theorem defectCubicB1W0Deriv_at_critPoint {rp : ℝ} :
    defectCubicB1W0Deriv (defectQuarticCritPoint rp) rp
      = 5 * rp - (2 / 3) * (rp ^ 2 + 9) * defectQuarticCritPoint rp := by
  have h2 := defectQuarticCritPoint_sq (rp := rp)
  have h3 : (defectQuarticCritPoint rp) ^ 3
      = defectQuarticCritPoint rp * ((rp ^ 2 + 9) / 18) := by
    linear_combination (defectQuarticCritPoint rp) * h2
  unfold defectCubicB1W0Deriv
  linear_combination 6 * h3

/-- 臨界点での P′ の値。 -/
theorem defectQuarticB1W0_deriv_at_critPoint {rp : ℝ} :
    deriv (fun r => defectQuarticB1W0 r rp) (defectQuarticCritPoint rp)
      = -2 * (5 * rp - (2 / 3) * (rp ^ 2 + 9)
        * defectQuarticCritPoint rp) := by
  rw [defectQuarticB1W0_deriv_eq, defectCubicB1W0Deriv_at_critPoint]

/-- g は (0, r*] 上で狭義単調減少（g′ < 0）。 -/
theorem defectCubicB1W0Deriv_strictAntiOn_Ioc_zero_crit {rp : ℝ} :
    StrictAntiOn (fun r => defectCubicB1W0Deriv r rp)
      (Ioc 0 (defectQuarticCritPoint rp)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (defectQuarticCritPoint rp))
    (defectCubicB1W0Deriv_continuous.continuousOn)
  intro x hx
  rw [interior_Ioc] at hx
  have hc := defectQuarticCritPoint_sq (rp := rp)
  have hxc : x ^ 2 < (defectQuarticCritPoint rp) ^ 2 :=
    (sq_lt_sq₀ hx.1.le defectQuarticCritPoint_pos.le).mpr hx.2
  rw [defectCubicB1W0Deriv_deriv_eq]
  nlinarith [hxc, hc]

/-- g は [r*, ∞) 上で狭義単調増加（g′ > 0）。 -/
theorem defectCubicB1W0Deriv_strictMonoOn_Ici_crit {rp : ℝ} :
    StrictMonoOn (fun r => defectCubicB1W0Deriv r rp)
      (Ici (defectQuarticCritPoint rp)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (defectQuarticCritPoint rp))
    (defectCubicB1W0Deriv_continuous.continuousOn)
  intro x hx
  rw [interior_Ici] at hx
  have hc := defectQuarticCritPoint_sq (rp := rp)
  have hlt : defectQuarticCritPoint rp < x := hx
  have hx0 : (0 : ℝ) ≤ x := (defectQuarticCritPoint_pos.trans hlt).le
  have hxc : (defectQuarticCritPoint rp) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ defectQuarticCritPoint_pos.le hx0).mpr hlt
  rw [defectCubicB1W0Deriv_deriv_eq]
  nlinarith [hxc, hc]

end CFT.WedgeDefectB1W0Deriv
