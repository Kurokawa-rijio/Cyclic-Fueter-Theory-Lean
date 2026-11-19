/-
  9-3 極限（エクストリーマル）極限の残り：喉の固有距離そのものの発散

  極端 RN（r₊ = r₋）では計量関数 f(r) = (r − r₊)²/r² が二重ゼロを持ち、
  t 一定の動径固有距離は
    L(ε) = ∫_{r₊+ε}^{r₊+R} dr / √f(r) = ∫_{r₊+ε}^{r₊+R} r/(r − r₊) dr
  で与えられる。被積分関数は 1 + r₊/(r − r₊) と書け、原始関数は
  r + r₊·log(r − r₊) なので
    L(ε) = (R − ε) + r₊·(log R − log ε)。
  ε → 0⁺ で −r₊·log ε → +∞ となり、喉の固有距離は発散する（無限の喉）。
  これが 9-3 の残り「喉の固有距離そのものの発散」の極端 RN 側の証明であり、
  12-8 (b) の「二重ゼロ ↔ 極端・T = 0・無限の喉」の「無限の喉」の部分を
  固有距離の形で裏づける。
  残り：非極端の場合の固有距離の有限性（f が一次ゼロなら 1/√f は可積分）
  と、くさび EYM 系の形での喉への接続（12-8 (b) の本体）。
-/
import CFT.Quantum.RNExtremalDoubleZero
import Mathlib.Analysis.SpecialFunctions.Integrals

open Real Filter Topology intervalIntegral

namespace CFT.ExtremalThroat

/-- 極端の場合の √f：r > r₊ では √(f(r)) = (r − r₊)/r。 -/
theorem extremal_sqrt_rnF (rp r : ℝ) (hp : 0 < rp) (hr : rp < r) :
    Real.sqrt (CFT.RNExtremalZero.rnF rp rp r) = (r - rp) / r := by
  rw [CFT.RNExtremalZero.rnF_extremal, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (by linarith : (0:ℝ) ≤ r - rp), Real.sqrt_sq (by linarith : (0:ℝ) ≤ r)]

/-- 固有距離の被積分関数：1/√f(r) = r/(r − r₊)（r > r₊）。 -/
theorem properLength_integrand (rp r : ℝ) (hp : 0 < rp) (hr : rp < r) :
    (Real.sqrt (CFT.RNExtremalZero.rnF rp rp r))⁻¹ = r / (r - rp) := by
  rw [extremal_sqrt_rnF rp r hp hr, inv_div]

/-- 喉の長さの積分：∫_{r₊+ε}^{r₊+R} r/(r − r₊) dr = (R − ε) + r₊·(log R − log ε)。 -/
theorem throatLength_integral (rp ε R : ℝ) (hp : 0 < rp) (hε : 0 < ε) (hεR : ε < R) :
    ∫ x in (rp + ε)..(rp + R), x / (x - rp)
      = (R - ε) + rp * (Real.log R - Real.log ε) := by
  have hab : rp + ε ≤ rp + R := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (rp + ε) (rp + R),
      HasDerivAt (fun x => x + rp * Real.log (x - rp)) (x / (x - rp)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxrp : 0 < x - rp := by linarith [hx.1]
    have hne : x - rp ≠ 0 := ne_of_gt hxrp
    have hlog : HasDerivAt (fun x => Real.log (x - rp)) (x - rp)⁻¹ x := by
      have h := (Real.hasDerivAt_log hne).comp x ((hasDerivAt_id x).sub_const rp)
      simpa using h
    have h2 : HasDerivAt (fun x => x + rp * Real.log (x - rp))
        (1 + rp * (x - rp)⁻¹) x := by
      have h := (hasDerivAt_id x).add (hlog.const_mul rp)
      simpa only [id_eq] using h
    have h3 : (1 : ℝ) + rp * (x - rp)⁻¹ = x / (x - rp) := by
      rw [eq_div_iff hne, add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one]
      ring
    rw [h3] at h2
    exact h2
  have hint : IntervalIntegrable (fun x => x / (x - rp)) MeasureTheory.volume (rp + ε) (rp + R) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id (continuousOn_id.sub continuousOn_const)
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    show x - rp ≠ 0
    exact ne_of_gt (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have e1 : rp + R - rp = R := by ring
  have e2 : rp + ε - rp = ε := by ring
  rw [e1, e2]
  ring

/-- 喉の長さは正（ε < R のとき）。 -/
theorem throatLength_pos (rp ε R : ℝ) (hp : 0 < rp) (hε : 0 < ε) (hεR : ε < R) :
    0 < ∫ x in (rp + ε)..(rp + R), x / (x - rp) := by
  rw [throatLength_integral rp ε R hp hε hεR]
  have hlog : Real.log ε < Real.log R := Real.log_lt_log hε hεR
  have h2 : 0 < rp * (Real.log R - Real.log ε) := mul_pos hp (by linarith)
  linarith

/-- 喉の長さは ε → 0⁺ で +∞ に発散する。 -/
theorem throatLength_tendsto_atTop (rp R : ℝ) (hp : 0 < rp) (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R), x / (x - rp)) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun ε : ℝ => Real.log ε) (𝓝[>] 0) atBot := by
    have h := tendsto_log_nhdsWithin_zero.mono_left
      (nhdsWithin_mono 0 (fun x (hx : 0 < x) => hx.ne'))
    exact h
  have hneg : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp hlog
  have hmain : Tendsto (fun ε : ℝ => rp * -Real.log ε) (𝓝[>] 0) atTop :=
    hneg.const_mul_atTop hp
  have hbounded : Tendsto (fun ε : ℝ => (R - ε) + rp * Real.log R) (𝓝[>] 0)
      (𝓝 (R + rp * Real.log R)) := by
    have h1 : Tendsto (fun ε : ℝ => R - ε) (𝓝[>] 0) (𝓝 R) := by
      have hcont : Continuous (fun ε : ℝ => R - ε) := by fun_prop
      have h := (hcont.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h
    exact h1.add tendsto_const_nhds
  have hsum : Tendsto (fun ε : ℝ => rp * -Real.log ε + ((R - ε) + rp * Real.log R))
      (𝓝[>] 0) atTop := hmain.atTop_add hbounded
  have heq : (fun ε : ℝ => rp * -Real.log ε + ((R - ε) + rp * Real.log R))
      =ᶠ[𝓝[>] 0] (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R), x / (x - rp)) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    rw [throatLength_integral rp ε R hp hε.1 hε.2]
    ring
  exact hsum.congr' heq

/-- 固有距離の形での喉の長さ：∫_{r₊+ε}^{r₊+R} dr/√f(r) = (R − ε) + r₊·(log R − log ε)。 -/
theorem throat_properLength_integral (rp ε R : ℝ) (hp : 0 < rp) (hε : 0 < ε) (hεR : ε < R) :
    ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rp x))⁻¹
      = (R - ε) + rp * (Real.log R - Real.log ε) := by
  calc ∫ x in (rp + ε)..(rp + R), (Real.sqrt (CFT.RNExtremalZero.rnF rp rp x))⁻¹
      = ∫ x in (rp + ε)..(rp + R), x / (x - rp) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hab : rp + ε ≤ rp + R := by linarith
        rw [Set.uIcc_of_le hab] at hx
        exact properLength_integrand rp x hp (by linarith [hx.1])
    _ = (R - ε) + rp * (Real.log R - Real.log ε) :=
        throatLength_integral rp ε R hp hε hεR

/-- まとめ：極端 RN の喉の固有距離は ε → 0⁺ で +∞ に発散する（無限の喉）。 -/
theorem extremal_throat_infinite (rp R : ℝ) (hp : 0 < rp) (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R),
      (Real.sqrt (CFT.RNExtremalZero.rnF rp rp x))⁻¹) (𝓝[>] 0) atTop := by
  have heq : (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R), x / (x - rp))
      =ᶠ[𝓝[>] 0] (fun ε : ℝ => ∫ x in (rp + ε)..(rp + R),
        (Real.sqrt (CFT.RNExtremalZero.rnF rp rp x))⁻¹) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    rw [throatLength_integral rp ε R hp hε.1 hε.2,
      throat_properLength_integral rp ε R hp hε.1 hε.2]
  exact (throatLength_tendsto_atTop rp R hp hR).congr' heq

end CFT.ExtremalThroat
