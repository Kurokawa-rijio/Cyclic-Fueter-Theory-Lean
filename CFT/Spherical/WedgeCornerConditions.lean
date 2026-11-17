import CFT.Spherical.WedgeEYMSystem

/-!
  命題集 `LEAN_GAP_TREES.md` 4-13（角条件の導出と照合）：
  くさび領域の頂点 (0, 0) で、方程式からデータの必要条件（角条件）を導き、
  帽子・首の接続データがそれを満たすことを確認する。
  4-1 で定式化された二重ヌル系（ℓ = 1 規格化）の言葉で述べる。
  接合の章（`CFT.Junction.RealFunctionJunction` の `rj_ruu_corner`）は
  [r_uu] の跳びを抽象的な値で証明しているが、ここでは実際の `WedgeFields` と
  `Du`/`Dv`/`Duv`/`Duu`/`Dvv` 作用素で、方程式そのものから導出する。

  角でのデータ（4-1 の `corner_values`・`corner_capW_slope`・`corner_capR_slope`）：
    r = 1、Ω = 1、W = 0、r_u = 0、r_v = 0、W_u = 1/√2、W_v = 0、Ω_u = 0、Ω_v = 0。
  方程式から導かれる角条件（`WedgeEvolutionEqs`・`WedgeConstraints` を (0,0) で評価）：
    r_uu = −1（C_u から）、r_vv = 0（C_v から）、r_uv = 0、W_uv = 0、Ω_uv = −1。
  照合（帽子・首のデータが角条件を満たす）：
    capR の 2 階微分は −1（= −2 W_u²/r の値と一致）、首の r ≡ 1、W ≡ 0 は C_v を満たす。
  恒等式の定数は sympy による明示計算（`/tmp/check413.py`）でも照合済み。
  解の存在・一意性には触れない（4-3、4-9、4-16 の領分）。
-/

namespace CFT.WedgeCorner

open CFT.Wedge
open Real

/-! ### 角でのデータの微分 -/

/-- 角での場の値（特性データから）。 -/
theorem data_values {F : WedgeFields} (hdata : HasWedgeData F) :
    F.r 0 0 = 1 ∧ F.Om 0 0 = 1 ∧ F.W 0 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [capR] using (hdata.1 0).1
  · simpa [capOm] using (hdata.1 0).2.1
  · simpa [capW] using (hdata.1 0).2.2

/-- 帽子面の u スライスは capR そのもの。 -/
theorem slice_r_cap {F : WedgeFields} (hdata : HasWedgeData F) :
    (fun u' => F.r u' 0) = capR :=
  funext fun u' => (hdata.1 u').1

/-- 帽子面の u スライスは capOm そのもの。 -/
theorem slice_Om_cap {F : WedgeFields} (hdata : HasWedgeData F) :
    (fun u' => F.Om u' 0) = capOm :=
  funext fun u' => (hdata.1 u').2.1

/-- 帽子面の u スライスは capW そのもの。 -/
theorem slice_W_cap {F : WedgeFields} (hdata : HasWedgeData F) :
    (fun u' => F.W u' 0) = capW :=
  funext fun u' => (hdata.1 u').2.2

/-- 首面の v スライスで r は定数 1。 -/
theorem slice_r_neck {F : WedgeFields} (hdata : HasWedgeData F) :
    (fun v' => F.r 0 v') = fun _ => (1 : ℝ) :=
  funext fun v' => (hdata.2 v').1

/-- 首面の v スライスは neckOm そのもの。 -/
theorem slice_Om_neck {F : WedgeFields} (hdata : HasWedgeData F) :
    (fun v' => F.Om 0 v') = neckOm :=
  funext fun v' => (hdata.2 v').2.1

/-- 首面の v スライスで W は定数 0。 -/
theorem slice_W_neck {F : WedgeFields} (hdata : HasWedgeData F) :
    (fun v' => F.W 0 v') = fun _ => (0 : ℝ) :=
  funext fun v' => (hdata.2 v').2.2

/-- 角での r_u = 0（帽子データの傾き）。 -/
theorem data_r_u {F : WedgeFields} (hdata : HasWedgeData F) : Du F.r 0 0 = 0 := by
  show deriv (fun u' => F.r u' 0) 0 = 0
  rw [slice_r_cap hdata]
  exact corner_capR_slope

/-- 角での r_v = 0（首の r は定数）。 -/
theorem data_r_v {F : WedgeFields} (hdata : HasWedgeData F) : Dv F.r 0 0 = 0 := by
  show deriv (fun v' => F.r 0 v') 0 = 0
  rw [slice_r_neck hdata]
  simp

/-- 角での W_u = 1/√2（帽子データの傾き）。 -/
theorem data_W_u {F : WedgeFields} (hdata : HasWedgeData F) :
    Du F.W 0 0 = 1 / Real.sqrt 2 := by
  show deriv (fun u' => F.W u' 0) 0 = 1 / Real.sqrt 2
  rw [slice_W_cap hdata]
  exact corner_capW_slope

/-- 角での W_v = 0（首の W は定数）。 -/
theorem data_W_v {F : WedgeFields} (hdata : HasWedgeData F) : Dv F.W 0 0 = 0 := by
  show deriv (fun v' => F.W 0 v') 0 = 0
  rw [slice_W_neck hdata]
  simp

/-- capOm の角での微分は 0（capR と同じ関数）。 -/
theorem deriv_capOm_zero : deriv capOm 0 = 0 := corner_capR_slope

/-- 角での Ω_u = 0（帽子データの傾き）。 -/
theorem data_Om_u {F : WedgeFields} (hdata : HasWedgeData F) : Du F.Om 0 0 = 0 := by
  show deriv (fun u' => F.Om u' 0) 0 = 0
  rw [slice_Om_cap hdata]
  exact deriv_capOm_zero

/-- neckOm の角での微分は 0（cosh の偶性：sinh 0 = 0）。 -/
theorem deriv_neckOm_zero : deriv neckOm 0 = 0 := by
  have hlin : HasDerivAt (fun v => v / Real.sqrt 2) (1 / Real.sqrt 2) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const (Real.sqrt 2)
  have hcosh : HasDerivAt (fun v => Real.cosh (v / Real.sqrt 2))
      (Real.sinh (0 / Real.sqrt 2) * (1 / Real.sqrt 2)) 0 := by
    have h := (hasDerivAt_cosh (0 / Real.sqrt 2)).comp 0 hlin
    simpa [Function.comp] using h
  have hsq : HasDerivAt (fun v => (Real.cosh (v / Real.sqrt 2)) ^ 2) 0 0 := by
    simpa using hcosh.pow 2
  have hne : (Real.cosh (0 / Real.sqrt 2)) ^ 2 ≠ 0 := by simp
  have hinv : HasDerivAt (fun v => ((Real.cosh (v / Real.sqrt 2)) ^ 2)⁻¹) 0 0 := by
    simpa using hsq.inv hne
  exact hinv.deriv

/-- 角での Ω_v = 0（首データの傾き）。 -/
theorem data_Om_v {F : WedgeFields} (hdata : HasWedgeData F) : Dv F.Om 0 0 = 0 := by
  show deriv (fun v' => F.Om 0 v') 0 = 0
  rw [slice_Om_neck hdata]
  exact deriv_neckOm_zero

/-! ### 方程式から導かれる角条件（必要条件） -/

/-- 角条件その1：C_u を (0,0) で評価すると r_uu = −1。
  r_u = 0、W_u = 1/√2、r = 1 より、r_uu = −2 W_u²/r = −1。 -/
theorem corner_ruu {F : WedgeFields} (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F) : Duu F.r 0 0 = -1 := by
  have hC := (hcon 0 0).1
  have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  rw [data_Om_u hdata, data_r_u hdata, data_W_u hdata, (data_values hdata).1, h2] at hC
  norm_num at hC
  linarith

/-- 角条件その2：C_v を (0,0) で評価すると r_vv = 0。 -/
theorem corner_rvv {F : WedgeFields} (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F) : Dvv F.r 0 0 = 0 := by
  have hC := (hcon 0 0).2
  rw [data_Om_v hdata, data_r_v hdata, data_W_v hdata, (data_values hdata).1] at hC
  norm_num at hC
  linarith

/-- 角条件その3：r の発展方程式を (0,0) で評価すると r_uv = 0。 -/
theorem corner_ruv {F : WedgeFields} (hdata : HasWedgeData F)
    (hev : WedgeEvolutionEqs F) : Duv F.r 0 0 = 0 := by
  have hE := (hev 0 0).1
  rw [(data_values hdata).2.1, (data_values hdata).2.2, data_r_u hdata, data_r_v hdata,
    (data_values hdata).1] at hE
  rw [hE]
  simp [rhsR]

/-- 角条件その4：W の発展方程式を (0,0) で評価すると W_uv = 0。 -/
theorem corner_Wuv {F : WedgeFields} (hdata : HasWedgeData F)
    (hev : WedgeEvolutionEqs F) : Duv F.W 0 0 = 0 := by
  have hE := (hev 0 0).2.2
  rw [(data_values hdata).2.1, (data_values hdata).2.2, (data_values hdata).1] at hE
  rw [hE]
  simp [rhsW]

/-- 角条件その5：Ω の発展方程式を (0,0) で評価すると Ω_uv = −1。
  r_uv = 0 を使う。 -/
theorem corner_Omuv {F : WedgeFields} (hdata : HasWedgeData F)
    (hev : WedgeEvolutionEqs F) : Duv F.Om 0 0 = -1 := by
  have hruv := corner_ruv hdata hev
  have hE := (hev 0 0).2.1
  rw [(data_values hdata).2.1, data_Om_u hdata, data_Om_v hdata, hruv,
    (data_values hdata).1, (data_values hdata).2.2] at hE
  rw [hE]
  simp [rhsOm]

/-! ### 照合：帽子・首のデータが角条件を満たす -/

/-- capR の倍角表示：cos²(u/√2) = (1 + cos(√2 u))/2。 -/
theorem capR_eq : capR = fun u => (1 + Real.cos (Real.sqrt 2 * u)) / 2 := by
  funext u
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have harg : 2 * (u / Real.sqrt 2) = Real.sqrt 2 * u := by
    rw [← mul_div_assoc, div_eq_iff hs2, mul_comm (Real.sqrt 2 * u) (Real.sqrt 2),
      ← mul_assoc, h2]
  have hcos := Real.cos_two_mul (u / Real.sqrt 2)
  rw [harg] at hcos
  simp only [capR]
  linarith [hcos]

/-- capR の1階微分（倍角表示で）。 -/
theorem deriv_capR (u : ℝ) :
    deriv capR u = -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2 := by
  have hlin : HasDerivAt (fun u => Real.sqrt 2 * u) (Real.sqrt 2) u := by
    simpa using (hasDerivAt_id u).const_mul (Real.sqrt 2)
  have hcos : HasDerivAt (fun u => Real.cos (Real.sqrt 2 * u))
      (-Real.sin (Real.sqrt 2 * u) * Real.sqrt 2) u := by
    have h := (hasDerivAt_cos (Real.sqrt 2 * u)).comp u hlin
    simpa [Function.comp] using h
  have h1 : HasDerivAt (fun u => (1 + Real.cos (Real.sqrt 2 * u)) / 2)
      ((-Real.sin (Real.sqrt 2 * u) * Real.sqrt 2) / 2) u :=
    (hcos.const_add 1).div_const 2
  have hcap : HasDerivAt capR (-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2) u := by
    rw [capR_eq]
    convert h1 using 1
    ring
  exact hcap.deriv

/-- capR の角での2階微分は −1（C_u から導かれる r_uu = −1 と一致）。 -/
theorem capR_second : deriv (deriv capR) 0 = -1 := by
  have hfun : deriv capR = fun u => -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2 :=
    funext deriv_capR
  rw [hfun]
  have hlin : HasDerivAt (fun u => Real.sqrt 2 * u) (Real.sqrt 2) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (Real.sqrt 2)
  have hsin : HasDerivAt (fun u => Real.sin (Real.sqrt 2 * u))
      (Real.cos (Real.sqrt 2 * 0) * Real.sqrt 2) 0 := by
    have h := (hasDerivAt_sin (Real.sqrt 2 * 0)).comp 0 hlin
    simpa [Function.comp] using h
  have h1 : HasDerivAt (fun u => -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2)
      (-(Real.sqrt 2 * (Real.cos (Real.sqrt 2 * 0) * Real.sqrt 2)) / 2) 0 :=
    ((hsin.const_mul (Real.sqrt 2)).neg).div_const 2
  rw [h1.deriv]
  simp only [mul_zero, Real.cos_zero, one_mul, mul_one]
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- capOm の角での2階微分も −1（capR と同じ関数）。 -/
theorem capOm_second : deriv (deriv capOm) 0 = -1 := capR_second

/-- 照合その1：帽子データは角で C_u を満たす。
  r_uu = −1、Ω_u = 0、r_u = 0、W_u = 1/√2、r = 1 より
  r_uu − (Ω_u/Ω) r_u + 2 W_u²/r = −1 + 0 + 1 = 0。 -/
theorem cap_cu_check :
    deriv (deriv capR) 0 - (deriv capOm 0 / capOm 0) * deriv capR 0
      + 2 * (deriv capW 0) ^ 2 / capR 0 = 0 := by
  have hR0 : capR 0 = 1 := by simp [capR]
  have hO0 : capOm 0 = 1 := by simp [capOm]
  have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  rw [capR_second, deriv_capOm_zero, corner_capR_slope, corner_capW_slope, hR0, hO0, h2]
  norm_num

/-- 照合その2：首データは角で C_v を満たす（r ≡ 1、W ≡ 0 の定数性）。 -/
theorem neck_cv_check :
    deriv (deriv (fun _ : ℝ => (1 : ℝ))) 0
      - (deriv neckOm 0 / neckOm 0) * deriv (fun _ : ℝ => (1 : ℝ)) 0
      + 2 * (deriv (fun _ : ℝ => (0 : ℝ))) 0 ^ 2 / 1 = 0 := by
  simp [deriv_neckOm_zero]

end CFT.WedgeCorner
