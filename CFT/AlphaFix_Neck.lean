/-
  独立監査(2026-11-04)の指摘を受けた作り直し:α-IX.14、XI.1、XI.3(首と帽子の動き)

  * IX.14(運動学:首 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²(IV.7 の座標)。作用:JT(IX.12)。力学:dilaton と Schwarzian)
      JT の dilaton の方程式 ∇_μ∇_νφ − g_μν□φ + g_μνφ/ℓ² = 0 は、a = cos(t/ℓ) の計量 −dt² + a²dz² で
        tt:−(a′/a)φ_t + φ_zz/a² − φ/ℓ² = 0、zz:φ_tt + φ/ℓ² = 0、tz:φ_tz − (a′/a)φ_z = 0
      (Christoffel 記号 Γ^t_zz = aa′、Γ^z_tz = a′/a)。
      φ = A sin(t/ℓ) + cos(t/ℓ)(B cosh(z/ℓ) + C sinh(z/ℓ)) は三つの式をみたす(`jt_neck_solution`、偏微分は
      `jt_dt` `jt_dtt` `jt_dz` `jt_dzz` `jt_dtz`)。静的な解は 0 だけ(`no_static_dilaton`):首の dilaton
      (r² − ℓ² の 1 次)は時間に依存する。z → −z と t → −t で対称な解は B cos(t/ℓ)cosh(z/ℓ) で、
      t = ±πℓ/2(帽子 a = ℓ cos η の崩壊と同じ cos)で 0 になる。
      この解の勾配は (∇φ)² = (B/ℓ)²(sinh²(z/ℓ) − sin²(t/ℓ)cosh²(z/ℓ))(`jt_gradient`)で、首の中心
      (t, z) = (0, 0) で 0:首の中心を分岐面とする JT の永遠のブラックホールの形(`jt_bifurcation`)。
      Schwarzian(Maldacena–Stanford–Yang 2016、外部)の前提は漸近的な AdS₂ の境界。首の半分の長さ L の
      接合は大域座標で sin u_c = sech(L/ℓ)、u_c ≤ πe^{−L/ℓ}(`junction_near_boundary`):長い首では接合が
      境界に近づき、前提が近似として成り立つ(条件 L/ℓ ≫ 1)。結合の規格化:IX.10 の (1/4G)∫φ(R + 2/ℓ²) を
      (1/16πG₂)∫φ(R + 2/ℓ²) と比べて G₂ = G/(4π)、S₀ = ℓ²/(4G₂) = πℓ²/G(IX.13 と一致)、
      C = φ_r/(8πG₂) = φ_r/(2G)(`jt_normalization`)。
  * XI.1(運動学:首の大域座標 (ℓ²/sin²u)(−dτ² + du²)、接合 u_c。作用:W の 2 次の作用。力学:成長率)
      モード e^{λτ}f(u):−f″ − f/sin²u = −λ²f。試験関数 f(u) = √u sin(π(log u − log u₁)/Y) を [u₁, u₁e^Y] に置く。
      (i) Liouville の変換を Lean で示す:変数 y = log u − log u₁ で
          ∫(f′² − f²/sin²u) du = ∫₀^Y G₂(y) dy(`liouville_actual`、f′ は `test_deriv`)、
          ∫ f² du = ∫₀^Y (u₁e^y)² sin²(πy/Y) dy(`liouville_norm`)、変数変換は `change_var`。
      (ii) sin u ≤ u から G₂ ≤ G₁(`G2_le_G1`)、∫₀^Y G₁ = (Y/2)((π/Y)² − 3/4)(`G1_integral`)。
          したがって Y > 2π/√3 なら本当の二次形式が負(`actual_form_neg`、比較の評価をもう外部にしない)。
          首への読み替え(L/ℓ > 2π/√3 + log 2):`long_neck_unstable_actual`。
      (iii) 成長率の下限:min–max(外部:正則な Sturm–Liouville 作用素、Dirichlet 条件)で
          −λ²∫f² ≤ ∫(f′² − f²/sin²u)。Y = 4 の窓で
            λ² ≥ (3/4 − π²/16)e^{2(L/ℓ − 4)}/π²(`growth_rate_bound`、L/ℓ > 4)。
          成長率は首の長さとともに指数関数的に増える。λ は首の中心の固有時間で測った率 × ℓ。
      (iv) 帽子の崩壊までの固有時間 ∫₀^{π/2} ℓ cos η dη = ℓ(`cap_collapse_time`)。
          L/ℓ ≥ 7 なら λ ≥ 1(`one_efold_before_collapse`):帽子が崩壊するまでに少なくとも 1 回 e 倍になる。
          前提:首は静的な背景(IX.11 の厳密解)、接合で Dirichlet 条件。時計は接合でそろえる(解釈)。
  * XI.3(運動学:帽子の波面 χ = π/2 − η。力学:捕捉面)
      波面の上の球は θ₊ = 0、θ₋ = −2 tan η < 0(`front_marginally_trapped`):0 < η < π/2 のすべての時刻、
      つまり崩壊の前に、周辺的に捕捉された球(見かけの地平面)が波面の上にある。首の球は半径 ℓ で一定なので
      θ± = 0(`neck_marginal`)。厳密に捕捉された球ができるかは r² − ℓ² の 2 次の項による(JT の 1 次では
      接合の条件 r = ℓ から係数が決まらない)。
-/
import CFT.AlphaXI_NeckInstability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds

namespace CFT.FixNeck

open Real Set MeasureTheory intervalIntegral

/-! ### IX.14 首の JT dilaton -/

/-- φ の t 微分 -/
theorem jt_dt (l A B C z t : ℝ) :
    HasDerivAt (fun t => A * sin (t / l) + cos (t / l) * (B * cosh (z / l) + C * sinh (z / l)))
      (A / l * cos (t / l) - sin (t / l) / l * (B * cosh (z / l) + C * sinh (z / l))) t := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) t := (hasDerivAt_id' t).div_const l
  have h1 := ((hasDerivAt_sin (t / l)).comp t hu).const_mul A
  have h2 := ((hasDerivAt_cos (t / l)).comp t hu).mul_const (B * cosh (z / l) + C * sinh (z / l))
  convert h1.add h2 using 1
  ring

/-- φ_t の t 微分 = φ_tt -/
theorem jt_dtt (l A B C z t : ℝ) :
    HasDerivAt (fun t => A / l * cos (t / l) - sin (t / l) / l * (B * cosh (z / l) + C * sinh (z / l)))
      (-(A / l ^ 2) * sin (t / l) - cos (t / l) / l ^ 2 * (B * cosh (z / l) + C * sinh (z / l))) t := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) t := (hasDerivAt_id' t).div_const l
  have h1 := ((hasDerivAt_cos (t / l)).comp t hu).const_mul (A / l)
  have h2 := (((hasDerivAt_sin (t / l)).comp t hu).div_const l).mul_const
    (B * cosh (z / l) + C * sinh (z / l))
  convert h1.sub h2 using 1
  ring

/-- φ の z 微分 -/
theorem jt_dz (l A B C t z : ℝ) :
    HasDerivAt (fun z => A * sin (t / l) + cos (t / l) * (B * cosh (z / l) + C * sinh (z / l)))
      (cos (t / l) * ((B * sinh (z / l) + C * cosh (z / l)) / l)) z := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) z := (hasDerivAt_id' z).div_const l
  have h1 := ((Real.hasDerivAt_cosh (z / l)).comp z hu).const_mul B
  have h2 := ((Real.hasDerivAt_sinh (z / l)).comp z hu).const_mul C
  have h := ((h1.add h2).const_mul (cos (t / l))).const_add (A * sin (t / l))
  convert h using 1
  ring

/-- φ_z の z 微分 = φ_zz -/
theorem jt_dzz (l B C t z : ℝ) :
    HasDerivAt (fun z => cos (t / l) * ((B * sinh (z / l) + C * cosh (z / l)) / l))
      (cos (t / l) * (B * cosh (z / l) + C * sinh (z / l)) / l ^ 2) z := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) z := (hasDerivAt_id' z).div_const l
  have h1 := ((Real.hasDerivAt_sinh (z / l)).comp z hu).const_mul B
  have h2 := ((Real.hasDerivAt_cosh (z / l)).comp z hu).const_mul C
  have h := ((h1.add h2).div_const l).const_mul (cos (t / l))
  convert h using 1
  ring

/-- φ_t の z 微分 = φ_tz -/
theorem jt_dtz (l A B C t z : ℝ) :
    HasDerivAt (fun z => A / l * cos (t / l) - sin (t / l) / l * (B * cosh (z / l) + C * sinh (z / l)))
      (-(sin (t / l) / l) * ((B * sinh (z / l) + C * cosh (z / l)) / l)) z := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) z := (hasDerivAt_id' z).div_const l
  have h1 := ((Real.hasDerivAt_cosh (z / l)).comp z hu).const_mul B
  have h2 := ((Real.hasDerivAt_sinh (z / l)).comp z hu).const_mul C
  have h := ((h1.add h2).const_mul (sin (t / l) / l)).const_sub (A / l * cos (t / l))
  convert h using 1
  ring

/-- 【α-IX.14】首の座標での JT の dilaton の方程式(tt、zz、tz)の解
φ = A sin(t/ℓ) + cos(t/ℓ)(B cosh(z/ℓ) + C sinh(z/ℓ)) -/
theorem jt_neck_solution (l A B C t z : ℝ) (hl : l ≠ 0) (hc : cos (t / l) ≠ 0) :
    let Z := B * cosh (z / l) + C * sinh (z / l)
    let Zz := (B * sinh (z / l) + C * cosh (z / l)) / l
    let φ := A * sin (t / l) + cos (t / l) * Z
    let φt := A / l * cos (t / l) - sin (t / l) / l * Z
    let φtt := -(A / l ^ 2) * sin (t / l) - cos (t / l) / l ^ 2 * Z
    let φz := cos (t / l) * Zz
    let φzz := cos (t / l) * Z / l ^ 2
    let φtz := -(sin (t / l) / l) * Zz
    let ap := -(sin (t / l) / l)
    let a := cos (t / l)
    -(ap / a) * φt + φzz / a ^ 2 - φ / l ^ 2 = 0 ∧ φtt + φ / l ^ 2 = 0 ∧ φtz - ap / a * φz = 0 := by
  intro Z Zz φ φt φtt φz φzz φtz ap a
  have hsc := sin_sq_add_cos_sq (t / l)
  refine ⟨?_, ?_, ?_⟩
  · have e : -(ap / a) * φt + φzz / a ^ 2 - φ / l ^ 2
        = -(Z / (l ^ 2 * cos (t / l))) * (sin (t / l) ^ 2 + cos (t / l) ^ 2 - 1) := by
      simp only [Z, φ, φt, φzz, ap, a]
      field_simp <;> ring
    rw [e, show sin (t / l) ^ 2 + cos (t / l) ^ 2 - 1 = 0 by linarith, mul_zero]
  · simp only [φtt, φ]
    field_simp <;> ring
  · simp only [φtz, ap, a, φz]
    field_simp <;> ring

/-- 【α-IX.14】静的な dilaton は 0 だけ:すべての (t, z) で φ_t = 0 なら A = B = C = 0 -/
theorem no_static_dilaton (l A B C : ℝ) (hl : 0 < l)
    (h : ∀ t z : ℝ, A / l * cos (t / l) - sin (t / l) / l * (B * cosh (z / l) + C * sinh (z / l)) = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hl0 := hl.ne'
  have hA : A = 0 := by
    have := h 0 0
    simp only [zero_div, cos_zero, sin_zero, cosh_zero, sinh_zero, mul_one, zero_mul, sub_zero] at this
    rcases div_eq_zero_iff.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hl0
  have hB : B = 0 := by
    have := h (l * (π / 2)) 0
    rw [show l * (π / 2) / l = π / 2 from mul_div_cancel_left₀ (π / 2) hl0, sin_pi_div_two,
      cos_pi_div_two] at this
    simp only [zero_div, cosh_zero, sinh_zero, mul_zero, mul_one, add_zero, zero_sub, neg_eq_zero] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (one_div_ne_zero hl0)
    · exact h1
  have hC : C = 0 := by
    have := h (l * (π / 2)) l
    rw [show l * (π / 2) / l = π / 2 from mul_div_cancel_left₀ (π / 2) hl0, sin_pi_div_two,
      cos_pi_div_two, div_self hl0, hB] at this
    have hs : 0 < sinh 1 := Real.sinh_pos_iff.2 one_pos
    have : C * sinh 1 = 0 := by
      have e : A / l * 0 - 1 / l * (0 * cosh 1 + C * sinh 1) = -(C * sinh 1) / l := by ring
      rw [e, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · linarith
      · exact absurd h1 hl0
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hs.ne'
  exact ⟨hA, hB, hC⟩

/-- 【α-IX.14】対称な解 φ = B cos(t/ℓ)cosh(z/ℓ) の勾配 (∇φ)² = −φ_t² + φ_z²/a² -/
theorem jt_gradient (l B t z : ℝ) (hl : l ≠ 0) (hc : cos (t / l) ≠ 0) :
    -(-(sin (t / l) / l) * (B * cosh (z / l))) ^ 2
      + (cos (t / l) * (B * sinh (z / l) / l)) ^ 2 / cos (t / l) ^ 2
      = (B / l) ^ 2 * (sinh (z / l) ^ 2 - sin (t / l) ^ 2 * cosh (z / l) ^ 2) := by
  field_simp <;> ring

/-- 【α-IX.14】首の中心 (0, 0) で勾配は 0(分岐面) -/
theorem jt_bifurcation (l B : ℝ) :
    (B / l) ^ 2 * (sinh (0 / l) ^ 2 - sin (0 / l) ^ 2 * cosh (0 / l) ^ 2) = 0 := by
  simp

/-- 【α-IX.14】接合 sin u_c = sech(L/ℓ)(0 < u_c ≤ π/2)なら u_c ≤ πe^{−L/ℓ}(長い首で境界に近づく) -/
theorem junction_near_boundary (L l uc : ℝ) (huc : 0 < uc) (huc2 : uc ≤ π / 2)
    (hjoin : sin uc = 1 / cosh (L / l)) : uc ≤ π * rexp (-(L / l)) := by
  have hpi := pi_pos
  have hJ : 2 / π * uc ≤ sin uc := mul_le_sin huc.le huc2
  have hcosh : rexp (L / l) / 2 ≤ cosh (L / l) := by
    rw [Real.cosh_eq]; have := exp_pos (-(L / l)); linarith
  have hch : 0 < cosh (L / l) := cosh_pos _
  have he := exp_pos (L / l)
  have h1 : 2 / π * uc ≤ 2 / rexp (L / l) := by
    calc 2 / π * uc ≤ sin uc := hJ
      _ = 1 / cosh (L / l) := hjoin
      _ ≤ 1 / (rexp (L / l) / 2) := one_div_le_one_div_of_le (by positivity) hcosh
      _ = 2 / rexp (L / l) := by field_simp
  have h2 : uc ≤ π / rexp (L / l) := by
    have h3 : uc * 2 * rexp (L / l) ≤ 2 * π := by
      rw [div_mul_eq_mul_div, div_le_div_iff hpi he] at h1
      linarith
    rw [le_div_iff₀ he]
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact h2

/-- 【α-IX.14】結合の規格化:G₂ = G/(4π) で 1/(16πG₂) = 1/(4G)、S₀ = ℓ²/(4G₂) = πℓ²/G、
C = φ_r/(8πG₂) = φ_r/(2G) -/
theorem jt_normalization (G l φr : ℝ) (hG : G ≠ 0) :
    1 / (16 * π * (G / (4 * π))) = 1 / (4 * G) ∧ l ^ 2 / (4 * (G / (4 * π))) = π * l ^ 2 / G ∧
    φr / (8 * π * (G / (4 * π))) = φr / (2 * G) := by
  have := pi_ne_zero
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ### XI.1 首の不安定性:Liouville の変換、成長率 -/

/-- y 変数の比較の積分の中身 G₁(y) = (s/2 + (π/Y)c)² − s²(s = sin(πy/Y)、c = cos(πy/Y)) -/
noncomputable def G1 (Y y : ℝ) : ℝ :=
  (sin (π / Y * y) / 2 + π / Y * cos (π / Y * y)) ^ 2 - sin (π / Y * y) ^ 2

/-- 本当のポテンシャル 1/sin²u での中身 G₂(y)(u = u₁e^y) -/
noncomputable def G2 (u1 Y y : ℝ) : ℝ :=
  (sin (π / Y * y) / 2 + π / Y * cos (π / Y * y)) ^ 2
    - sin (π / Y * y) ^ 2 * (u1 * rexp y / sin (u1 * rexp y)) ^ 2

/-- ∫₀^Y sin(πy/Y)cos(πy/Y) dy = 0 -/
theorem int_sin_cos (Y : ℝ) (hY : 0 < Y) :
    ∫ y in (0 : ℝ)..Y, sin (π / Y * y) * cos (π / Y * y) = 0 := by
  have hk : π / Y ≠ 0 := div_ne_zero pi_ne_zero hY.ne'
  have hd : ∀ x ∈ uIcc 0 Y, HasDerivAt (fun y => sin (π / Y * y) ^ 2 / (2 * (π / Y)))
      (sin (π / Y * x) * cos (π / Y * x)) x := by
    intro x _
    have hu : HasDerivAt (fun y : ℝ => π / Y * y) (π / Y * 1) x := (hasDerivAt_id' x).const_mul (π / Y)
    have h := (((hasDerivAt_sin (π / Y * x)).comp x hu).pow 2).div_const (2 * (π / Y))
    convert h using 1
    simp only [Function.comp_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp <;> ring
  rw [integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [show π / Y * Y = π from div_mul_cancel₀ π hY.ne', sin_pi]
  simp

/-- 【α-XI.1】∫₀^Y G₁ = (Y/2)((π/Y)² − 3/4) -/
theorem G1_integral (Y : ℝ) (hY : 0 < Y) : ∫ y in (0 : ℝ)..Y, G1 Y y = Y / 2 * ((π / Y) ^ 2 - 3 / 4) := by
  have e : ∀ y, G1 Y y = ((π / Y * cos (π / Y * y)) ^ 2 - 3 / 4 * sin (π / Y * y) ^ 2)
      + π / Y * (sin (π / Y * y) * cos (π / Y * y)) := by
    intro y; unfold G1; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    NeckInstability.Q_value Y hY, int_sin_cos Y hY]
  ring

/-- 変数変換 y = log u − log u₁:∫_{u₁}^{u₁e^Y} g(log u − log u₁) u⁻¹ du = ∫₀^Y g(y) dy -/
theorem change_var (g : ℝ → ℝ) (u1 Y : ℝ) (hu : 0 < u1) (hY : 0 < Y) (hg : ContinuousOn g (Icc 0 Y)) :
    ∫ u in u1..(u1 * rexp Y), g (log u - log u1) * u⁻¹ = ∫ y in (0 : ℝ)..Y, g y := by
  have hu2 : u1 ≤ u1 * rexp Y := by
    have : 1 ≤ rexp Y := by have := Real.add_one_le_exp Y; linarith
    nlinarith
  have hpos : ∀ x ∈ uIcc u1 (u1 * rexp Y), 0 < x := by
    intro x hx; rw [uIcc_of_le hu2] at hx; exact lt_of_lt_of_le hu hx.1
  have hd : ∀ x ∈ uIcc u1 (u1 * rexp Y), HasDerivAt (fun u => log u - log u1) (x⁻¹) x :=
    fun x hx => (hasDerivAt_log (hpos x hx).ne').sub_const _
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc u1 (u1 * rexp Y)) :=
    continuousOn_inv₀.mono fun x hx => by simpa using (hpos x hx).ne'
  have himg : (fun u => log u - log u1) '' uIcc u1 (u1 * rexp Y) ⊆ Icc 0 Y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [uIcc_of_le hu2] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hu hx.1
    constructor
    · have := Real.log_le_log hu hx.1; linarith
    · have := Real.log_le_log hx0 hx.2
      rw [Real.log_mul hu.ne' (exp_pos Y).ne', Real.log_exp] at this; linarith
  have h := intervalIntegral.integral_comp_mul_deriv' hd hc (hg.mono himg)
  simp only [Function.comp_apply] at h
  rw [h, Real.log_mul hu.ne' (exp_pos Y).ne', Real.log_exp]
  simp

/-- 試験関数 f(u) = √u sin(π(log u − log u₁)/Y) の微分 -/
theorem test_deriv (u1 Y u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun x => Real.sqrt x * sin (π / Y * (log x - log u1)))
      ((sin (π / Y * (log u - log u1)) / 2 + π / Y * cos (π / Y * (log u - log u1))) / Real.sqrt u) u := by
  have h1 := Real.hasDerivAt_sqrt hu.ne'
  have h2 := ((hasDerivAt_log hu.ne').sub_const (log u1)).const_mul (π / Y)
  have h3 := (hasDerivAt_sin (π / Y * (log u - log u1))).comp u h2
  have h := h1.mul h3
  convert h using 1
  have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  simp only [Function.comp_apply]
  rw [show u⁻¹ = (Real.sqrt u * Real.sqrt u)⁻¹ by rw [hsq]]
  field_simp <;> ring

/-- 中身の一致:f′² − f²/sin²u = G₂(log u − log u₁)·u⁻¹ -/
theorem integrand_eq (u1 Y u : ℝ) (hu1 : 0 < u1) (hu : 0 < u) (hsin : sin u ≠ 0) :
    ((sin (π / Y * (log u - log u1)) / 2 + π / Y * cos (π / Y * (log u - log u1))) / Real.sqrt u) ^ 2
      - (Real.sqrt u * sin (π / Y * (log u - log u1))) ^ 2 / sin u ^ 2
      = G2 u1 Y (log u - log u1) * u⁻¹ := by
  have he : u1 * rexp (log u - log u1) = u := by
    rw [Real.exp_sub, Real.exp_log hu, Real.exp_log hu1]; field_simp
  unfold G2
  rw [he]
  have hs : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hs0 : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  have hu0 : u ≠ 0 := hu.ne'
  rw [div_pow, mul_pow, hs]
  field_simp <;> ring

/-- 中身の一致(ノルム):f² = (u₁e^y)² sin²(πy/Y)·u⁻¹ -/
theorem norm_integrand_eq (u1 Y u : ℝ) (hu1 : 0 < u1) (hu : 0 < u) :
    (Real.sqrt u * sin (π / Y * (log u - log u1))) ^ 2
      = (u1 * rexp (log u - log u1)) ^ 2 * sin (π / Y * (log u - log u1)) ^ 2 * u⁻¹ := by
  have he : u1 * rexp (log u - log u1) = u := by
    rw [Real.exp_sub, Real.exp_log hu, Real.exp_log hu1]; field_simp
  rw [he, mul_pow, Real.sq_sqrt hu.le]
  have hu0 : u ≠ 0 := hu.ne'
  field_simp <;> ring

/-- G₂ は [0, Y] で連続(窓 u₁e^Y < π) -/
theorem G2_cont (u1 Y : ℝ) (hu1 : 0 < u1) (hwin : u1 * rexp Y < π) : ContinuousOn (G2 u1 Y) (Icc 0 Y) := by
  have hne : ∀ y ∈ Icc 0 Y, sin (u1 * rexp y) ≠ 0 := by
    intro y hy
    have hu : 0 < u1 * rexp y := mul_pos hu1 (exp_pos y)
    have : u1 * rexp y ≤ u1 * rexp Y := mul_le_mul_of_nonneg_left (exp_le_exp.2 hy.2) hu1.le
    exact (sin_pos_of_pos_of_lt_pi hu (lt_of_le_of_lt this hwin)).ne'
  have hw : ContinuousOn (fun y => u1 * rexp y / sin (u1 * rexp y)) (Icc 0 Y) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) hne
  have hA : Continuous fun y => (sin (π / Y * y) / 2 + π / Y * cos (π / Y * y)) ^ 2 := by fun_prop
  have hB : Continuous fun y => sin (π / Y * y) ^ 2 := by fun_prop
  exact hA.continuousOn.sub (hB.continuousOn.mul (hw.pow 2))

/-- 【α-XI.1】Liouville の変換(本当のポテンシャル):∫(f′² − f²/sin²u) du = ∫₀^Y G₂ -/
theorem liouville_actual (u1 Y : ℝ) (hu1 : 0 < u1) (hY : 0 < Y) (hwin : u1 * rexp Y < π) :
    ∫ u in u1..(u1 * rexp Y),
      (((sin (π / Y * (log u - log u1)) / 2 + π / Y * cos (π / Y * (log u - log u1))) / Real.sqrt u) ^ 2
        - (Real.sqrt u * sin (π / Y * (log u - log u1))) ^ 2 / sin u ^ 2)
      = ∫ y in (0 : ℝ)..Y, G2 u1 Y y := by
  have hu2 : u1 ≤ u1 * rexp Y := by
    have : 1 ≤ rexp Y := by have := Real.add_one_le_exp Y; linarith
    nlinarith
  rw [← change_var (G2 u1 Y) u1 Y hu1 hY (G2_cont u1 Y hu1 hwin)]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hu2] at hu
  have hu0 : 0 < u := lt_of_lt_of_le hu1 hu.1
  have hsin : sin u ≠ 0 := (sin_pos_of_pos_of_lt_pi hu0 (lt_of_le_of_lt hu.2 hwin)).ne'
  exact integrand_eq u1 Y u hu1 hu0 hsin

/-- 【α-XI.1】Liouville の変換(ノルム):∫ f² du = ∫₀^Y (u₁e^y)² sin²(πy/Y) dy -/
theorem liouville_norm (u1 Y : ℝ) (hu1 : 0 < u1) (hY : 0 < Y) :
    ∫ u in u1..(u1 * rexp Y), (Real.sqrt u * sin (π / Y * (log u - log u1))) ^ 2
      = ∫ y in (0 : ℝ)..Y, (u1 * rexp y) ^ 2 * sin (π / Y * y) ^ 2 := by
  have hu2 : u1 ≤ u1 * rexp Y := by
    have : 1 ≤ rexp Y := by have := Real.add_one_le_exp Y; linarith
    nlinarith
  rw [← change_var (fun y => (u1 * rexp y) ^ 2 * sin (π / Y * y) ^ 2) u1 Y hu1 hY
    (by apply Continuous.continuousOn; fun_prop)]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hu2] at hu
  have hu0 : 0 < u := lt_of_lt_of_le hu1 hu.1
  exact norm_integrand_eq u1 Y u hu1 hu0

/-- sin u ≤ u から G₂ ≤ G₁ -/
theorem G2_le_G1 (u1 Y y : ℝ) (hu1 : 0 < u1) (hy : u1 * rexp y < π) : G2 u1 Y y ≤ G1 Y y := by
  unfold G1 G2
  have hu : 0 < u1 * rexp y := mul_pos hu1 (exp_pos y)
  have hsin : 0 < sin (u1 * rexp y) := sin_pos_of_pos_of_lt_pi hu hy
  have hle : sin (u1 * rexp y) ≤ u1 * rexp y := sin_le hu.le
  have h1 : 1 ≤ (u1 * rexp y / sin (u1 * rexp y)) ^ 2 := by
    have : 1 ≤ u1 * rexp y / sin (u1 * rexp y) := by rw [le_div_iff₀ hsin]; linarith
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg (sin (π / Y * y))) (sub_nonneg.2 h1)]

/-- ∫₀^Y G₂ ≤ (Y/2)((π/Y)² − 3/4) -/
theorem actual_le (u1 Y : ℝ) (hu1 : 0 < u1) (hY : 0 < Y) (hwin : u1 * rexp Y < π) :
    ∫ y in (0 : ℝ)..Y, G2 u1 Y y ≤ Y / 2 * ((π / Y) ^ 2 - 3 / 4) := by
  rw [← G1_integral Y hY]
  apply intervalIntegral.integral_mono_on hY.le
  · exact (G2_cont u1 Y hu1 hwin).intervalIntegrable_of_Icc hY.le
  · apply Continuous.intervalIntegrable; unfold G1; fun_prop
  · intro y hy
    apply G2_le_G1 u1 Y y hu1
    calc u1 * rexp y ≤ u1 * rexp Y := mul_le_mul_of_nonneg_left (exp_le_exp.2 hy.2) hu1.le
      _ < π := hwin

/-- 【α-XI.1】Y > 2π/√3 なら本当の二次形式 ∫(f′² − f²/sin²u) は負 -/
theorem actual_form_neg (u1 Y : ℝ) (hu1 : 0 < u1) (hY : 2 * π / Real.sqrt 3 < Y) (hwin : u1 * rexp Y < π) :
    ∫ y in (0 : ℝ)..Y, G2 u1 Y y < 0 := by
  have hpos : 0 < 2 * π / Real.sqrt 3 := by positivity
  have hY0 : 0 < Y := lt_trans hpos hY
  have h1 := actual_le u1 Y hu1 hY0 hwin
  have h2 := (NeckInstability.Q_neg_iff Y hY0).2 hY
  linarith

/-- 【α-XI.1】首への読み替え:L/ℓ > 2π/√3 + log 2 なら、窓 [u_c, π/2] の本当の二次形式が負 -/
theorem long_neck_unstable_actual (L l uc : ℝ) (hl : 0 < l) (huc : 0 < uc) (huc2 : uc ≤ π / 2)
    (hjoin : sin uc = 1 / cosh (L / l)) (hL : 2 * π / Real.sqrt 3 + Real.log 2 < L / l) :
    ∫ y in (0 : ℝ)..(Real.log (π / (2 * uc))), G2 uc (Real.log (π / (2 * uc))) y < 0 := by
  have hY := NeckInstability.Y_lower L l uc hl huc huc2 hjoin
  have hY' : 2 * π / Real.sqrt 3 < Real.log (π / (2 * uc)) := by linarith
  apply actual_form_neg uc _ huc hY'
  have hp : 0 < π / (2 * uc) := by positivity
  rw [Real.exp_log hp]
  have : uc * (π / (2 * uc)) = π / 2 := by field_simp <;> ring
  rw [this]
  linarith [pi_pos]

/-- 【α-XI.1】成長率の下限:min–max(−λ²∫f² ≤ ∫(f′² − f²/sin²u))と Y = 4 の窓から
λ² ≥ (3/4 − π²/16)e^{2(L/ℓ − 4)}/π²(L/ℓ > 4) -/
theorem growth_rate_bound (L l uc lam2 : ℝ) (huc : 0 < uc) (huc2 : uc ≤ π / 2)
    (hjoin : sin uc = 1 / cosh (L / l)) (hL : 4 < L / l) (hlam : 0 ≤ lam2)
    (hRay : -lam2 * (∫ y in (0 : ℝ)..4, (uc * rexp y) ^ 2 * sin (π / 4 * y) ^ 2)
      ≤ ∫ y in (0 : ℝ)..4, G2 uc 4 y) :
    (3 / 4 - π ^ 2 / 16) * rexp (2 * (L / l - 4)) / π ^ 2 ≤ lam2 := by
  have hpi := pi_pos
  have hb := junction_near_boundary L l uc huc huc2 hjoin
  -- 窓 u_c e⁴ < π
  have hwin : uc * rexp 4 < π := by
    have h1 : uc * rexp 4 ≤ π * rexp (-(L / l)) * rexp 4 :=
      mul_le_mul_of_nonneg_right hb (exp_pos 4).le
    have h2 : rexp (-(L / l)) * rexp 4 < 1 := by
      rw [← Real.exp_add]
      have := Real.exp_lt_exp.2 (show -(L / l) + 4 < 0 by linarith)
      rwa [Real.exp_zero] at this
    calc uc * rexp 4 ≤ π * rexp (-(L / l)) * rexp 4 := h1
      _ = π * (rexp (-(L / l)) * rexp 4) := by ring
      _ < π * 1 := by gcongr
      _ = π := mul_one π
  -- 二次形式とノルムの評価
  have hQ := actual_le uc 4 huc (by norm_num) hwin
  have hN : ∫ y in (0 : ℝ)..4, (uc * rexp y) ^ 2 * sin (π / 4 * y) ^ 2 ≤ (uc * rexp 4) ^ 2 * 2 := by
    have hm : ∫ y in (0 : ℝ)..4, (uc * rexp y) ^ 2 * sin (π / 4 * y) ^ 2
        ≤ ∫ y in (0 : ℝ)..4, (uc * rexp 4) ^ 2 * sin (π / 4 * y) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable; fun_prop
      · apply Continuous.intervalIntegrable; fun_prop
      · intro y hy
        have h0 : 0 ≤ uc * rexp y := (mul_pos huc (exp_pos y)).le
        have h1 : uc * rexp y ≤ uc * rexp 4 := mul_le_mul_of_nonneg_left (exp_le_exp.2 hy.2) huc.le
        have h2 : (uc * rexp y) ^ 2 ≤ (uc * rexp 4) ^ 2 := pow_le_pow_left h0 h1 2
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul, NeckInstability.int_sin_sq 4 (by norm_num)] at hm
    calc _ ≤ (uc * rexp 4) ^ 2 * (4 / 2) := hm
      _ = (uc * rexp 4) ^ 2 * 2 := by norm_num
  -- −λ² N ≤ Q ≤ 2(π²/16 − 3/4) から λ² N₁ ≥ 2(3/4 − π²/16)
  have hπ2 : π ^ 2 < 9.93 := by nlinarith [pi_lt_d2]
  have hc : 0 < 3 / 4 - π ^ 2 / 16 := by linarith
  set D := (uc * rexp 4) ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hstep : 2 * (3 / 4 - π ^ 2 / 16) ≤ lam2 * (D * 2) := by
    have e : (4 : ℝ) / 2 * ((π / 4) ^ 2 - 3 / 4) = -(2 * (3 / 4 - π ^ 2 / 16)) := by ring
    rw [e] at hQ
    have h1 : lam2 * (∫ y in (0 : ℝ)..4, (uc * rexp y) ^ 2 * sin (π / 4 * y) ^ 2) ≤ lam2 * (D * 2) := by
      exact mul_le_mul_of_nonneg_left hN hlam
    linarith
  -- D ≤ π² e^{2(4 − L/ℓ)}
  have hDle : D * rexp (2 * (L / l - 4)) ≤ π ^ 2 := by
    have h0 : 0 ≤ uc * rexp 4 := (mul_pos huc (exp_pos 4)).le
    have h1 : uc * rexp 4 ≤ π * rexp (-(L / l)) * rexp 4 := mul_le_mul_of_nonneg_right hb (exp_pos 4).le
    have h2 : D ≤ (π * rexp (-(L / l)) * rexp 4) ^ 2 := pow_le_pow_left h0 h1 2
    have h3 : (π * rexp (-(L / l)) * rexp 4) ^ 2 * rexp (2 * (L / l - 4)) = π ^ 2 := by
      have e : rexp (-(L / l)) * rexp (-(L / l)) * (rexp 4 * rexp 4) * rexp (2 * (L / l - 4)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        rw [show -(L / l) + -(L / l) + (4 + 4) + 2 * (L / l - 4) = 0 by ring, Real.exp_zero]
      calc (π * rexp (-(L / l)) * rexp 4) ^ 2 * rexp (2 * (L / l - 4))
          = π ^ 2 * (rexp (-(L / l)) * rexp (-(L / l)) * (rexp 4 * rexp 4) * rexp (2 * (L / l - 4))) := by
            ring
        _ = π ^ 2 := by rw [e, mul_one]
    calc D * rexp (2 * (L / l - 4)) ≤ (π * rexp (-(L / l)) * rexp 4) ^ 2 * rexp (2 * (L / l - 4)) :=
          mul_le_mul_of_nonneg_right h2 (exp_pos _).le
      _ = π ^ 2 := h3
  have hE := exp_pos (2 * (L / l - 4))
  rw [div_le_iff₀ (by positivity)]
  have h4 : (3 / 4 - π ^ 2 / 16) * rexp (2 * (L / l - 4)) ≤ lam2 * D * rexp (2 * (L / l - 4)) :=
    mul_le_mul_of_nonneg_right (by linarith) hE.le
  have h5 := mul_le_mul_of_nonneg_left hDle hlam
  nlinarith

/-- 【α-XI.1】L/ℓ ≥ 7 なら λ² ≥ 1:帽子の崩壊の時間 ℓ のうちに少なくとも 1 回 e 倍になる -/
theorem one_efold_before_collapse (L l uc lam2 : ℝ) (huc : 0 < uc) (huc2 : uc ≤ π / 2)
    (hjoin : sin uc = 1 / cosh (L / l)) (hL : 7 ≤ L / l) (hlam : 0 ≤ lam2)
    (hRay : -lam2 * (∫ y in (0 : ℝ)..4, (uc * rexp y) ^ 2 * sin (π / 4 * y) ^ 2)
      ≤ ∫ y in (0 : ℝ)..4, G2 uc 4 y) :
    1 ≤ lam2 := by
  have hb := growth_rate_bound L l uc lam2 huc huc2 hjoin (by linarith) hlam hRay
  have hpi := pi_pos
  have hπ2 : π ^ 2 < 9.93 := by nlinarith [pi_lt_d2]
  have hc : (0.12 : ℝ) ≤ 3 / 4 - π ^ 2 / 16 := by linarith
  have he1 : (2.7 : ℝ) ≤ rexp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have he6 : (2.7 : ℝ) ^ 6 ≤ rexp 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left (by norm_num) he1 6
  have hE : rexp 6 ≤ rexp (2 * (L / l - 4)) := Real.exp_le_exp.2 (by linarith)
  have hX : (387 : ℝ) ≤ rexp (2 * (L / l - 4)) := by linarith
  have key : π ^ 2 ≤ (3 / 4 - π ^ 2 / 16) * rexp (2 * (L / l - 4)) := by
    have := mul_le_mul hc hX (by norm_num) (by linarith)
    linarith
  have : 1 ≤ (3 / 4 - π ^ 2 / 16) * rexp (2 * (L / l - 4)) / π ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- 【α-XI.1】帽子の崩壊までの固有時間 ∫₀^{π/2} ℓ cos η dη = ℓ -/
theorem cap_collapse_time (l : ℝ) : ∫ η in (0 : ℝ)..(π / 2), l * cos η = l := by
  rw [intervalIntegral.integral_const_mul, integral_cos, sin_pi_div_two, sin_zero]
  ring

/-! ### XI.3 捕捉面 -/

/-- 【α-XI.3】波面 χ = π/2 − η の上で θ₊ ∝ cot χ − tan η = 0、θ₋ ∝ −cot χ − tan η < 0(0 < η < π/2) -/
theorem front_marginally_trapped (η : ℝ) (h0 : 0 < η) (h1 : η < π / 2) :
    cos (π / 2 - η) / sin (π / 2 - η) - sin η / cos η = 0 ∧
    -(cos (π / 2 - η) / sin (π / 2 - η)) - sin η / cos η < 0 := by
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub]
  have hc : 0 < cos η := cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hs : 0 < sin η := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  constructor
  · ring
  · have : 0 < sin η / cos η := div_pos hs hc
    linarith

/-- 【α-XI.3】首の球(半径 ℓ で一定):ヌルの方向の微分は 0、θ± = 0 -/
theorem neck_marginal (l t : ℝ) : HasDerivAt (fun _ : ℝ => l) 0 t := hasDerivAt_const t l

/-! ### 非空性(X.6) -/

/-- 窓の例:u₁ = 10⁻⁶、Y = 4(2π/√3 < 4、u₁e⁴ < π) -/
theorem nonempty_window : ∃ u1 Y : ℝ, 0 < u1 ∧ 2 * π / Real.sqrt 3 < Y ∧ u1 * rexp Y < π := by
  refine ⟨1 / 1000000, 4, by norm_num, ?_, ?_⟩
  · have h3 : (1.7 : ℝ) < Real.sqrt 3 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs : 0 < Real.sqrt 3 := by linarith
    rw [div_lt_iff₀ hs]
    have := pi_lt_d2
    nlinarith
  · have he : rexp 4 = rexp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : rexp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : rexp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left (exp_pos 1).le h1.le 4
    have := pi_gt_three
    rw [he]
    nlinarith

end CFT.FixNeck
