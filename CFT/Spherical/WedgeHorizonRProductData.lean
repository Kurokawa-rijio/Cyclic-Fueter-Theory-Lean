/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **r_u·r_v の正の下界（第一段：データ面での基線）**。
  `WedgeHorizonDefectZeroPoint` の発散補題は、地平線の近くで
  r_u·r_v ≥ m > 0（と Ω 項の下界）を仮定として使う。ここではその検証の
  第一段として、r_u·r_v が特性データの両面の上ではちょうど 0 であること
  を証明する。すなわち正の下界はデータ面からではなく、内部での成長から
  来るものであることが固定される。

  (1) 帽子（v = 0）では (1−W²)²/r² = 1 になるため、r_uv の右辺は
  −r_u·r_v/r だけになる。したがって s(u) := r_v(u, 0) は線形 ODE
  s′ = −(r_u/r)·s をみたし、角での s(0) = 0 と ODE の一意性
  （`eq_zero_of_hasDerivAt_eq_mul_of_exists_eq_zero`）から
  r_v(u, 0) = 0（`Dv_r_cap_eq_zero`）。係数の上界は明示形
  |c(u)| ≤ √2/(2·cos²(a/√2)) で与える。
  (2) 首（u = 0）では r ≡ 1、W ≡ 0 なので r_uv の右辺は 0 になり、
  t(v) := r_u(0, v) は微分 0 の定数で、角での t(0) = 0 から
  r_u(0, v) = 0（`Du_r_neck_eq_zero`）。こちらも同じ ODE 一意性補題を
  c = 0 として使う。
  (3) 帰結として r_u·r_v = 0 が両データ面上で成り立ち、帽子の内部では
  r_u(u, 0) = −(√2/2)·sin(√2·u) < 0 である（`Du_r_cap_neg`）。

  残りは、地平線の近くでの r_u·r_v の符号と正の下界の、実際のくさび解
  からの検証（内部での成長）と、Ω 項の下界、ρ そのものの構成である。
  恒等式の定数は sympy による明示計算（`/tmp/check_rprod.py`）でも照合済み。
-/
import CFT.Spherical.WedgeCornerConditions
import CFT.Spherical.WedgeUniqueness
import CFT.Spherical.WedgeHorizonDefectPropagation

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeCorner CFT.WedgeDefectPropagation

namespace CFT.WedgeRProductData

/-- √2 の正値性（繰り返し使う）。 -/
theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num)

/-- π/√2 = π·√2/2。 -/
theorem pi_div_sqrt_two : Real.pi / Real.sqrt 2 = Real.pi * Real.sqrt 2 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  rw [mul_assoc, h2]

/-- a < π/√2 なら a/√2 < π/2。 -/
theorem div_sqrt_two_lt_pi_div_two {a : ℝ} (ha2 : a < Real.pi / Real.sqrt 2) :
    a / Real.sqrt 2 < Real.pi / 2 := by
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := sqrt_two_pos
  have h3 : a * Real.sqrt 2 < Real.pi := (lt_div_iff₀ hsqrt2).mp ha2
  rw [div_lt_iff₀ hsqrt2]
  have h4 : Real.pi / 2 * Real.sqrt 2 = Real.pi / Real.sqrt 2 := by
    rw [pi_div_sqrt_two]; ring
  rw [h4]
  exact ha2

/-- 帽子データは a < π/√2 の範囲で正（cos(u/√2) > 0）。 -/
theorem capR_pos_of_mem_Icc {a u : ℝ} (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) : 0 < capR u := by
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := sqrt_two_pos
  have harg : u / Real.sqrt 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have h0 : (0 : ℝ) ≤ u / Real.sqrt 2 := div_nonneg hu.1 hsqrt2.le
      linarith [Real.pi_pos]
    · have h1 : u / Real.sqrt 2 ≤ a / Real.sqrt 2 :=
        (div_le_div_iff_of_pos_right hsqrt2).mpr hu.2
      exact lt_of_le_of_lt h1 (div_sqrt_two_lt_pi_div_two ha2)
  have hcos : 0 < Real.cos (u / Real.sqrt 2) := Real.cos_pos_of_mem_Ioo harg
  simp only [capR]
  exact pow_pos hcos 2

/-- 帽子データは a < π/√2 の範囲で 0 でない。 -/
theorem capR_ne_zero_of_mem_Icc {a u : ℝ} (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) : capR u ≠ 0 :=
  ne_of_gt (capR_pos_of_mem_Icc ha2 hu)

/-- 帽子面での r_u は capR の微分に等しい（C² 級の場の微分とデータの一致）。 -/
theorem Du_r_cap_eq {F : WedgeFields} {a b u : ℝ}
    (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (hu : u ∈ Icc (0 : ℝ) a) (hv0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    Du F.r u 0 = deriv capR u := by
  have h1 : HasDerivAt (fun t => F.r t 0) (Du F.r u 0) u :=
    hC2r.deriv_u u hu 0 hv0
  rw [slice_r_cap hdata] at h1
  exact h1.deriv.symm

/-- 帽子面では r_uv の右辺は −r_u·r_v/r だけになる（(1−W²)²/r² = 1 のため）。 -/
theorem rhsR_cap_eq {F : WedgeFields} {a u : ℝ}
    (hdata : HasWedgeData F) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) :
    rhsR (F.Om u 0) (F.W u 0) (Du F.r u 0) (Dv F.r u 0) (F.r u 0)
      = -(Du F.r u 0) * Dv F.r u 0 / capR u := by
  have hcap : capR u ≠ 0 := capR_ne_zero_of_mem_Icc ha2 hu
  have hW : 1 - capW u ^ 2 = capR u := by
    have h := Real.sin_sq_add_cos_sq (u / Real.sqrt 2)
    simp only [capW, capR]
    linarith [h]
  have h1 : (1 - capW u ^ 2) ^ 2 / capR u ^ 2 = 1 := by
    rw [hW, div_self (pow_ne_zero 2 hcap)]
  have h2 : (1 / 2 : ℝ) * capOm u * ((1 - capW u ^ 2) ^ 2 / capR u ^ 2 - 1)
      / capR u = 0 := by
    rw [h1]
    simp
  unfold rhsR
  rw [(hdata.1 u).2.1, (hdata.1 u).2.2, (hdata.1 u).1, h2]
  ring

/-- 帽子面での s(u) := r_v(u, 0) の微分方程式（線形 ODE の形）。 -/
theorem Dv_r_cap_ode {F : WedgeFields} {a b u : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    HasDerivAt (fun u' => Dv F.r u' 0)
      ((-(Du F.r u 0) / capR u) * Dv F.r u 0) u := by
  have hder : HasDerivAt (fun u' => Dv F.r u' 0) (Duv F.r u 0) u :=
    hC2r.deriv_uv_u u hu 0 hv0
  have hev : Duv F.r u 0
      = rhsR (F.Om u 0) (F.W u 0) (Du F.r u 0) (Dv F.r u 0) (F.r u 0) :=
    (heq u 0).1
  rw [hev, rhsR_cap_eq hdata ha2 hu] at hder
  convert hder using 1
  ring

/-- ODE の係数 c(u) = −r_u/r の明示的上界（帽子面、[0, a] の内部）。 -/
theorem coeff_bound {F : WedgeFields} {a b u : ℝ}
    (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (ha : 0 < a) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    |-(Du F.r u 0) / capR u|
      ≤ Real.sqrt 2 / (2 * (Real.cos (a / Real.sqrt 2)) ^ 2) := by
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := sqrt_two_pos
  have hDu : Du F.r u 0 = -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2 := by
    rw [Du_r_cap_eq hdata hC2r ⟨hu.1.le, hu.2.le⟩ hv0, deriv_capR]
  have hcap_pos : 0 < capR u := capR_pos_of_mem_Icc ha2 ⟨hu.1.le, hu.2.le⟩
  have hcap_eq : capR u = (Real.cos (u / Real.sqrt 2)) ^ 2 := rfl
  have hcos_a_pos : 0 < Real.cos (a / Real.sqrt 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have h0 : (0 : ℝ) ≤ a / Real.sqrt 2 := div_nonneg ha.le hsqrt2.le
      linarith [Real.pi_pos]
    · exact div_sqrt_two_lt_pi_div_two ha2
  have hcos_le : Real.cos (a / Real.sqrt 2) ≤ Real.cos (u / Real.sqrt 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (div_nonneg hu.1.le hsqrt2.le)
      (by have h2 := div_sqrt_two_lt_pi_div_two ha2
          linarith [Real.pi_pos])
      ((div_le_div_iff_of_pos_right hsqrt2).mpr hu.2.le)
  have hsq : (Real.cos (a / Real.sqrt 2)) ^ 2
      ≤ (Real.cos (u / Real.sqrt 2)) ^ 2 :=
    pow_le_pow_left₀ hcos_a_pos.le hcos_le 2
  have hnum : |-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2|
      ≤ Real.sqrt 2 / 2 := by
    have h1 : |-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2|
        = Real.sqrt 2 * |Real.sin (Real.sqrt 2 * u)| / 2 := by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hsqrt2]
      norm_num
    rw [h1]
    have hsin : |Real.sin (Real.sqrt 2 * u)| ≤ 1 := Real.abs_sin_le_one _
    have h2 : Real.sqrt 2 * |Real.sin (Real.sqrt 2 * u)| ≤ Real.sqrt 2 := by
      simpa using mul_le_mul_of_nonneg_left hsin (Real.sqrt_nonneg 2)
    linarith [h2]
  calc |-(Du F.r u 0) / capR u|
      = |Du F.r u 0| / capR u := by
        rw [abs_div, abs_neg, abs_of_pos hcap_pos]
    _ = |-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2|
          / (Real.cos (u / Real.sqrt 2)) ^ 2 := by
        rw [hDu, hcap_eq]
    _ ≤ (Real.sqrt 2 / 2) / (Real.cos (a / Real.sqrt 2)) ^ 2 :=
        div_le_div₀ (by positivity) hnum (pow_pos hcos_a_pos 2) hsq
    _ = Real.sqrt 2 / (2 * (Real.cos (a / Real.sqrt 2)) ^ 2) := by ring

/-- 帽子面では r_v ≡ 0（s(u) := r_v(u, 0) の線形 ODE と角での初期値による）。 -/
theorem Dv_r_cap_eq_zero {F : WedgeFields} {a b u : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (ha : 0 < a) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    Dv F.r u 0 = 0 := by
  exact eq_zero_of_hasDerivAt_eq_mul_of_exists_eq_zero
    (f := fun u' => Dv F.r u' 0)
    (c := fun u' => -(Du F.r u' 0) / capR u')
    (a := (0 : ℝ)) (b := a)
    (M := Real.sqrt 2 / (2 * (Real.cos (a / Real.sqrt 2)) ^ 2))
    (fun t ht => Dv_r_cap_ode heq hdata hC2r ha2 ht hv0)
    (fun t ht => coeff_bound hdata hC2r ha ha2 ht hv0)
    ⟨0, ⟨le_rfl, ha.le⟩, data_r_v hdata⟩
    hu

/-- 首面では r_v ≡ 0（r ≡ 1 は v 方向に定数）。 -/
theorem Dv_r_neck_eq_zero {F : WedgeFields} {v : ℝ}
    (hdata : HasWedgeData F) : Dv F.r 0 v = 0 := by
  show deriv (fun v' => F.r 0 v') v = 0
  rw [slice_r_neck hdata]
  simp

/-- 首面では r_uv の右辺は 0（(1−W²)²/r² = 1 かつ r_v = 0 のため）。 -/
theorem rhsR_neck_eq_zero {F : WedgeFields} {v : ℝ}
    (hdata : HasWedgeData F) :
    rhsR (F.Om 0 v) (F.W 0 v) (Du F.r 0 v) (Dv F.r 0 v) (F.r 0 v) = 0 := by
  rw [(hdata.2 v).1, (hdata.2 v).2.2, Dv_r_neck_eq_zero hdata]
  unfold rhsR
  norm_num

/-- 首面での t(v) := r_u(0, v) の微分は 0（右辺が 0 のため）。 -/
theorem Du_r_neck_ode {F : WedgeFields} {a b v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (hv : v ∈ Icc (0 : ℝ) b) (ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a) :
    HasDerivAt (fun v' => Du F.r 0 v') ((0 : ℝ) * Du F.r 0 v) v := by
  have hder : HasDerivAt (fun v' => Du F.r 0 v') (Duv F.r 0 v) v :=
    hC2r.deriv_uv_v 0 ha0 v hv
  have hev : Duv F.r 0 v
      = rhsR (F.Om 0 v) (F.W 0 v) (Du F.r 0 v) (Dv F.r 0 v) (F.r 0 v) :=
    (heq 0 v).1
  rw [hev, rhsR_neck_eq_zero hdata] at hder
  simpa using hder

/-- 首面では r_u ≡ 0（t(v) の微分が 0 で角での初期値も 0）。 -/
theorem Du_r_neck_eq_zero {F : WedgeFields} {a b v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (hb : 0 < b) (hv : v ∈ Icc (0 : ℝ) b) (ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a) :
    Du F.r 0 v = 0 := by
  exact eq_zero_of_hasDerivAt_eq_mul_of_exists_eq_zero
    (f := fun v' => Du F.r 0 v')
    (c := fun _ => (0 : ℝ))
    (a := (0 : ℝ)) (b := b)
    (M := (0 : ℝ))
    (fun t ht => Du_r_neck_ode heq hdata hC2r ht ha0)
    (fun t ht => by simp)
    ⟨0, ⟨le_rfl, hb.le⟩, data_r_u hdata⟩
    hv

/-- 帽子面では r_u·r_v = 0。 -/
theorem rProduct_eq_zero_cap {F : WedgeFields} {a b u : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (ha : 0 < a) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    Du F.r u 0 * Dv F.r u 0 = 0 := by
  rw [Dv_r_cap_eq_zero heq hdata hC2r ha ha2 hu hv0, mul_zero]

/-- 首面では r_u·r_v = 0。 -/
theorem rProduct_eq_zero_neck {F : WedgeFields} {a b v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (hb : 0 < b) (hv : v ∈ Icc (0 : ℝ) b) (ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a) :
    Du F.r 0 v * Dv F.r 0 v = 0 := by
  rw [Du_r_neck_eq_zero heq hdata hC2r hb hv ha0, zero_mul]

/-- 帽子の内部では r_u < 0（r は帽子に沿って狭義単調減少）。 -/
theorem Du_r_cap_neg {F : WedgeFields} {a b u : ℝ}
    (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (ha : 0 < a) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    Du F.r u 0 < 0 := by
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := sqrt_two_pos
  have hDu : Du F.r u 0 = -(Real.sqrt 2 * Real.sin (Real.sqrt 2 * u)) / 2 := by
    rw [Du_r_cap_eq hdata hC2r ⟨hu.1.le, hu.2.le⟩ hv0, deriv_capR]
  rw [hDu]
  have hsin : 0 < Real.sin (Real.sqrt 2 * u) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hsqrt2 hu.1
    · have h1 : Real.sqrt 2 * u < Real.sqrt 2 * a :=
        mul_lt_mul_of_pos_left hu.2 hsqrt2
      have h2 : Real.sqrt 2 * a < Real.pi := by
        rw [mul_comm]
        exact (lt_div_iff₀ hsqrt2).mp ha2
      exact lt_trans h1 h2
  have hpos : (0 : ℝ) < Real.sqrt 2 * Real.sin (Real.sqrt 2 * u) :=
    mul_pos hsqrt2 hsin
  linarith [hpos]

/-- まとめ：r_u·r_v のデータ面での基線。 -/
theorem rProduct_data_baseline {F : WedgeFields} {a b : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F) (hC2r : C2On a b F.r)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a) (hb0 : (0 : ℝ) ∈ Icc (0 : ℝ) b) :
    (∀ u ∈ Icc (0 : ℝ) a, Dv F.r u 0 = 0)
      ∧ (∀ v ∈ Icc (0 : ℝ) b, Du F.r 0 v = 0)
      ∧ (∀ u ∈ Icc (0 : ℝ) a, Du F.r u 0 * Dv F.r u 0 = 0)
      ∧ (∀ v ∈ Icc (0 : ℝ) b, Du F.r 0 v * Dv F.r 0 v = 0)
      ∧ (∀ u ∈ Ioo (0 : ℝ) a, Du F.r u 0 < 0) :=
  ⟨fun u hu => Dv_r_cap_eq_zero heq hdata hC2r ha ha2 hu hb0,
   fun v hv => Du_r_neck_eq_zero heq hdata hC2r hb hv ha0,
   fun u hu => rProduct_eq_zero_cap heq hdata hC2r ha ha2 hu hb0,
   fun v hv => rProduct_eq_zero_neck heq hdata hC2r hb hv ha0,
   fun u hu => Du_r_cap_neg hdata hC2r ha ha2 hu hb0⟩

end CFT.WedgeRProductData
