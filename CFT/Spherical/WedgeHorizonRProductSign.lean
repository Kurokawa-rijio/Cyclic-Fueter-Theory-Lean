/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **r_u·r_v の内部での符号（第二段：拘束からの非正性）**。前段
  （`WedgeHorizonRProductData`）では r_u·r_v が特性データの両面の上では
  ちょうど 0 であること（帽子では r_v ≡ 0、首では r_u ≡ 0）と、帽子の内部
  では r_u < 0 であることを示した。ここでは拘束方程式から、内部でも
  r_u ≤ 0 かつ r_v ≤ 0 であること、したがって r_u·r_v ≥ 0 であることを示す。

  鍵は拘束を商の微分として読むことである。C_v は
    Dvv r − (Dv Ω/Ω)·Dv r + 2(Dv W)²/r = 0
  すなわち Dv (Dv r/Ω) = −2(Dv W)²/(r·Ω) ≤ 0（r > 0、Ω > 0 のもと）で
  ある。v = 0 では Dv r/Ω = 0（帽子で r_v = 0）なので、v 方向の単調性から
  内部では Dv r/Ω ≤ 0、したがって Dv r ≤ 0（`Dv_r_le_zero`）。
  C_u についても対称に、Du (Du r/Ω) = −2(Du W)²/(r·Ω) ≤ 0 で、u = 0 では
  Du r/Ω = 0（首で r_u = 0）なので、内部では Du r ≤ 0（`Du_r_le_zero`）。
  したがって r_u·r_v ≥ 0（`rProduct_nonneg`）。

  注意：C2On は混合 C² 級のみ（∂_u²、∂_v² は含まない）なので、Dvv・Duu
  の存在は他モジュールと同様に `HasDerivAt` の仮定として渡す。
  残りは、正の下界 r_u·r_v ≥ m > 0（`WedgeHorizonDefectZeroPoint` の
  仮定そのもの）と、Ω 項の下界、ρ そのものの構成である。
  恒等式の定数は sympy による明示計算（`/tmp/check_rprod_sign.py`）でも照合済み。
-/
import CFT.Spherical.WedgeHorizonRProductData

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeUniq CFT.WedgeRProductData CFT.CharUniqueness

namespace CFT.WedgeRProductSign

/-- C_v を商の微分として読む：v ↦ Dv r/Ω の微分は −2(Dv W)²/(r·Ω)。 -/
theorem Dv_r_div_Om_hasDerivAt {F : WedgeFields} {a b u v : ℝ}
    (hcon : WedgeConstraints F) (hC2Om : C2On a b F.Om)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    HasDerivAt (fun v' => Dv F.r u v' / F.Om u v')
      (-2 * (Dv F.W u v) ^ 2 / (F.r u v * F.Om u v)) v := by
  have hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v :=
    hC2Om.deriv_v u hu v hv
  have hdiv := hrvv.div hOmv hOm
  have hC := (hcon u v).2
  have key : Dvv F.r u v * F.Om u v - Dv F.r u v * Dv F.Om u v
      = -2 * (Dv F.W u v) ^ 2 * F.Om u v / F.r u v := by
    have hC' : Dvv F.r u v
        = (Dv F.Om u v / F.Om u v) * Dv F.r u v
          - 2 * (Dv F.W u v) ^ 2 / F.r u v := by
      linarith [hC]
    rw [hC']
    field_simp
    ring
  rw [key] at hdiv
  convert hdiv using 1
  field_simp
  ring

/-- v ↦ Dv r/Ω の微分は ≤ 0（r > 0、Ω > 0 のもと）。 -/
theorem Dv_r_div_Om_deriv_nonpos {F : WedgeFields} {a b u v : ℝ}
    (hcon : WedgeConstraints F) (hC2Om : C2On a b F.Om)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : 0 < F.Om u v) (hr : 0 < F.r u v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    deriv (fun v' => Dv F.r u v' / F.Om u v') v ≤ 0 := by
  rw [(Dv_r_div_Om_hasDerivAt hcon hC2Om hu hv hOm.ne' hr.ne' hrvv).deriv]
  have h3 : (0 : ℝ) ≤ 2 * (Dv F.W u v) ^ 2 / (F.r u v * F.Om u v) :=
    div_nonneg (by positivity) (mul_pos hr hOm).le
  have h4 : -2 * (Dv F.W u v) ^ 2 / (F.r u v * F.Om u v)
      = -(2 * (Dv F.W u v) ^ 2 / (F.r u v * F.Om u v)) := by ring
  rw [h4]
  exact neg_nonpos.mpr h3

/-- v ↦ Dv r/Ω は区間 [0, b] の上で連続。 -/
theorem Dv_r_div_Om_continuousOn {F : WedgeFields} {a b u : ℝ}
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (hu : u ∈ Icc (0 : ℝ) a)
    (hOm : ∀ v ∈ Icc (0 : ℝ) b, F.Om u v ≠ 0) :
    ContinuousOn (fun v' => Dv F.r u v' / F.Om u v') (Icc (0 : ℝ) b) := by
  have h1 : ContinuousOn (fun v' => Dv F.r u v') (Icc (0 : ℝ) b) :=
    sliceOn1 hC2r.cont_v hu
  have h2 : ContinuousOn (fun v' => F.Om u v') (Icc (0 : ℝ) b) :=
    sliceOn1 hC2Om.cont hu
  exact h1.div h2 hOm

/-- 内部では r_v ≤ 0（帽子で r_v = 0、拘束から Dv r/Ω は v 方向に非増加）。 -/
theorem Dv_r_le_zero {F : WedgeFields} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hrvv : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u' v'') (Dvv F.r u' v') v') :
    Dv F.r u v ≤ 0 := by
  have hb0 : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hcont : ContinuousOn (fun v' => Dv F.r u v' / F.Om u v')
      (Icc (0 : ℝ) b) :=
    Dv_r_div_Om_continuousOn hC2r hC2Om hu
      (fun v' hv' => (hOm u hu v' hv').ne')
  have hdiff : DifferentiableOn ℝ (fun v' => Dv F.r u v' / F.Om u v')
      (interior (Icc (0 : ℝ) b)) := by
    intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Icc (0 : ℝ) b := ⟨hx.1.le, hx.2.le⟩
    have hd : DifferentiableAt ℝ (fun v' => Dv F.r u v' / F.Om u v') x :=
      (Dv_r_div_Om_hasDerivAt hcon hC2Om hu hxI
        (hOm u hu x hxI).ne' (hr u hu x hxI).ne' (hrvv u hu x hxI)).differentiableAt
    exact hd.differentiableWithinAt
  have hder : ∀ x ∈ interior (Icc (0 : ℝ) b),
      deriv (fun v' => Dv F.r u v' / F.Om u v') x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Icc (0 : ℝ) b := ⟨hx.1.le, hx.2.le⟩
    exact Dv_r_div_Om_deriv_nonpos hcon hC2Om hu hxI
      (hOm u hu x hxI) (hr u hu x hxI) (hrvv u hu x hxI)
  have hanti : AntitoneOn (fun v' => Dv F.r u v' / F.Om u v') (Icc (0 : ℝ) b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) b) hcont hdiff hder
  have h0 : Dv F.r u 0 / F.Om u 0 = 0 := by
    rw [Dv_r_cap_eq_zero heq hdata hC2r ha ha2 hu hb0]
    simp
  have hle : Dv F.r u v / F.Om u v ≤ Dv F.r u 0 / F.Om u 0 := hanti hb0 hv hv.1
  rw [h0] at hle
  have hOmv : 0 < F.Om u v := hOm u hu v hv
  have hle2 : Dv F.r u v ≤ 0 * F.Om u v := (div_le_iff₀ hOmv).mp hle
  simpa using hle2

/-- C_u を商の微分として読む：u ↦ Du r/Ω の微分は −2(Du W)²/(r·Ω)。 -/
theorem Du_r_div_Om_hasDerivAt {F : WedgeFields} {a b u v : ℝ}
    (hcon : WedgeConstraints F) (hC2Om : C2On a b F.Om)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : F.Om u v ≠ 0) (hr : F.r u v ≠ 0)
    (hruu : HasDerivAt (fun u' => Du F.r u' v) (Duu F.r u v) u) :
    HasDerivAt (fun u' => Du F.r u' v / F.Om u' v)
      (-2 * (Du F.W u v) ^ 2 / (F.r u v * F.Om u v)) u := by
  have hOmu : HasDerivAt (fun u' => F.Om u' v) (Du F.Om u v) u :=
    hC2Om.deriv_u u hu v hv
  have hdiv := hruu.div hOmu hOm
  have hC := (hcon u v).1
  have key : Duu F.r u v * F.Om u v - Du F.r u v * Du F.Om u v
      = -2 * (Du F.W u v) ^ 2 * F.Om u v / F.r u v := by
    have hC' : Duu F.r u v
        = (Du F.Om u v / F.Om u v) * Du F.r u v
          - 2 * (Du F.W u v) ^ 2 / F.r u v := by
      linarith [hC]
    rw [hC']
    field_simp
    ring
  rw [key] at hdiv
  convert hdiv using 1
  field_simp
  ring

/-- u ↦ Du r/Ω の微分は ≤ 0（r > 0、Ω > 0 のもと）。 -/
theorem Du_r_div_Om_deriv_nonpos {F : WedgeFields} {a b u v : ℝ}
    (hcon : WedgeConstraints F) (hC2Om : C2On a b F.Om)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : 0 < F.Om u v) (hr : 0 < F.r u v)
    (hruu : HasDerivAt (fun u' => Du F.r u' v) (Duu F.r u v) u) :
    deriv (fun u' => Du F.r u' v / F.Om u' v) u ≤ 0 := by
  rw [(Du_r_div_Om_hasDerivAt hcon hC2Om hu hv hOm.ne' hr.ne' hruu).deriv]
  have h3 : (0 : ℝ) ≤ 2 * (Du F.W u v) ^ 2 / (F.r u v * F.Om u v) :=
    div_nonneg (by positivity) (mul_pos hr hOm).le
  have h4 : -2 * (Du F.W u v) ^ 2 / (F.r u v * F.Om u v)
      = -(2 * (Du F.W u v) ^ 2 / (F.r u v * F.Om u v)) := by ring
  rw [h4]
  exact neg_nonpos.mpr h3

/-- u ↦ Du r/Ω は区間 [0, a] の上で連続。 -/
theorem Du_r_div_Om_continuousOn {F : WedgeFields} {a b v : ℝ}
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u ∈ Icc (0 : ℝ) a, F.Om u v ≠ 0) :
    ContinuousOn (fun u' => Du F.r u' v / F.Om u' v) (Icc (0 : ℝ) a) := by
  have h1 : ContinuousOn (fun u' => Du F.r u' v) (Icc (0 : ℝ) a) :=
    sliceOn2 hC2r.cont_u hv
  have h2 : ContinuousOn (fun u' => F.Om u' v) (Icc (0 : ℝ) a) :=
    sliceOn2 hC2Om.cont hv
  exact h1.div h2 hOm

/-- 内部では r_u ≤ 0（首で r_u = 0、拘束から Du r/Ω は u 方向に非増加）。 -/
theorem Du_r_le_zero {F : WedgeFields} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun u'' => Du F.r u'' v') (Duu F.r u' v') u') :
    Du F.r u v ≤ 0 := by
  have ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a := ⟨le_rfl, ha.le⟩
  have hcont : ContinuousOn (fun u' => Du F.r u' v / F.Om u' v)
      (Icc (0 : ℝ) a) :=
    Du_r_div_Om_continuousOn hC2r hC2Om hv
      (fun u' hu' => (hOm u' hu' v hv).ne')
  have hdiff : DifferentiableOn ℝ (fun u' => Du F.r u' v / F.Om u' v)
      (interior (Icc (0 : ℝ) a)) := by
    intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Icc (0 : ℝ) a := ⟨hx.1.le, hx.2.le⟩
    have hd : DifferentiableAt ℝ (fun u' => Du F.r u' v / F.Om u' v) x :=
      (Du_r_div_Om_hasDerivAt hcon hC2Om hxI hv
        (hOm x hxI v hv).ne' (hr x hxI v hv).ne' (hruu x hxI v hv)).differentiableAt
    exact hd.differentiableWithinAt
  have hder : ∀ x ∈ interior (Icc (0 : ℝ) a),
      deriv (fun u' => Du F.r u' v / F.Om u' v) x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Icc (0 : ℝ) a := ⟨hx.1.le, hx.2.le⟩
    exact Du_r_div_Om_deriv_nonpos hcon hC2Om hxI hv
      (hOm x hxI v hv) (hr x hxI v hv) (hruu x hxI v hv)
  have hanti : AntitoneOn (fun u' => Du F.r u' v / F.Om u' v) (Icc (0 : ℝ) a) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) a) hcont hdiff hder
  have h0 : Du F.r 0 v / F.Om 0 v = 0 := by
    rw [Du_r_neck_eq_zero heq hdata hC2r hb hv ha0]
    simp
  have hle : Du F.r u v / F.Om u v ≤ Du F.r 0 v / F.Om 0 v := hanti ha0 hu hu.1
  rw [h0] at hle
  have hOmu : 0 < F.Om u v := hOm u hu v hv
  have hle2 : Du F.r u v ≤ 0 * F.Om u v := (div_le_iff₀ hOmu).mp hle
  simpa using hle2

/-- 内部では r_u·r_v ≥ 0（両因子とも ≤ 0）。 -/
theorem rProduct_nonneg {F : WedgeFields} {a b u v : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hrvv : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u' v'') (Dvv F.r u' v') v')
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun u'' => Du F.r u'' v') (Duu F.r u' v') u') :
    0 ≤ Du F.r u v * Dv F.r u v :=
  mul_nonneg_of_nonpos_of_nonpos
    (Du_r_le_zero heq hdata hcon hC2r hC2Om ha hb hu hv hOm hr hruu)
    (Dv_r_le_zero heq hdata hcon hC2r hC2Om ha hb ha2 hu hv hOm hr hrvv)

/-- まとめ：r_u・r_v の内部での符号。 -/
theorem rProduct_sign_interior {F : WedgeFields} {a b : ℝ}
    (heq : WedgeEvolutionEqs F) (hdata : HasWedgeData F)
    (hcon : WedgeConstraints F)
    (hC2r : C2On a b F.r) (hC2Om : C2On a b F.Om)
    (ha : 0 < a) (hb : 0 < b) (ha2 : a < Real.pi / Real.sqrt 2)
    (ha0 : (0 : ℝ) ∈ Icc (0 : ℝ) a) (hb0 : (0 : ℝ) ∈ Icc (0 : ℝ) b)
    (hOm : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.Om u' v')
    (hr : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b, 0 < F.r u' v')
    (hrvv : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun v'' => Dv F.r u' v'') (Dvv F.r u' v') v')
    (hruu : ∀ u' ∈ Icc (0 : ℝ) a, ∀ v' ∈ Icc (0 : ℝ) b,
      HasDerivAt (fun u'' => Du F.r u'' v') (Duu F.r u' v') u') :
    (∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) b, Du F.r u v ≤ 0)
      ∧ (∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) b, Dv F.r u v ≤ 0)
      ∧ (∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) b,
          0 ≤ Du F.r u v * Dv F.r u v)
      ∧ (∀ u ∈ Ioo (0 : ℝ) a, Du F.r u 0 < 0) :=
  ⟨fun u hu v hv => Du_r_le_zero heq hdata hcon hC2r hC2Om ha hb hu hv hOm hr hruu,
   fun u hu v hv => Dv_r_le_zero heq hdata hcon hC2r hC2Om ha hb ha2 hu hv hOm hr hrvv,
   fun u hu v hv => rProduct_nonneg heq hdata hcon hC2r hC2Om ha hb ha2 hu hv hOm hr hrvv hruu,
   fun u hu => Du_r_cap_neg hdata hC2r ha ha2 hu hb0⟩

end CFT.WedgeRProductSign
