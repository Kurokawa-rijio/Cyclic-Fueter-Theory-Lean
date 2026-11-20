/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **ソース項 S の v 微分の明示形（形式微分）**。前段
  （`WedgeHorizonDefectSource`）ではソース項 S が
    S = Ω(1−W²)²·a(r) + Ω·b(r) + r_u·r_v·c(r),
    a(r) = −2/r⁴ − g/(2r³), b(r) = 1/r² + g/(2r),
    c(r) = 2/r² − g′ + g/r
  と書き直された。ここではその明示形を v で形式的に微分し、
  ∂_v S の明示形を証明する（`defectSource_hasDerivAt_v`・
  `defectSource_deriv_v`）。微分には Ω_v, W_v, r_v, r_uv, r_vv と
  g, g′ の連鎖律（g″ まで）が入る。r_uv・r_vv はここでは抽象的な
  微分値として受け取る（発展方程式・拘束 C_v の代入は次の段）。
  係数 a, b, c の r 微分は
    da/dr = 8/r⁵ − g′/(2r³) + 3g/(2r⁴),
    db/dr = −2/r³ + g′/(2r) − g/(2r²),
    dc/dr = −4/r³ − g″ + g′/r − g/r²
  であり、恒等式の定数は sympy による明示計算
  （`/tmp/check_dSdv4.py`、構造化した明示形と直接微分の差 0）でも
  照合済み。RN への特殊化（`defectSource_hasDerivAt_v_rn`）では
  g = `rnLogDeriv`、g′ = `rnLogDeriv'`、g″ = `rnLogDeriv''` を使う。
-/
import CFT.Spherical.WedgeHorizonDefectSource

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource CFT.RNLogDeriv

namespace CFT.WedgeDefectSourceDeriv

/-- 係数 a(r) = −2/r⁴ − g/(2r³) の v 微分（連鎖律による）。 -/
theorem srcA_hasDerivAt_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v) :
    HasDerivAt (fun v' => -2 / (F.r u v') ^ 4 - g (F.r u v') / (2 * (F.r u v') ^ 3))
      ((8 / (F.r u v) ^ 5 - g' (F.r u v) / (2 * (F.r u v) ^ 3)
        + 3 * g (F.r u v) / (2 * (F.r u v) ^ 4)) * Dv F.r u v) v := by
  have h4 : HasDerivAt (fun v' => (F.r u v') ^ 4)
      (4 * (F.r u v) ^ 3 * Dv F.r u v) v := by
    have h := hrv.pow 4
    convert h using 1
  have hi : HasDerivAt (fun v' => ((F.r u v') ^ 4)⁻¹)
      (-(4 * (F.r u v) ^ 3 * Dv F.r u v) / ((F.r u v) ^ 4) ^ 2) v :=
    h4.inv (pow_ne_zero 4 hr)
  have h1 : HasDerivAt (fun v' => -2 / (F.r u v') ^ 4)
      ((8 / (F.r u v) ^ 5) * Dv F.r u v) v := by
    have h := hi.const_mul (-2)
    convert h using 1
    field_simp
    ring
  have h3 : HasDerivAt (fun v' => (F.r u v') ^ 3)
      (3 * (F.r u v) ^ 2 * Dv F.r u v) v := by
    have h := hrv.pow 3
    convert h using 1
  have h3' : HasDerivAt (fun v' => 2 * (F.r u v') ^ 3)
      (2 * (3 * (F.r u v) ^ 2 * Dv F.r u v)) v := h3.const_mul 2
  have hgcomp : HasDerivAt (fun v' => g (F.r u v'))
      (g' (F.r u v) * Dv F.r u v) v := hg.comp v hrv
  have h2 : HasDerivAt (fun v' => g (F.r u v') / (2 * (F.r u v') ^ 3))
      ((g' (F.r u v) / (2 * (F.r u v) ^ 3)
        - 3 * g (F.r u v) / (2 * (F.r u v) ^ 4)) * Dv F.r u v) v := by
    have h := hgcomp.div h3' (mul_ne_zero two_ne_zero (pow_ne_zero 3 hr))
    convert h using 1
    field_simp
    ring
  have h := h1.sub h2
  convert h using 1
  field_simp
  ring

/-- 係数 b(r) = 1/r² + g/(2r) の v 微分（連鎖律による）。 -/
theorem srcB_hasDerivAt_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v) :
    HasDerivAt (fun v' => 1 / (F.r u v') ^ 2 + g (F.r u v') / (2 * F.r u v'))
      ((-2 / (F.r u v) ^ 3 + g' (F.r u v) / (2 * F.r u v)
        - g (F.r u v) / (2 * (F.r u v) ^ 2)) * Dv F.r u v) v := by
  have h2 : HasDerivAt (fun v' => (F.r u v') ^ 2)
      (2 * (F.r u v) * Dv F.r u v) v := by
    have h := hrv.pow 2
    convert h using 1
    ring
  have hi : HasDerivAt (fun v' => ((F.r u v') ^ 2)⁻¹)
      (-(2 * (F.r u v) * Dv F.r u v) / ((F.r u v) ^ 2) ^ 2) v :=
    h2.inv (pow_ne_zero 2 hr)
  have h1 : HasDerivAt (fun v' => 1 / (F.r u v') ^ 2)
      ((-2 / (F.r u v) ^ 3) * Dv F.r u v) v := by
    have h := hi
    convert h using 1
    · ext v'
      rw [one_div]
    · field_simp
      ring
  have h2' : HasDerivAt (fun v' => 2 * F.r u v') (2 * Dv F.r u v) v :=
    hrv.const_mul 2
  have hgcomp : HasDerivAt (fun v' => g (F.r u v'))
      (g' (F.r u v) * Dv F.r u v) v := hg.comp v hrv
  have h2b : HasDerivAt (fun v' => g (F.r u v') / (2 * F.r u v'))
      ((g' (F.r u v) / (2 * F.r u v) - g (F.r u v) / (2 * (F.r u v) ^ 2))
        * Dv F.r u v) v := by
    have h := hgcomp.div h2' (mul_ne_zero two_ne_zero hr)
    convert h using 1
    field_simp
    ring
  have h := h1.add h2b
  convert h using 1
  field_simp
  ring

/-- 係数 c(r) = 2/r² − g′ + g/r の v 微分（連鎖律による）。 -/
theorem srcC_hasDerivAt_v {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v) :
    HasDerivAt (fun v' => 2 / (F.r u v') ^ 2 - g' (F.r u v')
        + g (F.r u v') / F.r u v')
      ((-4 / (F.r u v) ^ 3 - g'' (F.r u v) + g' (F.r u v) / F.r u v
        - g (F.r u v) / (F.r u v) ^ 2) * Dv F.r u v) v := by
  have h2 : HasDerivAt (fun v' => (F.r u v') ^ 2)
      (2 * (F.r u v) * Dv F.r u v) v := by
    have h := hrv.pow 2
    convert h using 1
    ring
  have hi : HasDerivAt (fun v' => ((F.r u v') ^ 2)⁻¹)
      (-(2 * (F.r u v) * Dv F.r u v) / ((F.r u v) ^ 2) ^ 2) v :=
    h2.inv (pow_ne_zero 2 hr)
  have h1 : HasDerivAt (fun v' => 2 / (F.r u v') ^ 2)
      ((-4 / (F.r u v) ^ 3) * Dv F.r u v) v := by
    have h := hi.const_mul 2
    convert h using 1
    field_simp
    ring
  have h2' : HasDerivAt (fun v' => g' (F.r u v'))
      (g'' (F.r u v) * Dv F.r u v) v := hg'.comp v hrv
  have h3 : HasDerivAt (fun v' => g (F.r u v') / F.r u v')
      ((g' (F.r u v) / F.r u v - g (F.r u v) / (F.r u v) ^ 2)
        * Dv F.r u v) v := by
    have h := (hg.comp v hrv).div hrv hr
    convert h using 1
    field_simp
    ring
  have h := (h1.sub h2').add h3
  convert h using 1
  field_simp
  ring

/-- ∂_v S の第 1 項 Ω(1−W²)²·a(r) の寄与。 -/
noncomputable def defectSourceDerivV1 (F : WedgeFields) (g g' : ℝ → ℝ) (u v : ℝ) : ℝ :=
  Dv F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
      * (-2 / (F.r u v) ^ 4 - g (F.r u v) / (2 * (F.r u v) ^ 3))
    + F.Om u v * (-4 * F.W u v * (1 - (F.W u v) ^ 2) * Dv F.W u v)
      * (-2 / (F.r u v) ^ 4 - g (F.r u v) / (2 * (F.r u v) ^ 3))
    + F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
      * ((8 / (F.r u v) ^ 5 - g' (F.r u v) / (2 * (F.r u v) ^ 3)
        + 3 * g (F.r u v) / (2 * (F.r u v) ^ 4)) * Dv F.r u v)

/-- ∂_v S の第 2 項 Ω·b(r) の寄与。 -/
noncomputable def defectSourceDerivV2 (F : WedgeFields) (g g' : ℝ → ℝ) (u v : ℝ) : ℝ :=
  Dv F.Om u v * (1 / (F.r u v) ^ 2 + g (F.r u v) / (2 * F.r u v))
    + F.Om u v * ((-2 / (F.r u v) ^ 3 + g' (F.r u v) / (2 * F.r u v)
      - g (F.r u v) / (2 * (F.r u v) ^ 2)) * Dv F.r u v)

/-- ∂_v S の第 3 項 r_u·r_v·c(r) の寄与。 -/
noncomputable def defectSourceDerivV3 (F : WedgeFields) (g g' g'' : ℝ → ℝ) (u v : ℝ) : ℝ :=
  Duv F.r u v * Dv F.r u v
      * (2 / (F.r u v) ^ 2 - g' (F.r u v) + g (F.r u v) / F.r u v)
    + Du F.r u v * Dvv F.r u v
      * (2 / (F.r u v) ^ 2 - g' (F.r u v) + g (F.r u v) / F.r u v)
    + Du F.r u v * Dv F.r u v
      * ((-4 / (F.r u v) ^ 3 - g'' (F.r u v) + g' (F.r u v) / F.r u v
        - g (F.r u v) / (F.r u v) ^ 2) * Dv F.r u v)

/-- ∂_v S の明示形（3 項の寄与の和）。 -/
noncomputable def defectSourceDerivV (F : WedgeFields) (g g' g'' : ℝ → ℝ) (u v : ℝ) : ℝ :=
  defectSourceDerivV1 F g g' u v
    + (defectSourceDerivV2 F g g' u v + defectSourceDerivV3 F g g' g'' u v)

/-- 第 1 項 Ω(1−W²)²·a(r) の v 微分。 -/
theorem defectSourceTerm1_hasDerivAt_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v) :
    HasDerivAt (fun v' => F.Om u v' * (1 - (F.W u v') ^ 2) ^ 2
        * (-2 / (F.r u v') ^ 4 - g (F.r u v') / (2 * (F.r u v') ^ 3)))
      (defectSourceDerivV1 F g g' u v) v := by
  have hWsq : HasDerivAt (fun v' => (F.W u v') ^ 2)
      (2 * F.W u v * Dv F.W u v) v := by
    have h := hWv.pow 2
    convert h using 1
    ring
  have hW2 : HasDerivAt (fun v' => (1 - (F.W u v') ^ 2) ^ 2)
      (-4 * F.W u v * (1 - (F.W u v) ^ 2) * Dv F.W u v) v := by
    have h1 : HasDerivAt (fun v' => 1 - (F.W u v') ^ 2)
        (0 - 2 * F.W u v * Dv F.W u v) v :=
      (hasDerivAt_const v (1 : ℝ)).sub hWsq
    have h := h1.pow 2
    convert h using 1
    ring
  have ha := srcA_hasDerivAt_v hr hg hrv
  have h := (hOmv.mul hW2).mul ha
  convert h using 1
  simp only [defectSourceDerivV1]
  ring

/-- 第 2 項 Ω·b(r) の v 微分。 -/
theorem defectSourceTerm2_hasDerivAt_v {F : WedgeFields} {g g' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v) :
    HasDerivAt (fun v' => F.Om u v' * (1 / (F.r u v') ^ 2 + g (F.r u v') / (2 * F.r u v')))
      (defectSourceDerivV2 F g g' u v) v := by
  have hb := srcB_hasDerivAt_v hr hg hrv
  have h := hOmv.mul hb
  convert h using 1

/-- 第 3 項 r_u·r_v·c(r) の v 微分。 -/
theorem defectSourceTerm3_hasDerivAt_v {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    HasDerivAt (fun v' => Du F.r u v' * Dv F.r u v'
        * (2 / (F.r u v') ^ 2 - g' (F.r u v') + g (F.r u v') / F.r u v'))
      (defectSourceDerivV3 F g g' g'' u v) v := by
  have hc := srcC_hasDerivAt_v hr hg hg' hrv
  have h := (hru.mul hrvv).mul hc
  convert h using 1
  simp only [defectSourceDerivV3]
  ring

/-- ソース項 S の v 微分の明示形（形式微分）。r_uv・r_vv は抽象的な
    微分値として受け取る。 -/
theorem defectSource_hasDerivAt_v {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    HasDerivAt (fun v' => defectSource F g g' u v')
      (defectSourceDerivV F g g' g'' u v) v := by
  have h1 := defectSourceTerm1_hasDerivAt_v hr hg hOmv hWv hrv
  have h2 := defectSourceTerm2_hasDerivAt_v hr hg hOmv hrv
  have h3 := defectSourceTerm3_hasDerivAt_v hr hg hg' hrv hru hrvv
  have hE := h1.add (h2.add h3)
  have hEq : (fun v' => defectSource F g g' u v')
      =ᶠ[𝓝 v] (fun v' => F.Om u v' * (1 - (F.W u v') ^ 2) ^ 2
        * (-2 / (F.r u v') ^ 4 - g (F.r u v') / (2 * (F.r u v') ^ 3))
      + (F.Om u v' * (1 / (F.r u v') ^ 2 + g (F.r u v') / (2 * F.r u v'))
        + Du F.r u v' * Dv F.r u v'
          * (2 / (F.r u v') ^ 2 - g' (F.r u v') + g (F.r u v') / F.r u v'))) := by
    have hne : ∀ᶠ v' in 𝓝 v, F.r u v' ≠ 0 := hrv.continuousAt.eventually_ne hr
    filter_upwards [hne] with v' hv'
    rw [defectSource_eq hv']
    ring
  have h := hE.congr_of_eventuallyEq hEq
  exact h

/-- ソース項 S の v 微分の `deriv` 版。 -/
theorem defectSource_deriv_v {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ}
    (hr : F.r u v ≠ 0)
    (hg : HasDerivAt g (g' (F.r u v)) (F.r u v))
    (hg' : HasDerivAt g' (g'' (F.r u v)) (F.r u v))
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    deriv (fun v' => defectSource F g g' u v') v
      = defectSourceDerivV F g g' g'' u v :=
  (defectSource_hasDerivAt_v hr hg hg' hOmv hWv hrv hru hrvv).deriv

/-- RN の対数微分の二階微分：
    g′(r) = −1/(r−r₊)² − 1/(r−r₋)² + 2/r² に対して
    g″(r) = 2/(r−r₊)³ + 2/(r−r₋)³ − 4/r³。 -/
noncomputable def rnLogDeriv'' (rp rm r : ℝ) : ℝ :=
  2 / (r - rp) ^ 3 + 2 / (r - rm) ^ 3 - 4 / r ^ 3

/-- RN の対数微分の一階微分は `rnLogDeriv''` を導関数に持つ。 -/
theorem rnLogDeriv'_hasDerivAt {rp rm r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) (hrm : r ≠ rm) :
    HasDerivAt (rnLogDeriv' rp rm) (rnLogDeriv'' rp rm r) r := by
  -- 導関数値の恒等式（底が原子的な場合。`(r − rp)` のような差を直接
  -- `field_simp` にかけると冪が展開されて `ring` が通らなくなるため、
  -- 原子的な底で一度証明してから代入する）。
  have key : ∀ a : ℝ, a ≠ 0 → 2 / a ^ 3 = -1 * (-(2 * a) / (a ^ 2) ^ 2) := by
    intro a ha
    field_simp
    ring
  have h1 : HasDerivAt (fun x => -1 / (x - rp) ^ 2) (2 / (r - rp) ^ 3) r := by
    have h2 : HasDerivAt (fun x => (x - rp) ^ 2) (2 * (r - rp)) r := by
      have h := ((hasDerivAt_id r).sub_const rp).pow 2
      convert h using 1
      simp only [id_eq]
      ring
    have hi := h2.inv (pow_ne_zero 2 (sub_ne_zero.mpr hrp))
    have h := hi.const_mul (-1)
    convert h using 1
    exact key _ (sub_ne_zero.mpr hrp)
  have h2' : HasDerivAt (fun x => -1 / (x - rm) ^ 2) (2 / (r - rm) ^ 3) r := by
    have h2 : HasDerivAt (fun x => (x - rm) ^ 2) (2 * (r - rm)) r := by
      have h := ((hasDerivAt_id r).sub_const rm).pow 2
      convert h using 1
      simp only [id_eq]
      ring
    have hi := h2.inv (pow_ne_zero 2 (sub_ne_zero.mpr hrm))
    have h := hi.const_mul (-1)
    convert h using 1
    exact key _ (sub_ne_zero.mpr hrm)
  have h3 : HasDerivAt (fun x => 2 / x ^ 2) (-4 / r ^ 3) r := by
    have h2 : HasDerivAt (fun x => x ^ 2) (2 * r) r := by
      have h := (hasDerivAt_id r).pow 2
      convert h using 1
      simp only [id_eq]
      ring
    have hi := h2.inv (pow_ne_zero 2 hr)
    have h := hi.const_mul 2
    convert h using 1
    field_simp
    ring
  have h := (h1.add h2').add h3
  convert h using 1
  · ext x
    simp only [rnLogDeriv']
    ring
  · simp only [rnLogDeriv'']
    ring

/-- RN への特殊化：ソース項 S の v 微分の明示形。 -/
theorem defectSource_hasDerivAt_v_rn {F : WedgeFields} {rp rm u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    HasDerivAt (fun v' => defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v')
      (defectSourceDerivV F (rnLogDeriv rp rm) (rnLogDeriv' rp rm)
        (rnLogDeriv'' rp rm) u v) v :=
  defectSource_hasDerivAt_v hr
    (rnLogDeriv_hasDerivAt hr hrp hrm) (rnLogDeriv'_hasDerivAt hr hrp hrm)
    hOmv hWv hrv hru hrvv

/-- RN への特殊化：ソース項 S の v 微分の `deriv` 版。 -/
theorem defectSource_deriv_v_rn {F : WedgeFields} {rp rm u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) (hrm : F.r u v ≠ rm)
    (hOmv : HasDerivAt (fun v' => F.Om u v') (Dv F.Om u v) v)
    (hWv : HasDerivAt (fun v' => F.W u v') (Dv F.W u v) v)
    (hrv : HasDerivAt (fun v' => F.r u v') (Dv F.r u v) v)
    (hru : HasDerivAt (fun v' => Du F.r u v') (Duv F.r u v) v)
    (hrvv : HasDerivAt (fun v' => Dv F.r u v') (Dvv F.r u v) v) :
    deriv (fun v' => defectSource F (rnLogDeriv rp rm) (rnLogDeriv' rp rm) u v') v
      = defectSourceDerivV F (rnLogDeriv rp rm) (rnLogDeriv' rp rm)
          (rnLogDeriv'' rp rm) u v :=
  (defectSource_hasDerivAt_v_rn hr hrp hrm hOmv hWv hrv hru hrvv).deriv

end CFT.WedgeDefectSourceDeriv
