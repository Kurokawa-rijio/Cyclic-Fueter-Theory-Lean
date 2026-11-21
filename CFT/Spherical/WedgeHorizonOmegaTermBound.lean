/-
  命題集 `LEAN_GAP_TREES.md` 12-8 (b) 対応仮説の証明への一段：

  **Ω 項の下界の第一段（対応仮説のもとでの 0 への収束）**。前段
  （`WedgeHorizonDefectZeroPoint`）では S = 0 になる一点の構成が、
  「切片の左端での負値＋地平線での発散」という二つの検証可能な条件に
  帰着され、その発散 `defectSource_tendsto_atTop_of_horizon` は Ω 項
    Ω(1−W²)²·(−2/r⁴ − g/(2r³)) + Ω·(1/r² + g/(2r))
  が下から抑えられること（仮定 `hOm`）と r_u·r_v ≥ m > 0 を仮定として
  使う。ここではその Ω 項について、対応仮説 Ω = c·f(r)（極端版）のもとで
  地平線で 0 に収束すること、したがって下から抑えられることを示す。

  鍵は極端 RN での係数の簡約である。g = 2/(r−r₊) − 2/r のもとで
    1/r² + g/(2r) = 1/(r(r−r₊))、
    −2/r⁴ − g/(2r³) = −(2r−r₊)/(r⁴(r−r₊))
  となる（`omegaTermCoeff_second`・`omegaTermCoeff_first`）。
  対応仮説 Ω = c·(r−r₊)²/r² を代入すると Ω 項は
    c·(r−r₊)·(1/r³ − (1−W²)²(2r−r₊)/r⁶)
  と書け（`omegaTerm_of_correspondence`）、(r−r₊) → 0 に対して括弧内は
  有限の極限を持つので、Ω 項は r → r₊⁺ で 0 に収束する
  （`omegaTerm_tendsto_zero`）。くさびへの適用として、切片上で
  r → r₊ かつ W が収束すれば Ω 項は u → u₀⁻ で 0 に収束し
  （`omegaTerm_tendsto_zero_of_correspondence`）、したがって
  `defectSource_tendsto_atTop_of_horizon` の仮定 `hOm` そのものが
  対応仮説から従う（`omegaTerm_bddBelow_of_correspondence`）。

  残りは、r_u·r_v の正の下界 m > 0 の実際のくさび解からの検証と、
  ρ そのものの構成（対応仮説そのもの）である。
  恒等式の定数は sympy による明示計算でも照合済み。
-/
import CFT.Spherical.WedgeHorizonDefectZeroPoint

open Real Set Filter Topology
open CFT.Wedge CFT.RNLogDeriv CFT.RNExtremalZero

namespace CFT.WedgeOmegaTermBound

/-- Ω 項の第二係数の極端版の簡約：1/r² + g/(2r) = 1/(r(r−r₊))。 -/
theorem omegaTermCoeff_second {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    1 / r ^ 2 + rnLogDeriv rp rp r / (2 * r) = 1 / (r * (r - rp)) := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  rw [rnLogDeriv_extremal]
  field_simp
  ring

/-- Ω 項の第一係数の極端版の簡約：−2/r⁴ − g/(2r³) = −(2r−r₊)/(r⁴(r−r₊))。 -/
theorem omegaTermCoeff_first {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    -2 / r ^ 4 - rnLogDeriv rp rp r / (2 * r ^ 3)
      = -(2 * r - rp) / (r ^ 4 * (r - rp)) := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  rw [rnLogDeriv_extremal]
  field_simp
  ring

/-- Ω 項の因数分解形：hOm の式は Ω·[(1−W²)²·(−(2r−r₊)/(r⁴(r−r₊))) + 1/(r(r−r₊))]。 -/
theorem omegaTerm_eq_factored {F : WedgeFields} {rp u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) :
    F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v))
      = F.Om u v * ((1 - (F.W u v) ^ 2) ^ 2
          * (-(2 * F.r u v - rp) / ((F.r u v) ^ 4 * (F.r u v - rp)))
          + 1 / (F.r u v * (F.r u v - rp))) := by
  rw [omegaTermCoeff_first hr hrp, omegaTermCoeff_second hr hrp]
  ring

/-- 対応仮説 Ω = c·f(r) のもとでの Ω 項の閉形。 -/
theorem omegaTerm_of_correspondence {F : WedgeFields} {rp c u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp)
    (hOm : F.Om u v = c * rnF rp rp (F.r u v)) :
    F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v))
      = c * (F.r u v - rp) * (1 / (F.r u v) ^ 3
          - (1 - (F.W u v) ^ 2) ^ 2 * (2 * F.r u v - rp) / (F.r u v) ^ 6) := by
  rw [omegaTerm_eq_factored hr hrp, hOm, rnF_extremal]
  have h1 : F.r u v - rp ≠ 0 := sub_ne_zero.mpr hrp
  field_simp
  ring

/-- r の版：対応形の Ω 項は r → r₊⁺ で 0 に収束する（W は固定）。 -/
theorem omegaTerm_tendsto_zero {rp c w : ℝ} (hrp0 : rp ≠ 0) :
    Tendsto (fun r => c * (r - rp)
        * (1 / r ^ 3 - (1 - w ^ 2) ^ 2 * (2 * r - rp) / r ^ 6))
      (𝓝[>] rp) (𝓝 0) := by
  have hsub : Tendsto (fun r : ℝ => r - rp) (𝓝[>] rp) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r - rp) (𝓝 rp) (𝓝 (rp - rp)) :=
      continuousAt_id.sub_const rp
    simpa using h.mono_left nhdsWithin_le_nhds
  have hbr : Tendsto (fun r : ℝ => 1 / r ^ 3 - (1 - w ^ 2) ^ 2 * (2 * r - rp) / r ^ 6)
      (𝓝[>] rp) (𝓝 (1 / rp ^ 3 - (1 - w ^ 2) ^ 2 * (2 * rp - rp) / rp ^ 6)) := by
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] rp) (𝓝 rp) := by
      simpa using tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id.tendsto
    have h1 : Tendsto (fun r : ℝ => 1 / r ^ 3) (𝓝[>] rp) (𝓝 (1 / rp ^ 3)) := by
      have h := (hid.pow 3).inv₀ (pow_ne_zero 3 hrp0)
      simpa [one_div] using h
    have h2 : Tendsto (fun r : ℝ => (1 - w ^ 2) ^ 2 * (2 * r - rp) / r ^ 6)
        (𝓝[>] rp) (𝓝 ((1 - w ^ 2) ^ 2 * (2 * rp - rp) / rp ^ 6)) := by
      have hnum : Tendsto (fun r : ℝ => (1 - w ^ 2) ^ 2 * (2 * r - rp)) (𝓝[>] rp)
          (𝓝 ((1 - w ^ 2) ^ 2 * (2 * rp - rp))) :=
        tendsto_const_nhds.mul ((hid.const_mul 2).sub_const rp)
      exact hnum.div (hid.pow 6) (pow_ne_zero 6 hrp0)
    exact h1.sub h2
  simpa using (hsub.const_mul c).mul hbr

/-- くさびへの適用：対応仮説のもとで Ω 項は u → u₀⁻ で 0 に収束する。 -/
theorem omegaTerm_tendsto_zero_of_correspondence {F : WedgeFields} {rp c u₀ v w₀ : ℝ}
    (hrp0 : rp ≠ 0) (hu₀ : 0 < u₀)
    (hr0 : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ 0)
    (hrne : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ rp)
    (hrlim : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝[>] rp))
    (hW : Tendsto (fun u => F.W u v) (𝓝[<] u₀) (𝓝 w₀))
    (hOm : ∀ u ∈ Ioo 0 u₀, F.Om u v = c * rnF rp rp (F.r u v)) :
    Tendsto (fun u => F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
          * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
        + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)))
      (𝓝[<] u₀) (𝓝 0) := by
  have hr : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝 rp) :=
    hrlim.mono_right nhdsWithin_le_nhds
  have hsub : Tendsto (fun u => F.r u v - rp) (𝓝[<] u₀) (𝓝 0) := by
    simpa using hr.sub_const rp
  have hbr : Tendsto (fun u => 1 / (F.r u v) ^ 3
        - (1 - (F.W u v) ^ 2) ^ 2 * (2 * F.r u v - rp) / (F.r u v) ^ 6)
      (𝓝[<] u₀) (𝓝 (1 / rp ^ 3 - (1 - w₀ ^ 2) ^ 2 * (2 * rp - rp) / rp ^ 6)) := by
    have h1 : Tendsto (fun u => 1 / (F.r u v) ^ 3) (𝓝[<] u₀) (𝓝 (1 / rp ^ 3)) := by
      have h := (hr.pow 3).inv₀ (pow_ne_zero 3 hrp0)
      simpa [one_div] using h
    have h2 : Tendsto (fun u => (1 - (F.W u v) ^ 2) ^ 2 * (2 * F.r u v - rp) / (F.r u v) ^ 6)
        (𝓝[<] u₀) (𝓝 ((1 - w₀ ^ 2) ^ 2 * (2 * rp - rp) / rp ^ 6)) := by
      have hW2 : Tendsto (fun u => (1 - (F.W u v) ^ 2) ^ 2) (𝓝[<] u₀)
          (𝓝 ((1 - w₀ ^ 2) ^ 2)) :=
        (tendsto_const_nhds.sub (hW.pow 2)).pow 2
      have hlin : Tendsto (fun u => 2 * F.r u v - rp) (𝓝[<] u₀) (𝓝 (2 * rp - rp)) :=
        (hr.const_mul 2).sub_const rp
      have h6 : Tendsto (fun u => (F.r u v) ^ 6) (𝓝[<] u₀) (𝓝 (rp ^ 6)) := hr.pow 6
      exact (hW2.mul hlin).div h6 (pow_ne_zero 6 hrp0)
    exact h1.sub h2
  have hmul : Tendsto (fun u => c * (F.r u v - rp)
        * (1 / (F.r u v) ^ 3 - (1 - (F.W u v) ^ 2) ^ 2 * (2 * F.r u v - rp) / (F.r u v) ^ 6))
      (𝓝[<] u₀) (𝓝 0) := by
    simpa using (hsub.const_mul c).mul hbr
  refine hmul.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
  exact (omegaTerm_of_correspondence (hr0 u hu) (hrne u hu) (hOm u hu)).symm

/-- 対応仮説のもとで Ω 項は地平線の近くで下から抑えられる —
    `defectSource_tendsto_atTop_of_horizon` の仮定 `hOm` そのもの。 -/
theorem omegaTerm_bddBelow_of_correspondence {F : WedgeFields} {rp c u₀ v w₀ : ℝ}
    (hrp0 : rp ≠ 0) (hu₀ : 0 < u₀)
    (hr0 : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ 0)
    (hrne : ∀ u ∈ Ioo 0 u₀, F.r u v ≠ rp)
    (hrlim : Tendsto (fun u => F.r u v) (𝓝[<] u₀) (𝓝[>] rp))
    (hW : Tendsto (fun u => F.W u v) (𝓝[<] u₀) (𝓝 w₀))
    (hOm : ∀ u ∈ Ioo 0 u₀, F.Om u v = c * rnF rp rp (F.r u v)) :
    ∃ M, ∀ᶠ u in 𝓝[<] u₀,
      M ≤ F.Om u v * (1 - (F.W u v) ^ 2) ^ 2
            * (-2 / (F.r u v) ^ 4 - rnLogDeriv rp rp (F.r u v) / (2 * (F.r u v) ^ 3))
          + F.Om u v * (1 / (F.r u v) ^ 2 + rnLogDeriv rp rp (F.r u v) / (2 * F.r u v)) := by
  refine ⟨-1, ?_⟩
  have h := omegaTerm_tendsto_zero_of_correspondence hrp0 hu₀ hr0 hrne hrlim hW hOm
  have hev := h.eventually
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  exact hev.mono (fun u hu => hu.1.le)

end CFT.WedgeOmegaTermBound
