/-
  5-7 半古典極限の照合

  ħ → 0 で、厳密解の族 Ψ = A(b) e^{iaσ(b)/ħ} が Hamilton–Jacobi 方程式の解
  S = aσ(b) に戻ること。第9章の照合の量子側の受け口。

  * 位相 S = aσ(b) の微分は ∂_a S = σ(b)、∂_b S = aσ′(b) で、古典の
    Hamiltonian Hfun(a, b, ∂_a S, ∂_b S) = 0 を厳密に満たす
    (`phase_hj`・`phase_hj_deriv`、`CFT.AlphaCompleteA.hj_exact` の当てはめ)。
  * WKB 恒等式（`CFT.WKB.wkb_identity`）の ħ⁰ 項はちょうどこの HJ 式
    （`hjExpr`、b²·Hfun に等しい）であり、σ² = Q と σσ′ = (C − 8c²b)/2 から
    0 になる（`hjExpr_zero`）。よって ĤΨ = e^{iS/ħ} · (iħb/2c)(σA′ + σ′A)
    （`wkb_remainder`）：WKB の級数は ħ¹ で終わり、ħ⁰ 項は無い。
  * 位相で割った WDW 作用 `wkbRescaled` は ħ の 1 次式
    （`wkbRescaled_eq`）で、ħ → 0 で 0 に収束する（`semiclassical_limit`）。
    すなわち厳密解の族は ħ → 0 で HJ 方程式の解に戻る。
  注意：ĤΨ そのものは位相因子 e^{iS/ħ} を含んで振動するため、極限を取る
  には位相で割った剰余を見るのが正しい形である。
-/
import CFT.Quantum.WDWExactWKB
import CFT.Quantum.WDWOutgoingCorrespondence
import CFT.Spherical.CompletionNeckDynamics

open Complex Filter Topology

namespace CFT.WDWSemi

variable (c l : ℝ)

/-- WKB 恒等式に現れる Hamilton–Jacobi 式（実数版） -/
noncomputable def hjExpr (C a b : ℝ) : ℝ :=
  1 / (4 * c) * (a * (CFT.WDWOutgoing.sig c l C b) ^ 2
    - 2 * a * b * (CFT.WDWOutgoing.sig c l C b)
      * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b)))
    - c * a * (b ^ 2 - l ^ 2)

/-- σ² = Q -/
theorem sig_sq (C b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) :
    (CFT.WDWOutgoing.sig c l C b) ^ 2 = C * b - 4 * c ^ 2 * (b ^ 2 + l ^ 2) :=
  Real.sq_sqrt hQ.le

/-- σσ′ = (C − 8c²b)/2 -/
theorem sig_mul_sig' (C b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) :
    CFT.WDWOutgoing.sig c l C b * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b))
      = (C - 8 * c ^ 2 * b) / 2 := by
  have hne : CFT.WDWOutgoing.sig c l C b ≠ 0 := CFT.WDWOutgoing.sig_ne_zero c l C b hQ
  field_simp
  ring

/-- HJ 式は 0：位相 S = aσ(b) は Hamilton–Jacobi 方程式の解 -/
theorem hjExpr_zero (C a b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0) :
    hjExpr c l C a b = 0 := by
  have hne : CFT.WDWOutgoing.sig c l C b ≠ 0 := CFT.WDWOutgoing.sig_ne_zero c l C b hQ
  have hs2 := sig_sq c l C b hQ
  have key : 2 * a * b * (CFT.WDWOutgoing.sig c l C b)
      * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b))
      = a * b * (C - 8 * c ^ 2 * b) := by
    field_simp
    ring
  have hX : a * (CFT.WDWOutgoing.sig c l C b) ^ 2
      - 2 * a * b * (CFT.WDWOutgoing.sig c l C b)
        * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b))
      = 4 * c ^ 2 * a * (b ^ 2 - l ^ 2) := by
    rw [key, hs2]
    ring
  show 1 / (4 * c) * (a * (CFT.WDWOutgoing.sig c l C b) ^ 2
      - 2 * a * b * (CFT.WDWOutgoing.sig c l C b)
        * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b)))
      - c * a * (b ^ 2 - l ^ 2) = 0
  rw [hX]
  field_simp
  ring

/-- 位相 S = aσ(b) の a 微分は σ(b) -/
theorem phase_hasDerivAt_a (C a b : ℝ) :
    HasDerivAt (fun x => x * CFT.WDWOutgoing.sig c l C b) (CFT.WDWOutgoing.sig c l C b) a := by
  simpa using (hasDerivAt_id a).mul_const (CFT.WDWOutgoing.sig c l C b)

/-- 位相 S = aσ(b) の b 微分は aσ′(b) -/
theorem phase_hasDerivAt_b (C a b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) :
    HasDerivAt (fun y => a * CFT.WDWOutgoing.sig c l C y)
      (a * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b))) b :=
  (CFT.WDWOutgoing.hasDerivAt_sig c l C b hQ).const_mul a

/-- 位相の微分を代入した Hfun は 0（HJ 方程式） -/
theorem phase_hj (C a b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0) (hb2 : b ≠ 0) :
    CFT.AlphaCompleteA.Hfun a b (CFT.WDWOutgoing.sig c l C b)
      (a * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b))) c l = 0 :=
  CFT.AlphaCompleteA.hj_exact a b c l C (CFT.WDWOutgoing.sig c l C b)
    ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b)) hb2 hc
    (sig_sq c l C b hQ) (sig_mul_sig' c l C b hQ)

/-- HJ 式 = b² · Hfun(a, b, σ, aσ′)（両辺とも 0） -/
theorem hjExpr_eq (C a b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0) (hb2 : b ≠ 0) :
    hjExpr c l C a b = b ^ 2 * CFT.AlphaCompleteA.Hfun a b (CFT.WDWOutgoing.sig c l C b)
      (a * ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b))) c l := by
  rw [hjExpr_zero c l C a b hQ hc, phase_hj c l C a b hQ hc hb2, mul_zero]

/-- 位相の実際の微分（deriv 形）での HJ 方程式 -/
theorem phase_hj_deriv (C a b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0) (hb2 : b ≠ 0) :
    CFT.AlphaCompleteA.Hfun a b
      (deriv (fun x => x * CFT.WDWOutgoing.sig c l C b) a)
      (deriv (fun y => a * CFT.WDWOutgoing.sig c l C y) b) c l = 0 := by
  rw [(phase_hasDerivAt_a c l C a b).deriv, (phase_hasDerivAt_b c l C a b hQ).deriv]
  exact phase_hj c l C a b hQ hc hb2

/-- WKB 恒等式の ħ⁰ 項（HJ 項）は消える：ĤΨ = e^{iS/ħ} · (iħb/2c)(σA′ + σ′A) -/
theorem wkb_remainder (hb : ℝ) (hhb0 : hb ≠ 0) (C : ℝ) (A : ℝ → ℝ) (a b A' : ℝ)
    (hA : HasDerivAt A A' b) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0)
    (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => CFT.WKB.Psia hb⁻¹ A (CFT.WDWOutgoing.sig c l C) x b) Daa a)
    (hDab : HasDerivAt (fun y => CFT.WKB.Psia hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a y) Dab b) :
    CFT.WKB.wdwOp c l hb a b (CFT.WKB.Psi hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a b) Daa Dab
      = exp (I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)) *
        (2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ) *
          (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
            + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ))) := by
  have hhb : hb * hb⁻¹ = 1 := mul_inv_cancel₀ hhb0
  have hσ := CFT.WDWOutgoing.hasDerivAt_sig c l C b hQ
  rw [CFT.WKB.wkb_identity c l hb⁻¹ A (CFT.WDWOutgoing.sig c l C) hb hhb a b A'
    ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b)) hA hσ Daa Dab hDaa hDab]
  have hHJ : (1 / (4 * (c : ℂ))) * ((a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) ^ 2
      - 2 * (a : ℂ) * (b : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ))
        * ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ))
      - (c : ℂ) * (a : ℂ) * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2) = 0 := by
    have hcast : (1 / (4 * (c : ℂ))) * ((a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) ^ 2
        - 2 * (a : ℂ) * (b : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ))
          * ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ))
        - (c : ℂ) * (a : ℂ) * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2)
        = ((hjExpr c l C a b : ℝ) : ℂ) := by
      simp only [hjExpr]
      push_cast
      ring
    rw [hcast, hjExpr_zero c l C a b hQ hc]
    simp
  rw [hHJ]
  simp

/-- 位相で割った WDW 作用（ħ = hb、κ = 1/hb）。Daa/Dab は正準の偏微分値。 -/
noncomputable def wkbRescaled (C : ℝ) (A : ℝ → ℝ) (a b A' : ℝ) (hb : ℝ) : ℂ :=
  CFT.WKB.wdwOp c l hb a b (CFT.WKB.Psi hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a b)
    (I * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)
      * (I * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)
        * CFT.WKB.Psi hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a b))
    (I * ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * ((hb⁻¹ : ℝ) : ℂ)
      * CFT.WKB.Psi hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a b
      + I * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)
        * (((A' : ℂ) * exp (I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ))
          + (A b : ℂ) * (exp (I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ))
            * (I * (a : ℂ) * ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * ((hb⁻¹ : ℝ) : ℂ))))))
    * exp (-(I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)))

/-- 位相で割った WDW 作用は ħ の 1 次式：ħ⁰ 項は無い -/
theorem wkbRescaled_eq (C : ℝ) (A : ℝ → ℝ) (a b A' : ℝ)
    (hA : HasDerivAt A A' b) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0)
    (hb : ℝ) (hhb0 : hb ≠ 0) :
    wkbRescaled c l C A a b A' hb
      = 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ) *
        (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
          + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ)) := by
  have hDaa := CFT.WKB.hasDerivAt_Psia_a hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a b
  have hDab := CFT.WKB.hasDerivAt_Psia_b hb⁻¹ A (CFT.WDWOutgoing.sig c l C) a b A'
    ((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b)) hA
    (CFT.WDWOutgoing.hasDerivAt_sig c l C b hQ)
  simp only [wkbRescaled]
  rw [wkb_remainder c l hb hhb0 C A a b A' hA hQ hc _ _ hDaa hDab]
  calc exp (I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)) *
        (2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ) *
          (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
            + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ)))
        * exp (-(I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)))
      = (2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ) *
          (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
            + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ)))
        * (exp (I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ))
          * exp (-(I * (a : ℂ) * ((CFT.WDWOutgoing.sig c l C b : ℂ)) * ((hb⁻¹ : ℝ) : ℂ)))) := by ring
    _ = 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ) *
          (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
            + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ)) := by
      rw [← Complex.exp_add]
      simp

/-- 【5-7】半古典極限：位相で割った WDW 作用は ħ → 0 で 0 に収束する。
    すなわち ħ⁰ の項は Hamilton–Jacobi 方程式そのものであり、厳密解の族は
    ħ → 0 で HJ 方程式の解 S = aσ(b) に戻る。 -/
theorem semiclassical_limit (C : ℝ) (A : ℝ → ℝ) (a b A' : ℝ)
    (hA : HasDerivAt A A' b) (hQ : 0 < CFT.WKB.Q c l C b) (hc : c ≠ 0) :
    Tendsto (wkbRescaled c l C A a b A') (𝓝[≠] 0) (𝓝 0) := by
  have hev : (wkbRescaled c l C A a b A') =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun hb => (hb : ℂ) * (2 * (1 / (4 * (c : ℂ))) * I * (b : ℂ) *
        (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
          + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ)))) := by
    filter_upwards [self_mem_nhdsWithin] with hb hhb
    rw [wkbRescaled_eq c l C A a b A' hA hQ hc hb hhb]
    ring
  refine Tendsto.congr' hev.symm ?_
  have h1 : Tendsto (fun hb : ℝ => (hb : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0)
  have h2 : Tendsto (fun hb : ℝ => (hb : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds h1
  have h3 := h2.mul_const (2 * (1 / (4 * (c : ℂ))) * I * (b : ℂ) *
    (((CFT.WDWOutgoing.sig c l C b : ℂ)) * (A' : ℂ)
      + ((((C - 8 * c ^ 2 * b) / (2 * CFT.WDWOutgoing.sig c l C b) : ℝ)) : ℂ) * (A b : ℂ)))
  simpa using h3

end CFT.WDWSemi
