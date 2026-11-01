/-
  α-VI.4 (Z33) の補強:二つの枝、Laplace–Beltrami の順序、重ね合わせ

  AlphaIV_WKB の `wdw_exact_sqrt` は、順序「運動量を右に置く」(作用素 `wdwOp`)と正の枝 σ = +√Q で、
  Ψ = e^{iaσ/ħ}/σ が Q > 0 の各点で厳密解になることを示した。ここでは次を加える。

  1. 一般形(`wdw_exact_of`):σ(b) = s ≠ 0、s² = Q(b)、s σ′ = Q′(b)/2、A = 1/σ(A(b) = s⁻¹、A′ = −σ′/s²)
     なら Ψ = A e^{iaσ/ħ} は厳密解。正の枝 σ = +√Q と負の枝 σ = −√Q(`wdw_exact_neg`)の両方を含む。
  2. 重ね合わせ(`wdwOp_linear`):作用素は線形なので、二つの枝の一次結合 α Ψ₊ + β Ψ₋ も解。
     固定した C での一般解はこの 2 次元(古典の p_a = ±√Q の二つの向き)。
  3. Laplace–Beltrami の順序(`wdwOpLB`):超計量 G の Laplace–Beltrami 作用素による順序
     (AlphaIV_Reduction の `lb_operator`)では、運動項に −(ħ²/4c)∂_a が加わる。
     このとき Ψ = √b e^{iaσ/ħ}/σ(σ = √Q)が厳密解(`wdw_exact_LB`)。WKB の級数はやはり ħ¹ で終わり、
     変わるのは輸送方程式だけ:(σA)′ = σA/(2b)、A = √b/σ。
  これで「順序の選び方」は、二つの自然な順序(運動量を右、Laplace–Beltrami)の両方で厳密解があることになる。
  順序の違いは振幅の因子 √b だけで、位相(Hamilton–Jacobi の解 aσ)と定義域 Q > 0 は同じ。
-/
import CFT.AlphaIV_WKB

namespace CFT.WKB2

open Complex CFT.WKB

noncomputable section

variable (c l κ : ℝ)

/-- 【α-VI.4】厳密解の一般形:σ(b) = s、s² = Q、sσ′ = Q′/2、A(b) = s⁻¹、A′ = −σ′/s² -/
theorem wdw_exact_of (A σ : ℝ → ℝ) (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0) (C a b s σ' A' : ℝ)
    (hs : s ≠ 0) (hsq : s ^ 2 = Q c l C b) (hσb : σ b = s) (hAb : A b = s⁻¹)
    (hσ : HasDerivAt σ σ' b) (hA : HasDerivAt A A' b)
    (hσ' : s * σ' = (C - 8 * c ^ 2 * b) / 2) (hA' : A' = -σ' / s ^ 2)
    (Daa Dab : ℂ) (hDaa : HasDerivAt (fun x => Psia κ A σ x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ A σ a y) Dab b) :
    wdwOp c l hb a b (Psi κ A σ a b) Daa Dab = 0 := by
  rw [wkb_identity c l κ A σ hb hhb a b A' σ' hA hσ Daa Dab hDaa hDab, hσb, hAb, hA']
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hsqC : (s : ℂ) ^ 2 = (C : ℂ) * b - 4 * (c : ℂ) ^ 2 * ((b : ℂ) ^ 2 + (l : ℂ) ^ 2) := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hsq
    simpa [Q] using this
  have hσ'C : (s : ℂ) * (σ' : ℂ) = ((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / 2 := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hσ'
    push_cast at this
    exact this
  have hic : (1 / (4 * (c : ℂ))) * (4 * c) = 1 := by field_simp
  have h2 : (s : ℂ) * (-(σ' : ℂ) / (s : ℂ) ^ 2) + (σ' : ℂ) * (s : ℂ)⁻¹ = 0 := by
    field_simp <;> ring
  push_cast
  generalize exp (I * (a : ℂ) * (s : ℂ) * (κ : ℂ)) = E
  linear_combination (E * (s : ℂ)⁻¹) * ((1 / (4 * (c : ℂ))) * a * hsqC
      - (2 * (1 / (4 * (c : ℂ))) * a * b) * hσ'C + ((c : ℂ) * a * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2)) * hic)
    + (E * 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ)) * h2

/-- 【α-VI.4】負の枝:σ = −√Q、A = 1/σ でも Ψ は厳密解(古典の p_a = −√Q に対応) -/
theorem wdw_exact_neg (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0) (C a b : ℝ) (hQ : 0 < Q c l C b)
    (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => Psia κ (fun y => (-Real.sqrt (Q c l C y))⁻¹)
      (fun y => -Real.sqrt (Q c l C y)) x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ (fun y => (-Real.sqrt (Q c l C y))⁻¹)
      (fun y => -Real.sqrt (Q c l C y)) a y) Dab b) :
    wdwOp c l hb a b (Psi κ (fun y => (-Real.sqrt (Q c l C y))⁻¹) (fun y => -Real.sqrt (Q c l C y)) a b)
      Daa Dab = 0 := by
  have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
  have hσ : HasDerivAt (fun y => -Real.sqrt (Q c l C y))
      (-((C - 8 * c ^ 2 * b) / (2 * Real.sqrt (Q c l C b)))) b :=
    ((hasDerivAt_Q c l C b).sqrt hQ.ne').neg
  have hne : (fun y => -Real.sqrt (Q c l C y)) b ≠ 0 := by
    simp only [ne_eq, neg_eq_zero]; exact hspos.ne'
  have hA := hσ.inv hne
  have hne' : Real.sqrt (Q c l C b) ≠ 0 := hspos.ne'
  exact wdw_exact_of c l κ _ _ hb hhb hc C a b (-Real.sqrt (Q c l C b)) _ _
    (neg_ne_zero.mpr hspos.ne') (by rw [neg_sq]; exact Real.sq_sqrt hQ.le) rfl rfl hσ hA
    (by field_simp <;> ring) rfl Daa Dab hDaa hDab

/-- 重ね合わせ:wdwOp は (Ψ, Ψ_aa, Ψ_ab) について線形 -/
theorem wdwOp_linear (hb a b : ℝ) (α β Ψ₁ Ψ₂ D₁ D₂ E₁ E₂ : ℂ) :
    wdwOp c l hb a b (α * Ψ₁ + β * Ψ₂) (α * D₁ + β * D₂) (α * E₁ + β * E₂)
      = α * wdwOp c l hb a b Ψ₁ D₁ E₁ + β * wdwOp c l hb a b Ψ₂ D₂ E₂ := by
  simp only [wdwOp]
  ring

/-- Laplace–Beltrami の順序(b² 倍した拘束):Ĥ_LB Ψ = Ĥ Ψ − (ħ²/4c) ∂_aΨ(AlphaIV_Reduction `lb_operator`) -/
def wdwOpLB (hb a b : ℝ) (Ψ Ψa Ψaa Ψab : ℂ) : ℂ :=
  wdwOp c l hb a b Ψ Ψaa Ψab - (1 / (4 * (c : ℂ))) * (hb : ℂ) ^ 2 * Ψa

/-- 【α-VI.4】Laplace–Beltrami の順序でも、Ψ = √b e^{iaσ/ħ}/σ(σ = √Q、b > 0)は Q > 0 の各点で厳密解 -/
theorem wdw_exact_LB (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0) (C a b : ℝ) (hb0 : 0 < b)
    (hQ : 0 < Q c l C b) (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => Psia κ (fun y => Real.sqrt y / Real.sqrt (Q c l C y))
      (fun y => Real.sqrt (Q c l C y)) x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ (fun y => Real.sqrt y / Real.sqrt (Q c l C y))
      (fun y => Real.sqrt (Q c l C y)) a y) Dab b) :
    wdwOpLB c l hb a b
      (Psi κ (fun y => Real.sqrt y / Real.sqrt (Q c l C y)) (fun y => Real.sqrt (Q c l C y)) a b)
      (Psia κ (fun y => Real.sqrt y / Real.sqrt (Q c l C y)) (fun y => Real.sqrt (Q c l C y)) a b)
      Daa Dab = 0 := by
  have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
  have hrpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hσ : HasDerivAt (fun y => Real.sqrt (Q c l C y))
      ((C - 8 * c ^ 2 * b) / (2 * Real.sqrt (Q c l C b))) b :=
    (hasDerivAt_Q c l C b).sqrt hQ.ne'
  have hr' : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt b)) b :=
    Real.hasDerivAt_sqrt hb0.ne'
  have hA := hr'.div hσ hspos.ne'
  simp only [wdwOpLB]
  rw [wkb_identity c l κ _ _ hb hhb a b _ _ hA hσ Daa Dab hDaa hDab]
  simp only [Psia, Psi]
  set s := Real.sqrt (Q c l C b) with hs
  set r := Real.sqrt b with hr
  have hsq : s ^ 2 = Q c l C b := Real.sq_sqrt hQ.le
  have hrsq : r ^ 2 = b := Real.sq_sqrt hb0.le
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hu : (hb : ℂ) * (κ : ℂ) = 1 := by exact_mod_cast hhb
  have hsqC : (s : ℂ) ^ 2 = (C : ℂ) * b - 4 * (c : ℂ) ^ 2 * ((b : ℂ) ^ 2 + (l : ℂ) ^ 2) := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hsq
    simpa [Q] using this
  have hrsqC : (r : ℂ) ^ 2 = (b : ℂ) := by exact_mod_cast hrsq
  have hic : (1 / (4 * (c : ℂ))) * (4 * c) = 1 := by field_simp
  have hsσ : (s : ℂ) * (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)) = ((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / 2 := by
    field_simp <;> ring
  -- Hamilton–Jacobi(ħ⁰)
  have h1 : (1 / (4 * (c : ℂ))) * ((a : ℂ) * (s : ℂ) ^ 2
      - 2 * (a : ℂ) * (b : ℂ) * (s : ℂ) * (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)))
      - (c : ℂ) * (a : ℂ) * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2) = 0 := by
    linear_combination ((1 / (4 * (c : ℂ))) * a) * hsqC - (2 * (1 / (4 * (c : ℂ))) * a * b) * hsσ
      + ((c : ℂ) * a * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2)) * hic
  -- 輸送(ħ¹):(σA)′ = (√b)′ = 1/(2√b)
  have hsi : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hri : (r : ℂ) * (r : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hr0
  have h2 : (s : ℂ) * ((1 / (2 * (r : ℂ)) * s - r * (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)))
      / (s : ℂ) ^ 2) + (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)) * ((r : ℂ) / s) = 1 / (2 * r) := by
    linear_combination ((r : ℂ)⁻¹ / 2 * ((s : ℂ) * (s : ℂ)⁻¹ + 1)
      - (r : ℂ) * (((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / (2 * s)) * (s : ℂ)⁻¹) * hsi
  have h3 : (s : ℂ) * ((r : ℂ) / s) = r := by linear_combination (r : ℂ) * hsi
  have h4 : (b : ℂ) * (1 / (2 * (r : ℂ))) = r / 2 := by
    rw [← hrsqC]
    linear_combination ((r : ℂ) / 2) * hri
  push_cast
  generalize exp (I * (a : ℂ) * (s : ℂ) * (κ : ℂ)) = E
  linear_combination (E * ((r : ℂ) / s)) * h1
    + (E * 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ)) * h2
    + (E * 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ)) * h4
    + (-((1 / (4 * (c : ℂ))) * (hb : ℂ) ^ 2 * I * (κ : ℂ) * E)) * h3
    + (-((1 / (4 * (c : ℂ))) * I * E * (r : ℂ) * (hb : ℂ))) * hu

/-- 【α-VI.4】Laplace–Beltrami の順序の厳密解の一般形:σ(b) = s、s² = Q、sσ′ = Q′/2、A(b) = r/s、
r² = b、輸送方程式 sA′ + σ′(r/s) = 1/(2r)(すなわち (σA)′ = (√b)′) -/
theorem wdw_exact_LB_of (A σ : ℝ → ℝ) (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0)
    (C a b s r σ' A' : ℝ) (hs : s ≠ 0) (hr : r ≠ 0) (hsq : s ^ 2 = Q c l C b) (hrsq : r ^ 2 = b)
    (hσb : σ b = s) (hAb : A b = r / s) (hσ : HasDerivAt σ σ' b) (hA : HasDerivAt A A' b)
    (hσ' : s * σ' = (C - 8 * c ^ 2 * b) / 2) (htr : s * A' + σ' * (r / s) = 1 / (2 * r))
    (Daa Dab : ℂ) (hDaa : HasDerivAt (fun x => Psia κ A σ x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ A σ a y) Dab b) :
    wdwOpLB c l hb a b (Psi κ A σ a b) (Psia κ A σ a b) Daa Dab = 0 := by
  simp only [wdwOpLB]
  rw [wkb_identity c l κ A σ hb hhb a b A' σ' hA hσ Daa Dab hDaa hDab]
  simp only [Psia, Psi, hσb, hAb]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hu : (hb : ℂ) * (κ : ℂ) = 1 := by exact_mod_cast hhb
  have hsqC : (s : ℂ) ^ 2 = (C : ℂ) * b - 4 * (c : ℂ) ^ 2 * ((b : ℂ) ^ 2 + (l : ℂ) ^ 2) := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hsq
    simpa [Q] using this
  have hrsqC : (r : ℂ) ^ 2 = (b : ℂ) := by exact_mod_cast hrsq
  have hσ'C : (s : ℂ) * (σ' : ℂ) = ((C : ℂ) - 8 * (c : ℂ) ^ 2 * b) / 2 := by
    have := congrArg (fun t : ℝ => (t : ℂ)) hσ'
    push_cast at this
    exact this
  have htrC : (s : ℂ) * (A' : ℂ) + (σ' : ℂ) * ((r : ℂ) / (s : ℂ)) = 1 / (2 * (r : ℂ)) := by
    have := congrArg (fun t : ℝ => (t : ℂ)) htr
    push_cast at this
    exact this
  have hic : (1 / (4 * (c : ℂ))) * (4 * c) = 1 := by field_simp
  have hsi : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hri : (r : ℂ) * (r : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hr0
  have h3 : (s : ℂ) * ((r : ℂ) / s) = r := by linear_combination (r : ℂ) * hsi
  have h4 : (b : ℂ) * (1 / (2 * (r : ℂ))) = r / 2 := by
    rw [← hrsqC]
    linear_combination ((r : ℂ) / 2) * hri
  push_cast
  generalize exp (I * (a : ℂ) * (s : ℂ) * (κ : ℂ)) = E
  linear_combination (E * ((r : ℂ) / s)) * ((1 / (4 * (c : ℂ))) * a * hsqC
      - (2 * (1 / (4 * (c : ℂ))) * a * b) * hσ'C + ((c : ℂ) * a * ((b : ℂ) ^ 2 - (l : ℂ) ^ 2)) * hic)
    + (E * 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ) * (b : ℂ)) * htrC
    + (E * 2 * (1 / (4 * (c : ℂ))) * I * (hb : ℂ)) * h4
    + (-((1 / (4 * (c : ℂ))) * (hb : ℂ) ^ 2 * I * (κ : ℂ) * E)) * h3
    + (-((1 / (4 * (c : ℂ))) * I * E * (r : ℂ) * (hb : ℂ))) * hu

/-- 【α-VI.4】Laplace–Beltrami の順序の負の枝:σ = −√Q、Ψ = √b e^{iaσ/ħ}/σ も厳密解 -/
theorem wdw_exact_LB_neg (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0) (C a b : ℝ) (hb0 : 0 < b)
    (hQ : 0 < Q c l C b) (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => Psia κ (fun y => Real.sqrt y / (-Real.sqrt (Q c l C y)))
      (fun y => -Real.sqrt (Q c l C y)) x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ (fun y => Real.sqrt y / (-Real.sqrt (Q c l C y)))
      (fun y => -Real.sqrt (Q c l C y)) a y) Dab b) :
    wdwOpLB c l hb a b
      (Psi κ (fun y => Real.sqrt y / (-Real.sqrt (Q c l C y))) (fun y => -Real.sqrt (Q c l C y)) a b)
      (Psia κ (fun y => Real.sqrt y / (-Real.sqrt (Q c l C y))) (fun y => -Real.sqrt (Q c l C y)) a b)
      Daa Dab = 0 := by
  have hspos : 0 < Real.sqrt (Q c l C b) := Real.sqrt_pos.mpr hQ
  have hrpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hs' : Real.sqrt (Q c l C b) ≠ 0 := hspos.ne'
  have hr' : Real.sqrt b ≠ 0 := hrpos.ne'
  have hσ : HasDerivAt (fun y => -Real.sqrt (Q c l C y))
      (-((C - 8 * c ^ 2 * b) / (2 * Real.sqrt (Q c l C b)))) b :=
    ((hasDerivAt_Q c l C b).sqrt hQ.ne').neg
  have hrd : HasDerivAt (fun y => Real.sqrt y) (1 / (2 * Real.sqrt b)) b :=
    Real.hasDerivAt_sqrt hb0.ne'
  have hne : (fun y => -Real.sqrt (Q c l C y)) b ≠ 0 := by
    simp only [ne_eq, neg_eq_zero]; exact hs'
  have hA := hrd.div hσ hne
  exact wdw_exact_LB_of c l κ _ _ hb hhb hc C a b (-Real.sqrt (Q c l C b)) (Real.sqrt b) _ _
    (neg_ne_zero.mpr hs') hr' (by rw [neg_sq]; exact Real.sq_sqrt hQ.le) (Real.sq_sqrt hb0.le)
    rfl rfl hσ hA (by field_simp <;> ring) (by field_simp <;> ring) Daa Dab hDaa hDab

end

end CFT.WKB2
