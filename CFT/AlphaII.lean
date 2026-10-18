/-
  α-II 統一方程式 U21′ と三つの相(Z2〜Z5)

  形式化した内容
  * α-II.1 (Z2)  (I) の係数:Hamilton 拘束 R = 16πGρ と ρ = |Rm|²/(8g²) から
                 R = (ℓ*²/2)|Rm|²、ℓ*² = 4πG/g²。
                 (II) のトレース部分は縮約 Bianchi により −½∇R になる。
                 ∇R = 0 と (I) から |Ric|² = R/(2ℓ²) + R²/4(したがって一定)。
                 3 次元の恒等式 |Rm|² = 4|Ric|² − R²(断面曲率による表示)。
  * α-II.2 (Z3)  Cheng–Ishikawa–Shiohama の分類(外部定理)が与える候補
                 {平坦, S³(a), H³(a), S²(a)×ℝ, H²(a)×ℝ} のうち (I) を満たすのは
                 平坦、S³(ℓ)、S²(ℓ)×ℝ だけ。
  * α-II.4 (Z4)  κ = Σ(λᵢ+λⱼ−R/2)(λᵢ−λⱼ)² = σ₁³ − 4σ₁σ₂ + 9σ₃、
                 (I) のもとでの固有値の角度表示と κ の閉じた式、窓定理(κ < 0 ⇒ Rℓ² < 2)。
  * α-II.9 (Z5)  BR の首の lapse N = cosh(s/ℓ) は N″ = N/ℓ² を満たす(AdS₂ 因子の式)。

  外部定理として仮定に置くもの(Lean 内では仮定、README に出典)
  * Cheng–Ishikawa–Shiohama 1999 の分類(Theorem A)と Theorem B(α-II.3)

  形式化していない内容
  * α-II.5(C 行列の階数 ≤ 2)、α-II.6(Gröbner 基底 {1})、α-II.9 の不存在部分:
    証明書の出力が必要(README)
-/
import CFT.Basic

open Real

namespace CFT.AlphaII

/-! ### α-II.1 (I) の係数と保存量 -/

/-- Hamilton 拘束 R = 16πG ρ に ρ = |Rm|²/(8g²) を入れると R = (ℓ*²/2)|Rm|²、ℓ*² = 4πG/g² -/
theorem coeff_I (G g Rm2 : ℝ) (hg : g ≠ 0) :
    16 * π * G * (Rm2 / (8 * g ^ 2)) = (4 * π * G / g ^ 2) / 2 * Rm2 := by
  field_simp
  ring

/-- 3 次元では Rm は断面曲率 K₁₂, K₁₃, K₂₃ で決まり、Ricci 固有値は
    λ₁ = K₁₂ + K₁₃ などになる。このとき |Rm|² = 4ΣK² = 4|Ric|² − R² -/
theorem rm2_3d (K12 K13 K23 : ℝ) :
    4 * (K12 ^ 2 + K13 ^ 2 + K23 ^ 2)
      = 4 * ((K12 + K13) ^ 2 + (K12 + K23) ^ 2 + (K13 + K23) ^ 2)
        - ((K12 + K13) + (K12 + K23) + (K13 + K23)) ^ 2 := by
  ring

/-- (I) を |Ric|² について解く:|Ric|² = R/(2ℓ²) + R²/4。R が一定なら |Ric|² も一定 -/
theorem ric2_of_I (R Ric2 l : ℝ) (hl : l ≠ 0) (hI : R = l ^ 2 / 2 * (4 * Ric2 - R ^ 2)) :
    Ric2 = R / (2 * l ^ 2) + R ^ 2 / 4 := by
  have h4 : 4 * Ric2 * l ^ 2 = 2 * R + l ^ 2 * R ^ 2 := by linear_combination (-2 : ℝ) * hI
  field_simp
  linarith [h4]

/-- (II) のトレース部分:縮約 Bianchi divRic = ½∇R のもとで
    g^{cd}(∇_c Ric_bd − ∇_b Ric_cd) = −½ ∇_b R。よって (II) ⇒ ∇R = 0 -/
theorem trace_II (divRic dR : ℝ) (hBianchi : divRic = dR / 2) (hII : divRic - dR = 0) :
    dR = 0 := by
  linarith

/-! ### α-II.2 完備解の分類(CIS の候補から (I) が選ぶもの) -/

/-- CIS 1999 の結論に現れる完備な局所共形平坦モデル -/
inductive Model
  | flat
  | sphere (a : ℝ)      -- S³(a)
  | hyp (a : ℝ)         -- H³(a)
  | sphProd (a : ℝ)     -- S²(a) × ℝ
  | hypProd (a : ℝ)     -- H²(a) × ℝ

/-- 各モデルのスカラー曲率 R -/
noncomputable def Model.R : Model → ℝ
  | .flat => 0
  | .sphere a => 6 / a ^ 2
  | .hyp a => -6 / a ^ 2
  | .sphProd a => 2 / a ^ 2
  | .hypProd a => -2 / a ^ 2

/-- 各モデルの |Rm|²(断面曲率 K について 3 次元の空間形は 12K²、積は 4K²) -/
noncomputable def Model.Rm2 : Model → ℝ
  | .flat => 0
  | .sphere a => 12 / a ^ 4
  | .hyp a => 12 / a ^ 4
  | .sphProd a => 4 / a ^ 4
  | .hypProd a => 4 / a ^ 4

/-- 方程式 (I) -/
def SatI (l : ℝ) (M : Model) : Prop := M.R = l ^ 2 / 2 * M.Rm2

private lemma eq_of_sq_eq {a l : ℝ} (ha : 0 < a) (hl : 0 < l) (h : a ^ 2 = l ^ 2) : a = l := by
  have h2 : (a - l) * (a + l) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · linarith

theorem satI_flat (l : ℝ) : SatI l .flat := by
  simp [SatI, Model.R, Model.Rm2]

theorem satI_sphere (l a : ℝ) (hl : 0 < l) (ha : 0 < a) : SatI l (.sphere a) ↔ a = l := by
  simp only [SatI, Model.R, Model.Rm2]
  constructor
  · intro h
    have ha0 : a ≠ 0 := ha.ne'
    field_simp at h
    have : a ^ 2 = l ^ 2 := by nlinarith [pow_pos ha 2]
    exact eq_of_sq_eq ha hl this
  · rintro rfl
    field_simp
    ring

theorem not_satI_hyp (l a : ℝ) (ha : 0 < a) : ¬ SatI l (.hyp a) := by
  simp only [SatI, Model.R, Model.Rm2]
  intro h
  have h1 : -6 / a ^ 2 < 0 := by
    have : 0 < 6 / a ^ 2 := by positivity
    linarith [neg_div (a ^ 2) (6 : ℝ)]
  have h2 : 0 ≤ l ^ 2 / 2 * (12 / a ^ 4) := by positivity
  linarith

theorem satI_sphProd (l a : ℝ) (hl : 0 < l) (ha : 0 < a) : SatI l (.sphProd a) ↔ a = l := by
  simp only [SatI, Model.R, Model.Rm2]
  constructor
  · intro h
    have ha0 : a ≠ 0 := ha.ne'
    field_simp at h
    have : a ^ 2 = l ^ 2 := by nlinarith [pow_pos ha 2]
    exact eq_of_sq_eq ha hl this
  · rintro rfl
    field_simp
    ring

theorem not_satI_hypProd (l a : ℝ) (ha : 0 < a) : ¬ SatI l (.hypProd a) := by
  simp only [SatI, Model.R, Model.Rm2]
  intro h
  have h1 : -2 / a ^ 2 < 0 := by
    have : 0 < 2 / a ^ 2 := by positivity
    linarith [neg_div (a ^ 2) (2 : ℝ)]
  have h2 : 0 ≤ l ^ 2 / 2 * (4 / a ^ 4) := by positivity
  linarith

/-- α-II.2 のまとめ:CIS の候補のうち (I) を満たすのは平坦、S³(ℓ)、S²(ℓ)×ℝ だけ -/
theorem three_phases (l : ℝ) (hl : 0 < l) (M : Model)
    (hpos : ∀ a, (M = .sphere a ∨ M = .hyp a ∨ M = .sphProd a ∨ M = .hypProd a) → 0 < a)
    (h : SatI l M) :
    M = .flat ∨ M = .sphere l ∨ M = .sphProd l := by
  cases M with
  | flat => exact Or.inl rfl
  | sphere a =>
    have ha := hpos a (Or.inl rfl)
    exact Or.inr (Or.inl (by rw [(satI_sphere l a hl ha).1 h]))
  | hyp a =>
    exact absurd h (not_satI_hyp l a (hpos a (Or.inr (Or.inl rfl))))
  | sphProd a =>
    have ha := hpos a (Or.inr (Or.inr (Or.inl rfl)))
    exact Or.inr (Or.inr (by rw [(satI_sphProd l a hl ha).1 h]))
  | hypProd a =>
    exact absurd h (not_satI_hypProd l a (hpos a (Or.inr (Or.inr (Or.inr rfl)))))

/-! ### α-II.4 Bochner 恒等式の κ と窓定理 -/

/-- κ = Σ_{i<j} (λᵢ + λⱼ − R/2)(λᵢ − λⱼ)² = σ₁³ − 4σ₁σ₂ + 9σ₃(R = σ₁) -/
theorem kappa_sym (l1 l2 l3 : ℝ) :
    let s1 := l1 + l2 + l3
    let s2 := l1 * l2 + l2 * l3 + l3 * l1
    let s3 := l1 * l2 * l3
    (l1 + l2 - s1 / 2) * (l1 - l2) ^ 2 + (l2 + l3 - s1 / 2) * (l2 - l3) ^ 2
      + (l1 + l3 - s1 / 2) * (l1 - l3) ^ 2 = s1 ^ 3 - 4 * s1 * s2 + 9 * s3 := by
  intro s1 s2 s3
  ring

/-- 固有値の角度表示 λᵢ = R/3 + q cᵢ(Σcᵢ = 0、Σ_{i<j}cᵢcⱼ = −3/4、Πcᵢ = cos3θ/4)と
    (I) から決まる q = √R·√(12 − 2Rℓ²)/(6ℓ) のもとで
    κ = (6 − Rℓ²) R^{3/2}/(48ℓ³) · [2ℓ√R + √(12 − 2Rℓ²) cos3θ] -/
theorem kappa_closed (sR t l C c1 c2 c3 : ℝ) (hl : l ≠ 0)
    (he1 : c1 + c2 + c3 = 0) (he2 : c1 * c2 + c2 * c3 + c3 * c1 = -3 / 4)
    (he3 : c1 * c2 * c3 = C / 4) (ht : t ^ 2 = 12 - 2 * sR ^ 2 * l ^ 2) :
    let R := sR ^ 2
    let q := sR * t / (6 * l)
    let l1 := R / 3 + q * c1
    let l2 := R / 3 + q * c2
    let l3 := R / 3 + q * c3
    let s1 := l1 + l2 + l3
    let s2 := l1 * l2 + l2 * l3 + l3 * l1
    let s3 := l1 * l2 * l3
    s1 ^ 3 - 4 * s1 * s2 + 9 * s3
      = (6 - R * l ^ 2) * sR ^ 3 / (48 * l ^ 3) * (2 * l * sR + t * C) := by
  intro R q l1 l2 l3 s1 s2 s3
  have hs1 : s1 = R + q * (c1 + c2 + c3) := by simp only [s1, l1, l2, l3]; ring
  have hs2 : s2 = R ^ 2 / 3 + 2 * R / 3 * q * (c1 + c2 + c3)
      + q ^ 2 * (c1 * c2 + c2 * c3 + c3 * c1) := by simp only [s2, l1, l2, l3]; ring
  have hs3 : s3 = R ^ 3 / 27 + R ^ 2 / 9 * q * (c1 + c2 + c3)
      + R / 3 * q ^ 2 * (c1 * c2 + c2 * c3 + c3 * c1) + q ^ 3 * (c1 * c2 * c3) := by
    simp only [s3, l1, l2, l3]; ring
  rw [hs1, hs2, hs3, he1, he2, he3]
  have h6 : 6 - sR ^ 2 * l ^ 2 = t ^ 2 / 2 := by linarith [ht]
  simp only [q, R]
  rw [h6]
  field_simp
  ring

/-- 窓定理:0 < x = Rℓ² < 6、cos3θ ≥ −1、かつ κ の角括弧
    2√x + √(12 − 2x) cos3θ が負なら x < 2 -/
theorem window (x c : ℝ) (hx0 : 0 < x) (hx6 : x < 6) (hc : -1 ≤ c)
    (hneg : 2 * √x + √(12 - 2 * x) * c < 0) : x < 2 := by
  have hs : 0 ≤ √(12 - 2 * x) := Real.sqrt_nonneg _
  have h1 : -√(12 - 2 * x) ≤ √(12 - 2 * x) * c := by nlinarith
  have h2 : 2 * √x < √(12 - 2 * x) := by linarith
  have h3 : (2 * √x) ^ 2 < (√(12 - 2 * x)) ^ 2 := by
    have : 0 ≤ 2 * √x := by positivity
    nlinarith
  rw [mul_pow, Real.sq_sqrt hx0.le, Real.sq_sqrt (by linarith)] at h3
  linarith

/-- 窓定理の後半:κ < 0 の条件 cos3θ < −√(2x/(6−x)) は、
    角括弧を負にする条件と同値(0 < x < 6) -/
theorem window_cos (x c : ℝ) (hx0 : 0 < x) (hx6 : x < 6) :
    2 * √x + √(12 - 2 * x) * c < 0 ↔ c < -(2 * √x / √(12 - 2 * x)) := by
  have hpos : 0 < √(12 - 2 * x) := Real.sqrt_pos.2 (by linarith)
  constructor
  · intro h
    rw [lt_neg, div_lt_iff hpos]
    linarith
  · intro h
    rw [lt_neg, div_lt_iff hpos] at h
    linarith

/-! ### α-II.9 BR の首の lapse -/

theorem br_lapse_d1 (l s : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun s => cosh (s / l)) (sinh (s / l) / l) s := by
  have h := (hasDerivAt_cosh (s / l)).comp s ((hasDerivAt_id s).div_const l)
  convert h using 1
  ring

/-- N = cosh(s/ℓ) について N″ = N/ℓ² -/
theorem br_lapse_d2 (l s : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun s => sinh (s / l) / l) (cosh (s / l) / l ^ 2) s := by
  have h := ((hasDerivAt_sinh (s / l)).comp s ((hasDerivAt_id s).div_const l)).div_const l
  convert h using 1
  ring

end CFT.AlphaII
