/-
  α-XI.4(新):首を Higgs 場で支える(EYM–Higgs)

  運動学:ダンベルの首(AdS₂ × S²、半径 ℓ、磁荷 1)。そのまま変えない。
  作用:EYM に随伴表現の Higgs Φ を足す。L = R/(16πG) − (1/4g²)F² − ½|DΦ|² − (λ/4)(|Φ|² − v²)²。
  ansatz:Witten の磁気的な形(W)と、はりねずみ Φ = H(r) x̂(外部:'t Hooft–Polyakov の縮約、この ansatz が
  場の方程式と両立すること)。縮約したエネルギー密度(静的)は
    ρ = (1/2g²)((1 − W²)²/r⁴ + 2W′²/r²) + ½H′² + W²H²/r² + (λ/4)(H² − v²)²
  (|D_rΦ| = |H′|、接線の |D_θΦ| = |D_φΦ| = |W H|/r)。

  力学(Lean で示すこと)
  1. 首 W = 0、H = v(真空)は厳密な解のまま:
     * Higgs の寄与は 0 で ρ は純粋な EYM の首と同じ(`neck_rho`、AlphaII_EYM `rho`)。したがってハミルトン拘束と
       首の半径 ℓ² = 4πG/g² は変わらない(III.7、AlphaII_EYM `ell_neck`)。
     * Higgs の応力は DΦ = 0、V(v) = 0 で 0(`higgs_stress_zero`)。
     * W と H の方程式の力の項 ∂U/∂W(W = 0)、∂U/∂H(H = v)は 0(`force_W_zero`、`force_H_zero`)。
       場は一定なので微分の項も 0。
  2. W のモードの質量:U(W) − U(0) = (v²/r² − 1/(g²r⁴))W² + W⁴/(2g²r⁴)(`quad_expansion`)、
     運動の係数 W′²/(g²r²)(ρ の W′ の項)。したがって □δW = m²δW、m² = g²v² − 1/r²(`w_mass`)。
     首 r = ℓ で m²ℓ² = −1 + m_W²ℓ²(m_W = gv、`w_mass_neck`)。v = 0 で IX.15 の −1 に戻る。
  3. 安定の条件:BF 限界 m²ℓ² ≥ −1/4 ⇔ m_W²ℓ² ≥ 3/4(`bf_condition`)。ℓ² = 4πG/g²、G = 1/M_Pl² なら
     ⇔ v² ≥ 3M_Pl²/(16π)、つまり v ≥ √(3/16π) M_Pl ≈ 0.244 M_Pl、m_W ≥ √(3/16π) g M_Pl(`planck_condition`)。
  4. どの長さの首でも安定(BF 限界を上回るとき):大域座標 (ℓ²/sin²u)(−dτ² + du²) のモードの二次形式で
     f = √(sin u) h とおくと f′² − ¼f²/sin²u = sin u(h′² + ¼h²) + d/du(½ cos u h²)(`hardy_pointwise`)。
     接合 [a, b](0 < a、b < π)で f = 0 なら ∫(f′² − ¼f²/sin²u) = ∫ sin u(h′² + ¼h²) ≥ 0(`hardy_neck`)、
     m²ℓ² ≥ −1/4 なら ∫(f′² + m²ℓ² f²/sin²u) ≥ 0(`no_growing_mode`)。min–max(外部)で成長するモードはない。
     純粋な EYM(m²ℓ² = −1)で長い首が不安定だったこと(XI.1)と、長い首でしか使えない Schwarzian(IX.14)との
     衝突が、Higgs で解ける。
  未:帽子(W = cos χ)は Higgs の勾配のエネルギーで解が変わる(XI.7)。
  WGC:安定の条件 m_W ≳ 0.24 g M_Pl は、磁気的な WGC の切断 Λ ~ g M_Pl と同じ尺度(解釈)。
  Lee–Nair–Weinberg 1992:磁荷の RN は破れたゲージ理論で地平線が小さいと古典的に不安定(定性的に一致)。
-/
import CFT.AlphaII_EYM
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals

namespace CFT.HiggsNeck

open Real Set intervalIntegral

/-! ### 1. 首は厳密な解のまま -/

/-- 縮約したエネルギー密度 -/
noncomputable def rhoH (g lam v W W1 H H1 r : ℝ) : ℝ :=
  1 / (2 * g ^ 2) * ((1 - W ^ 2) ^ 2 / r ^ 4 + 2 * W1 ^ 2 / r ^ 2) + H1 ^ 2 / 2 + W ^ 2 * H ^ 2 / r ^ 2
    + lam / 4 * (H ^ 2 - v ^ 2) ^ 2

/-- 【α-XI.4】首(W = 0、H = v)で ρ は純粋な EYM の首の値と同じ -/
theorem neck_rho (g lam v r : ℝ) : rhoH g lam v 0 0 v 0 r = CFT.EYM.rho g 0 0 r := by
  unfold rhoH CFT.EYM.rho
  ring

/-- 【α-XI.4】Higgs の応力 T_μν = Σ D_μΦD_νΦ − g_μν(½|DΦ|² + V) は DΦ = 0、V = 0 で 0 -/
theorem higgs_stress_zero (gmn kin V : ℝ) (DmuDnu : ℝ) (hD : DmuDnu = 0) (hk : kin = 0) (hV : V = 0) :
    DmuDnu - gmn * (kin / 2 + V) = 0 := by
  rw [hD, hk, hV]; ring

/-- 真空で V(v) = (λ/4)(v² − v²)² = 0、勾配 |D_rΦ| = H′ = 0、|D_θΦ| = WH/r = 0 -/
theorem neck_vacuum (lam v r : ℝ) : lam / 4 * (v ^ 2 - v ^ 2) ^ 2 = 0 ∧ (0 : ℝ) * v / r = 0 := by
  constructor <;> ring

/-- ポテンシャルの部分 U(W, H) = (1/(2g²r⁴))(1 − W²)² + (H²/r²)W² + (λ/4)(H² − v²)² -/
noncomputable def U (g lam v W H r : ℝ) : ℝ :=
  1 / (2 * g ^ 2 * r ^ 4) * (1 - W ^ 2) ^ 2 + H ^ 2 / r ^ 2 * W ^ 2 + lam / 4 * (H ^ 2 - v ^ 2) ^ 2

/-- U は ρ の微分を含まない部分 -/
theorem U_eq_rho (g lam v W H r : ℝ) (hg : g ≠ 0) (hr : r ≠ 0) :
    U g lam v W H r = rhoH g lam v W 0 H 0 r := by
  unfold U rhoH
  field_simp <;> ring

/-- a(1 − W²)² + bW² + c の微分 -/
theorem poly_deriv (a b c w : ℝ) :
    HasDerivAt (fun W => a * (1 - W ^ 2) ^ 2 + b * W ^ 2 + c)
      (a * (2 * (1 - w ^ 2) * (-(2 * w))) + b * (2 * w)) w := by
  have h1 : HasDerivAt (fun W : ℝ => 1 - W ^ 2) (-(2 * w)) w := by
    simpa using (hasDerivAt_pow 2 w).const_sub 1
  have h2 := (h1.pow 2).const_mul a
  have h3 := (hasDerivAt_pow 2 w).const_mul b
  have h := (h2.add h3).add_const c
  convert h using 1
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]

/-- 【α-XI.4】W の方程式の力の項は W = 0 で 0 -/
theorem force_W_zero (g lam v r : ℝ) : HasDerivAt (fun W => U g lam v W v r) 0 0 := by
  have h := poly_deriv (1 / (2 * g ^ 2 * r ^ 4)) (v ^ 2 / r ^ 2) (lam / 4 * (v ^ 2 - v ^ 2) ^ 2) 0
  convert h using 1
  simp

/-- 【α-XI.4】H の方程式の力の項は W = 0、H = v で 0 -/
theorem force_H_zero (g lam v r : ℝ) : HasDerivAt (fun H => U g lam v 0 H r) 0 v := by
  have h1 : HasDerivAt (fun H : ℝ => H ^ 2 - v ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).sub_const (v ^ 2)
  have h2 := (h1.pow 2).const_mul (lam / 4)
  have h3 := ((hasDerivAt_pow 2 v).div_const (r ^ 2)).mul_const ((0 : ℝ) ^ 2)
  have h := (h3.add h2).const_add (1 / (2 * g ^ 2 * r ^ 4) * (1 - (0 : ℝ) ^ 2) ^ 2)
  unfold U
  convert h using 1
  · funext H; ring
  · simp

/-! ### 2. W のモードの質量 -/

/-- 【α-XI.4】U(W) − U(0) = (v²/r² − 1/(g²r⁴))W² + W⁴/(2g²r⁴) -/
theorem quad_expansion (g lam v W r : ℝ) :
    U g lam v W v r - U g lam v 0 v r
      = (v ^ 2 / r ^ 2 - 1 / (g ^ 2 * r ^ 4)) * W ^ 2 + 1 / (2 * g ^ 2 * r ^ 4) * W ^ 4 := by
  unfold U
  ring

/-- 【α-XI.4】運動の係数 K = 1/(g²r²)(ρ の W′ の項)と 2 次の係数 κ から m² = κ/K = g²v² − 1/r² -/
theorem w_mass (g v r : ℝ) (hg : g ≠ 0) (hr : r ≠ 0) :
    (v ^ 2 / r ^ 2 - 1 / (g ^ 2 * r ^ 4)) / (1 / (g ^ 2 * r ^ 2)) = g ^ 2 * v ^ 2 - 1 / r ^ 2 := by
  field_simp
  ring

/-- ρ の W′ の項は W′²/(g²r²) -/
theorem kinetic_coeff (g W1 r : ℝ) (hg : g ≠ 0) (hr : r ≠ 0) :
    1 / (2 * g ^ 2) * (2 * W1 ^ 2 / r ^ 2) = 1 / (g ^ 2 * r ^ 2) * W1 ^ 2 := by
  field_simp
  ring

/-- 【α-XI.4】首 r = ℓ で m²ℓ² = −1 + m_W²ℓ²(m_W = gv)。v = 0 で IX.15 の −1 -/
theorem w_mass_neck (g v l : ℝ) (hl : l ≠ 0) :
    (g ^ 2 * v ^ 2 - 1 / l ^ 2) * l ^ 2 = -1 + (g * v) ^ 2 * l ^ 2 ∧
    (g ^ 2 * 0 ^ 2 - 1 / l ^ 2) * l ^ 2 = -1 := by
  constructor <;> field_simp <;> ring

/-! ### 3. 安定の条件 -/

/-- 【α-XI.4】BF 限界:−1 + m_W²ℓ² ≥ −1/4 ⇔ m_W²ℓ² ≥ 3/4 -/
theorem bf_condition (x : ℝ) : -1 / 4 ≤ -1 + x ↔ 3 / 4 ≤ x := by
  constructor <;> intro h <;> linarith

/-- 共形次元 Δ = ½ ± √(¼ + m²ℓ²) は m²ℓ² ≥ −1/4 で実(Δ(Δ − 1) = m²ℓ²) -/
theorem delta_real (μ : ℝ) (hμ : -1 / 4 ≤ μ) :
    let Δ := 1 / 2 + Real.sqrt (1 / 4 + μ)
    Δ * (Δ - 1) = μ := by
  intro Δ
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 4 + μ by linarith)
  simp only [Δ]
  linear_combination h

/-- 【α-XI.4】ℓ² = 4πG/g²、G = 1/M² なら m_W²ℓ² = 4πv²/M²、
m_W²ℓ² ≥ 3/4 ⇔ v² ≥ 3M²/(16π) ⇔ m_W² ≥ 3g²M²/(16π) -/
theorem planck_condition (g v M : ℝ) (hg : g ≠ 0) (hM : 0 < M) :
    (g * v) ^ 2 * (4 * π * (1 / M ^ 2) / g ^ 2) = 4 * π * v ^ 2 / M ^ 2 ∧
    (3 / 4 ≤ 4 * π * v ^ 2 / M ^ 2 ↔ 3 * M ^ 2 / (16 * π) ≤ v ^ 2) ∧
    (3 * M ^ 2 / (16 * π) ≤ v ^ 2 ↔ 3 * g ^ 2 * M ^ 2 / (16 * π) ≤ (g * v) ^ 2) := by
  have hpi := pi_pos
  have hM2 : 0 < M ^ 2 := by positivity
  have hg2 : 0 < g ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    ring
  · rw [le_div_iff₀ hM2, div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  · rw [mul_pow, div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    constructor
    · intro h; nlinarith
    · intro h
      have : g ^ 2 * (3 * M ^ 2) ≤ g ^ 2 * (v ^ 2 * (16 * π)) := by nlinarith
      exact le_of_mul_le_mul_left this hg2

/-! ### 4. どの長さの首でも成長するモードはない -/

/-- 【α-XI.4】f = √s h、f′ = c h/(2√s) + √s h′(s = sin u > 0、s² + c² = 1)で
f′² − ¼f²/s² = s h′² + ¼ s h² + (−½ s h² + c h h′) -/
theorem hardy_pointwise (s c h hd : ℝ) (hs : 0 < s) (hsc : s ^ 2 + c ^ 2 = 1) :
    (1 / 2 * c * h / Real.sqrt s + Real.sqrt s * hd) ^ 2 - 1 / 4 * (Real.sqrt s * h) ^ 2 / s ^ 2
      = s * hd ^ 2 + 1 / 4 * s * h ^ 2 + (-(1 / 2) * s * h ^ 2 + c * h * hd) := by
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 < q ∧ s = q ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  rw [Real.sqrt_sq hq.le]
  have hq0 : q ≠ 0 := hq.ne'
  have e : (1 / 2 * c * h / q + q * hd) ^ 2 - 1 / 4 * (q * h) ^ 2 / (q ^ 2) ^ 2
      - (q ^ 2 * hd ^ 2 + 1 / 4 * q ^ 2 * h ^ 2 + (-(1 / 2) * q ^ 2 * h ^ 2 + c * h * hd))
      = ((q ^ 2) ^ 2 + c ^ 2 - 1) * h ^ 2 / (4 * q ^ 2) := by
    field_simp
    ring
  have h0 : ((q ^ 2) ^ 2 + c ^ 2 - 1) * h ^ 2 / (4 * q ^ 2) = 0 := by
    rw [show (q ^ 2) ^ 2 + c ^ 2 - 1 = 0 by linarith, zero_mul, zero_div]
  rw [h0] at e
  exact sub_eq_zero.mp e

/-- 【α-XI.4】接合 [a, b](0 < a ≤ b < π)で h(a) = h(b) = 0 なら
∫(f′² − ¼f²/sin²u) = ∫ sin u(h′² + ¼h²) -/
theorem hardy_neck (a b : ℝ) (h hd : ℝ → ℝ) (hab : a ≤ b) (ha : 0 < a) (hb : b < π)
    (hh : ∀ u, HasDerivAt h (hd u) u) (hcd : Continuous hd) (hc : Continuous h)
    (ha0 : h a = 0) (hb0 : h b = 0) :
    ∫ u in a..b, ((1 / 2 * cos u * h u / Real.sqrt (sin u) + Real.sqrt (sin u) * hd u) ^ 2
        - 1 / 4 * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2)
      = ∫ u in a..b, sin u * (hd u ^ 2 + 1 / 4 * h u ^ 2) := by
  have hcongr : ∀ u ∈ uIcc a b,
      ((1 / 2 * cos u * h u / Real.sqrt (sin u) + Real.sqrt (sin u) * hd u) ^ 2
        - 1 / 4 * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2)
      = sin u * (hd u ^ 2 + 1 / 4 * h u ^ 2) + (-(1 / 2) * sin u * h u ^ 2 + cos u * h u * hd u) := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hs : 0 < sin u := sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])
    rw [hardy_pointwise (sin u) (cos u) (h u) (hd u) hs (sin_sq_add_cos_sq u)]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have c1 : Continuous fun u => sin u * (hd u ^ 2 + 1 / 4 * h u ^ 2) := by fun_prop
  have c2 : Continuous fun u => -(1 / 2) * sin u * h u ^ 2 + cos u * h u * hd u := by fun_prop
  rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun u => 1 / 2 * cos u * h u ^ 2)
      (-(1 / 2) * sin x * h x ^ 2 + cos x * h x * hd x) x := by
    intro x _
    have k := ((hasDerivAt_cos x).const_mul (1 / 2)).mul ((hh x).pow 2)
    convert k using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  rw [integral_eq_sub_of_hasDerivAt hF (c2.intervalIntegrable _ _), ha0, hb0]
  ring

/-- 【α-XI.4】m²ℓ² ≥ −1/4 なら、接合で 0 になるどの試験関数でも二次形式 ∫(f′² + m²ℓ² f²/sin²u) ≥ 0 -/
theorem no_growing_mode (a b μ : ℝ) (h hd : ℝ → ℝ) (hab : a ≤ b) (ha : 0 < a) (hb : b < π)
    (hμ : -1 / 4 ≤ μ) (hh : ∀ u, HasDerivAt h (hd u) u) (hcd : Continuous hd) (hc : Continuous h)
    (ha0 : h a = 0) (hb0 : h b = 0) :
    0 ≤ ∫ u in a..b, ((1 / 2 * cos u * h u / Real.sqrt (sin u) + Real.sqrt (sin u) * hd u) ^ 2
        + μ * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2) := by
  have hpos : ∀ u ∈ Icc a b, 0 < sin u := fun u hu =>
    sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])
  have hne : ∀ u ∈ Icc a b, sin u ≠ 0 := fun u hu => (hpos u hu).ne'
  have csq : Continuous fun u => Real.sqrt (sin u) := Real.continuous_sqrt.comp continuous_sin
  have hsqne : ∀ u ∈ Icc a b, Real.sqrt (sin u) ≠ 0 := fun u hu => (Real.sqrt_pos.2 (hpos u hu)).ne'
  have hfc : ∀ c : ℝ, ContinuousOn (fun u => c * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2) (Icc a b) :=
    fun c => (continuous_const.mul ((csq.mul hc).pow 2)).continuousOn.div
      (continuous_sin.pow 2).continuousOn (fun u hu => pow_ne_zero 2 (hne u hu))
  have hfd : ContinuousOn (fun u => 1 / 2 * cos u * h u / Real.sqrt (sin u) + Real.sqrt (sin u) * hd u)
      (Icc a b) :=
    (((continuous_const.mul continuous_cos).mul hc).continuousOn.div csq.continuousOn hsqne).add
      (csq.mul hcd).continuousOn
  have hle : ∫ u in a..b, ((1 / 2 * cos u * h u / Real.sqrt (sin u) + Real.sqrt (sin u) * hd u) ^ 2
        - 1 / 4 * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2)
      ≤ ∫ u in a..b, ((1 / 2 * cos u * h u / Real.sqrt (sin u) + Real.sqrt (sin u) * hd u) ^ 2
        + μ * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2) := by
    apply intervalIntegral.integral_mono_on hab
    · exact ((hfd.pow 2).sub (hfc (1 / 4))).intervalIntegrable_of_Icc hab
    · exact ((hfd.pow 2).add (hfc μ)).intervalIntegrable_of_Icc hab
    · intro u hu
      have hq : 0 ≤ (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2 := by positivity
      have : -(1 / 4) * ((Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2)
          ≤ μ * ((Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2) := mul_le_mul_of_nonneg_right (by linarith) hq
      have e1 : 1 / 4 * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2
          = 1 / 4 * ((Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2) := by ring
      have e2 : μ * (Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2
          = μ * ((Real.sqrt (sin u) * h u) ^ 2 / sin u ^ 2) := by ring
      rw [e1, e2]
      linarith
  rw [hardy_neck a b h hd hab ha hb hh hcd hc ha0 hb0] at hle
  have hnn : 0 ≤ ∫ u in a..b, sin u * (hd u ^ 2 + 1 / 4 * h u ^ 2) := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    have := hpos u hu
    positivity
  linarith

end CFT.HiggsNeck
