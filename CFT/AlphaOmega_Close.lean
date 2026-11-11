/-
  段階 19(2026-11-11):部分の項目を、定理の形に述べ直して閉じる

  * α-X.7(くさびは捕捉領域):`oc_raychaudhuri` 拘束 C_u = 0 から (r_u/Ω)_u = −2W_u²/(rΩ) ≤ 0、
    `oc_trapped` 初めに 0 なら以後 r_u/Ω ≤ 0。波面 u = 0(首、r_u = 0)と v = 0(帽子、r_v = 0)から出るので、
    くさび全体で r_u ≤ 0、r_v ≤ 0(捕捉領域)。崩壊の詳細(寿命 1.271ℓ など)は数値。
  * α-XI.5(dyon の首):`oc_attractor` 有効ポテンシャル p²/x + q²x(x = e^{2φ})は x = p/q で最小値 2pq、
    `oc_EB` E·B ∝ pq/r⁴ ≠ 0(カイラルアノマリーの源は 0 でない。アノマリーの式は外部)。
  * α-XI.7(Higgs):`oc_higgs_vev` Higgs が真空の値 h = v にとどまるなら W = 0(首は h = v のまま厳密解)、
    `oc_higgs_sym` 帽子が残るのは h ≡ 0 のときで、そのときポテンシャル λv⁴/4 が宇宙定数として加わる。
  * α-XII.5(共通の時計):`oc_ads_global`、`oc_ads_sync` 首 AdS₂ の大域座標と同期座標の埋め込み、
    `oc_focus` 首の同期座標の焦点(t = πℓ/2)は η = π/2、χ = π/2 の一点で、帽子の崩壊 Ω = ℓ cos η = 0 と
    同じ共形時間。共形時間 η が帽子と首の共通の時計。
  * α-XII.8、XV.4(一様なモードの量子化):`oc_omega_level` Ω の準位と ℓ²、`oc_well` 一様な YM のポテンシャル
    K(1 − f²)²(K = 3π²/g²)は障壁の頂上 f = 0 でエネルギー K(帽子)、井戸の底の振動数は 2、
    `oc_parity` 弱結合の準位 2m + 1 は Ω の準位 n + ½ と決して一致しない。
    したがって α = 3π/(4n + 2) は「YM のエネルギー = 障壁の頂上の値」とおいた半古典の式で、
    固有値の条件としては弱結合で解がない(否定的な結論)。
  * α-XIV.7(二つの n):`oc_discrete_casimir` 実のウェイト h の表現(離散系列)の Casimir は h(h − 1) ≥ −1/4、
    `oc_principal` 首の W は Casimir −1 = Δ(Δ − 1)、Δ = ½ ± i√3/2(主系列)、`oc_node_spacing` 節の間隔 2π/√3。
    量子の n(離散系列の準位)と古典の n(主系列の対数周期の節)は別の種類の表現に属する。
  * α-XV.5(状態と境界条件):`oc_invariant_not_regular` sl(2,ℝ) で不変な配位は r = 定数で、極で r = 0 なら恒等的に 0。
    正則な宇宙は必ず対称性を破る。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

open Real

namespace CFT.OC

/-! ### α-X.7:くさびは捕捉領域 -/

/-- 拘束 C_u = r_uu − (Ω_u/Ω) r_u + 2W_u²/r = 0 から (r_u/Ω)_u = (r_uu Ω − r_u Ω_u)/Ω² = −2W_u²/(rΩ) -/
theorem oc_raychaudhuri (r Om ru ruu Omu Wu : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (hC : ruu - Omu / Om * ru + 2 * Wu ^ 2 / r = 0) :
    (ruu * Om - ru * Omu) / Om ^ 2 = -(2 * Wu ^ 2 / (r * Om)) := by
  have e : ruu = Omu / Om * ru - 2 * Wu ^ 2 / r := by linarith
  rw [e]
  field_simp
  ring

/-- 右辺は r > 0、Ω > 0 で 0 以下 -/
theorem oc_raychaudhuri_sign (r Om Wu : ℝ) (hr : 0 < r) (hO : 0 < Om) :
    -(2 * Wu ^ 2 / (r * Om)) ≤ 0 := by
  have : 0 ≤ 2 * Wu ^ 2 / (r * Om) := by positivity
  linarith

/-- 微分が 0 以下で初めに 0 なら、以後 0 以下(g = r_u/Ω を波面から測る) -/
theorem oc_trapped {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hneg : ∀ x, g' x ≤ 0)
    (h0 : g 0 = 0) {x : ℝ} (hx : 0 ≤ x) : g x ≤ 0 := by
  have ha : Antitone g :=
    antitone_of_deriv_nonpos (fun x => (hg x).differentiableAt) (fun x => by rw [(hg x).deriv]; exact hneg x)
  have h := ha hx
  rw [h0] at h
  exact h

/-! ### α-XI.5:dyon の首 -/

/-- 有効ポテンシャル p²/x + q²x(x = e^{2φ} > 0)は 2pq 以上で、等号は x = p/q(アトラクター) -/
theorem oc_attractor (p q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    2 * p * q ≤ p ^ 2 / x + q ^ 2 * x ∧ (p ^ 2 / x + q ^ 2 * x = 2 * p * q ↔ x = p / q) := by
  have hx0 : x ≠ 0 := hx.ne'
  have e : p ^ 2 / x + q ^ 2 * x - 2 * p * q = (p - q * x) ^ 2 / x := by
    field_simp
    ring
  have hnn : 0 ≤ (p - q * x) ^ 2 / x := div_nonneg (sq_nonneg _) hx.le
  refine ⟨by linarith, ?_, ?_⟩
  · intro h
    have h0 : (p - q * x) ^ 2 / x = 0 := by linarith
    have h1 := (div_eq_zero_iff.mp h0).resolve_right hx0
    have h2 : p - q * x = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
    rw [eq_div_iff hq.ne']
    linear_combination -h2
  · intro h
    have h2 : p - q * x = 0 := by rw [h]; field_simp
    have h0 : (p - q * x) ^ 2 / x = 0 := by rw [h2]; simp
    linarith

/-- E·B ∝ pq/r⁴ は p, q ≠ 0 なら 0 でない -/
theorem oc_EB (p q r : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) : p * q / r ^ 4 ≠ 0 :=
  div_ne_zero (mul_ne_zero hp hq) (pow_ne_zero 4 hr)

/-! ### α-XI.7:Higgs -/

/-- Higgs の方程式の一様な解 h = v(真空の値)は −2W²v/r² − λ(v² − v²)v = 0、つまり W = 0 を要求する -/
theorem oc_higgs_vev (W v r lam : ℝ) (hv : v ≠ 0) (hr : r ≠ 0)
    (h : -2 * W ^ 2 * v / r ^ 2 - lam * (v ^ 2 - v ^ 2) * v = 0) : W = 0 := by
  rw [sub_self, mul_zero, zero_mul, sub_zero] at h
  rcases div_eq_zero_iff.mp h with h1 | h1
  · have hW : W ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact h3
      · exact absurd h2 hv
    exact (pow_eq_zero_iff two_ne_zero).mp hW
  · exact absurd h1 (pow_ne_zero 2 hr)

/-- 対称な相 h = 0 のポテンシャルエネルギー (λ/4)(h² − v²)² = λv⁴/4(宇宙定数として加わる) -/
theorem oc_higgs_sym (lam v : ℝ) : lam / 4 * (0 ^ 2 - v ^ 2) ^ 2 = lam * v ^ 4 / 4 := by ring

/-! ### α-XII.5:共形時間が共通の時計 -/

/-- 首 AdS₂ の大域座標の埋め込み(sin χ をかけた形):X₀ = cos η/sin χ、X₁ = sin η/sin χ、X₂ = cos χ/sin χ は
  −X₀² − X₁² + X₂² = −1 をみたす -/
theorem oc_ads_global (η χ : ℝ) : -(cos η) ^ 2 - (sin η) ^ 2 + (cos χ) ^ 2 = -(sin χ) ^ 2 := by
  linear_combination -(sin_sq_add_cos_sq η) + sin_sq_add_cos_sq χ

/-- 同期座標 −dt² + cos²t dz² の埋め込み:X₀ = cos t cosh z、X₁ = sin t、X₂ = cos t sinh z -/
theorem oc_ads_sync (t z : ℝ) :
    -(cos t * cosh z) ^ 2 - (sin t) ^ 2 + (cos t * sinh z) ^ 2 = -1 := by
  linear_combination (-(cos t) ^ 2) * (Real.cosh_sq z) - sin_sq_add_cos_sq t

/-- 同期座標の焦点 cos t = 0(t = π/2)では X₀ = X₂ = 0、つまり cos η = 0、cos χ = 0:
  焦点は η = π/2、χ = π/2 の一点。同じ η で帽子の倍率 ℓ cos η も 0(崩壊) -/
theorem oc_focus (l t z η χ : ℝ) (ht : cos t = 0)
    (h0 : cos t * cosh z * sin χ = cos η) (h2 : cos t * sinh z * sin χ = cos χ) :
    cos η = 0 ∧ cos χ = 0 ∧ l * cos η = 0 := by
  rw [ht, zero_mul, zero_mul] at h0 h2
  exact ⟨h0.symm, h2.symm, by rw [← h0, mul_zero]⟩

/-! ### α-XII.8、XV.4:一様なモードの量子化 -/

/-- Ω の振動子(質量 M、振動数 1):古典のエネルギー (M/2)ℓ² を n + ½ とおくと ℓ² = (2n + 1)/M -/
theorem oc_omega_level (M l : ℝ) (n : ℕ) (hM : M ≠ 0) :
    M / 2 * l ^ 2 = n + 1 / 2 ↔ l ^ 2 = (2 * n + 1) / M := by
  constructor
  · intro h
    rw [eq_div_iff hM]
    linear_combination 2 * h
  · intro h
    rw [h]
    field_simp
    ring

/-- 一様な YM のポテンシャル V = K(1 − f²)²:障壁の頂上 f = 0 で V = K(帽子のエネルギー)、
  井戸の底 f = 1 で V″ = K(12f² − 4) = 8K、質量 2K なので振動数の 2 乗は 4(振動数 2) -/
theorem oc_well (K : ℝ) (hK : K ≠ 0) :
    K * (1 - 0 ^ 2) ^ 2 = K ∧ K * (12 * 1 ^ 2 - 4) / (2 * K) = 4 := by
  constructor
  · ring
  · field_simp
    ring

/-- 弱結合の YM の準位 2m + 1 は、Ω の準位 n + ½ と一致しない -/
theorem oc_parity (m n : ℕ) : (2 * (m : ℝ) + 1) ≠ n + 1 / 2 := by
  intro h
  have h3 : ((4 * m + 2 : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h4 : 4 * m + 2 = 2 * n + 1 := by exact_mod_cast h3
  omega

/-! ### α-XIV.7:二つの n -/

/-- 実のウェイト h の表現(離散系列)の Casimir h(h − 1) は −1/4 以上で、−1 にはならない -/
theorem oc_discrete_casimir (h : ℝ) : -1 / 4 ≤ h * (h - 1) ∧ h * (h - 1) ≠ -1 := by
  have key : -1 / 4 ≤ h * (h - 1) := by nlinarith [sq_nonneg (h - 1 / 2)]
  exact ⟨key, by intro e; linarith⟩

/-- 首の W(m²ℓ² = −1)のウェイト Δ = ½ ± iν、ν = √3/2:Δ(Δ − 1) の実部 −¼ − ν² = −1(主系列) -/
theorem oc_principal : -(1 / 4 : ℝ) - (Real.sqrt 3 / 2) ^ 2 = -1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [div_pow, h3]
  norm_num

/-- 喉の中のモード e^{−s/2}cos(√3 s/2) の節の間隔は 2π/√3(位相 √3 s/2 が π 進む) -/
theorem oc_node_spacing : Real.sqrt 3 / 2 * (2 * π / Real.sqrt 3) = π := by
  have h : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-! ### α-XV.5:不変な配位は正則でない -/

/-- sl(2,ℝ) で不変な配位は r = Ω sin χ が定数(oq_neck_unique)。極で r = 0 なら恒等的に 0:
  正則な(両極で閉じた)宇宙は対称性で不変になれない -/
theorem oc_invariant_not_regular (r : ℝ → ℝ) (a : ℝ) (hconst : ∀ χ, r χ = a) (h0 : r 0 = 0) :
    ∀ χ, r χ = 0 := by
  intro χ
  rw [hconst χ, ← hconst 0, h0]

end CFT.OC
