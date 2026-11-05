/-
  橋 A:W = r′ は「ねじれ」(2026-11-05、否定的な結果 VII.8-C が指した先)

  VII.8-C(内部の S⁹ の Dirac の核は 0)は、カイラルなモードの出どころが内部空間ではないことを示した。
  ダンベルの側を調べると、次のことがわかった。

  * 運動学:断面 dρ² + r(ρ)²dΩ²、球対称な SU(2) の場 W(ρ)、ダンベルでは W = r′(II.1)。
  * 作用:アイソスピン ½ の Dirac 場と随伴 Higgs(XI.4)の湯川結合 G。
  * 力学:
    (1) 平坦空間のはりねずみの上で、スピンとアイソスピンの一重項 u = f(ρ)ε(ε = iσ₂)について
        σ·D(fε) = [f′ + (1 − W)/ρ · f](x̂·σ)ε(`gauge_singlet`:ゲージ場の項の 2×2 行列の恒等式)、
        湯川の項 M(fε) = −(Gvh/2) f (x̂·σ)ε(`eps_xsT`)。
    (2) 共形写像で曲がった断面に移すと、係数は (r′ − W)/r になる(`conformal_transfer`。
        Dirac 作用素の共形共変性 χ = (r/R)f は外部:Hitchin)。
    (3) ダンベルでは W = r′ なので係数は 0:スピン接続とゲージ場がちょうど打ち消し合い、
        一重項は共変的に一定(`twist_cancel`)。アイソスピンがスピンの役をする(Jackiw–Rebbi の
        「アイソスピンからのスピン」)が、ダンベルでは幾何(W = r′)そのものがそれを実現する。
    (4) Higgs を入れると、ゼロモードは厳密に f = exp(∓∫m)、g = ±i f(m = Gvh/2、`zero_mode`、`system_reduce`)。
        形は Higgs の分布だけで決まる。首で m ≥ m₀ なら |f|² ≤ e^{−2m₀x} で、二つの帽子に一つずつ局在する
        (`localization`)。
    (5) 極 2(W = −1、純粋ゲージ)では、スピン枠とゲージの遷移が一重項の上で打ち消し合う:
        (x̂·σ)ε(i x̂·σ)ᵀ = −iε(`pole_singlet`)。
  * 正直な訂正:局在するのは接合ではなく帽子(単極子の芯)。4 次元の γ⁵ のカイラリティは出ない
    (湯川が γ⁵ を破る)。ゼロモードは Jackiw–Rebbi のフェルミオン数 ±½ の状態。Callias の指数
    (帽子ごとに 1、全体で 0)は外部。本当のカイラリティの候補は dyon の首の E·B(XI.5、未計算)。
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

namespace CFT.BridgeTwist

open Matrix Complex

/-- Pauli 行列 -/
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
/-- ε = iσ₂(スピンとアイソスピンの一重項) -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
/-- x̂·σ -/
def xs (x0 x1 x2 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (x0 : ℂ) • s1 + (x1 : ℂ) • s2 + (x2 : ℂ) • s3

/-- ε = iσ₂ -/
theorem eps_eq : eps = I • s2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eps, s2]

/-- 【橋 A】ε(x̂·σ)ᵀ = −(x̂·σ)ε(湯川の項 M(fε) = −(Gvh/2)f(x̂·σ)ε の核心) -/
theorem eps_xsT (x0 x1 x2 : ℝ) : eps * (xs x0 x1 x2)ᵀ = -(xs x0 x1 x2 * eps) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eps, xs, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    (try constructor) <;> ring

/-- (x̂·σ)² = |x̂|² -/
theorem xs_sq (x0 x1 x2 : ℝ) :
    xs x0 x1 x2 * xs x0 x1 x2 = ((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [xs, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    (try constructor) <;> ring

/-- 【橋 A】平坦なはりねずみのゲージ場の項:
−(i/2) Σ ε_{akj} x̂_j σ_k ε σ_aᵀ = (x̂·σ)ε(σ·D(fε) の (1 − W)/ρ の項) -/
theorem gauge_singlet (x0 x1 x2 : ℝ) :
    (-I / 2) • ((x2 : ℂ) • (s2 * eps * s1ᵀ) + (x0 : ℂ) • (s3 * eps * s2ᵀ) + (x1 : ℂ) • (s1 * eps * s3ᵀ)
      - (x1 : ℂ) • (s3 * eps * s1ᵀ) - (x0 : ℂ) • (s2 * eps * s3ᵀ) - (x2 : ℂ) • (s1 * eps * s2ᵀ))
      = xs x0 x1 x2 * eps := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eps, xs, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    (try constructor) <;> ring

/-- 【橋 A】極 2:(x̂·σ)ε(i x̂·σ)ᵀ = −iε(|x̂| = 1)。スピン枠とゲージの遷移が一重項の上で打ち消し合う -/
theorem pole_singlet (x0 x1 x2 : ℝ) (h : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 = 1) :
    xs x0 x1 x2 * eps * (I • xs x0 x1 x2)ᵀ = -I • eps := by
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.mul_assoc, eps_xsT, Matrix.mul_neg,
    ← Matrix.mul_assoc, xs_sq, h]
  simp only [Complex.ofReal_one, one_smul, Matrix.one_mul, smul_neg, neg_smul]

/-! ### 共形写像:平坦の係数 (1 − W)/R から曲がった係数 (r′ − W)/r へ -/

/-- χ = (r/R)f の微分(dR/dρ = R/r) -/
theorem chi_deriv (r R f : ℝ → ℝ) (r' f' ρ : ℝ) (hr : HasDerivAt r r' ρ)
    (hR : HasDerivAt R (R ρ / r ρ) ρ) (hf : HasDerivAt f f' ρ) (hr0 : r ρ ≠ 0) (hR0 : R ρ ≠ 0) :
    HasDerivAt (fun x => r x / R x * f x) ((r' - 1) / R ρ * f ρ + r ρ / R ρ * f') ρ := by
  have h := (hr.div hR hR0).mul hf
  convert h using 1
  field_simp <;> ring

/-- 【橋 A】平坦の残差 E_flat = dχ/dR + (1 − W)/R χ + Ω m χ(Ω = r/R、dχ/dR = (dχ/dρ)(r/R))は
曲がった残差 E_curv = f′ + (r′ − W)/r f + m f の (r/R)² 倍 -/
theorem conformal_transfer (r r' R f f' W m : ℝ) (hr0 : r ≠ 0) (hR0 : R ≠ 0) :
    ((r' - 1) / R * f + r / R * f') * (r / R) + (1 - W) / R * (r / R * f) + r / R * m * (r / R * f)
      = (r / R) ^ 2 * (f' + (r' - W) / r * f + m * f) := by
  field_simp <;> ring

/-- 【橋 A】ダンベル(W = r′)では係数 (r′ − W)/r = 0:スピン接続とゲージ場が打ち消し合う -/
theorem twist_cancel (r r' W : ℝ) (hW : W = r') : (r' - W) / r = 0 := by
  rw [hW, sub_self, zero_div]

/-! ### ゼロモード -/

/-- 【橋 A】係数 0 の系 f′ = −i m g、g′ = i m f は g = s·i·f(s = ±1)で f′ = s m f になる -/
theorem system_reduce (m f s : ℝ) (hs : s ^ 2 = 1) :
    -(I * m * ((s : ℂ) * I * f)) = (s : ℂ) * m * f ∧ (s : ℂ) * I * ((s : ℂ) * m * f) = I * m * f := by
  have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  constructor
  · linear_combination (-(s : ℂ) * m * f) * Complex.I_sq
  · linear_combination (I * m * f) * hs'

/-- 【橋 A】ゼロモード f = exp(s·M)(M′ = m、s = ±1)は f′ = s m f -/
theorem zero_mode (M m : ℝ → ℝ) (s ρ : ℝ) (hM : HasDerivAt M (m ρ) ρ) :
    HasDerivAt (fun x => Real.exp (s * M x)) (s * m ρ * Real.exp (s * M ρ)) ρ := by
  have h := (hM.const_mul s).exp
  convert h using 1
  ring

/-- 【橋 A】局在:[a, b](首)で m ≥ m₀ なら |f|² = exp(−2(M(b) − M(a))) ≤ exp(−2m₀(b − a)) -/
theorem localization (M m : ℝ → ℝ) (a b m0 : ℝ) (hab : a ≤ b) (hM : ∀ x, HasDerivAt M (m x) x)
    (hm : ∀ x ∈ Set.Icc a b, m0 ≤ m x) :
    Real.exp (-2 * (M b - M a)) ≤ Real.exp (-2 * (m0 * (b - a))) := by
  apply Real.exp_le_exp.2
  have hmono : MonotoneOn (fun x => M x - m0 * x) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x _ => ((hM x).sub ((hasDerivAt_id' x).const_mul m0)).continuousAt.continuousWithinAt
    · exact fun x _ => ((hM x).sub ((hasDerivAt_id' x).const_mul m0)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hd := ((hM x).sub ((hasDerivAt_id' x).const_mul m0)).deriv
      rw [hd]
      have := hm x ⟨hx.1.le, hx.2.le⟩
      simp only [mul_one]
      linarith
  have := hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  simp only at this
  nlinarith [this]

end CFT.BridgeTwist
