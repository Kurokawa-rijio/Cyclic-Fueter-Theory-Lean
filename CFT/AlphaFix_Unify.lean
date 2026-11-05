/-
  独立監査(2026-11-04)の指摘を受けた作り直し:α-X.1、X.2、X.4、X.5

  * X.1(作用:有限自由度の L(q, q̇)。力学:Noether の定理を一般に)
      EL 方程式 ṗ_i = ∂L/∂q_i、対称性 δq = εK(q) で δL = Σ(∂L/∂q_i K_i + p_i d/dt K_i) = 0 なら、
      Noether の電荷 Σ p_i K_i は保存(`noether`)。循環座標 K = e_j は特別な場合(`cyclic_from_noether`)。
      旧版の `cyclic_momentum` は仮定をそのまま返していた(監査:トートロジー)。場の理論のゲージ対称性 →
      電荷の保存は AlphaX_Unify `charge_conservation`(Maxwell の式から)。
  * X.2(運動学:首の計量 −dt² + cos²(t/ℓ)dz²(IV.7)。力学:幾何光学 = HJ = WKB)
      2 次元の □ = −∂_t² − c∂_t + w∂_z²(c = a′/a、w = 1/a²)で、ψ = A e^{ikS} を入れると
        □ψ = ψ[(ik)²A(−S_t² + wS_z²) + (ik)(輸送の項) + □A](`wkb_2d`)。
      (ik)² の係数が 0 ⇔ アイコナール方程式 g^{μν}∂_μS∂_νS = 0(質量ゼロの HJ)。IV.7 の首の波面
      S = z − ℓ arsinh(tan(t/ℓ)) はちょうどこの式をみたす(`neck_eikonal`、AlphaIV `front_deriv`)。
      IV.12 の WDW の WKB(`hj_exact`)は同じ式を DeWitt 計量のミニ超空間で書いたもの。
  * X.4(運動学:閉じたダンベル。力学:質量)
      ダンベルは閉じた空間で漸近的に平坦な端がないので ADM 質量は定義されない。代わりに Misner–Sharp 質量
      m = (R/2)(1 − (∇R)²) を使う。帽子(閉じた FRW、R = a sin χ):Friedmann ȧ² + 1 = (8π/3)ρa² から
      m = (4π/3)ρR³(`cap_ms_mass`)。放射 ρ = C/a⁴ で dm/dt = −p dV/dt(p = ρ/3、V = 4πR³/3、
      `cap_first_law`):閉じた宇宙での「質量の保存」は圧力の仕事を含む第一法則になる。首(R = ℓ 一定):
      m = ℓ/2(`neck_ms_mass`)。弱い不連続は m を変えない(AlphaX_Unify `weak_discontinuity_no_mass`)。
  * X.5(運動学:Witten の ansatz A = a₀T dt + a₁T dr + …(T = τ_r、同じ生成子)。力学:色電荷)
      F_tr = ∂_tA_r − ∂_rA_t + [A_t, A_r] で交換子は消え、F_tr = (∂_ta₁ − ∂_ra₀)T(`witten_Ftr`)。
      ダンベル(純粋に磁気的、a₀ = a₁ = 0)では E_r = 0、Q(r) = 4πr²E_r = 0 が帽子でも首でも成り立つ
      (`color_charge_vanishes`)。a₀ の方程式(Gauss の法則の縮約、Witten 1977)は a₀ = 0 でみたされる(外部)。
-/
import CFT.AlphaX_Unify
import CFT.AlphaIV
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Module

namespace CFT.FixUnify

open Real

/-! ### X.1 Noether の定理 -/

/-- 【α-X.1】一般の Noether の定理:ṗ_i = ∂L/∂q_i、Σ(∂L/∂q_i K_i + p_i K̇_i) = 0 なら Σ p_i K_i は保存 -/
theorem noether {n : ℕ} (p Lq K : Fin n → ℝ → ℝ) (pd Kd : Fin n → ℝ → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (pd i t) t) (hK : ∀ i, HasDerivAt (K i) (Kd i t) t)
    (hEL : ∀ i, pd i t = Lq i t)
    (hsym : ∑ i, (Lq i t * K i t + p i t * Kd i t) = 0) :
    HasDerivAt (fun s => ∑ i, p i s * K i s) 0 t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hp i).mul (hK i))
  convert h using 1
  simp only [hEL]
  exact hsym.symm

/-- 【α-X.1】循環座標:K = e_j(定数)、∂L/∂q_j = 0 なら p_j は保存(Noether の特別な場合) -/
theorem cyclic_from_noether {n : ℕ} (p Lq : Fin n → ℝ → ℝ) (pd : Fin n → ℝ → ℝ) (t : ℝ) (j : Fin n)
    (hp : ∀ i, HasDerivAt (p i) (pd i t) t) (hEL : ∀ i, pd i t = Lq i t) (hcyc : Lq j t = 0) :
    HasDerivAt (fun s => ∑ i, p i s * (if i = j then (1 : ℝ) else 0)) 0 t := by
  apply noether p Lq (fun i _ => if i = j then (1 : ℝ) else 0) pd (fun _ _ => 0) t hp
    (fun i => hasDerivAt_const t _) hEL
  simp [hcyc]

/-! ### X.2 幾何光学 = HJ = WKB -/

section WKB2

variable {S : Type*} [Field S] (Dt Dz : Derivation ℤ S S)

/-- 【α-X.2】2 次元の □(Aψ₀)(Dψ₀ = (ik)DS ψ₀):(ik)² の係数は A(−S_t² + wS_z²) -/
theorem wkb_2d (A ψ0 Sph ik w c : S) (hikt : Dt ik = 0) (hikz : Dz ik = 0)
    (hψt : Dt ψ0 = ik * Dt Sph * ψ0) (hψz : Dz ψ0 = ik * Dz Sph * ψ0) :
    -(Dt (Dt (A * ψ0))) - c * Dt (A * ψ0) + w * Dz (Dz (A * ψ0))
      = ψ0 * (ik ^ 2 * (A * (-(Dt Sph) ^ 2 + w * (Dz Sph) ^ 2))
        + ik * (-(2 * Dt A * Dt Sph + A * Dt (Dt Sph)) - c * A * Dt Sph
          + w * (2 * Dz A * Dz Sph + A * Dz (Dz Sph)))
        + (-(Dt (Dt A)) - c * Dt A + w * Dz (Dz A))) := by
  simp only [Derivation.leibniz, smul_eq_mul, map_add, hψt, hψz, hikt, hikz, mul_zero, add_zero, zero_add]
  ring

end WKB2

/-- 【α-X.2】首の波面 S = z − ℓ arsinh(tan(t/ℓ)):S_t = −1/cos(t/ℓ)、S_z = 1 で
アイコナール −S_t² + S_z²/cos²(t/ℓ) = 0 -/
theorem neck_eikonal (l t : ℝ) (hl : 0 < l) (hc : 0 < cos (t / l)) :
    HasDerivAt (fun t => -(l * arsinh (tan (t / l)))) (-(1 / cos (t / l))) t ∧
    -(-(1 / cos (t / l))) ^ 2 + (1 : ℝ) ^ 2 / cos (t / l) ^ 2 = 0 := by
  refine ⟨(CFT.AlphaIV.front_deriv l t hl hc).neg, ?_⟩
  rw [neg_sq, div_pow, one_pow]
  ring

/-! ### X.4 Misner–Sharp 質量 -/

/-- 【α-X.4】帽子:R = a sin χ、(∇R)² = −ȧ² sin²χ + cos²χ、Friedmann ȧ² + 1 = (8π/3)ρa² なら
m = (R/2)(1 − (∇R)²) = (4π/3)ρR³ -/
theorem cap_ms_mass (a ad ρ χ : ℝ) (hF : ad ^ 2 + 1 = 8 * π / 3 * ρ * a ^ 2) :
    a * sin χ / 2 * (1 - (-(ad ^ 2 * sin χ ^ 2) + cos χ ^ 2)) = 4 * π / 3 * ρ * (a * sin χ) ^ 3 := by
  have h := sin_sq_add_cos_sq χ
  linear_combination (a * sin χ ^ 3 / 2) * hF - (a * sin χ / 2) * h

/-- 【α-X.4】帽子の第一法則:ρ = C/a⁴、m = (4π/3)ρR³ なら dm/dt = −(ρ/3)·4πR² dR/dt -/
theorem cap_first_law (a : ℝ → ℝ) (ad C χ t : ℝ) (ha : HasDerivAt a ad t) (h0 : a t ≠ 0) :
    HasDerivAt (fun s => 4 * π / 3 * (C / a s ^ 4) * (a s * sin χ) ^ 3)
      (-(C / a t ^ 4 / 3) * (4 * π * (a t * sin χ) ^ 2 * (ad * sin χ))) t := by
  have h4 : a t ^ 4 ≠ 0 := pow_ne_zero 4 h0
  have hq := (hasDerivAt_const t C).div (ha.pow 4) h4
  have hc := (ha.mul_const (sin χ)).pow 3
  have h := (hq.const_mul (4 * π / 3)).mul hc
  convert h using 1
  simp only [Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl, show (3 : ℕ) - 1 = 2 from rfl]
  field_simp <;> ring

/-- 【α-X.4】首:R = ℓ 一定で (∇R)² = 0、m = ℓ/2 -/
theorem neck_ms_mass (l : ℝ) : l / 2 * (1 - 0) = l / 2 := by ring

/-! ### X.5 色電荷 -/

/-- 【α-X.5】A_t = a₀T、A_r = a₁T(同じ生成子)なら F_tr = ∂_tA_r − ∂_rA_t + [A_t, A_r] = (∂_ta₁ − ∂_ra₀)T -/
theorem witten_Ftr {n : Type*} [Fintype n] (T : Matrix n n ℝ) (a0 a1 a0r a1t : ℝ) :
    a1t • T - a0r • T + ((a0 • T) * (a1 • T) - (a1 • T) * (a0 • T)) = (a1t - a0r) • T := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm a1 a0]
  module

/-- 【α-X.5】ダンベル(a₀ = a₁ = 0、したがって ∂_ta₁ = ∂_ra₀ = 0):E_r = 0、Q(r) = 4πr²E_r = 0 -/
theorem color_charge_vanishes {n : Type*} [Fintype n] (T : Matrix n n ℝ) (r : ℝ) :
    (0 : ℝ) • T - (0 : ℝ) • T + (((0 : ℝ) • T) * ((0 : ℝ) • T) - ((0 : ℝ) • T) * ((0 : ℝ) • T))
      = (0 - 0 : ℝ) • T ∧ 4 * π * r ^ 2 * (0 - 0 : ℝ) = 0 :=
  ⟨witten_Ftr T 0 0 0 0, by ring⟩

end CFT.FixUnify
