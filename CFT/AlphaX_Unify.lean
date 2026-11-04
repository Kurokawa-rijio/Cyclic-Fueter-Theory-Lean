/-
  α-X:統一と整合性(X.1〜X.6)

  * X.1 Noether の定理(縮約した作用、有限自由度)
      - 時間並進:L が時間に陽によらなければ E = q̇ ∂L/∂q̇ − L は Euler–Lagrange の解で保存(`energy_conserved`)。
        L(q(t), q̇(t)) の微分の連鎖律は入力(多変数の連鎖律、標準)。
      - 循環座標:∂L/∂q = 0 なら p = ∂L/∂q̇ は保存(`cyclic_momentum`)。
      - 回転:中心力 m q̈ = f(t) q なら角運動量 q × m q̇ は保存(`angular_momentum`)。
      - ゲージ → 電荷:∂_μF^{μν} = j^ν、F 反対称なら ∂_ν j^ν = 0(`charge_conservation`)。
  * X.2 幾何光学 = Hamilton–Jacobi = WKB:ψ = A e^{iS/ħ}(∂_μ e^{iS/ħ} = (i/ħ)∂_μS e^{iS/ħ})で
      ∂_μ∂_μ(Aψ₀) = ψ₀[(i/ħ)²A(∂_μS)² + (i/ħ)(2∂_μA∂_μS + A∂_μ∂_μS) + ∂_μ∂_μA](`wkb_orders`)。
      η で足すと、1/ħ² の次数は Hamilton–Jacobi(IV.12)、1/ħ の次数は振幅の輸送、m = 0 では
      光線(ヌルの特性曲線、IV.7 の波面)が幾何光学。
  * X.3 ゲージ場 = 接続、力 = 曲率:U(1) では A ↦ A + dλ で F は不変(`abelian_gauge_invariance`)。
      非可換では F ↦ gFg⁻¹(GaugeCovariance `curvature_covariant`)。重力ではスピン接続(Z16、AlphaCompleteB)、
      運動量空間では Wigner・Berry・Fueter の接続(V.1、AlphaV_Wigner:A_B = V A_F V⁻¹ + V dV⁻¹)。
  * X.4 質量:Misner–Sharp 質量 m = (r/2)(1 + 2r_u r_v/Ω) は r、r_u、r_v、Ω だけで決まるので、
      弱い不連続(2 階の微分だけが跳ぶ)の上で [m] = 0(`weak_discontinuity_no_mass`):[W_u] は質量を運ばない。
      ダンベルは閉じた空間なので ADM 質量(空間的な無限遠での極限)は定義されない(部分)。
  * X.5 色電荷:Witten 型の磁気的な ansatz(a₀ = a₁ = 0)では電場の動径成分 E_r^a = 0 で、接合面の両側で
      Q^a = ∮ E_r^a = 0(`color_charge_zero`)。ansatz が無矛盾な切り詰めであることは外部(Witten 1977)。
  * X.6 非空性:主要な定理の仮定をみたす具体例(`nonempty_*`)。帽子の ODE(a = ℓ cos η)、弦理論の
      アトラクター(p = q = 1)、首の厳密解、Wigner 回転(Λ = 1)、焦点の定理の仮定。
      RealLine の橋渡しを使う定理(III.1 など)の非空性は、橋渡しの課題とともに残す(部分)。
-/
import CFT.AlphaVIII_Z44Cap
import CFT.AlphaVIII_StringAttractor
import CFT.AlphaIX_JT
import CFT.AlphaV_Wigner
import CFT.GaugeCovariance

namespace CFT.Unify

open Real Set

/-! ### X.1 Noether -/

/-- 【α-X.1】時間並進:E = v ∂L/∂v − L は保存(EL:d/dt ∂L/∂v = ∂L/∂q、連鎖律 dL/dt = L_q v + L_v a) -/
theorem energy_conserved (Lt v a Lq Lv : ℝ → ℝ) (t : ℝ)
    (hv : HasDerivAt v (a t) t) (hL : HasDerivAt Lt (Lq t * v t + Lv t * a t) t)
    (hEL : HasDerivAt Lv (Lq t) t) :
    HasDerivAt (fun s => v s * Lv s - Lt s) 0 t := by
  have h := (hv.mul hEL).sub hL
  convert h using 1; ring

/-- 【α-X.1】循環座標:∂L/∂q = 0 なら p = ∂L/∂v は保存 -/
theorem cyclic_momentum (Lv : ℝ → ℝ) (t : ℝ) (hEL : HasDerivAt Lv 0 t) : HasDerivAt Lv 0 t := hEL

/-- 【α-X.1】中心力 m q̈ = f q なら J_z = m(q₀v₁ − q₁v₀) は保存(他の成分も同じ) -/
theorem angular_momentum (m : ℝ) (q0 q1 v0 v1 a0 a1 f : ℝ → ℝ) (t : ℝ)
    (h0 : HasDerivAt q0 (v0 t) t) (h1 : HasDerivAt q1 (v1 t) t)
    (g0 : HasDerivAt v0 (a0 t) t) (g1 : HasDerivAt v1 (a1 t) t)
    (hf0 : m * a0 t = f t * q0 t) (hf1 : m * a1 t = f t * q1 t) :
    HasDerivAt (fun s => m * (q0 s * v1 s - q1 s * v0 s)) 0 t := by
  have h := ((h0.mul g1).sub (h1.mul g0)).const_mul m
  convert h using 1
  linear_combination q1 t * hf0 - q0 t * hf1

section Charge

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- 【α-X.1】電荷の保存:∂_μF^{μν} = j^ν、F^{μν} = −F^{νμ}、∂ が可換なら ∂_ν j^ν = 0 -/
theorem charge_conservation (F : Fin 4 → Fin 4 → S) (j : Fin 4 → S)
    (hF : ∀ μ ν, F μ ν = -F ν μ) (hcomm : ∀ i k f, d i (d k f) = d k (d i f))
    (hM : ∀ ν, ∑ μ, d μ (F μ ν) = j ν) : ∑ ν, d ν (j ν) = 0 := by
  have e : ∑ ν, d ν (j ν) = ∑ ν, ∑ μ, d ν (d μ (F μ ν)) := by
    simp only [← hM, map_sum]
  have e2 : ∑ ν, ∑ μ, d ν (d μ (F μ ν)) = -∑ ν, ∑ μ, d ν (d μ (F μ ν)) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hcomm μ ν, hF ν μ, map_neg, map_neg, neg_neg]
  have h2 : (2 : S) * ∑ ν, ∑ μ, d ν (d μ (F μ ν)) = 0 := by linear_combination e2
  rw [e]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

end Charge

/-! ### X.2 WKB の次数 -/

section WKB

variable {S : Type*} [Field S] (D : Derivation ℤ S S)

/-- 【α-X.2】D(Dψ₀) = (ik)DS ψ₀ のとき D²(Aψ₀) = ψ₀[(ik)²A(DS)² + (ik)(2DA·DS + A D²S) + D²A](k = 1/ħ、i² = −1) -/
theorem wkb_orders (A ψ0 Sph ik : S) (hik : D ik = 0) (hψ : D ψ0 = ik * D Sph * ψ0) :
    D (D (A * ψ0)) = ψ0 * (ik ^ 2 * A * (D Sph) ^ 2 + ik * (2 * D A * D Sph + A * D (D Sph)) + D (D A)) := by
  simp only [Derivation.leibniz, smul_eq_mul, map_add, hψ, hik, mul_zero, add_zero, zero_add]
  ring

end WKB

/-! ### X.3 ゲージ = 接続 -/

section Gauge

variable {S : Type*} [Field S] (d : Fin 4 → Derivation ℤ S S)

/-- 【α-X.3】U(1):A ↦ A + dλ で F_{μν} = ∂_μA_ν − ∂_νA_μ は不変 -/
theorem abelian_gauge_invariance (A : Fin 4 → S) (lam : S) (hcomm : ∀ i k f, d i (d k f) = d k (d i f))
    (μ ν : Fin 4) :
    d μ (A ν + d ν lam) - d ν (A μ + d μ lam) = d μ (A ν) - d ν (A μ) := by
  rw [map_add, map_add, hcomm μ ν lam]; ring

end Gauge

/-! ### X.4 質量 -/

/-- Misner–Sharp 質量 m = (r/2)(1 + 2r_u r_v/Ω) -/
noncomputable def msMass (r ru rv Om : ℝ) : ℝ := r / 2 * (1 + 2 * ru * rv / Om)

/-- 【α-X.4】弱い不連続:r、r_u、r_v、Ω が両側で等しければ [m] = 0(2 階の微分の跳びは質量を運ばない) -/
theorem weak_discontinuity_no_mass (r ru rv Om r' ru' rv' Om' : ℝ)
    (h1 : r = r') (h2 : ru = ru') (h3 : rv = rv') (h4 : Om = Om') :
    msMass r ru rv Om - msMass r' ru' rv' Om' = 0 := by
  subst h1 h2 h3 h4; ring

/-! ### X.5 色電荷 -/

/-- 【α-X.5】a₀ = a₁ = 0 の ansatz:E_r^a = ∂_t A_r^a − ∂_r A_t^a + … = 0 なので Q^a = 4πr²E_r^a = 0(両側で) -/
theorem color_charge_zero (r : ℝ) (Er : Fin 3 → ℝ) (hE : ∀ a, Er a = 0) :
    ∀ a, 4 * π * r ^ 2 * Er a = 0 := by
  intro a; rw [hE a, mul_zero]

/-! ### X.6 非空性 -/

/-- 帽子の ODE の仮定をみたす例:a = ℓ cos η -/
theorem nonempty_cap (l : ℝ) :
    (∀ η, HasDerivAt (fun x => l * cos x) (l * -sin η) η) ∧
    (∀ η, HasDerivAt (fun x => l * -sin x) (-(l * cos η)) η) ∧ l * cos 0 = l ∧ l * -sin 0 = 0 := by
  refine ⟨fun η => (hasDerivAt_cos η).const_mul l, fun η => ?_, by simp, by simp⟩
  have := ((hasDerivAt_sin η).neg).const_mul l
  convert this using 1; ring

/-- 弦理論のアトラクターの仮定をみたす例:p = q = 1、v₁ = v₂ = 2、e = 1、w = 1 -/
theorem nonempty_attractor :
    (1 : ℝ) - 1 * 1 * 2 / 2 = 0 ∧ (1 / 4 : ℝ) * (2 - 1 * (2 * 1 ^ 2 * 2 / 2 ^ 2 + 2 * 1 ^ 2 / 2)) = 0 ∧
    (1 / 4 : ℝ) * (-2 + 1 * (2 * 1 ^ 2 / 2 + 2 * 1 ^ 2 * 2 / 2 ^ 2)) = 0 ∧
    (1 / 4 : ℝ) * (2 * 1 ^ 2 * 2 / 2 - 2 * 1 ^ 2 * 2 / 2) = 0 := by norm_num

/-- 首の厳密解の仮定をみたす例:Φ = ℓ²、R₂ = −2/ℓ² -/
theorem nonempty_neck (l : ℝ) (hl : l ≠ 0) :
    CFT.JT.U l (l ^ 2) = 0 ∧ -2 / l ^ 2 + 2 * l ^ 2 / (l ^ 2) ^ 2 = 0 := by
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  constructor
  · simp only [CFT.JT.U]; field_simp
  · field_simp <;> ring

/-- Wigner 回転の仮定をみたす例:Λ = L₁ = L₂ = L₂⁻¹ = 1 -/
theorem nonempty_wigner :
    Matrix.conjTranspose (1 : CFT.Wigner.M2) = 1 ∧ (1 : CFT.Wigner.M2) * 1 = 1 ∧
    (1 : CFT.Wigner.M2) * ((1 : CFT.Wigner.M2) * 1) * Matrix.conjTranspose (1 : CFT.Wigner.M2) = 1 * 1 := by
  simp

/-- 焦点の定理の仮定をみたす例:θ(s) = 2/(s − 2) は [0, 1] で θ < 0、θ′ = −θ²/2 -/
theorem nonempty_focusing (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun x => 2 / (x - 2)) (-(2 / (s - 2)) ^ 2 / 2) s ∧ 2 / (s - 2) < 0 := by
  have hs2 : s - 2 ≠ 0 := by linarith [hs.2]
  constructor
  · have h := ((hasDerivAt_id' s).sub_const 2).inv hs2 |>.const_mul 2
    convert h using 1 <;> first | (funext x; ring) | (field_simp <;> ring)
  · apply div_neg_of_pos_of_neg (by norm_num); linarith [hs.2]

end CFT.Unify
