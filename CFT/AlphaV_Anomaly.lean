/-
  α-V.7 (Z31) の補強:トレースアノマリーと保存則から、閉じた FRW の量子応力のエネルギー密度を決める

  外部の入力(確立した定理。適用条件)
  (A1) トレースアノマリー:質量ゼロの共形不変な自由場(スカラー、Weyl/Dirac スピノル、Maxwell 場。
       背景のゲージ場に結合しない場)について
         ⟨T^μ_μ⟩_ren = (ħ/16π²)(c_E C² − a_E E₄ + b □R)
       (Capper–Duff 1974、Deser–Duff–Isham 1976、Duff 1977、Birrell–Davies §6.3)。
       a_E は場の種類だけで決まり、自由場では a_E > 0(1 スカラー、1 Weyl、1 ベクトルあたり 1/360、11/720、62/360)。
       b は R² の有限な対抗項で動かせる(繰り込みの方式。Brown–Ottewill 1986)。ここでは b = 0 を選ぶ
       (重力の作用に R² の項を入れない方式)。b ≠ 0 は ⁽¹⁾H の項を加えることに相当する。
  (A2) 繰り込まれた応力は保存する(Wald の公理)。状態は FRW の対称性をもつ(共形真空など)。
  (A3) FRW は共形平坦(C = 0)。したがって E₄ = −2(R_μνR^μν − R²/3) = 2 tr ⁽³⁾H = 24uX(AlphaV_FRW)。
  背景の SU(2) 場の量子揺らぎ自身は (A1) の対象外(β 関数の項 ∝ F² が跡に加わる)。それは別の問題として残す。

  ここで Lean で示すこと(すべて実関数で)
  * β の決定:⟨T⟩ ⊃ β ⁽³⁾H、跡 12βuX = −(ħa_E/16π²)·24uX ⇒ β = −ħa_E/(8π²)(`beta_from_anomaly`)。
    したがって ρ_anom = −β·3X² = (3ħa_E/8π²)X²、κ₂ = 3a_E/(8π²) > 0(`kappa2_pos`)。
  * FRW での決定:等方な応力では、保存則 ρ̇ = −3(ȧ/a)(ρ + p) と跡 tr = −ρ + 3p から
    ρ̇ = −(ȧ/a)(4ρ + tr)。ρ_q = κ₁/a⁴ + (3ħa_E/8π²)X² はこれをみたし(`rho_q_conserved`)、
    同じ跡をもつ解はこれと κ/a⁴ の差しかない(`rho_unique`:a⁴(ρ − ρ_q) は一定)。
    つまり ⟨T⟩ の形(状態の項 + β⁽³⁾H)は仮定ではなく、(A1)〜(A3) から従う。κ₁ は状態(共形真空)の定数。
-/
import CFT.AlphaV_FRW

namespace CFT.Anomaly

open Real Set CFT.FRW

noncomputable section

/-- 【α-V.7】β の決定:β · 12uX = −(ħa_E/16π²) · 2 · 12uX(uX ≠ 0)⇒ β = −ħa_E/(8π²) -/
theorem beta_from_anomaly (hb aE β u X : ℝ) (huX : u * X ≠ 0)
    (h : β * (12 * u * X) = -(hb * aE / (16 * π ^ 2)) * (2 * (12 * u * X))) :
    β = -(hb * aE / (8 * π ^ 2)) := by
  have h12 : 12 * u * X ≠ 0 := by
    rw [mul_assoc]; exact mul_ne_zero (by norm_num) huX
  refine mul_right_cancel₀ h12 (h.trans ?_)
  ring

/-- 【α-V.7】ρ_anom = −β·⁽³⁾H⁰₀ = (3ħa_E/8π²) X²、a_E > 0 なら κ₂ = 3a_E/(8π²) > 0 -/
theorem kappa2_pos (hb aE X : ℝ) (hhb : 0 < hb) (haE : 0 < aE) :
    -(-(hb * aE / (8 * π ^ 2))) * (3 * X ^ 2) = hb * (3 * aE / (8 * π ^ 2)) * X ^ 2 ∧
    0 < 3 * aE / (8 * π ^ 2) := by
  constructor
  · ring
  · have := Real.pi_pos; positivity

/-- 量子応力のエネルギー密度の候補 ρ_q = κ₁/a⁴ + k X²(k = 3ħa_E/8π²) -/
def rhoq (κ1 k : ℝ) (a ad : ℝ → ℝ) (τ : ℝ) : ℝ :=
  κ1 * ((a τ * a τ) * (a τ * a τ))⁻¹ + k * (Xf a ad τ * Xf a ad τ)

/-- 【α-V.7】ρ_q は保存則 ρ̇ = −(ȧ/a)(4ρ + tr) をみたす。跡は tr = −4k u X(= −(ħa_E/16π²)·24uX) -/
theorem rho_q_conserved (κ1 k : ℝ) (a ad : ℝ → ℝ) (add t : ℝ) (ha : HasDerivAt a (ad t) t)
    (had : HasDerivAt ad add t) (ha0 : a t ≠ 0) :
    HasDerivAt (rhoq κ1 k a ad)
      (-(ad t / a t) * (4 * rhoq κ1 k a ad t + (-4 * k * (add / a t) * Xf a ad t))) t := by
  have haa : a t * a t ≠ 0 := mul_ne_zero ha0 ha0
  have h4 : (a t * a t) * (a t * a t) ≠ 0 := mul_ne_zero haa haa
  have hX : HasDerivAt (Xf a ad)
      (((add * ad t + ad t * add) * (a t * a t) - (ad t * ad t + 1) * (ad t * a t + a t * ad t))
        / (a t * a t) ^ 2) t :=
    ((had.mul had).add_const 1).div (ha.mul ha) haa
  have h1 := (((ha.mul ha).mul (ha.mul ha)).inv h4).const_mul κ1
  have h2 := (hX.mul hX).const_mul k
  refine (h1.add h2).congr_deriv ?_
  simp only [rhoq, Xf]
  field_simp <;> ring

/-- 【α-V.7】一意性:同じ跡 tr をもち保存則をみたす等方な ρ は、ρ_q と κ/a⁴ の差しかない
(区間 [t₀, t₁] の上で a⁴(ρ − ρ_q) は一定) -/
theorem rho_unique (κ1 k : ℝ) (a ad add ρ tr : ℝ → ℝ) (t0 t1 : ℝ)
    (ha : ∀ t ∈ Icc t0 t1, HasDerivAt a (ad t) t) (had : ∀ t ∈ Icc t0 t1, HasDerivAt ad (add t) t)
    (ha0 : ∀ t ∈ Icc t0 t1, a t ≠ 0)
    (hρ : ∀ t ∈ Icc t0 t1, HasDerivAt ρ (-(ad t / a t) * (4 * ρ t + tr t)) t)
    (htr : ∀ t ∈ Icc t0 t1, tr t = -4 * k * (add t / a t) * Xf a ad t) :
    ∀ t ∈ Icc t0 t1, a t ^ 4 * (ρ t - rhoq κ1 k a ad t) = a t0 ^ 4 * (ρ t0 - rhoq κ1 k a ad t0) := by
  have hd : ∀ t ∈ Icc t0 t1, HasDerivAt (fun τ => a τ ^ 4 * (ρ τ - rhoq κ1 k a ad τ)) 0 t := by
    intro t ht
    have hq := rho_q_conserved κ1 k a ad (add t) t (ha t ht) (had t ht) (ha0 t ht)
    have h := ((ha t ht).pow 4).mul ((hρ t ht).sub hq)
    refine h.congr_deriv ?_
    rw [htr t ht]
    have h0 := ha0 t ht
    simp only [Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl]
    field_simp <;> ring
  have hcont : ContinuousOn (fun τ => a τ ^ 4 * (ρ τ - rhoq κ1 k a ad τ)) (Icc t0 t1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hder : ∀ t ∈ Ico t0 t1,
      HasDerivWithinAt (fun τ => a τ ^ 4 * (ρ τ - rhoq κ1 k a ad τ)) 0 (Ici t) t :=
    fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hcont hder

end

end CFT.Anomaly
