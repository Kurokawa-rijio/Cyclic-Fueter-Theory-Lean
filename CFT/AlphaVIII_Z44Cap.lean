/-
  α-VIII.7(Z44):帽子の厳密な崩壊で Killing スピノルの不存在を示す(IV.5 の類を使わない版)

  旧版 z44_full は IV.5 の類 (rW)² ≥ κ を使ったが、その類はダンベルの首(W = 0)を含まない
  (2026-10-21 の訂正)。ここでは帽子(閉じた放射 FRW、共形時間 η)の厳密な崩壊を使う。
  帽子の領域は中心の世界線が波面に着く η = π/2 まで厳密な FRW(AlphaS5 `center_before_front`)なので、
  ダンベル全体に Killing スピノルがあれば、この領域に制限したものも Killing スピノル。

  入力(α の命題として示した事実)
  * 帽子の場の方程式(tt と θθ 成分、AlphaS5 `cap_00`、`cap_22`)と時間対称な初期値から
    中心に沿って a″ = −a、a(0) = ℓ、a′(0) = 0(IV.5、完)。ここでは実の ODE として受け取り、
    解が a = ℓ cos η だけであることを示す(`cap_unique`)。
  * 曲率の不変量(Kretschmann)K = 24ℓ⁴/a⁸(AlphaS5_Curvature `kret_cap`)。一様なので χ によらない。
  外部の事実(二つ)
  * Killing スピノル ε があれば K^μ = ε̄γ^με は Killing ベクトルで、正規直交枠の時間成分は ε†ε > 0
    (Tod 1983、Gauntlett–Gutowski ほか)。共形時間の成分は K^η = ε†ε / a。
  * Killing ベクトルは曲率から作ったスカラーを保つ:K^η ∂_η K + K^χ ∂_χ K = 0(L_K g = 0 の帰結)。

  Lean で示すこと
  * cap_unique:a″ = −a、a(0) = ℓ、a′(0) = 0 の解は a = ℓ cos η だけ(エネルギーの方法)。
  * kret_deriv_ne:0 < η < π/2 で ∂_η(24ℓ⁴/(ℓ cos η)⁸) ≠ 0(曲率は単調に増える)。
  * no_killing_spinor_cap:上の二つの外部の事実のもとで、帽子の領域に Killing スピノルはない。
    旧版と違い、喉の対称性・IV.5 の類・`* 0` の形の仮定を使わない。
-/
import CFT.AlphaVIII_Z44
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace CFT.Z44Cap

open Real Set

/-- 【α-VIII.7】帽子の ODE の解は一つ:a″ = −a、a(0) = ℓ、a′(0) = 0 ⇒ a = ℓ cos η -/
theorem cap_unique (l : ℝ) (a ad : ℝ → ℝ) (ha : ∀ η, HasDerivAt a (ad η) η)
    (had : ∀ η, HasDerivAt ad (-a η) η) (h0 : a 0 = l) (hd0 : ad 0 = 0) :
    ∀ η, a η = l * cos η := by
  let E : ℝ → ℝ := fun t => (a t - l * cos t) ^ 2 + (ad t + l * sin t) ^ 2
  have hE : ∀ t, HasDerivAt E 0 t := by
    intro t
    have h1 := ((ha t).sub ((hasDerivAt_cos t).const_mul l)).pow 2
    have h2 := ((had t).add ((hasDerivAt_sin t).const_mul l)).pow 2
    show HasDerivAt (fun t => (a t - l * cos t) ^ 2 + (ad t + l * sin t) ^ 2) 0 t
    convert h1.add h2 using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  have hconst : ∀ t, E t = E 0 := by
    intro t
    exact is_const_of_deriv_eq_zero (fun x => (hE x).differentiableAt)
      (fun x => (hE x).deriv) t 0
  have hE0 : E 0 = 0 := by simp [E, h0, hd0]
  intro η
  have h := hconst η
  rw [hE0] at h
  have h1 : (a η - l * cos η) ^ 2 = 0 := by
    have := sq_nonneg (ad η + l * sin η)
    have := sq_nonneg (a η - l * cos η)
    simp only [E] at h
    linarith
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  linarith

/-- 曲率の不変量 K(η) = 24ℓ⁴/(ℓ cos η)⁸ の η 微分 -/
theorem kret_hasDeriv (l η : ℝ) (hc : l * cos η ≠ 0) :
    HasDerivAt (fun s => 24 * l ^ 4 * ((l * cos s) ^ 8)⁻¹)
      (24 * l ^ 4 * (-(8 * (l * cos η) ^ 7 * (l * -sin η)) / ((l * cos η) ^ 8) ^ 2)) η := by
  have hg : HasDerivAt (fun s => (l * cos s) ^ 8) (8 * (l * cos η) ^ 7 * (l * -sin η)) η := by
    have := ((hasDerivAt_cos η).const_mul l).pow 8
    convert this using 1
  exact (hg.inv (pow_ne_zero 8 hc)).const_mul (24 * l ^ 4)

/-- 【α-VIII.7】0 < η < π/2、ℓ > 0 で ∂_η K ≠ 0(帽子の曲率は単調に増え、時間によらない形にならない) -/
theorem kret_deriv_ne (l η : ℝ) (hl : 0 < l) (h1 : 0 < η) (h2 : η < π / 2) :
    24 * l ^ 4 * (-(8 * (l * cos η) ^ 7 * (l * -sin η)) / ((l * cos η) ^ 8) ^ 2) ≠ 0 := by
  have hc : 0 < cos η := cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have hs : 0 < sin η := sin_pos_of_pos_of_lt_pi h1 (by linarith [pi_pos])
  have hlc : 0 < l * cos η := mul_pos hl hc
  have hnum : 0 < 8 * (l * cos η) ^ 7 * (l * sin η) := by positivity
  have hden : 0 < ((l * cos η) ^ 8) ^ 2 := by positivity
  have : 0 < 24 * l ^ 4 * (8 * (l * cos η) ^ 7 * (l * sin η) / ((l * cos η) ^ 8) ^ 2) := by positivity
  have e : 24 * l ^ 4 * (-(8 * (l * cos η) ^ 7 * (l * -sin η)) / ((l * cos η) ^ 8) ^ 2)
      = 24 * l ^ 4 * (8 * (l * cos η) ^ 7 * (l * sin η) / ((l * cos η) ^ 8) ^ 2) := by
    ring
  rw [e]; exact this.ne'

/-- 【α-VIII.7】帽子に Killing スピノルはない。
  入力:帽子の ODE(IV.5)、曲率の不変量 K(η, χ) = 24ℓ⁴/a(η)⁸(`kret_cap`)、
  外部の事実:K^η = ε†ε/a(Killing スピノルの双線形)、K^η ∂_η K + K^χ ∂_χ K = 0(Killing ベクトルはスカラーを保つ) -/
theorem no_killing_spinor_cap (l : ℝ) (hl : 0 < l) (a ad : ℝ → ℝ) (ha : ∀ η, HasDerivAt a (ad η) η)
    (had : ∀ η, HasDerivAt ad (-a η) η) (h0 : a 0 = l) (hd0 : ad 0 = 0)
    (Kr : ℝ → ℝ → ℝ) (hKr : ∀ η χ, Kr η χ = 24 * l ^ 4 * ((a η) ^ 8)⁻¹)
    (Kη Kχ : ℝ → ℝ → ℝ) (ε : ℝ → ℝ → Fin 4 → ℝ × ℝ) (hε : ∀ η χ, ε η χ ≠ 0)
    (hKη : ∀ η χ, Kη η χ = (∑ i, ((ε η χ i).1 ^ 2 + (ε η χ i).2 ^ 2)) / a η)
    (dKη dKχ : ℝ → ℝ → ℝ)
    (hdη : ∀ η χ, HasDerivAt (fun s => Kr s χ) (dKη η χ) η)
    (hdχ : ∀ η χ, HasDerivAt (fun s => Kr η s) (dKχ η χ) χ)
    (hKill : ∀ η ∈ Ioo 0 (π / 2), ∀ χ, Kη η χ * dKη η χ + Kχ η χ * dKχ η χ = 0) : False := by
  have hcos := cap_unique l a ad ha had h0 hd0
  set η0 : ℝ := π / 4 with hη0
  have hpi := pi_pos
  have h1 : 0 < η0 := by rw [hη0]; positivity
  have h2 : η0 < π / 2 := by rw [hη0]; linarith
  have hc : 0 < cos η0 := cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have hlc : l * cos η0 ≠ 0 := (mul_pos hl hc).ne'
  -- ∂_χ K = 0(一様)
  have hχ0 : dKχ η0 0 = 0 := by
    have hconst : HasDerivAt (fun s => Kr η0 s) 0 0 := by
      have : (fun s => Kr η0 s) = fun _ => 24 * l ^ 4 * ((a η0) ^ 8)⁻¹ := funext fun s => hKr η0 s
      rw [this]; exact hasDerivAt_const _ _
    exact (hdχ η0 0).unique hconst
  -- ∂_η K ≠ 0
  have hfun : (fun s => Kr s 0) = fun s => 24 * l ^ 4 * ((l * cos s) ^ 8)⁻¹ := by
    funext s; rw [hKr, hcos]
  have hη : dKη η0 0 ≠ 0 := by
    have hd := hdη η0 0
    rw [hfun] at hd
    rw [hd.unique (kret_hasDeriv l η0 hlc)]
    exact kret_deriv_ne l η0 hl h1 h2
  -- K^η > 0
  have hK : 0 < Kη η0 0 := by
    rw [hKη, hcos]
    exact div_pos (CFT.Z44.killing_time_pos (ε η0 0) (hε η0 0)) (mul_pos hl hc)
  have := hKill η0 ⟨h1, h2⟩ 0
  rw [hχ0, mul_zero, add_zero] at this
  rcases mul_eq_zero.mp this with h | h
  · exact hK.ne' h
  · exact hη h

end CFT.Z44Cap
