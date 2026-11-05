/-
  確かめが足りなかった項目を、ダンベルの幾何で作り直す(2026-11-05)

  * II.3(運動学:球対称な空間の断面 ds² + r(s)²dΩ²。作用:ハミルトン拘束(II.2 の三つの相))
      CIS Theorem B(一般の大域的分類)の引用を、ダンベルの対称性(球対称)の範囲では自分で示す。
      相の式 rr″ + 1 − r′² = 0 とハミルトン拘束の三つの場合:
      (a) S³ 相 1 − r′² = r²/ℓ²:r″ = −r/ℓ² で、解は r = r(0) cos(s/ℓ) + ℓ r′(0) sin(s/ℓ) だけ(`s3_global`、
          ODE の解の一意性をエネルギーの方法で)。振幅は ℓ(r(0)² + ℓ²r′(0)² = ℓ²)で r ≤ ℓ、
          r = 0 の点では r′² = 1(極で滑らかに閉じる:円錐の特異点がない、`s3_pole_regular`)。
          つまり大域的には半径 ℓ の丸い S³(周期 2πℓ のうち長さ πℓ ごとに閉じる)。
      (b) 平坦相 1 − r′² = 0:r″ = 0、r = r(0) + r′(0)s、r′ = ±1(`flat_global`)。
      (c) 首 r′ = r″ = 0:r = ℓ(AlphaII_EYM `phase_neck`)。
      したがって球対称なダンベルの断面は、半径 ℓ の S³ の一部・平坦・半径 ℓ の円柱をつないだものに限られる。
      球対称でない一般の場合は CIS Theorem B(外部)だが、ダンベルにはこの範囲で足りる。
  * IX.11(運動学:首 AdS₂ × S²。作用:EYM)
      2 次元の方程式を仮定に置いていた点を、4 次元の Einstein 方程式で確かめる。首の混合 Ricci の固有値
      (−1/ℓ², −1/ℓ², 1/ℓ², 1/ℓ²)(AlphaV_NeckQuantum `neck_ricci`)から R = 0、G^μ_ν = R^μ_ν。
      YM の応力(AlphaII_EYM `neck_stress`)ρ = 1/(2g²ℓ⁴)、p_r = −ρ、p_T = ρ で、G = 8πG T の 4 成分が
      すべて成り立つ ⇔ ℓ² = 4πG/g²(`neck_einstein`)。
  * IX.17(運動学:帽子 a = ℓ cos η。作用:EYM(Friedmann))
      帽子の YM の輻射 ρ = 3/(2g²a⁴)(AlphaII_EYM `cap_stress` を半径 a で)と ℓ² = 4πG/g² から、
      共形時間の Friedmann a′² + a² = (8πG/3)ρa⁴ = ℓ² を a = ℓ cos η がみたす(`cap_friedmann_l`)。
      帽子の最大の半径は首の半径 ℓ に等しい。
  * IX.25(運動学:首の静的な計量 −N²dt² + dx² + R²dΩ²、N = cosh(x/ℓ)、R = ℓ。作用:輻射の流体)
      静水圧の式を仮定に置いていた点を、∇_μT^μ_x = 0 から導く。対角な計量の Christoffel 記号
      Γ^t_tx = N′/N、Γ^θ_θx = R′/R(`christoffel_static`)で ∇_μT^μ_x = p′ + (N′/N)(ρ + p)(`static_euler`)。
      輻射(p = aT⁴/3、ρ = aT⁴)では (TN)′ = 0(AlphaIX_Thermo `tolman`)。首では T(x) = T₀/cosh(x/ℓ)
      (`neck_tolman`):局所温度は中心で最大で、接合に向かって下がる。
  * IX.32(運動学:Euclid の首 dτ² + cosh²(τ/ℓ)dz²(曲率 −1/ℓ²、IX.22))
      ダンベルの Euclid の首はコンパクトな H²/Γ ではないので、閉曲面のエルゴード性は当てはまらない
      (命題を改める)。かわりにダンベルの首で成り立つことを示す:測地線の偏差 J″ = −KJ = J/ℓ² の解
      J = cosh(s/ℓ)(`jacobi_neck`)は J ≥ e^{s/ℓ}/2(`lyapunov_neck`):隣り合う測地線は Lyapunov 指数 1/ℓ で
      指数関数的に離れる(カオスの幾何的な起源)。
  * VIII.7(運動学:帽子の領域 0 < η < π/2、0 < χ < π/2 − η)
      仮定(ODE と曲率の式)がダンベル全体で成り立つ形だった点を、帽子の領域だけに絞る
      (`cap_unique_local`、`no_killing_spinor_local`)。
-/
import CFT.AlphaVIII_Z44Cap
import CFT.AlphaII_EYM
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace CFT.FixGeo

open Real Set Filter Topology

/-! ### II.3 球対称な断面の大域的分類 -/

/-- 【α-II.3 (a)】S³ 相:r″ = −r/ℓ² なら r = r(0) cos(s/ℓ) + ℓ r′(0) sin(s/ℓ) -/
theorem s3_global (l : ℝ) (hl : l ≠ 0) (r rd : ℝ → ℝ) (hr : ∀ s, HasDerivAt r (rd s) s)
    (hrd : ∀ s, HasDerivAt rd (-(r s / l ^ 2)) s) :
    ∀ s, r s = r 0 * cos (s / l) + l * rd 0 * sin (s / l) := by
  let y : ℝ → ℝ := fun s => r 0 * cos (s / l) + l * rd 0 * sin (s / l)
  let yd : ℝ → ℝ := fun s => -(r 0 / l) * sin (s / l) + l * rd 0 / l * cos (s / l)
  have hu : ∀ s, HasDerivAt (fun x : ℝ => x / l) (1 / l) s := fun s => (hasDerivAt_id' s).div_const l
  have hy : ∀ s, HasDerivAt y (yd s) s := by
    intro s
    have h := (((hasDerivAt_cos (s / l)).comp s (hu s)).const_mul (r 0)).add
      (((hasDerivAt_sin (s / l)).comp s (hu s)).const_mul (l * rd 0))
    convert h using 1
    simp only [yd]; ring
  have hyd : ∀ s, HasDerivAt yd (-(y s / l ^ 2)) s := by
    intro s
    have h := (((hasDerivAt_sin (s / l)).comp s (hu s)).const_mul (-(r 0 / l))).add
      (((hasDerivAt_cos (s / l)).comp s (hu s)).const_mul (l * rd 0 / l))
    convert h using 1
    simp only [y]; field_simp <;> ring
  let E : ℝ → ℝ := fun s => (r s - y s) ^ 2 / l ^ 2 + (rd s - yd s) ^ 2
  have hE : ∀ s, HasDerivAt E 0 s := by
    intro s
    have h1 := (((hr s).sub (hy s)).pow 2).div_const (l ^ 2)
    have h2 := ((hrd s).sub (hyd s)).pow 2
    show HasDerivAt (fun s => (r s - y s) ^ 2 / l ^ 2 + (rd s - yd s) ^ 2) 0 s
    convert h1.add h2 using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  have hconst : ∀ s, E s = E 0 := fun s =>
    is_const_of_deriv_eq_zero (fun x => (hE x).differentiableAt) (fun x => (hE x).deriv) s 0
  have hy0 : y 0 = r 0 := by simp [y]
  have hyd0 : yd 0 = rd 0 := by
    simp only [yd, sin_zero, cos_zero, mul_zero, mul_one, zero_add]; field_simp <;> ring
  have hE0 : E 0 = 0 := by
    show (r 0 - y 0) ^ 2 / l ^ 2 + (rd 0 - yd 0) ^ 2 = 0
    rw [hy0, hyd0]; ring
  intro s
  have h := hconst s
  rw [hE0] at h
  have hl2 : 0 < l ^ 2 := by positivity
  have h1 : (r s - y s) ^ 2 / l ^ 2 = 0 := by
    have := sq_nonneg (rd s - yd s)
    have : 0 ≤ (r s - y s) ^ 2 / l ^ 2 := by positivity
    simp only [E] at h
    linarith
  have h2 : (r s - y s) ^ 2 = 0 := by
    rcases div_eq_zero_iff.1 h1 with h | h
    · exact h
    · exact absurd h hl2.ne'
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
  simp only [y] at this
  linarith

/-- 【α-II.3 (a)】ハミルトン拘束 1 − r′² = r²/ℓ² なら振幅は ℓ(r(0)² + ℓ²r′(0)² = ℓ²)、したがって r ≤ ℓ -/
theorem s3_amplitude (l r0 rd0 s : ℝ) (hl : 0 < l) (hc : 1 - rd0 ^ 2 = r0 ^ 2 / l ^ 2) :
    r0 ^ 2 + (l * rd0) ^ 2 = l ^ 2 ∧ r0 * cos (s / l) + l * rd0 * sin (s / l) ≤ l := by
  have hl0 := hl.ne'
  have e : r0 ^ 2 + (l * rd0) ^ 2 = l ^ 2 := by
    have : r0 ^ 2 = l ^ 2 * (1 - rd0 ^ 2) := by rw [hc]; field_simp <;> ring
    rw [this]; ring
  refine ⟨e, ?_⟩
  -- Cauchy–Schwarz:(A cos + B sin)² + (A sin − B cos)² = (A² + B²)(cos² + sin²) = ℓ²
  have h1 := sin_sq_add_cos_sq (s / l)
  have key : (r0 * cos (s / l) + l * rd0 * sin (s / l)) ^ 2 + (r0 * sin (s / l) - l * rd0 * cos (s / l)) ^ 2
      = l ^ 2 := by
    linear_combination (sin (s / l) ^ 2 + cos (s / l) ^ 2) * e + l ^ 2 * h1
  have hcs : (r0 * cos (s / l) + l * rd0 * sin (s / l)) ^ 2 ≤ l ^ 2 := by
    nlinarith [sq_nonneg (r0 * sin (s / l) - l * rd0 * cos (s / l))]
  by_contra hc'
  push_neg at hc'
  nlinarith [hc', hl, hcs]

/-- 【α-II.3 (a)】極(r = 0)では r′² = 1:滑らかに閉じる(円錐の特異点がない) -/
theorem s3_pole_regular (l rd0 : ℝ) (hc : 1 - rd0 ^ 2 = (0 : ℝ) ^ 2 / l ^ 2) : rd0 ^ 2 = 1 := by
  have h0 : (0 : ℝ) ^ 2 / l ^ 2 = 0 := by simp
  rw [h0] at hc; linarith

/-- 【α-II.3 (b)】平坦相:r″ = 0 なら r = r(0) + r′(0)s、拘束から r′(0)² = 1 -/
theorem flat_global (r rd : ℝ → ℝ) (hr : ∀ s, HasDerivAt r (rd s) s) (hrd : ∀ s, HasDerivAt rd 0 s) :
    ∀ s, r s = r 0 + rd 0 * s := by
  have hc : ∀ s, rd s = rd 0 := fun s =>
    is_const_of_deriv_eq_zero (fun x => (hrd x).differentiableAt) (fun x => (hrd x).deriv) s 0
  let F : ℝ → ℝ := fun s => r s - rd 0 * s
  have hF : ∀ s, HasDerivAt F 0 s := by
    intro s
    have h := (hr s).sub ((hasDerivAt_id' s).const_mul (rd 0))
    convert h using 1
    rw [hc s]; ring
  intro s
  have := is_const_of_deriv_eq_zero (fun x => (hF x).differentiableAt) (fun x => (hF x).deriv) s 0
  simp only [F, mul_zero, sub_zero] at this
  linarith

/-! ### IX.11 首の 4 次元の Einstein 方程式 -/

/-- 【α-IX.11】首:Ricci の固有値 (−1/ℓ², −1/ℓ², 1/ℓ², 1/ℓ²)(R = 0)と YM の応力で、
G^μ_ν = 8πG T^μ_ν の 4 成分 ⇔ ℓ² = 4πG/g² -/
theorem neck_einstein (G g l : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) (hG : G ≠ 0) :
    let R := -1 / l ^ 2 + -1 / l ^ 2 + 1 / l ^ 2 + 1 / l ^ 2
    (R = 0) ∧
    ((-1 / l ^ 2 - R / 2 = 8 * π * G * (-CFT.EYM.rho g 0 0 l) ∧
      -1 / l ^ 2 - R / 2 = 8 * π * G * CFT.EYM.pr g 0 0 l ∧
      1 / l ^ 2 - R / 2 = 8 * π * G * CFT.EYM.pT g 0 0 l) ↔ l ^ 2 = 4 * π * G / g ^ 2) := by
  intro R
  have hR : R = 0 := by simp only [R]; ring
  refine ⟨hR, ?_⟩
  obtain ⟨h1, h2, h3⟩ := CFT.EYM.neck_stress g l hg hl
  rw [hR, h1, h2, h3]
  have key : 1 / l ^ 2 = 8 * π * G * (1 / (2 * g ^ 2 * l ^ 4)) ↔ l ^ 2 = 4 * π * G / g ^ 2 := by
    rw [← CFT.EYM.ell_neck G g l hg hl hG]
    constructor
    · intro h; linear_combination (-2) * h
    · intro h; linear_combination (-1 / 2) * h
  constructor
  · rintro ⟨-, -, h⟩
    exact key.1 (by linear_combination h)
  · intro h
    have k := key.2 h
    exact ⟨by linear_combination (-1) * k, by linear_combination (-1) * k, by linear_combination k⟩

/-! ### IX.17 帽子の Friedmann と ℓ -/

/-- 【α-IX.17】ρ = 3/(2g²a⁴)、ℓ² = 4πG/g² なら a = ℓ cos η は a′² + a² = (8πG/3)ρa⁴ をみたす -/
theorem cap_friedmann_l (G g l η : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) (hc : cos η ≠ 0)
    (hℓ : l ^ 2 = 4 * π * G / g ^ 2) :
    (l * -sin η) ^ 2 + (l * cos η) ^ 2 = 8 * π * G / 3 * (3 / (2 * g ^ 2 * (l * cos η) ^ 4)) * (l * cos η) ^ 4 := by
  have hlc : l * cos η ≠ 0 := mul_ne_zero hl hc
  have e1 : (l * -sin η) ^ 2 + (l * cos η) ^ 2 = l ^ 2 := by
    linear_combination l ^ 2 * sin_sq_add_cos_sq η
  have e2 : 8 * π * G / 3 * (3 / (2 * g ^ 2 * (l * cos η) ^ 4)) * (l * cos η) ^ 4 = 4 * π * G / g ^ 2 := by
    field_simp <;> ring
  rw [e1, e2, hℓ]

/-- 帽子の輻射:半径 a の帽子の YM の応力 ρ = 3/(2g²a⁴)(AlphaII_EYM `cap_stress`) -/
theorem cap_rho (g a x : ℝ) (hg : g ≠ 0) (ha : a ≠ 0) (hx : sin x ≠ 0) :
    CFT.EYM.rho g (cos x) (-(sin x) / a) (a * sin x) = 3 / (2 * g ^ 2 * a ^ 4) :=
  (CFT.EYM.cap_stress g a x hg ha hx).1

/-! ### IX.25 首の Tolman–Ehrenfest -/

/-- 対角な計量 g_tt = −N²、g_θθ = R² の Christoffel 記号:Γ^t_tx = ½g^tt ∂_x g_tt = N′/N、
Γ^θ_θx = ½g^θθ ∂_x g_θθ = R′/R -/
theorem christoffel_static (N Nd R Rd : ℝ) (hN : N ≠ 0) (hR : R ≠ 0) :
    1 / 2 * (-1 / N ^ 2) * (-(2 * N * Nd)) = Nd / N ∧ 1 / 2 * (1 / R ^ 2) * (2 * R * Rd) = Rd / R := by
  constructor <;> field_simp <;> ring

/-- 【α-IX.25】∇_μT^μ_x = p′ + Γ^μ_μx p − Γ^λ_μx T^μ_λ(T = diag(−ρ, p, p, p))= p′ + (N′/N)(ρ + p) -/
theorem static_euler (pd p ρ Γt Γθ : ℝ) :
    pd + (Γt + 2 * Γθ) * p - (Γt * (-ρ) + 2 * Γθ * p) = pd + Γt * (ρ + p) := by ring

/-- 【α-IX.25】首 N = cosh(x/ℓ):輻射 T(x) = T₀/cosh(x/ℓ) は (TN)′ = 0 をみたし、
p = aT⁴/3、ρ = aT⁴ で p′ + (N′/N)(ρ + p) = 0 -/
theorem neck_tolman (a T0 l x : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun y => a * (T0 / cosh (y / l)) ^ 4 / 3)
      (-(sinh (x / l) / l / cosh (x / l)) * (a * (T0 / cosh (x / l)) ^ 4 + a * (T0 / cosh (x / l)) ^ 4 / 3)) x := by
  have hc : cosh (x / l) ≠ 0 := (cosh_pos _).ne'
  have hu : HasDerivAt (fun y : ℝ => y / l) (1 / l) x := (hasDerivAt_id' x).div_const l
  have hch := (Real.hasDerivAt_cosh (x / l)).comp x hu
  have hT := (hasDerivAt_const x T0).div hch hc
  have h := ((hT.pow 4).const_mul a).div_const 3
  convert h using 1
  simp only [Function.comp_apply, Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl]
  field_simp <;> ring

/-! ### IX.32 Euclid の首の測地線の偏差 -/

/-- 【α-IX.32】Jacobi の方程式 J″ = J/ℓ²(K = −1/ℓ²)の解 J = cosh(s/ℓ) -/
theorem jacobi_neck (l s : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun x => cosh (x / l)) (sinh (s / l) / l) s ∧
    HasDerivAt (fun x => sinh (x / l) / l) (cosh (s / l) / l ^ 2) s := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) s := (hasDerivAt_id' s).div_const l
  constructor
  · have h := (Real.hasDerivAt_cosh (s / l)).comp s hu
    convert h using 1; ring
  · have h := ((Real.hasDerivAt_sinh (s / l)).comp s hu).div_const l
    convert h using 1; field_simp <;> ring

/-- 【α-IX.32】J(s) = cosh(s/ℓ) ≥ e^{s/ℓ}/2:隣の測地線は Lyapunov 指数 1/ℓ で離れる -/
theorem lyapunov_neck (l s : ℝ) : rexp (s / l) / 2 ≤ cosh (s / l) := by
  rw [Real.cosh_eq]
  have := exp_pos (-(s / l))
  linarith

/-! ### VIII.7 帽子の領域に絞った Killing スピノルの不存在 -/

/-- 【α-VIII.7】帽子の ODE を [0, π/2) でだけ仮定しても a = ℓ cos η -/
theorem cap_unique_local (l : ℝ) (a ad : ℝ → ℝ) (ha : ∀ η ∈ Ico 0 (π / 2), HasDerivAt a (ad η) η)
    (had : ∀ η ∈ Ico 0 (π / 2), HasDerivAt ad (-a η) η) (h0 : a 0 = l) (hd0 : ad 0 = 0) :
    ∀ η ∈ Ico 0 (π / 2), a η = l * cos η := by
  let E : ℝ → ℝ := fun t => (a t - l * cos t) ^ 2 + (ad t + l * sin t) ^ 2
  have hE : ∀ t ∈ Ico 0 (π / 2), HasDerivAt E 0 t := by
    intro t ht
    have h1 := ((ha t ht).sub ((hasDerivAt_cos t).const_mul l)).pow 2
    have h2 := ((had t ht).add ((hasDerivAt_sin t).const_mul l)).pow 2
    show HasDerivAt (fun t => (a t - l * cos t) ^ 2 + (ad t + l * sin t) ^ 2) 0 t
    convert h1.add h2 using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  intro η hη
  have hsub : Icc 0 η ⊆ Ico 0 (π / 2) := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hη.2⟩
  have hcont : ContinuousOn E (Icc 0 η) := fun x hx => (hE x (hsub hx)).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun x hx => (hE x (hsub (Ico_subset_Icc_self hx))).hasDerivWithinAt) η ⟨hη.1, le_refl η⟩
  have hE0 : E 0 = 0 := by simp [E, h0, hd0]
  rw [hE0] at hconst
  have h1 : (a η - l * cos η) ^ 2 = 0 := by
    have := sq_nonneg (ad η + l * sin η)
    have := sq_nonneg (a η - l * cos η)
    simp only [E] at hconst
    linarith
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  linarith

/-- 【α-VIII.7】帽子の領域(0 ≤ η < π/2 の ODE、0 < η < π/2・0 < χ < π/2 − η の曲率の式と Killing の式)だけを仮定しても
Killing スピノルはない(点 (π/4, π/8) で ∂_χK = 0、∂_ηK ≠ 0、K^η > 0) -/
theorem no_killing_spinor_local (l : ℝ) (hl : 0 < l) (a ad : ℝ → ℝ)
    (ha : ∀ η ∈ Ico 0 (π / 2), HasDerivAt a (ad η) η)
    (had : ∀ η ∈ Ico 0 (π / 2), HasDerivAt ad (-a η) η) (h0 : a 0 = l) (hd0 : ad 0 = 0)
    (Kr : ℝ → ℝ → ℝ)
    (hKr : ∀ η ∈ Ioo 0 (π / 2), ∀ χ ∈ Ioo 0 (π / 2 - η), Kr η χ = 24 * l ^ 4 * ((a η) ^ 8)⁻¹)
    (Kη Kχ : ℝ → ℝ → ℝ) (ε : ℝ → ℝ → Fin 4 → ℝ × ℝ) (hε : ∀ η χ, ε η χ ≠ 0)
    (hKη : ∀ η χ, Kη η χ = (∑ i, ((ε η χ i).1 ^ 2 + (ε η χ i).2 ^ 2)) / a η)
    (dKη dKχ : ℝ → ℝ → ℝ)
    (hdη : ∀ η χ, HasDerivAt (fun s => Kr s χ) (dKη η χ) η)
    (hdχ : ∀ η χ, HasDerivAt (fun s => Kr η s) (dKχ η χ) χ)
    (hKill : ∀ η ∈ Ioo 0 (π / 2), ∀ χ ∈ Ioo 0 (π / 2 - η), Kη η χ * dKη η χ + Kχ η χ * dKχ η χ = 0) :
    False := by
  have hcap := cap_unique_local l a ad ha had h0 hd0
  have hpi := pi_pos
  set η0 : ℝ := π / 4 with hη0
  set χ0 : ℝ := π / 8 with hχ0
  have h1 : 0 < η0 := by rw [hη0]; positivity
  have h2 : η0 < π / 2 := by rw [hη0]; linarith
  have hχ1 : χ0 ∈ Ioo 0 (π / 2 - η0) := ⟨by rw [hχ0]; positivity, by rw [hχ0, hη0]; linarith⟩
  have hc : 0 < cos η0 := cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have hlc : l * cos η0 ≠ 0 := (mul_pos hl hc).ne'
  -- ∂_χ K = 0:χ0 の近くで Kr η0 χ は一定
  have hχ : dKχ η0 χ0 = 0 := by
    have hev : (fun s => Kr η0 s) =ᶠ[𝓝 χ0] fun _ => 24 * l ^ 4 * ((a η0) ^ 8)⁻¹ := by
      filter_upwards [Ioo_mem_nhds hχ1.1 hχ1.2] with s hs
      exact hKr η0 ⟨h1, h2⟩ s hs
    have hconst : HasDerivAt (fun s => Kr η0 s) 0 χ0 :=
      (hasDerivAt_const χ0 (24 * l ^ 4 * ((a η0) ^ 8)⁻¹)).congr_of_eventuallyEq hev
    exact (hdχ η0 χ0).unique hconst
  -- ∂_η K ≠ 0:η0 の近くで Kr s χ0 = 24ℓ⁴(ℓ cos s)⁻⁸
  have hη : dKη η0 χ0 ≠ 0 := by
    have hev : (fun s => Kr s χ0) =ᶠ[𝓝 η0] fun s => 24 * l ^ 4 * ((l * cos s) ^ 8)⁻¹ := by
      filter_upwards [Ioo_mem_nhds (show π / 8 < η0 by rw [hη0]; linarith)
        (show η0 < 3 * π / 8 by rw [hη0]; linarith)] with s hs
      have hs1 : s ∈ Ioo 0 (π / 2) := ⟨by linarith [hs.1, hpi], by linarith [hs.2]⟩
      have hs2 : χ0 ∈ Ioo 0 (π / 2 - s) := ⟨hχ1.1, by rw [hχ0]; linarith [hs.2]⟩
      show Kr s χ0 = 24 * l ^ 4 * ((l * cos s) ^ 8)⁻¹
      rw [hKr s hs1 χ0 hs2, hcap s ⟨hs1.1.le, hs1.2⟩]
    have hd := (CFT.Z44Cap.kret_hasDeriv l η0 hlc).congr_of_eventuallyEq hev
    rw [(hdη η0 χ0).unique hd]
    exact CFT.Z44Cap.kret_deriv_ne l η0 hl h1 h2
  -- K^η > 0
  have hK : 0 < Kη η0 χ0 := by
    rw [hKη, hcap η0 ⟨h1.le, h2⟩]
    exact div_pos (CFT.Z44.killing_time_pos (ε η0 χ0) (hε η0 χ0)) (mul_pos hl hc)
  have := hKill η0 ⟨h1, h2⟩ χ0 hχ1
  rw [hχ, mul_zero, add_zero] at this
  rcases mul_eq_zero.mp this with h | h
  · exact hK.ne' h
  · exact hη h

end CFT.FixGeo
