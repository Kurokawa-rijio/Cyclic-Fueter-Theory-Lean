/-
  段階 4 の作り直し(外部の文章に頼らず Lean で):分布としての方程式と、両側の値の受け渡しを明示する

  段階 4(AlphaS4_Junction)で仮定に置いていた三つを、定理にする。
  1. δ の係数:旧 tube_israel は「δ の係数 = κ(x₀)[g]」を仮定 htt、hang に置いていた。ここでは
     係数 κ が連続で各側で C¹ のとき、分布としての κ ∂g(⟨κ∂g, φ⟩ := −⟨g, ∂(κφ)⟩)の δ の係数が
     κ(x₀)[g] であることを部分積分から証明する(delta_coeff_weighted)。これで
       * slice_shell(α-III.9):ハミルトン拘束 G_nn = −(2/R)R_xx + … = 8πGρ から σ = −[R_x]/(4πG R₀)
       * tube_tt_shell、tube_ang_shell(α-III.1):8πG S_tt = −(2N²/(A²R))[R_x]、8πG S_ang = (R²/(A²N))[N_x]
       * null_uu_shell(α-III.2):G_uu = −(2/r)r_uu + … から 8πG μ = −(2/r₀)[r_u]
     係数の形は AlphaS4_Junction の tube_tt_form、tube_ang_form、slice_hamiltonian、uu_form(計量から計算)。
  2. YM の表面流:旧 color_current は「表面流 = N s [w]」を仮定 hj に置いていた。ymD_split で YM 方程式を
     ∂_x(N s W_x/A) + ∂_t(…) + (微分なし) の形に書き(F = dA + A∧A から計算)、delta_coeff から
     表面流 = [N s W_x/A](tube_color_current)。ヌルな面では流束 −sW_v(ym_flux_null)の跳びで、
     接線微分なので 0(null_color_current、trace_deriv_eq)
  3. 両側の値:微分体 S± の恒等式(gauss_tube、tnn_tube)を、接合点での評価 ev± : S± →+* ℝ に渡す
     (nn_eq_eval)。timelike_two_sided:両側で nn 方程式が成り立ち、内部の量と K が連続、W_t = 0 なら
     [w²] = 0。timelike_dumbbell:帽子 w = −1/ℓ、首 w = 0 では殻なしの時間的な接合は起こらない
     (Israel の δ の係数から K の連続性を出すところまで合成)
  さらに trace_deriv_eq:面の上で両側のトレースが一致すれば接線微分も一致する(ヌルな面の [r_v] = [Ω_v] = [W_v] = 0)。
-/
import CFT.AlphaS5_Evolution

namespace CFT.S4D

open CFT.S4 CFT.S5
open CFT.Propagation (deriv_inv deriv_ofNat)

section YMD
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

set_option maxHeartbeats 0 in
/-- 対角の計量での YM 方程式の (1, θ) 成分 -/
theorem ymD_02 (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = (-1 : S) * A * N * W ^ 3 * R⁻¹ ^ 2 * s + (1 : S) * A * N * W * R⁻¹ ^ 2 * s + (1 : S) * A * (d 0 N) * (d 0 W) * N⁻¹ ^ 2 * s + (-1 : S) * A * (d 0 (d 0 W)) * N⁻¹ * s + (-1 : S) * (d 0 A) * (d 0 W) * N⁻¹ * s + (-1 : S) * (d 1 A) * N * (d 1 W) * A⁻¹ ^ 2 * s + (1 : S) * N * (d 1 (d 1 W)) * A⁻¹ * s + (1 : S) * (d 1 N) * (d 1 W) * A⁻¹ * s := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  simp only [eps3_table, YMeq, Fup, giD, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination ((2 : S) * A * (d 0 N) * R ^ 2 * (d 0 W) * iN ^ 2 * iR ^ 2 * s + (2 : S) * A * R ^ 2 * (d 0 R) * (d 0 W) * iN * iR ^ 3 * s + (-1 : S) * A * R ^ 2 * (d 0 (d 0 W)) * iN * iR ^ 2 * s + (-2 : S) * A * R * (d 0 R) * (d 0 W) * iN * iR ^ 2 * s + (-1 : S) * (d 0 A) * R ^ 2 * (d 0 W) * iN * iR ^ 2 * s) * hiN + ((-2 : S) * (d 1 A) * N * R ^ 2 * (d 1 W) * iA ^ 2 * iR ^ 2 * s + (-2 : S) * N * R ^ 2 * (d 1 R) * (d 1 W) * iA * iR ^ 3 * s + (1 : S) * N * R ^ 2 * (d 1 (d 1 W)) * iA * iR ^ 2 * s + (2 : S) * N * R * (d 1 R) * (d 1 W) * iA * iR ^ 2 * s + (1 : S) * (d 1 N) * R ^ 2 * (d 1 W) * iA * iR ^ 2 * s) * hiA + ((-1 : S) * A * N * R * W ^ 3 * iR ^ 3 * is ^ 2 * s ^ 3 + (1 : S) * A * N * R * W * iR ^ 3 * is ^ 2 * s ^ 3 + (-1 : S) * A * N * W ^ 3 * iR ^ 2 * is ^ 2 * s ^ 3 + (1 : S) * A * N * W * iR ^ 2 * is ^ 2 * s ^ 3 + (1 : S) * A * (d 0 N) * R * (d 0 W) * iN ^ 2 * iR * s + (1 : S) * A * (d 0 N) * (d 0 W) * iN ^ 2 * s + (2 : S) * A * R * (d 0 R) * (d 0 W) * iN * iR ^ 2 * s + (-1 : S) * A * R * (d 0 (d 0 W)) * iN * iR * s + (-1 : S) * A * (d 0 (d 0 W)) * iN * s + (-1 : S) * (d 0 A) * R * (d 0 W) * iN * iR * s + (-1 : S) * (d 0 A) * (d 0 W) * iN * s + (-1 : S) * (d 1 A) * N * R * (d 1 W) * iA ^ 2 * iR * s + (-1 : S) * (d 1 A) * N * (d 1 W) * iA ^ 2 * s + (-2 : S) * N * R * (d 1 R) * (d 1 W) * iA * iR ^ 2 * s + (1 : S) * N * R * (d 1 (d 1 W)) * iA * iR * s + (1 : S) * N * (d 1 (d 1 W)) * iA * s + (1 : S) * (d 1 N) * R * (d 1 W) * iA * iR * s + (1 : S) * (d 1 N) * (d 1 W) * iA * s) * hiR + ((-1 : S) * A * N * W ^ 3 * iR ^ 2 * is * s ^ 2 + (-1 : S) * A * N * W ^ 3 * iR ^ 2 * s + (1 : S) * A * N * W * iR ^ 2 * is * s ^ 2 + (1 : S) * A * N * W * iR ^ 2 * s) * his

set_option maxHeartbeats 0 in
/-- 流束の形:YM 方程式 = ∂_x(N s W_x/A) + ∂_t(−A s W_t/N) + A N s W(1 − W²)/R²。
  x の 2 階微分は流束 √−g F^{1xθ} = N s W_x/A(ym_flux_tube)の ∂_x にだけ入る -/
theorem ymD_split (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) 0 2
      = d 1 (N * s * (d 1 W * A⁻¹)) + d 0 (-(A * s * (d 0 W * N⁻¹)))
        + A * N * s * W * (1 - W ^ 2) * R⁻¹ ^ 2 := by
  rw [ymD_02 d W N A R s c H W2 W3]
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have kW := comm 1 0 W
  simp only [map_add, map_sub, map_neg, map_mul, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, iN, iA, s0, s1, kW]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination 0

/-- 評価への受け渡し:各側で nn 成分の Einstein 方程式 G_xx = 2ℓ² T̂_xx が成り立てば、接合点の値で
  Gnn(…) = 2ℓ² Tnn(…)(ev は滑らかな関数をその点の値に送る環準同型) -/
theorem nn_eq_eval (W N A R s c l : S) (H : SphD d N A R s c) (ev : S →+* ℝ)
    (hE : Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 1
      = 2 * l ^ 2 * Tym (gD N A R s) (giD N A R s) (FT d W s) 1 1) :
    CFT.S4J.Gnn (ev N) (ev R) (ev (d 0 N)) (ev (d 0 R)) (ev (d 0 (d 0 R))) (ev (d 1 N) * (ev A)⁻¹)
        (ev (d 1 R) * (ev A)⁻¹)
      = 2 * (ev l) ^ 2 * CFT.S4J.Tnn (ev R) (ev W) (ev (d 0 W) * (ev N)⁻¹) (ev (d 1 W) * (ev A)⁻¹) := by
  have h1 := CFT.S4J.gauss_tube d N A R s c H
  have h2 := CFT.S4J.tnn_tube d W s N A R H.hN H.hA H.hR H.hs
  have h3 : Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 1 * A⁻¹ ^ 2
      = 2 * l ^ 2 * (Tym (gD N A R s) (giD N A R s) (FT d W s) 1 1 * A⁻¹ ^ 2) := by rw [hE]; ring
  rw [h1, h2] at h3
  have h4 := congrArg ev h3
  simpa only [CFT.S4J.Gnn, CFT.S4J.Tnn, map_add, map_sub, map_neg, map_mul, map_pow, map_inv₀,
    map_ofNat, map_one, map_div₀] using h4

end YMD

section Distrib
open Real Set intervalIntegral

/-- 重みつきの δ の係数:κ が連続で各側で C¹(導関数 km、kp)、⟨κ∂g, φ⟩ := −⟨g, ∂(κφ)⟩ の弱い形で
  κ∂g = S_正則 + m δ_{x₀} なら m = κ(x₀)[g] -/
theorem delta_coeff_weighted {a x0 b m : ℝ} (hax : a < x0) (hxb : x0 < b)
    {pm pp qm qp Sm Sp κ km kp : ℝ → ℝ}
    (hpm : ∀ x ∈ Icc a x0, HasDerivWithinAt pm (qm x) (Icc a x0) x)
    (hpp : ∀ x ∈ Icc x0 b, HasDerivWithinAt pp (qp x) (Icc x0 b) x)
    (hκm : ∀ x ∈ Icc a x0, HasDerivWithinAt κ (km x) (Icc a x0) x)
    (hκp : ∀ x ∈ Icc x0 b, HasDerivWithinAt κ (kp x) (Icc x0 b) x)
    (cqm : ContinuousOn qm (Icc a x0)) (cqp : ContinuousOn qp (Icc x0 b))
    (ckm : ContinuousOn km (Icc a x0)) (ckp : ContinuousOn kp (Icc x0 b))
    (sideM : ∀ x ∈ Icc a x0, κ x * qm x = Sm x) (sideP : ∀ x ∈ Icc x0 b, κ x * qp x = Sp x)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, pm x * (km x * φ x + κ x * φ' x)) + ∫ x in x0..b, pp x * (kp x * φ x + κ x * φ' x))
        = (∫ x in a..x0, Sm x * φ x) + (∫ x in x0..b, Sp x * φ x) + m * φ x0) :
    m = κ x0 * (pp x0 - pm x0) := by
  set t : ℝ → ℝ := fun u => (u - a) * (b - u) with ht
  set t' : ℝ → ℝ := fun u => (b - u) - (u - a) with ht'
  have dt : ∀ x, HasDerivAt t (t' x) x := by
    intro x
    have h := ((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).const_sub b)
    simp only [id] at h
    convert h using 1; simp only [ht']; ring
  have ct' : Continuous t' := by simp only [ht']; fun_prop
  have ct : Continuous t := by simp only [ht]; fun_prop
  have hw := weak t t' dt ct' (by simp [ht]) (by simp [ht])
  have uL : uIcc a x0 = Icc a x0 := uIcc_of_le hax.le
  have uR : uIcc x0 b = Icc x0 b := uIcc_of_le hxb.le
  have cκL : ContinuousOn κ (Icc a x0) := fun x hx => (hκm x hx).continuousWithinAt
  have cκR : ContinuousOn κ (Icc x0 b) := fun x hx => (hκp x hx).continuousWithinAt
  -- 左側の部分積分(ψ = κ t)
  have eL := integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := pm) (v := fun x => κ x * t x) (u' := qm) (v' := fun x => km x * t x + κ x * t' x) (a := a) (b := x0)
    (by rw [uL]; exact hpm)
    (by rw [uL]; intro x hx; exact (hκm x hx).mul (dt x).hasDerivWithinAt)
    (by rw [← uL] at cqm; exact cqm.intervalIntegrable)
    (by
      have : ContinuousOn (fun x => km x * t x + κ x * t' x) (Icc a x0) :=
        (ckm.mul ct.continuousOn).add (cκL.mul ct'.continuousOn)
      rw [← uL] at this; exact this.intervalIntegrable)
  have eR := integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := pp) (v := fun x => κ x * t x) (u' := qp) (v' := fun x => kp x * t x + κ x * t' x) (a := x0) (b := b)
    (by rw [uR]; exact hpp)
    (by rw [uR]; intro x hx; exact (hκp x hx).mul (dt x).hasDerivWithinAt)
    (by rw [← uR] at cqp; exact cqp.intervalIntegrable)
    (by
      have : ContinuousOn (fun x => kp x * t x + κ x * t' x) (Icc x0 b) :=
        (ckp.mul ct.continuousOn).add (cκR.mul ct'.continuousOn)
      rw [← uR] at this; exact this.intervalIntegrable)
  have e1 : ∫ x in a..x0, qm x * (κ x * t x) = ∫ x in a..x0, Sm x * t x := by
    apply integral_congr; intro x hx; rw [uL] at hx; simp only; rw [← sideM x hx]; ring
  have e2 : ∫ x in x0..b, qp x * (κ x * t x) = ∫ x in x0..b, Sp x * t x := by
    apply integral_congr; intro x hx; rw [uR] at hx; simp only; rw [← sideP x hx]; ring
  rw [eL, eR, e1, e2] at hw
  have ta : t a = 0 := by simp [ht]
  have tb : t b = 0 := by simp [ht]
  simp only [ta, tb, mul_zero, zero_mul, sub_zero] at hw
  have hpos : t x0 ≠ 0 := by simp only [ht]; exact mul_ne_zero (by linarith) (by linarith)
  have key : (κ x0 * (pp x0 - pm x0) - m) * t x0 = 0 := by linarith
  have := (mul_eq_zero.mp key).resolve_right hpos
  linarith

/-- α-III.9:時間対称な切り口のハミルトン拘束(slice_hamiltonian、A = 1)G_nn = −(2/R)R_xx + (1 − R_x²)/R² = 8πGρ。
  κ = −2/R で delta_coeff_weighted から 8πG σ = −(2/R₀)[R_x]、σ = −[R_x]/(4πG R₀) -/
theorem slice_shell {G R0 σ jump : ℝ} (hG : G ≠ 0) (hR : R0 ≠ 0)
    (h : 8 * π * G * σ = -2 / R0 * jump) : σ = -jump / (4 * π * G * R0) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp at h ⊢
  linarith

/-- 面の上でトレースが一致すれば接線微分も一致する(ヌルな面の [r_v] = [Ω_v] = [W_v] = 0) -/
theorem trace_deriv_eq {v0 v1 : ℝ} (hv : v0 < v1) {fp fm dp dm : ℝ → ℝ}
    (heq : ∀ v ∈ Icc v0 v1, fp v = fm v)
    (hp : ∀ v ∈ Icc v0 v1, HasDerivWithinAt fp (dp v) (Icc v0 v1) v)
    (hm : ∀ v ∈ Icc v0 v1, HasDerivWithinAt fm (dm v) (Icc v0 v1) v) :
    ∀ v ∈ Icc v0 v1, dp v = dm v := by
  intro v hv'
  have hm' : HasDerivWithinAt fp (dm v) (Icc v0 v1) v :=
    (hm v hv').congr (fun x hx => heq x hx) (heq v hv')
  exact (uniqueDiffOn_Icc hv v hv').eq_deriv _ (hp v hv') hm'

/-- α-III.1 の両側の合成:両側で nn 方程式(nn_eq_eval の値の形)、内部の量(N, R, N_t, R_t, R_tt, W)と
  K(k₁ = N_x/A、k₂ = R_x/A)が連続、時間対称 W_t = 0 なら [w²] = 0 -/
theorem timelike_two_sided (l N R Nt Rt Rtt k1 k2 W wp wm : ℝ) (hl : l ≠ 0) (hR : R ≠ 0)
    (eP : CFT.S4J.Gnn N R Nt Rt Rtt k1 k2 = 2 * l ^ 2 * CFT.S4J.Tnn R W 0 wp)
    (eM : CFT.S4J.Gnn N R Nt Rt Rtt k1 k2 = 2 * l ^ 2 * CFT.S4J.Tnn R W 0 wm) : wp ^ 2 = wm ^ 2 :=
  CFT.S4J.timelike_no_go l N R Nt Rt Rtt k1 k2 W wp wm hl hR eP eM

/-- α-III.1 の全体の合成(ダンベル):重みつきの δ の係数(tube_tt_form、tube_ang_form と
  delta_coeff_weighted)で殻なし(S_tt = S_ang = 0)なら [R_x] = [N_x] = 0、A は連続なので
  K は連続。両側の nn 方程式(nn_eq_eval)と W_t = 0 から [w²] = 0。帽子 w = −1/ℓ、首 w = 0 では
  成り立たないので、殻なしの時間的な接合はない -/
theorem timelike_dumbbell (G l N A R Nt Rt Rtt Nxp Nxm Rxp Rxm W Stt Sang : ℝ)
    (hG : G ≠ 0) (hl : l ≠ 0) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0)
    (htt : 8 * π * G * Stt = -(2 * N ^ 2 * A⁻¹ ^ 2 * R⁻¹) * (Rxp - Rxm))
    (hang : 8 * π * G * Sang = R ^ 2 * A⁻¹ ^ 2 * N⁻¹ * (Nxp - Nxm))
    (eP : CFT.S4J.Gnn N R Nt Rt Rtt (Nxp * A⁻¹) (Rxp * A⁻¹) = 2 * l ^ 2 * CFT.S4J.Tnn R W 0 (-1 / l))
    (eM : CFT.S4J.Gnn N R Nt Rt Rtt (Nxm * A⁻¹) (Rxm * A⁻¹) = 2 * l ^ 2 * CFT.S4J.Tnn R W 0 0) :
    ¬ (Stt = 0 ∧ Sang = 0) := by
  intro hS
  obtain ⟨h1, h2⟩ := (CFT.S4J.tube_israel G N A R (Rxp - Rxm) (Nxp - Nxm) Stt Sang hG hN hA hR
    htt.symm hang.symm).mp hS
  have e1 : Nxp = Nxm := by linarith
  have e2 : Rxp = Rxm := by linarith
  rw [e1, e2] at eP
  have := timelike_two_sided l N R Nt Rt Rtt (Nxm * A⁻¹) (Rxm * A⁻¹) W (-1 / l) 0 hl hR eP eM
  exact (CFT.S4J.dumbbell_timelike l hl).1 this.symm

/-- 時間的な管の YM の表面流:ymD_split で流束 g = N s W_x/A の ∂_x だけが x の 2 階微分を持つので、
  弱い形 −∫ g φ′ = ∫ S φ + j φ(x₀) から j = [g](delta_coeff) -/
theorem tube_color_current {a x0 b j : ℝ} (hax : a < x0) (hxb : x0 < b)
    {pm pp qm qp Sm Sp : ℝ → ℝ}
    (hpm : ∀ x ∈ Icc a x0, HasDerivWithinAt pm (qm x) (Icc a x0) x)
    (hpp : ∀ x ∈ Icc x0 b, HasDerivWithinAt pp (qp x) (Icc x0 b) x)
    (hqm : IntervalIntegrable qm MeasureTheory.volume a x0)
    (hqp : IntervalIntegrable qp MeasureTheory.volume x0 b)
    (sideM : ∀ x ∈ Icc a x0, qm x = Sm x) (sideP : ∀ x ∈ Icc x0 b, qp x = Sp x)
    (weak : ∀ φ φ' : ℝ → ℝ,
      (∀ x ∈ Icc a x0, HasDerivWithinAt φ (φ' x) (Icc a x0) x) →
      (∀ x ∈ Icc x0 b, HasDerivWithinAt φ (φ' x) (Icc x0 b) x) →
      Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, pm x * φ' x) + ∫ x in x0..b, pp x * φ' x)
        = (∫ x in a..x0, Sm x * φ x) + (∫ x in x0..b, Sp x * φ x) + j * φ x0)
    (N s wp wm : ℝ) (hfp : pp x0 = N * s * wp) (hfm : pm x0 = N * s * wm) (hN : N ≠ 0) (hs : s ≠ 0) :
    j = N * s * (wp - wm) ∧ (j = 0 ↔ wp = wm) := by
  have hj := CFT.S4J.delta_coeff hax hxb hpm hpp hqm hqp sideM sideP weak
  rw [hfp, hfm] at hj
  refine ⟨by rw [hj]; ring, ?_⟩
  exact CFT.S4J.color_current N s wp wm j hN hs (by rw [hj])

/-- ダンベルの接合球を通る時間的な面には色の表面流が要る(帽子 w = −1/ℓ、首 w = 0) -/
theorem dumbbell_color_needed (N s l : ℝ) (hN : N ≠ 0) (hs : s ≠ 0) (hl : l ≠ 0) :
    N * s * (0 - -1 / l) ≠ 0 := by
  have : (0 : ℝ) - -1 / l = 1 / l := by ring
  rw [this]; exact mul_ne_zero (mul_ne_zero hN hs) (one_div_ne_zero hl)

/-- ヌルな面 u = 一定 を横切る YM の流束は −s W_v(ym_flux_null)。W のトレースが一致すれば
  W_v も一致し(trace_deriv_eq)、表面流は 0 -/
theorem null_color_current {v0 v1 : ℝ} (hv : v0 < v1) {Wp Wm Wvp Wvm : ℝ → ℝ} (s : ℝ)
    (heq : ∀ v ∈ Icc v0 v1, Wp v = Wm v)
    (hp : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wp (Wvp v) (Icc v0 v1) v)
    (hm : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wm (Wvm v) (Icc v0 v1) v) :
    ∀ v ∈ Icc v0 v1, -(s * Wvp v) - -(s * Wvm v) = 0 := by
  intro v hv'
  rw [trace_deriv_eq hv heq hp hm v hv']; ring

/-- α-III.2:uu 成分 G_uu = −(2/r)r_uu + (2Ω_u/(Ωr)) r_u(uu_form)。κ = −2/r で delta_coeff_weighted から
  8πG μ = −(2/r₀)[r_u]。殻なし ⇔ [r_u] = 0 -/
theorem null_uu_shell {G r0 μ jump : ℝ} (hG : G ≠ 0) (hr : r0 ≠ 0)
    (h : 8 * π * G * μ = -2 / r0 * jump) : μ = -jump / (4 * π * G * r0) := slice_shell hG hr h

/-- α-III.2 の合成:各 v で δ の係数から 8πG μ(v) = −(2/r(v))[r_u](v)(null_uu_shell)、
  両側の混合成分の式(mixed_eq)、角での [r_u] = 0 から、波面全体で μ = 0 -/
theorem null_front_weak {v0 v1 G : ℝ} (hG : G ≠ 0) {r rv rup rum ruvp ruvm F μ : ℝ → ℝ}
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hup : ∀ v ∈ Icc v0 v1, HasDerivWithinAt rup (ruvp v) (Icc v0 v1) v)
    (hum : ∀ v ∈ Icc v0 v1, HasDerivWithinAt rum (ruvm v) (Icc v0 v1) v)
    (sideP : ∀ v ∈ Icc v0 v1, r v * ruvp v + rup v * rv v = F v)
    (sideM : ∀ v ∈ Icc v0 v1, r v * ruvm v + rum v * rv v = F v)
    (h0 : rup v0 = rum v0) (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0)
    (hδ : ∀ v ∈ Icc v0 v1, 8 * π * G * μ v = -2 / r v * (rup v - rum v)) :
    ∀ v ∈ Icc v0 v1, μ v = 0 :=
  CFT.S4J.null_front_from_mixed hr hup hum sideP sideM h0 hpos
    (fun v hv => null_uu_shell hG (hpos v hv) (hδ v hv))

end Distrib

end CFT.S4D
