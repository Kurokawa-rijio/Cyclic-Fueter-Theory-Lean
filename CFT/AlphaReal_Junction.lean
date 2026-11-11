/-
  接合の最終定理を実関数で証明し直す(2026-11-11、RealLine を使わない版)

  AlphaS4_Final の最終定理(timelike_final、color_final、slice_final、null_final)は、微分体 S の元を
  線の上の関数に送る環準同型の族 RealLine を仮定にしていた。体からの環準同型は単射なので、
  中間値の定理と合わせると x ↦ ev_x(f) は定数になってしまい、非定数の関数(ダンベルの帽子)では
  仮定が満たせない(定理の中身が空になる)。ここでは同じ内容を、実関数と弱い形(分布としての)方程式
  だけで述べ直し、ダンベルの具体的な関数で証明する。さらに各定理の仮定が実際に満たせること(非空性)を
  部分積分で示す。

  小分けの構成:
  * `rj_weak_of_pieces`:各側で C¹ の流束 p を部分積分すると、弱い形の方程式が δ の係数 [p] で成り立つ
    (非空性の道具)。
  * `rj_delta_coeff_one`:κ = 1 の場合の δ の係数の補題(既存の delta_coeff_weighted を呼ぶ)。
  * α-III.1(ゲージ場):`rj_color_dumbbell` 時間対称な切り口で帽子 W = cos(x/ℓ)、首 W = 0。
    分布としての YM 方程式の δ の係数(表面の色の流れ)は j = s/ℓ ≠ 0。`rj_color_nonempty` で仮定は満たせる。
  * α-III.1(重力):`rj_cap_tube_radius`、`rj_tube_mismatch` 帽子側の赤道の管の面積半径は
    固有時間 τ で √(ℓ² − τ²)、首側は ℓ。τ ≠ 0 で一致しないので、時間的な管は第一基本形式が連続な
    接合面になれない(Israel 接合の第一条件)。瞬間 τ = 0 での [T_nn] ≠ 0 は AlphaIII.israel_impossible。
  * α-III.9(空間的):`rj_slice_dumbbell` 時間対称な切り口の R″ の弱い形の δ の係数は [R′] = 0、
    よって面密度 σ = 0(殻なし)。一方で断面のスカラー曲率は 6/ℓ² から 2/ℓ² へ跳ぶ。`rj_slice_nonempty`。
  * α-III.2(ヌル):`rj_null_real` 各 v で横断方向の弱い形の uu 方程式(κ = 1)と、波面に沿う混合成分の式、
    角での [r_u] = 0 から、波面全体で面密度 μ = 0。`rj_front_tangential` 波面に沿う W の連続から
    [T_vv] ∝ [W_v²] = 0 と YM の表面流 [−sW_v] = 0(k^μ[T_μν] = 0 の接線成分)。`rj_null_witness` で仮定は満たせる。
  * α-IV.2:`rj_Wu_transport` W_uv が両側で波面の共通の値で決まるなら [W_u] は波面に沿って一定。
    `rj_capWu_corner` 角での値 1/(√2ℓ)、`rj_ruu_corner` 拘束 C_u = 0 から角での [r_uu] = −1/ℓ。
-/
import CFT.AlphaS4_Distrib
import CFT.AlphaS4_Junction
import CFT.AlphaIII
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Set intervalIntegral

namespace CFT.RJ

/-! ### 道具:部分積分と δ の係数(κ = 1) -/

/-- 部分積分:各側で C¹ の流束 p(導関数 q)をとると、弱い形の方程式が δ の係数 [p] = p₊(x₀) − p₋(x₀) で
  成り立つ(最終定理の仮定が空でないことを示す道具) -/
theorem rj_weak_of_pieces {a x0 b : ℝ} {pm pp qm qp : ℝ → ℝ}
    (hpm : ∀ x, HasDerivAt pm (qm x) x) (hpp : ∀ x, HasDerivAt pp (qp x) x)
    (cqm : Continuous qm) (cqp : Continuous qp) :
    ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, pm x * φ' x) + ∫ x in x0..b, pp x * φ' x)
        = (∫ x in a..x0, qm x * φ x) + (∫ x in x0..b, qp x * φ x) + (pp x0 - pm x0) * φ x0 := by
  intro φ φ' hφ hc ha hb
  have i1 := integral_mul_deriv_eq_deriv_mul (a := a) (b := x0) (fun x _ => hpm x) (fun x _ => hφ x)
    (cqm.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have i2 := integral_mul_deriv_eq_deriv_mul (a := x0) (b := b) (fun x _ => hpp x) (fun x _ => hφ x)
    (cqp.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  rw [i1, i2, ha, hb]
  ring

/-- δ の係数(κ = 1):各側で p′ = 源、弱い形 ∂p = 源 + m δ_{x₀} なら m = [p] -/
theorem rj_delta_coeff_one {a x0 b m : ℝ} (hax : a < x0) (hxb : x0 < b) {pm pp qm qp Sm Sp : ℝ → ℝ}
    (hpm : ∀ x ∈ Icc a x0, HasDerivWithinAt pm (qm x) (Icc a x0) x)
    (hpp : ∀ x ∈ Icc x0 b, HasDerivWithinAt pp (qp x) (Icc x0 b) x)
    (cqm : ContinuousOn qm (Icc a x0)) (cqp : ContinuousOn qp (Icc x0 b))
    (sideM : ∀ x ∈ Icc a x0, qm x = Sm x) (sideP : ∀ x ∈ Icc x0 b, qp x = Sp x)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..x0, pm x * φ' x) + ∫ x in x0..b, pp x * φ' x)
        = (∫ x in a..x0, Sm x * φ x) + (∫ x in x0..b, Sp x * φ x) + m * φ x0) :
    m = pp x0 - pm x0 := by
  have h := CFT.S4D.delta_coeff_weighted (m := m) hax hxb (pm := pm) (pp := pp) (qm := qm) (qp := qp)
    (Sm := Sm) (Sp := Sp) (κ := fun _ => 1) (km := fun _ => 0) (kp := fun _ => 0) hpm hpp
    (fun x _ => hasDerivWithinAt_const x _ 1) (fun x _ => hasDerivWithinAt_const x _ 1)
    cqm cqp continuousOn_const continuousOn_const
    (fun x hx => by simp only [one_mul]; exact sideM x hx)
    (fun x hx => by simp only [one_mul]; exact sideP x hx)
    (fun φ φ' h1 h2 h3 h4 => by simpa only [zero_mul, zero_add, one_mul] using weak φ φ' h1 h2 h3 h4)
  simpa using h

/-! ### α-III.1(ゲージ場):表面の色の流れ -/

/-- 帽子の時間対称な切り口(固有の半径 x、N = A = 1)の YM の流束 s·W_x、W = cos(x/ℓ)(s は角度の因子 sin θ) -/
noncomputable def capFlux (l s : ℝ) : ℝ → ℝ := fun x => s * (-sin (x / l) * (1 / l))

/-- 帽子の流束の x 微分 -/
noncomputable def capFluxD (l s : ℝ) : ℝ → ℝ := fun x => s * (-(cos (x / l) * (1 / l)) * (1 / l))

theorem rj_capW_hasDeriv (l x : ℝ) : HasDerivAt (fun x => cos (x / l)) (-sin (x / l) * (1 / l)) x :=
  ((hasDerivAt_id' x).div_const l).cos

theorem rj_capFlux_hasDeriv (l s x : ℝ) : HasDerivAt (capFlux l s) (capFluxD l s x) x :=
  ((((hasDerivAt_id' x).div_const l).sin).neg.mul_const (1 / l)).const_mul s

theorem rj_capFluxD_cont (l s : ℝ) : Continuous (capFluxD l s) := by
  unfold capFluxD; fun_prop

/-- α-III.1(ゲージ場):帽子(左、W = cos(x/ℓ))と首(右、W = 0)を赤道 x₀ = ℓπ/2 でつないだ時間対称な切り口。
  分布としての YM 方程式の δ の係数(表面の色の流れ)j は s/ℓ で、0 になれない -/
theorem rj_color_dumbbell {l s a b j : ℝ} (hl : 0 < l) (hs : s ≠ 0)
    (ha : a < l * π / 2) (hb : l * π / 2 < b)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..l * π / 2, capFlux l s x * φ' x) + ∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ' x)
        = (∫ x in a..l * π / 2, capFluxD l s x * φ x) + (∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ x)
          + j * φ (l * π / 2)) :
    j = s / l ∧ j ≠ 0 := by
  have h := rj_delta_coeff_one (m := j) ha hb (pm := capFlux l s) (pp := fun _ => 0)
    (qm := capFluxD l s) (qp := fun _ => 0) (Sm := capFluxD l s) (Sp := fun _ => 0)
    (fun x _ => (rj_capFlux_hasDeriv l s x).hasDerivWithinAt) (fun x _ => hasDerivWithinAt_const x _ 0)
    (rj_capFluxD_cont l s).continuousOn continuousOn_const (fun _ _ => rfl) (fun _ _ => rfl) weak
  have hl0 : l ≠ 0 := hl.ne'
  have e : l * π / 2 / l = π / 2 := by field_simp <;> ring
  have hj : j = s / l := by
    rw [h]; simp only [capFlux, e, sin_pi_div_two]; ring
  exact ⟨hj, by rw [hj]; exact div_ne_zero hs hl.ne'⟩

/-- 非空性:上の弱い形の方程式は j = [流束] で実際に成り立つ(部分積分) -/
theorem rj_color_nonempty (l s a b : ℝ) :
    ∃ j : ℝ, ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..l * π / 2, capFlux l s x * φ' x) + ∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ' x)
        = (∫ x in a..l * π / 2, capFluxD l s x * φ x) + (∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ x)
          + j * φ (l * π / 2) :=
  ⟨_, rj_weak_of_pieces (pm := capFlux l s) (pp := fun _ => 0) (qm := capFluxD l s) (qp := fun _ => 0)
    (rj_capFlux_hasDeriv l s) (fun x => hasDerivAt_const x 0) (rj_capFluxD_cont l s) continuous_const⟩

/-! ### α-III.1(重力):時間的な管は接合面になれない -/

/-- 帽子の赤道の管 χ = π/2 の面積半径 ℓ cos η を、管に沿う固有時間 τ = ℓ sin η で書くと √(ℓ² − τ²) -/
theorem rj_cap_tube_radius (l η : ℝ) (hl : 0 ≤ l) (hη : 0 ≤ cos η) :
    l * cos η = Real.sqrt (l ^ 2 - (l * sin η) ^ 2) := by
  have e : l ^ 2 - (l * sin η) ^ 2 = (l * cos η) ^ 2 := by
    linear_combination (-l ^ 2) * sin_sq_add_cos_sq η
  rw [e, Real.sqrt_sq (mul_nonneg hl hη)]

/-- 首の管の面積半径は ℓ のまま。τ ≠ 0 では √(ℓ² − τ²) ≠ ℓ:管の第一基本形式は τ = 0 の瞬間を除いて
  連続にならず、時間的な管は接合面になれない(Israel 接合の第一条件) -/
theorem rj_tube_mismatch (l τ : ℝ) (hτ : τ ≠ 0) (hτl : τ ^ 2 ≤ l ^ 2) :
    Real.sqrt (l ^ 2 - τ ^ 2) ≠ l := by
  intro h
  have h0 : 0 ≤ l ^ 2 - τ ^ 2 := by linarith
  have h1 := Real.sq_sqrt h0
  rw [h] at h1
  have h2 : τ ^ 2 = 0 := by linarith
  exact hτ ((pow_eq_zero_iff two_ne_zero).mp h2)

/-! ### α-III.9(空間的):時間対称な切り口 -/

/-- 帽子の面積半径 R = ℓ sin(x/ℓ) とその微分 -/
noncomputable def capR (l : ℝ) : ℝ → ℝ := fun x => l * sin (x / l)
noncomputable def capR1 (l : ℝ) : ℝ → ℝ := fun x => l * (cos (x / l) * (1 / l))
noncomputable def capR2 (l : ℝ) : ℝ → ℝ := fun x => l * (-sin (x / l) * (1 / l) * (1 / l))

theorem rj_capR_hasDeriv (l x : ℝ) : HasDerivAt (capR l) (capR1 l x) x :=
  (((hasDerivAt_id' x).div_const l).sin).const_mul l

theorem rj_capR1_hasDeriv (l x : ℝ) : HasDerivAt (capR1 l) (capR2 l x) x :=
  ((((hasDerivAt_id' x).div_const l).cos).mul_const (1 / l)).const_mul l

theorem rj_capR2_cont (l : ℝ) : Continuous (capR2 l) := by
  unfold capR2; fun_prop

/-- 断面のスカラー曲率 ³R = 2(1 − R′² − 2RR″)/R² -/
noncomputable def scal3 (R R1 R2 : ℝ) : ℝ := 2 * (1 - R1 ^ 2 - 2 * R * R2) / R ^ 2

/-- α-III.9:帽子(R = ℓ sin(x/ℓ))と首(R = ℓ)を赤道でつないだ時間対称な切り口。R″ の弱い形の δ の係数は
  [R′] = 0 で、ハミルトン拘束の面密度 σ(8πGσ = −(2/ℓ)·m)は 0(殻なし)。一方、断面のスカラー曲率は
  帽子側 6/ℓ²、首側 2/ℓ² で跳ぶ(エネルギー密度の段差) -/
theorem rj_slice_dumbbell {l a b m G σ : ℝ} (hl : 0 < l) (hG : G ≠ 0)
    (ha : a < l * π / 2) (hb : l * π / 2 < b)
    (weak : ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..l * π / 2, capR1 l x * φ' x) + ∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ' x)
        = (∫ x in a..l * π / 2, capR2 l x * φ x) + (∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ x)
          + m * φ (l * π / 2))
    (hσ : 8 * π * G * σ = -2 / l * m) :
    m = 0 ∧ σ = 0 ∧ scal3 (capR l (l * π / 2)) (capR1 l (l * π / 2)) (capR2 l (l * π / 2)) = 6 / l ^ 2
      ∧ scal3 l 0 0 = 2 / l ^ 2 := by
  have h := rj_delta_coeff_one (m := m) ha hb (pm := capR1 l) (pp := fun _ => 0)
    (qm := capR2 l) (qp := fun _ => 0) (Sm := capR2 l) (Sp := fun _ => 0)
    (fun x _ => (rj_capR1_hasDeriv l x).hasDerivWithinAt) (fun x _ => hasDerivWithinAt_const x _ 0)
    (rj_capR2_cont l).continuousOn continuousOn_const (fun _ _ => rfl) (fun _ _ => rfl) weak
  have hl0 : l ≠ 0 := hl.ne'
  have e : l * π / 2 / l = π / 2 := by field_simp <;> ring
  have hm : m = 0 := by
    rw [h]; simp only [capR1, e, cos_pi_div_two]; ring
  have hπ : π ≠ 0 := pi_ne_zero
  refine ⟨hm, ?_, ?_, ?_⟩
  · rw [hm, mul_zero] at hσ
    have : 8 * π * G ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG
    exact (mul_eq_zero.mp hσ).resolve_left this
  · simp only [scal3, capR, capR1, capR2, e, sin_pi_div_two, cos_pi_div_two]
    field_simp <;> ring
  · simp only [scal3]
    field_simp <;> ring

/-- 非空性:上の弱い形の方程式は m = [R′] で実際に成り立つ -/
theorem rj_slice_nonempty (l a b : ℝ) :
    ∃ m : ℝ, ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..l * π / 2, capR1 l x * φ' x) + ∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ' x)
        = (∫ x in a..l * π / 2, capR2 l x * φ x) + (∫ x in (l * π / 2)..b, (fun _ => (0 : ℝ)) x * φ x)
          + m * φ (l * π / 2) :=
  ⟨_, rj_weak_of_pieces (pm := capR1 l) (pp := fun _ => 0) (qm := capR2 l) (qp := fun _ => 0)
    (rj_capR1_hasDeriv l) (fun x => hasDerivAt_const x 0) (rj_capR2_cont l) continuous_const⟩

/-! ### α-III.2(ヌル):波面に殻も表面流もない -/

/-- α-III.2:二重ヌル座標 (u, v)、波面 u = u₀。各 v で横断方向の r_u(左 Rum v、右 Rup v)が古典的な
  uu 方程式 ∂_u(r_u) = 源 をみたし、分布としての式の δ の係数が m(v)(面密度 μ:8πGμ = −(2/r)m)。
  波面に沿って両側の混合成分の式 r r_uv + r_u r_v = F(F は波面の共通の値)、角 v₀ で [r_u] = 0、r ≠ 0。
  このとき波面全体で μ = 0(殻なし) -/
theorem rj_null_real {v0 v1 a u0 b G : ℝ} (hau : a < u0) (hub : u0 < b) (hG : G ≠ 0)
    {Rum Rup Ruum Ruup Sm Sp : ℝ → ℝ → ℝ} {m r rv ruvp ruvm F μ : ℝ → ℝ}
    (hRum : ∀ v ∈ Icc v0 v1, ∀ u ∈ Icc a u0, HasDerivWithinAt (Rum v) (Ruum v u) (Icc a u0) u)
    (hRup : ∀ v ∈ Icc v0 v1, ∀ u ∈ Icc u0 b, HasDerivWithinAt (Rup v) (Ruup v u) (Icc u0 b) u)
    (cRum : ∀ v ∈ Icc v0 v1, ContinuousOn (Ruum v) (Icc a u0))
    (cRup : ∀ v ∈ Icc v0 v1, ContinuousOn (Ruup v) (Icc u0 b))
    (sM : ∀ v ∈ Icc v0 v1, ∀ u ∈ Icc a u0, Ruum v u = Sm v u)
    (sP : ∀ v ∈ Icc v0 v1, ∀ u ∈ Icc u0 b, Ruup v u = Sp v u)
    (weak : ∀ v ∈ Icc v0 v1, ∀ φ φ' : ℝ → ℝ, (∀ x, HasDerivAt φ (φ' x) x) → Continuous φ' →
      φ a = 0 → φ b = 0 →
      -((∫ x in a..u0, Rum v x * φ' x) + ∫ x in u0..b, Rup v x * φ' x)
        = (∫ x in a..u0, Sm v x * φ x) + (∫ x in u0..b, Sp v x * φ x) + m v * φ u0)
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hup : ∀ v ∈ Icc v0 v1, HasDerivWithinAt (fun v => Rup v u0) (ruvp v) (Icc v0 v1) v)
    (hum : ∀ v ∈ Icc v0 v1, HasDerivWithinAt (fun v => Rum v u0) (ruvm v) (Icc v0 v1) v)
    (sideP : ∀ v ∈ Icc v0 v1, r v * ruvp v + Rup v u0 * rv v = F v)
    (sideM : ∀ v ∈ Icc v0 v1, r v * ruvm v + Rum v u0 * rv v = F v)
    (h0 : Rup v0 u0 = Rum v0 u0) (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0)
    (hμ : ∀ v ∈ Icc v0 v1, 8 * π * G * μ v = -2 / r v * m v) :
    ∀ v ∈ Icc v0 v1, μ v = 0 := by
  have hm : ∀ v ∈ Icc v0 v1, m v = Rup v u0 - Rum v u0 := fun v hv =>
    rj_delta_coeff_one hau hub (hRum v hv) (hRup v hv) (cRum v hv) (cRup v hv) (sM v hv) (sP v hv)
      (weak v hv)
  exact CFT.S4D.null_front_weak hG (r := r) (rv := rv) (rup := fun v => Rup v u0)
    (rum := fun v => Rum v u0) (ruvp := ruvp) (ruvm := ruvm) (F := F) hr hup hum sideP sideM h0 hpos
    (fun v hv => by rw [hμ v hv, hm v hv])

/-- α-III.2(接線成分):波面に沿って W が連続なら、接線微分 W_v も一致する。よって [T_vv] ∝ [W_v²] = 0、
  YM の表面流 [−s W_v] = 0(k^μ[T_μν] = 0 の接線成分。横断成分 T_uu は有限の段差をもってよい) -/
theorem rj_front_tangential {v0 v1 : ℝ} (hv : v0 < v1) {Wp Wm Wvp Wvm : ℝ → ℝ}
    (heq : ∀ v ∈ Icc v0 v1, Wp v = Wm v)
    (hp : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wp (Wvp v) (Icc v0 v1) v)
    (hm : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wm (Wvm v) (Icc v0 v1) v) (s : ℝ) :
    ∀ v ∈ Icc v0 v1, Wvp v ^ 2 - Wvm v ^ 2 = 0 ∧ -(s * Wvp v) - -(s * Wvm v) = 0 := by
  intro v hv'
  have h := CFT.S4D.trace_deriv_eq hv heq hp hm v hv'
  rw [h]
  constructor <;> ring

/-- 非空性:rj_null_real の仮定はすべて満たせる(両側が同じ滑らかな解の場合) -/
theorem rj_null_witness {G : ℝ} (hG : G ≠ 0) : ∀ v ∈ Icc (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) v = 0 :=
  rj_null_real (v0 := 0) (v1 := 1) (a := 0) (u0 := 1) (b := 2) (G := G) (by norm_num) (by norm_num) hG
    (Rum := fun _ _ => 0) (Rup := fun _ _ => 0) (Ruum := fun _ _ => 0) (Ruup := fun _ _ => 0)
    (Sm := fun _ _ => 0) (Sp := fun _ _ => 0) (m := fun _ => 0) (r := fun _ => 1) (rv := fun _ => 0)
    (ruvp := fun _ => 0) (ruvm := fun _ => 0) (F := fun _ => 0) (μ := fun _ => 0)
    (fun _ _ u _ => hasDerivWithinAt_const u _ 0) (fun _ _ u _ => hasDerivWithinAt_const u _ 0)
    (fun _ _ => continuousOn_const) (fun _ _ => continuousOn_const)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ φ φ' _ _ _ _ => by simp)
    (fun v _ => hasDerivWithinAt_const v _ 1) (fun v _ => hasDerivWithinAt_const v _ 0)
    (fun v _ => hasDerivWithinAt_const v _ 0)
    (fun _ _ => by simp) (fun _ _ => by simp) rfl (fun _ _ => one_ne_zero) (fun _ _ => by simp)

/-! ### α-IV.2:波面に沿う跳びの輸送 -/

/-- α-IV.2:両側の W_uv が波面の共通の値 G(v)(= Ω W(1 − W²)/(2r²) の共通の跡)で決まるなら、
  [W_u] は波面に沿って一定(角での値のまま運ばれる) -/
theorem rj_Wu_transport {v0 v1 : ℝ} {Wup Wum Wuvp Wuvm Gf : ℝ → ℝ}
    (hp : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wup (Wuvp v) (Icc v0 v1) v)
    (hm : ∀ v ∈ Icc v0 v1, HasDerivWithinAt Wum (Wuvm v) (Icc v0 v1) v)
    (sP : ∀ v ∈ Icc v0 v1, Wuvp v = Gf v) (sM : ∀ v ∈ Icc v0 v1, Wuvm v = Gf v) :
    ∀ v ∈ Icc v0 v1, Wup v - Wum v = Wup v0 - Wum v0 := by
  intro v hv
  have h := CFT.S4J.jump_transport (v0 := v0) (v1 := v1) (r := fun _ => 1) (rv := fun _ => 0)
    (q := fun v => (Wup v - Wum v) - (Wup v0 - Wum v0)) (q' := fun v => Wuvp v - Wuvm v)
    (fun v _ => hasDerivWithinAt_const v _ 1)
    (fun v hv => ((hp v hv).sub (hm v hv)).sub_const _)
    (fun v hv => by simp [sP v hv, sM v hv]) (by simp) (fun _ _ => one_ne_zero) v hv
  simp only at h
  linarith

/-- α-IV.2(角の値):帽子の初期データ W_C(u) = sin(u/(√2ℓ))(v = 0 の上)の u 微分は角 u = 0 で 1/(√2ℓ) -/
theorem rj_capWu_corner (l : ℝ) :
    HasDerivAt (fun u => sin (u / (Real.sqrt 2 * l))) (1 / (Real.sqrt 2 * l)) 0 := by
  have h := ((hasDerivAt_id' (0 : ℝ)).div_const (Real.sqrt 2 * l)).sin
  simpa using h

/-- α-IV.2(角での [r_uu]):拘束 C_u = r_uu − 2σ_u r_u + 2ℓ²W_u²/r = 0 を両側で使い、角(r = ℓ、r_u = 0)で
  帽子 W_u = 1/(√2ℓ)、首 W_u = 0 なら [r_uu] = −1/ℓ(帽子の r = ℓcos²(u/(√2ℓ)) の 2 階微分と一致) -/
theorem rj_ruu_corner (l σu Wup Wum rupp rumm : ℝ) (hl : l ≠ 0)
    (hP : rupp - 2 * σu * 0 + 2 * l ^ 2 * Wup ^ 2 / l = 0)
    (hM : rumm - 2 * σu * 0 + 2 * l ^ 2 * Wum ^ 2 / l = 0)
    (hWp : Wup = 1 / (Real.sqrt 2 * l)) (hWm : Wum = 0) :
    rupp - rumm = -1 / l := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hW : Wup ^ 2 = 1 / (2 * l ^ 2) := by rw [hWp, div_pow, mul_pow, h2, one_pow]
  have e1 : rupp = -(2 * l ^ 2 * Wup ^ 2 / l) := by linarith
  have e2 : rumm = -(2 * l ^ 2 * Wum ^ 2 / l) := by linarith
  rw [e1, e2, hW, hWm]
  field_simp <;> ring

end CFT.RJ
