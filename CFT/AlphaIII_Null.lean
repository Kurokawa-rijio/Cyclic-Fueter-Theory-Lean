/-
  α-III.9(Z23)の残り:ヌルな面の接合(球対称の Barrabès–Israel)を、分布としての Einstein 方程式から導く

  二重ヌル座標 ds² = −2e^{2σ} du dv + r² dΩ²。面 u = u₀ はヌル(生成子 ∂_v)。
  Einstein 方程式の uu 成分(Raychaudhuri の式、標準の公式で入力):
    r_uu − 2σ_u r_u = −4πG r T_uu
  ヌルな殻:T_uu = T_正則 + μ δ(u − u₀)(μ は殻の面密度)。v を固定した線に沿って、r と σ は連続、
  r_u は u₀ で跳んでよい。
  定理:
    * null_shell_from_weak:各側で uu 方程式が成り立ち、全体で分布として
        −∫ r_u φ′ = ∫ (2σ_u r_u − 4πG r T_正則) φ − 4πG r₀ μ φ(u₀)
      がすべての試験関数(両端で 0、各側で C¹)について成り立つなら μ = −[r_u]/(4πG r₀)。
      条件を仮定に置かず、δ の係数は部分積分(weak_second_derivative)と試験関数 (u − a)(b − u)
      から出る
    * null_no_shell_iff:殻なし ⇔ [r_u] = 0
    * null_ruu_jump:殻なしなら [r_uu] = −4πG r₀ [T_uu](σ_u、r_u が連続)
    * null_ruu_jump_ym:YM の 4πG T_uu = 2W_u²/r²(AlphaIV の単位)で [r_uu] = −(2/r₀)[W_u²]
      (AlphaIV の ruu_jump と一致)
  ダンベルでは:接合は [r] = [r′] = 0(Z1、AlphaIntegrals の junction_jumps)なので、接合から出る光円錐の
  上で r は C¹ で殻はなく、跳ぶのは W_u と r_uu だけ(波面の輸送 α-IV.2)。
  外部に残るもの:G_uu = −(2/r)(r_uu − 2σ_u r_u) の曲率の計算(教科書の公式)。
  非球対称なヌル面(一般の Barrabès–Israel)は扱わない(台帳の命題は球対称)。
-/
import CFT.AlphaIII_Junction

open Real intervalIntegral Set

namespace CFT.Null

/-- 試験関数 φ = (u − a)(b − u) の微分 -/
theorem tent_deriv (a b u : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (fun u => (u - a) * (b - u)) ((b - u) - (u - a)) s u := by
  have h := ((hasDerivAt_id u).sub_const a).mul ((hasDerivAt_id u).const_sub b)
  simp only [id] at h
  convert h.hasDerivWithinAt using 1; ring

/-- 分布としての uu 方程式から、ヌルな殻の面密度 μ = −[r_u]/(4πG r₀) -/
theorem null_shell_from_weak {a u₀ b G r₀ μ : ℝ} (hau : a < u₀) (hub : u₀ < b)
    (hG : G ≠ 0) (hr : r₀ ≠ 0)
    {pm pp qm qp Sm Sp : ℝ → ℝ}
    (hpm : ∀ x ∈ Icc a u₀, HasDerivWithinAt pm (qm x) (Icc a u₀) x)
    (hpp : ∀ x ∈ Icc u₀ b, HasDerivWithinAt pp (qp x) (Icc u₀ b) x)
    (hqm : IntervalIntegrable qm MeasureTheory.volume a u₀)
    (hqp : IntervalIntegrable qp MeasureTheory.volume u₀ b)
    -- 各側の uu 方程式(r_uu = 2σ_u r_u − 4πG r T_正則 =: S)
    (sideM : ∀ x ∈ Icc a u₀, qm x = Sm x) (sideP : ∀ x ∈ Icc u₀ b, qp x = Sp x)
    -- 分布としての方程式(すべての試験関数で)
    (weak : ∀ φ φ' : ℝ → ℝ,
      (∀ x ∈ Icc a u₀, HasDerivWithinAt φ (φ' x) (Icc a u₀) x) →
      (∀ x ∈ Icc u₀ b, HasDerivWithinAt φ (φ' x) (Icc u₀ b) x) →
      Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..u₀, pm x * φ' x) + ∫ x in u₀..b, pp x * φ' x)
        = (∫ x in a..u₀, Sm x * φ x) + (∫ x in u₀..b, Sp x * φ x) - 4 * π * G * r₀ * μ * φ u₀) :
    μ = -(pp u₀ - pm u₀) / (4 * π * G * r₀) := by
  set φ : ℝ → ℝ := fun u => (u - a) * (b - u) with hφ
  set φ' : ℝ → ℝ := fun u => (b - u) - (u - a) with hφ'
  have dφm : ∀ x ∈ Icc a u₀, HasDerivWithinAt φ (φ' x) (Icc a u₀) x := fun x _ => tent_deriv a b x _
  have dφp : ∀ x ∈ Icc u₀ b, HasDerivWithinAt φ (φ' x) (Icc u₀ b) x := fun x _ => tent_deriv a b x _
  have cφ' : Continuous φ' := by simp only [hφ']; fun_prop
  have hw := weak φ φ' dφm dφp cφ' (by simp [hφ]) (by simp [hφ])
  have hparts := CFT.Junction.weak_second_derivative hau.le hub.le hpm hpp dφm dφp hqm hqp
    (cφ'.intervalIntegrable _ _) (cφ'.intervalIntegrable _ _) (by simp [hφ]) (by simp [hφ])
  have e1 : ∫ x in a..u₀, qm x * φ x = ∫ x in a..u₀, Sm x * φ x := by
    apply integral_congr; intro x hx; rw [uIcc_of_le hau.le] at hx; simp only; rw [sideM x hx]
  have e2 : ∫ x in u₀..b, qp x * φ x = ∫ x in u₀..b, Sp x * φ x := by
    apply integral_congr; intro x hx; rw [uIcc_of_le hub.le] at hx; simp only; rw [sideP x hx]
  rw [hparts, e1, e2] at hw
  have hpos : φ u₀ ≠ 0 := by
    simp only [hφ]; exact mul_ne_zero (by linarith) (by linarith)
  have key : ((pp u₀ - pm u₀) + 4 * π * G * r₀ * μ) * φ u₀ = 0 := by linarith
  have k2 := (mul_eq_zero.mp key).resolve_right hpos
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  linarith

/-- 殻なし ⇔ [r_u] = 0 -/
theorem null_no_shell_iff (G r₀ jump : ℝ) (hG : G ≠ 0) (hr : r₀ ≠ 0) :
    -jump / (4 * π * G * r₀) = 0 ↔ jump = 0 :=
  CFT.Junction.no_shell_iff G r₀ jump hG hr

/-- 殻なし(r_u 連続)なら、各側の uu 方程式から [r_uu] = −4πG r₀ [T_uu] -/
theorem null_ruu_jump (G r₀ su ru Tp Tm ruup ruum : ℝ)
    (hp : ruup = 2 * su * ru - 4 * π * G * r₀ * Tp) (hm : ruum = 2 * su * ru - 4 * π * G * r₀ * Tm) :
    ruup - ruum = -(4 * π * G * r₀) * (Tp - Tm) := by
  rw [hp, hm]; ring

/-- YM の 4πG T_uu = 2W_u²/r²(AlphaIV の単位)で [r_uu] = −(2/r₀)[W_u²] -/
theorem null_ruu_jump_ym (r₀ su ru Wup Wum ruup ruum : ℝ) (hr : r₀ ≠ 0)
    (hp : ruup = 2 * su * ru - r₀ * (2 * Wup ^ 2 / r₀ ^ 2))
    (hm : ruum = 2 * su * ru - r₀ * (2 * Wum ^ 2 / r₀ ^ 2)) :
    ruup - ruum = -(2 / r₀) * (Wup ^ 2 - Wum ^ 2) := by
  rw [hp, hm]; field_simp; ring

end CFT.Null
