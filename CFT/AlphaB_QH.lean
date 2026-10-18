/-
  B(ダンベルの基礎):量子球面 Q と相対論の双曲面(質量殻)の接合

  運動量空間の三つの面(静止質量 m > 0、E = √(m² + p²)、p は動径の運動量):
    Q(量子球面):点 (w, x) = (m/E, p/E)、w² + x² = 1(U(p) = (m − iσ·p)/E、AlphaVII_Chirality の shell_unit)
    H(質量殻の双曲面):点 (X₀, u) = (E/m, p/m)、X₀² − u² = 1(4 元速度)
    N(Newton):X₀ = 1 の平面(接点での共通の接平面)
  * qh_reciprocal:w·X₀ = 1、x = u/X₀(Q の高さは H の高さの逆数:同じ固有速度 u の上で
    Q と H は逆数の関係。Q の北半球全体 = H の一枚の葉、赤道 = 光円錐の無限遠、南半球 = m < 0 の葉)
  * gudermann:ラピディティ η(p = m sinh η)に対し、Q の極角 χ = gd η = arctan(sinh η) は
    sin χ = tanh η = v(速度)、cos χ = 1/cosh η = 1/γ、tan χ = sinh η = p/m
    (台帳 Z10 の Gudermann 関数がここにも現れる:Q の角度 = ラピディティの Gudermann 関数)
  * gd_deriv:dχ/dη = 1/cosh η(Q の弧長 = 1/γ で重みをつけたラピディティ)
  * conformal:Q の計量 = (H の計量)/E²(ds_Q² = dχ² + sin²χ dφ²、ds_H² = m²(dη² + sinh²η dφ²))
    ⇒ 任意の領域 R の面積は Area_Q(R) = ∫_R dA_H/E²(2 次元)、体積は ∫_R dV_H/E³(3 次元)
  傾き:
    * slope_H:双曲面 E(p) = √(m² + p²) の傾き dE/dp = p/E = v(速度)
    * slope_Q:Q の断面 w(x) = √(1 − x²) の傾きは x = p/E で −p/m(固有速度、γv)
  法線:
    * normal_H:Minkowski 内積で、接ベクトル (v, 1) と n = (E/m, p/m) は直交、⟨n, n⟩ = −1:法線 = 4 元速度
    * normal_Q:Euclid 内積で、接ベクトル (−p/m, 1) と N = (m/E, p/E) は直交、|N| = 1:法線 = 状態 U そのもの
    * contact:接点 p = 0 では n = N = (1, 0)(静止系の時間の向き)、運動量 (E, p) = m·n:
      接点から垂直に出るものは静止系の 4 元速度で、その長さが静止質量 m
  曲がり方(接点で反対向き):
    * curv_H:X₀(u) = √(1 + u²) の 2 階微分は u = 0 で +1
    * curv_Q:w(u) = 1/√(1 + u²) の 2 階微分は u = 0 で −1
    * cayley_klein:混在の族 Σ_κ:X₀ = √(1 − κ X²) はすべて接点 (1, 0) を通り傾き 0、
      2 階微分 −κ。κ = 1 が Q、κ = −1 が H、κ = 0 が Newton(速度の単位で κ = ±1/c²)
  面積(2+1 次元の図、p ∈ R²):
    * area_H:H の円板(ラピディティ η₀ まで)の面積 2πm²(cosh η₀ − 1) = 2πm(E₀ − m)(運動エネルギーに比例)
    * area_Q:Q の帽子(χ₀ = gd η₀ まで)の面積 2π(1 − cos χ₀) = 2π(1 − m/E₀)
    * area_ratio:Area_H = m E₀ · Area_Q、半球全体(E₀ → ∞)は 2π
    * gauss_bonnet_H:H の円板で ∫K dA + ∮k_g = 2π(曲率 −1/m²、境界の測地曲率 coth η₀/m)
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals

open Real

namespace CFT.QH

/-- 逆数の関係 -/
theorem qh_reciprocal (m p E : ℝ) (hm : 0 < m) (hE : 0 < E) (hEp : E ^ 2 = m ^ 2 + p ^ 2) :
    (m / E) * (E / m) = 1 ∧ p / E = (p / m) / (E / m) ∧
    (m / E) ^ 2 + (p / E) ^ 2 = 1 ∧ (E / m) ^ 2 - (p / m) ^ 2 = 1 := by
  refine ⟨by field_simp, by field_simp, ?_, ?_⟩
  · field_simp; linarith
  · field_simp; linarith

/-- Gudermann 関数:sin(gd η) = tanh η、cos(gd η) = 1/cosh η、tan(gd η) = sinh η -/
theorem gudermann (η : ℝ) :
    sin (arctan (sinh η)) = sinh η / cosh η ∧ cos (arctan (sinh η)) = 1 / cosh η ∧
    tan (arctan (sinh η)) = sinh η := by
  have hc : √(1 + sinh η ^ 2) = cosh η := by
    rw [show 1 + sinh η ^ 2 = cosh η ^ 2 by rw [cosh_sq]; ring]
    exact Real.sqrt_sq (cosh_pos η).le
  refine ⟨?_, ?_, tan_arctan _⟩
  · rw [sin_arctan, hc]
  · rw [cos_arctan, hc]

/-- 運動量で書くと:p = m sinh η、E = m cosh η なら sin χ = p/E、cos χ = m/E -/
theorem gudermann_momentum (m η : ℝ) (hm : 0 < m) :
    sin (arctan (sinh η)) = (m * sinh η) / (m * cosh η) ∧
    cos (arctan (sinh η)) = m / (m * cosh η) := by
  obtain ⟨h1, h2, -⟩ := gudermann η
  have hc := (cosh_pos η).ne'
  refine ⟨?_, ?_⟩
  · rw [h1]; field_simp; ring
  · rw [h2]; field_simp

theorem gd_deriv (η : ℝ) : HasDerivAt (fun t => arctan (sinh t)) (1 / cosh η) η := by
  have h := (hasDerivAt_sinh η).arctan
  convert h using 1
  rw [show 1 + sinh η ^ 2 = cosh η ^ 2 by rw [cosh_sq]; ring]
  field_simp [(cosh_pos η).ne']
  ring

/-- Q の計量 = H の計量 / E²:(gd′)² = m²/(m cosh η)²·1、sin²(gd η) = m² sinh²η/(m cosh η)² -/
theorem conformal (m η : ℝ) (hm : 0 < m) :
    (1 / cosh η) ^ 2 = (m ^ 2 * 1) / (m * cosh η) ^ 2 ∧
    sin (arctan (sinh η)) ^ 2 = (m ^ 2 * sinh η ^ 2) / (m * cosh η) ^ 2 := by
  have hc := (cosh_pos η).ne'
  refine ⟨by field_simp; ring, ?_⟩
  rw [(gudermann η).1]; field_simp; ring

/-- 双曲面の傾き:dE/dp = p/E -/
theorem slope_H (m p : ℝ) (hm : 0 < m) :
    HasDerivAt (fun q => √(m ^ 2 + q ^ 2)) (p / √(m ^ 2 + p ^ 2)) p := by
  have hne : m ^ 2 + p ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_id p).pow 2).const_add (m ^ 2) |>.sqrt hne
  convert h using 1; simp; field_simp; ring

/-- Q の断面の傾き:w(x) = √(1 − x²) の傾きは −x/√(1 − x²)、x = p/E では −p/m -/
theorem slope_Q (x : ℝ) (hx : x ^ 2 < 1) :
    HasDerivAt (fun y => √(1 - y ^ 2)) (-x / √(1 - x ^ 2)) x := by
  have hne : 1 - x ^ 2 ≠ 0 := by linarith
  have h := ((hasDerivAt_id x).pow 2).const_sub 1 |>.sqrt hne
  convert h using 1
  simp only [id, Nat.cast_ofNat, pow_one, mul_one, Nat.add_one_sub_one]
  rw [neg_div, neg_div, mul_div_mul_left _ _ (two_ne_zero)]

theorem slope_Q_value (m p : ℝ) (hm : 0 < m) :
    -(p / √(m ^ 2 + p ^ 2)) / √(1 - (p / √(m ^ 2 + p ^ 2)) ^ 2) = -(p / m) := by
  have hE : 0 < √(m ^ 2 + p ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hE2 : √(m ^ 2 + p ^ 2) ^ 2 = m ^ 2 + p ^ 2 := Real.sq_sqrt (by positivity)
  have h1 : 1 - (p / √(m ^ 2 + p ^ 2)) ^ 2 = (m / √(m ^ 2 + p ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, hE2]; field_simp
  rw [h1, Real.sqrt_sq (div_pos hm hE).le]
  field_simp; ring

/-- Minkowski の法線 = 4 元速度 -/
theorem normal_H (m p E : ℝ) (hm : 0 < m) (hE : 0 < E) (hEp : E ^ 2 = m ^ 2 + p ^ 2) :
    -(p / E) * (E / m) + 1 * (p / m) = 0 ∧ -(E / m) ^ 2 + (p / m) ^ 2 = -1 := by
  constructor
  · field_simp; ring
  · rw [div_pow, div_pow, hEp]; field_simp

/-- Euclid の法線 = 状態 U -/
theorem normal_Q (m p E : ℝ) (hm : 0 < m) (hE : 0 < E) (hEp : E ^ 2 = m ^ 2 + p ^ 2) :
    -(p / m) * (m / E) + 1 * (p / E) = 0 ∧ (m / E) ^ 2 + (p / E) ^ 2 = 1 := by
  constructor
  · field_simp; ring
  · field_simp; linarith

/-- 接点 p = 0:二つの法線は (1, 0) で一致し、運動量は m 倍の法線 -/
theorem contact (m : ℝ) (hm : 0 < m) :
    (√(m ^ 2 + 0 ^ 2) / m, (0 : ℝ) / m) = ((1 : ℝ), (0 : ℝ)) ∧
    (m / √(m ^ 2 + 0 ^ 2), (0 : ℝ) / √(m ^ 2 + 0 ^ 2)) = ((1 : ℝ), (0 : ℝ)) ∧
    (√(m ^ 2 + 0 ^ 2), (0 : ℝ)) = (m * 1, m * 0) := by
  have h : √(m ^ 2 + 0 ^ 2) = m := by simp [Real.sqrt_sq hm.le]
  simp [Real.sqrt_sq hm.le, hm.ne']

/-! ### 曲がり方 -/

/-- Σ_κ:f(X) = √(1 − κX²) の微分 -/
theorem ck_deriv (κ X : ℝ) (h : 0 < 1 - κ * X ^ 2) :
    HasDerivAt (fun Y => √(1 - κ * Y ^ 2)) (-(κ * X) / √(1 - κ * X ^ 2)) X := by
  have h' := (((hasDerivAt_id X).pow 2).const_mul κ).const_sub 1 |>.sqrt h.ne'
  convert h' using 1; simp; field_simp; ring

/-- 接点での 2 階微分は −κ(f′(X) = −κX/√(1 − κX²) の X = 0 での微分) -/
theorem cayley_klein (κ : ℝ) :
    HasDerivAt (fun X => -(κ * X) / √(1 - κ * X ^ 2)) (-κ) 0 ∧
    √(1 - κ * 0 ^ 2) = 1 ∧ -(κ * 0) / √(1 - κ * 0 ^ 2) = 0 := by
  refine ⟨?_, by simp, by simp⟩
  have hs : HasDerivAt (fun X => √(1 - κ * X ^ 2)) (-(κ * 0) / √(1 - κ * 0 ^ 2)) 0 :=
    ck_deriv κ 0 (by simp)
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul κ).neg.div hs (by simp)
  convert h using 1; simp

/-- H(κ = −1):X₀ = √(1 + u²) の 2 階微分は +1、Q(κ = 1):w = √(1 − x²) は −1 -/
theorem curv_H_Q :
    HasDerivAt (fun X => -((-1) * X) / √(1 - (-1) * X ^ 2)) 1 0 ∧
    HasDerivAt (fun X => -(1 * X) / √(1 - 1 * X ^ 2)) (-1) 0 := by
  have h1 := (cayley_klein (-1)).1
  have h2 := (cayley_klein 1).1
  exact ⟨by simpa using h1, h2⟩

/-- Q を固有速度 u の上のグラフにすると w(u) = 1/√(1 + u²) = 1/X₀(u)、u = 0 での 2 階微分は −1 -/
theorem curv_Q_over_u :
    HasDerivAt (fun u => -u / √(1 + u ^ 2) ^ 3) (-1) 0 := by
  have hs : HasDerivAt (fun u => √(1 + u ^ 2)) (0 / √(1 + 0 ^ 2)) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).pow 2).const_add 1 |>.sqrt (by norm_num)
    convert this using 1; simp
  have h := (hasDerivAt_id (0 : ℝ)).neg.div (hs.pow 3) (by simp)
  convert h using 1; simp

/-! ### 面積 -/

theorem area_H (m η0 : ℝ) :
    ∫ η in (0 : ℝ)..η0, 2 * π * m ^ 2 * sinh η = 2 * π * m * (m * cosh η0 - m) := by
  have h : ∀ η ∈ Set.uIcc (0 : ℝ) η0, HasDerivAt (fun t => 2 * π * m ^ 2 * cosh t) (2 * π * m ^ 2 * sinh η) η :=
    fun η _ => (hasDerivAt_cosh η).const_mul _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp; ring

theorem area_Q (χ0 : ℝ) : ∫ χ in (0 : ℝ)..χ0, 2 * π * sin χ = 2 * π * (1 - cos χ0) := by
  rw [intervalIntegral.integral_const_mul, integral_sin]; simp

/-- χ₀ = gd η₀ のとき Q の帽子は 2π(1 − m/E₀)、Area_H = m E₀ Area_Q -/
theorem area_ratio (m η0 : ℝ) (hm : 0 < m) :
    2 * π * (1 - cos (arctan (sinh η0))) = 2 * π * (1 - m / (m * cosh η0)) ∧
    2 * π * m * (m * cosh η0 - m) = m * (m * cosh η0) * (2 * π * (1 - m / (m * cosh η0))) := by
  have hc := (cosh_pos η0).ne'
  refine ⟨?_, ?_⟩
  · rw [(gudermann_momentum m η0 hm).2]
  · field_simp; ring

/-- 半球全体の面積 2π -/
theorem hemisphere_area : ∫ χ in (0 : ℝ)..(π / 2), 2 * π * sin χ = 2 * π := by
  rw [area_Q]; simp

/-- H の円板の Gauss–Bonnet:−(1/m²)·Area + (cosh η₀/(m sinh η₀))·(2πm sinh η₀) = 2π -/
theorem gauss_bonnet_H (m η0 : ℝ) (hm : 0 < m) (hη : 0 < η0) :
    -(1 / m ^ 2) * (2 * π * m * (m * cosh η0 - m)) + cosh η0 / (m * sinh η0) * (2 * π * m * sinh η0)
      = 2 * π := by
  have hs : sinh η0 ≠ 0 := (sinh_pos_iff.2 hη).ne'
  field_simp; ring

end CFT.QH
