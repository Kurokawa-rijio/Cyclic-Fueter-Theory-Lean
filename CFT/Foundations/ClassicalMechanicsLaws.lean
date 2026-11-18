/-
  段階 2(質点の力学)の有名方程式(2026-11-18)

  時間の導分 d(d = d/dt)の上の代数で述べる(IX・4-2 と同じ導分代数の流儀)。
  * Kepler 問題(平面、引力 −k r/|r|³、質量 1):ri = 1/r、(x² + y²) ri² = 1、d ri = −(x ẋ + y ẏ) ri³ として
    - `kepler_angular_momentum`:L = x ẏ − y ẋ は保存(面積速度一定、Kepler の第 2 法則)。
    - `kepler_energy`:E = ½(ẋ² + ẏ²) − k/r は保存。
    - `kepler_lrl_x`、`kepler_lrl_y`:Laplace–Runge–Lenz ベクトル A = (ẏL − kx/r, −ẋL − ky/r) は保存。
    - `kepler_orbit`:A·x = L² − k r。|A| = ke とおくと r = (L²/k)/(1 + e cos θ)、軌道は円錐曲線(第 1 法則)。
  * `oscillator_energy`:ẍ = −ω²x なら ẋ² + ω²x²(エネルギーの 2 倍)は保存。
  * 剛体の Euler 方程式 I₁ω̇₁ = (I₂ − I₃)ω₂ω₃(巡回)について
    `rigid_energy`(Σ I_i ω_i²、回転エネルギー T の 2 倍)と `rigid_angular_momentum`(|L|² = Σ I_i²ω_i²)は保存。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

namespace CFT.Mechanics

variable {S : Type*} [Field S] [CharZero S]
variable (d : Derivation ℤ S S)

section Kepler

variable (x y vx vy ri k : S)

/-- Kepler 問題の仮定 -/
structure KeplerMotion : Prop where
  dx : d x = vx
  dy : d y = vy
  dvx : d vx = -(k * x * ri ^ 3)
  dvy : d vy = -(k * y * ri ^ 3)
  dri : d ri = -((x * vx + y * vy) * ri ^ 3)
  dk : d k = 0
  norm : (x ^ 2 + y ^ 2) * ri ^ 2 = 1

theorem kepler_angular_momentum (h : KeplerMotion d x y vx vy ri k) :
    d (x * vy - y * vx) = 0 := by
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, h.dx, h.dy, h.dvx, h.dvy]
  ring

theorem kepler_energy (h : KeplerMotion d x y vx vy ri k) :
    d ((1/2 : S) * (vx * vx + vy * vy) - k * ri) = 0 := by
  have h12 : d (1/2 : S) = 0 := by
    have e := map_nsmul d 2 (1/2 : S)
    rw [nsmul_eq_mul, nsmul_eq_mul, show ((2:ℕ):S) * (1/2) = 1 by norm_num,
      Derivation.map_one_eq_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (by norm_num)
  simp only [map_sub, map_add, Derivation.leibniz, smul_eq_mul, h.dvx, h.dvy, h.dri, h.dk, h12]
  ring

theorem kepler_lrl_x (h : KeplerMotion d x y vx vy ri k) :
    d (vy * (x * vy - y * vx) - k * x * ri) = 0 := by
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, h.dx, h.dy, h.dvx, h.dvy, h.dri, h.dk]
  linear_combination (k * vx * ri) * h.norm

theorem kepler_lrl_y (h : KeplerMotion d x y vx vy ri k) :
    d (-(vx * (x * vy - y * vx)) - k * y * ri) = 0 := by
  simp only [map_sub, map_neg, Derivation.leibniz, smul_eq_mul, h.dx, h.dy, h.dvx, h.dvy, h.dri,
    h.dk]
  linear_combination (k * vy * ri) * h.norm

/-- 軌道の式 A·x = L² − k r(r ri = 1、x² + y² = r²) -/
theorem kepler_orbit (r : S) (hr2 : x ^ 2 + y ^ 2 = r ^ 2) (hri : r * ri = 1) :
    (vy * (x * vy - y * vx) - k * x * ri) * x + (-(vx * (x * vy - y * vx)) - k * y * ri) * y
      = (x * vy - y * vx) ^ 2 - k * r := by
  linear_combination (-(k * ri)) * hr2 + (-(k * r)) * hri

end Kepler

/-- 調和振動子のエネルギー保存 -/
theorem oscillator_energy (x v ω : S) (hx : d x = v) (hv : d v = -(ω ^ 2 * x)) (hω : d ω = 0) :
    d (v * v + ω * ω * (x * x)) = 0 := by
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hx, hv, hω]
  ring

/-- 剛体の Euler 方程式からの 2T = Σ I_i ω_i²(回転エネルギーの 2 倍)の保存 -/
theorem rigid_energy (w1 w2 w3 I1 I2 I3 : S) (hI1 : d I1 = 0) (hI2 : d I2 = 0) (hI3 : d I3 = 0)
    (e1 : I1 * d w1 = (I2 - I3) * w2 * w3) (e2 : I2 * d w2 = (I3 - I1) * w3 * w1)
    (e3 : I3 * d w3 = (I1 - I2) * w1 * w2) :
    d (I1 * (w1 * w1) + I2 * (w2 * w2) + I3 * (w3 * w3)) = 0 := by
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hI1, hI2, hI3]
  linear_combination (2 * w1) * e1 + (2 * w2) * e2 + (2 * w3) * e3

/-- 剛体の角運動量の大きさの保存 -/
theorem rigid_angular_momentum (w1 w2 w3 I1 I2 I3 : S) (hI1 : d I1 = 0) (hI2 : d I2 = 0)
    (hI3 : d I3 = 0)
    (e1 : I1 * d w1 = (I2 - I3) * w2 * w3) (e2 : I2 * d w2 = (I3 - I1) * w3 * w1)
    (e3 : I3 * d w3 = (I1 - I2) * w1 * w2) :
    d ((I1 * w1) * (I1 * w1) + (I2 * w2) * (I2 * w2) + (I3 * w3) * (I3 * w3)) = 0 := by
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hI1, hI2, hI3]
  linear_combination (2 * I1 * w1) * e1 + (2 * I2 * w2) * e2 + (2 * I3 * w3) * e3

end CFT.Mechanics
