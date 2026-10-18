/-
  α-III.9(Z23):非球対称の非ヌル接合(一般の Israel 条件)

  超曲面 Σ(次元 n、時間的または空間的)の誘導計量 h(n×n の可逆な対称行列、成分は任意の枠)、
  外曲率の跳び J = [K_ab](両側の K の差)、トレース [K] = tr(h⁻¹J)。
  Israel の条件(Lanczos 方程式)
    S_ab = −(1/(8πG))([K_ab] − h_ab[K])
  について:
    * israel_trace:tr(h⁻¹S) = (n − 1)[K]/(8πG)
    * israel_inverse:n ≠ 1 なら [K_ab] = −8πG(S_ab − h_ab·tr(h⁻¹S)/(n − 1))
      (n = 3 では [K_ab] = −8πG(S_ab − ½h_ab S)、教科書の形)
    * israel_no_shell:殻がない(S = 0)⇔ 外曲率が連続([K_ab] = 0)
  球対称の空間的な切り口(AlphaIII_Junction)は、K_ab の跳びが [r′]/r の形になる特別な場合。
  未形式化:ヌルな面(Barrabès–Israel の横断曲率)、超曲面上の分布としての Einstein 方程式から
  Israel 条件そのものを導くこと(ここでは条件を出発点とする)。
-/
import CFT.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace CFT.Israel

variable {n : ℕ}

/-- h に関するトレース tr(h⁻¹ A) -/
noncomputable def trh (h A : Matrix (Fin n) (Fin n) ℝ) : ℝ := (h⁻¹ * A).trace

/-- Israel の条件で決まる表面応力 S = −(1/(8πG))(J − tr_h(J)·h) -/
noncomputable def surfS (G : ℝ) (h J : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (-(1 / (8 * Real.pi * G))) • (J - trh h J • h)

theorem trh_self (h : Matrix (Fin n) (Fin n) ℝ) (hd : IsUnit h.det) : trh h h = n := by
  simp [trh, nonsing_inv_mul h hd, trace_one]

theorem trh_linear (h A B : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) :
    trh h (a • A + b • B) = a * trh h A + b * trh h B := by
  simp [trh, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul]

/-- tr(h⁻¹S) = (n − 1)[K]/(8πG) -/
theorem israel_trace (G : ℝ) (h J : Matrix (Fin n) (Fin n) ℝ) (hd : IsUnit h.det) :
    trh h (surfS G h J) = (n - 1) * trh h J / (8 * Real.pi * G) := by
  have e : surfS G h J = (-(1 / (8 * Real.pi * G))) • J + ((1 / (8 * Real.pi * G)) * trh h J) • h := by
    simp only [surfS, smul_sub, smul_smul]; rw [sub_eq_add_neg, ← neg_smul]; ring_nf
  rw [e, trh_linear, trh_self h hd]; ring

/-- 逆向き:[K_ab] = −8πG(S_ab − h_ab·tr(h⁻¹S)/(n − 1)) -/
theorem israel_inverse (G : ℝ) (hG : G ≠ 0) (h J : Matrix (Fin n) (Fin n) ℝ) (hd : IsUnit h.det)
    (hn : (n : ℝ) ≠ 1) :
    J = (-(8 * Real.pi * G)) • (surfS G h J - (trh h (surfS G h J) / (n - 1)) • h) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn1 : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hn
  have c : 8 * Real.pi * G ≠ 0 := by positivity
  rw [israel_trace G h J hd]
  have e1 : (n - 1) * trh h J / (8 * Real.pi * G) / (n - 1) = trh h J / (8 * Real.pi * G) := by
    field_simp; ring
  rw [e1]
  ext i j
  simp only [surfS, smul_apply, sub_apply, smul_eq_mul]
  field_simp

/-- 殻がない ⇔ 外曲率が連続 -/
theorem israel_no_shell (G : ℝ) (hG : G ≠ 0) (h J : Matrix (Fin n) (Fin n) ℝ) (hd : IsUnit h.det)
    (hn : (n : ℝ) ≠ 1) : surfS G h J = 0 ↔ J = 0 := by
  constructor
  · intro hS
    rw [israel_inverse G hG h J hd hn, hS]; simp [trh]
  · intro hJ; simp [surfS, hJ, trh]

/-- n = 3(4 次元時空の中の超曲面)では [K_ab] = −8πG(S_ab − ½ h_ab S) -/
theorem israel_inverse_three (G : ℝ) (hG : G ≠ 0) (h J : Matrix (Fin 3) (Fin 3) ℝ) (hd : IsUnit h.det) :
    J = (-(8 * Real.pi * G)) • (surfS G h J - ((1 / 2 : ℝ) * trh h (surfS G h J)) • h) := by
  have := israel_inverse (n := 3) G hG h J hd (by norm_num)
  convert this using 4; norm_num; ring

/-- 空間的な切り口の中の球面 r = r₀(外曲率 K = (r′/r)h、平均曲率 H = 2r′/r)では
  表面密度 σ = −[H]/(8πG) が AlphaIII_Junction の σ = −[r′]/(4πG r₀) と一致 -/
theorem sphere_consistency (G r₀ jump : ℝ) (hG : G ≠ 0) (hr : r₀ ≠ 0) :
    -(2 * jump / r₀) / (8 * Real.pi * G) = -jump / (4 * Real.pi * G * r₀) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp; ring

end CFT.Israel
