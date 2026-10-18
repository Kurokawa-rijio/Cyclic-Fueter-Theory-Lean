/-
  α-VII.8(Z28-f):B − L の値の群論的な導出(Pati–Salam 型の埋め込み SU(4)_C ⊃ SU(3)_C)

  クォークの 3 色とレプトンを 4 つ目の色とみなし、B − L を SU(4) の対角生成子 X = diag(d₀, d₁, d₂, d₃) とする。
    * bl_commute_color:diag(d) が色の入れ替え行列 P01, P12(SU(3) の Weyl 群の元)と可換なら d₀ = d₁ = d₂
    * bl_direction:さらに跡ゼロ(su(4) の元)なら X = a·diag(1, 1, 1, −3)(向きは一意)
    * bl_normalization:規格化は一つの入力で決まる。ν_L が中性
      (Q = T₃L + T₃R + X/2、ν_L は T₃L = 1/2, T₃R = 0)なら レプトンの B−L = −1、クォークの B−L = 1/3
    * bl_charges:このとき一世代の電荷は 0, −1, 2/3, −1/3(AlphaVII_N1 の表の X の値が導かれる)
    * bl_anomaly_*:U(1)_{B−L} のゲージ anomaly は右手のニュートリノを含めた 16 成分で相殺
      (Σ(B−L) = 0、Σ(B−L)³ = 0)、右手のニュートリノがないと相殺しない
  未形式化:四元数の幾何からこの埋め込み(SU(4) ⊃ SU(3) × U(1)_{B−L})自体を導く写像。
-/
import CFT.Basic

namespace CFT.BL

open Matrix

/-- 色 0 と 1、1 と 2 の入れ替え行列(SU(3)_C の Weyl 群の元、4 つ目の色は動かさない) -/
def P01 : Matrix (Fin 4) (Fin 4) ℚ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
def P12 : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

/-- 色の入れ替えと可換 ⇒ 3 色で値が等しい -/
theorem bl_commute_color (d : Fin 4 → ℚ) (h01 : diagonal d * P01 = P01 * diagonal d)
    (h12 : diagonal d * P12 = P12 * diagonal d) : d 0 = d 1 ∧ d 1 = d 2 := by
  have a := congrFun (congrFun h01 0) 1
  have b := congrFun (congrFun h12 1) 2
  simp [P01, P12, Matrix.mul_apply, Fin.sum_univ_four] at a b
  exact ⟨a, b⟩

/-- 跡ゼロも課すと d = a·(1, 1, 1, −3):向きは一意 -/
theorem bl_direction (d : Fin 4 → ℚ) (h01 : diagonal d * P01 = P01 * diagonal d)
    (h12 : diagonal d * P12 = P12 * diagonal d) (htr : (diagonal d).trace = 0) :
    d = fun i => d 0 * ![1, 1, 1, -3] i := by
  obtain ⟨e1, e2⟩ := bl_commute_color d h01 h12
  simp [Matrix.trace, Fin.sum_univ_four] at htr
  funext i; fin_cases i <;> simp <;> linarith

/-- ν_L が中性(1/2 + 0 + X_lep/2 = 0)なら、レプトン −1、クォーク 1/3 -/
theorem bl_normalization (a : ℚ) (hnu : (1 / 2 : ℚ) + 0 + (a * (-3)) / 2 = 0) :
    a * (-3) = -1 ∧ a * 1 = 1 / 3 := by
  constructor <;> linarith

/-- 規格化した B−L から電荷 Q = T₃L + T₃R + (B−L)/2 を計算すると一世代の値になる -/
theorem bl_charges (a : ℚ) (hnu : (1 / 2 : ℚ) + 0 + (a * (-3)) / 2 = 0) :
    ((1 / 2 : ℚ) + (a * (-3)) / 2 = 0) ∧ ((-1 / 2 : ℚ) + (a * (-3)) / 2 = -1) ∧
    ((1 / 2 : ℚ) + a / 2 = 2 / 3) ∧ ((-1 / 2 : ℚ) + a / 2 = -1 / 3) := by
  have ha : a = 1 / 3 := by linarith
  subst ha; norm_num

/-- 左手 Weyl で数えた一世代 16 成分の B−L(右手の場は共役なので符号が反転) -/
def blWeyl16 : List (ℚ × ℚ) :=
  -- (多重度, B−L):Q_L(6)、u_Rᶜ(3)、d_Rᶜ(3)、L(2)、e_Rᶜ(1)、ν_Rᶜ(1)
  [(6, 1/3), (3, -1/3), (3, -1/3), (2, -1), (1, 1), (1, 1)]

theorem bl_anomaly_linear : (blWeyl16.map fun f => f.1 * f.2).sum = 0 := by norm_num [blWeyl16]
theorem bl_anomaly_cubic : (blWeyl16.map fun f => f.1 * f.2 ^ 3).sum = 0 := by norm_num [blWeyl16]

/-- 右手のニュートリノを除くと相殺しない -/
theorem bl_anomaly_needs_nuR :
    ((blWeyl16.take 5).map fun f => f.1 * f.2 ^ 3).sum ≠ 0 := by norm_num [blWeyl16]

/-- 右手のニュートリノがないと、一世代あたり Σ(B−L) = −1(重力混合)、Σ(B−L)³ = −1(U(1)_{B−L}³) -/
theorem bl_anomaly_without_nuR :
    ((blWeyl16.take 5).map fun f => f.1 * f.2).sum = -1 ∧
    ((blWeyl16.take 5).map fun f => f.1 * f.2 ^ 3).sum = -1 := by
  norm_num [blWeyl16]

/-- 三世代では −3 -/
theorem bl_anomaly_three_generations :
    3 * ((blWeyl16.take 5).map fun f => f.1 * f.2 ^ 3).sum = -3 := by
  norm_num [blWeyl16]

end CFT.BL
