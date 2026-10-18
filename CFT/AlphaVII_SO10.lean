/-
  α-VII.8(Z28-f):内部空間 S⁹ から Pati–Salam への写像と一世代の電荷(台帳 40022e17 の経路)

  丸い S⁹ ⊂ R¹⁰ の等長群は SO(10)(Kaluza–Klein で四次元のゲージ対称性になる)。Z28-d の楕円体変形
  x_ρ = (ρ y_H, y₆)(R¹⁰ = R⁴ ⊕ R⁶)は、ρ ≠ 1 で対称性を SO(4) × SO(6) に破る:
    * ellipsoid_breaks:diag(ρ,ρ,ρ,ρ,1,…,1)(ρ ≠ 1)と可換な行列は R⁴ と R⁶ をまたぐ成分が 0
  局所的に SO(6) ≅ SU(4)_C、SO(4) ≅ SU(2)_L × SU(2)_R(Pati–Salam)。
  S⁹ の最低 Dirac 固有空間は 16 次元のスピノル表現(台帳)。その重み(±1/2)⁵(マイナスが偶数個)を
  2 倍した符号 e ∈ {±1}⁵ で表し、R⁶ 側の三つ(e₀, e₁, e₂)と R⁴ 側の二つ(e₃, e₄)に分ける:
    B − L = −(2/3)(w₀+w₁+w₂)、T₃L = (w₃+w₄)/2、T₃R = (w₃−w₄)/2、Q = T₃L + T₃R + (B−L)/2。
    * spinor16_charges:16 個の重みの (6Q, 3(B−L), 4T₃L, 4T₃R) は、標準模型の一世代
      (Q_L, L, u^c, d^c, e^c, ν^c、左手 Weyl)の表と並べ替えを除いて一致
    * higgs_bidoublet:ベクトル表現 10 のうち R⁴ 側 ±e₃, ±e₄ は (1,2,2)(Higgs の二重項):
      電荷 1, 0, 0, −1、中性成分 ±e₄ の超電荷 Y = ∓1/2
    * yukawa_weight:16·16·10 の重みの和が 0 になる組がある(Yukawa 結合の存在の重みの条件)
  B−L の向きと規格化は AlphaVII_BL(跡ゼロと ν_L の中性)と一致する。
  未形式化:最低 Dirac モードが質量ゼロのカイラルな場になること(台帳でも未証明:丸い S⁹ は
  Lichnerowicz により正の固有値)、Yukawa の SO(10) 不変な縮約(C Γ^a)の構成。
-/
import CFT.Basic

open Matrix

namespace CFT.SO10

/-- 対角行列 diag(p) と可換なら、p_i ≠ p_j の成分は 0 -/
theorem ellipsoid_breaks {n : ℕ} (p : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (h : diagonal p * X = X * diagonal p) (i j : Fin n) (hij : p i ≠ p j) : X i j = 0 := by
  have := congrFun (congrFun h i) j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have : (p i - p j) * X i j = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hij)

/-- 16 次元スピノルの重み(2 倍した符号、マイナスが偶数個) -/
def signs : List (List ℤ) :=
  ((((([1, -1].flatMap fun a => [1, -1].flatMap fun b => [1, -1].flatMap fun c =>
    [1, -1].flatMap fun d => [1, -1].map fun e => [a, b, c, d, e]))))).filter
    (fun l => (l.count (-1)) % 2 == 0)

/-- (6Q, 3(B−L), 4T₃L, 4T₃R) -/
def charges (l : List ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let s := l.getD 0 0 + l.getD 1 0 + l.getD 2 0
  (3 * l.getD 3 0 - s, -s, l.getD 3 0 + l.getD 4 0, l.getD 3 0 - l.getD 4 0)

/-- 標準模型の一世代(左手 Weyl):Q_L(3 色 × 2)、L、u^c、d^c、e^c、ν^c -/
def oneGeneration : List (ℤ × ℤ × ℤ × ℤ) :=
  [(4, 1, 2, 0), (4, 1, 2, 0), (4, 1, 2, 0),        -- u_L:Q = 2/3, B−L = 1/3, T₃L = 1/2
   (-2, 1, -2, 0), (-2, 1, -2, 0), (-2, 1, -2, 0),  -- d_L:Q = −1/3
   (0, -3, 2, 0), (-6, -3, -2, 0),                  -- ν_L, e_L
   (-4, -1, 0, -2), (-4, -1, 0, -2), (-4, -1, 0, -2), -- u^c:Q = −2/3, T₃R = −1/2
   (2, -1, 0, 2), (2, -1, 0, 2), (2, -1, 0, 2),     -- d^c:Q = 1/3
   (6, 3, 0, 2), (0, 3, 0, -2)]                     -- e^c:Q = 1、ν^c:Q = 0

theorem spinor16_count : signs.length = 16 := by decide

theorem spinor16_charges : (signs.map charges).Perm oneGeneration := by decide

/-- ベクトル表現 10 の R⁴ 側の重み ±e₃, ±e₄(重み w は 1 倍の単位):
  (6Q, 6Y)、Q = T₃L + T₃R、Y = T₃R(B−L = 0) -/
def higgsWeights : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1)]  -- (w₃, w₄)
def higgsQY (w : ℤ × ℤ) : ℤ × ℤ := (3 * (w.1 + w.2) + 3 * (w.1 - w.2), 3 * (w.1 - w.2))

theorem higgs_bidoublet :
    higgsWeights.map higgsQY = [(6, 3), (-6, -3), (0, -3), (0, 3)] := by decide

/-- 16·16·10 の重みの和が 0 になる組(2 倍の単位):例えば e₄ 成分で釣り合う -/
theorem yukawa_weight :
    ∃ w ∈ signs, ∃ w' ∈ signs, List.zipWith (· + ·) (List.zipWith (· + ·) w w') [0, 0, 0, 0, -2] = [0, 0, 0, 0, 0] := by
  refine ⟨[1, 1, 1, 1, 1], by decide, [-1, -1, -1, -1, 1], by decide, by decide⟩

end CFT.SO10
