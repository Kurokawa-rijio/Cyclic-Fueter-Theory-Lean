/-
  α-V.1 (Z17):Dirac 方程式から Pauli 方程式へ。Foldy–Wouthuysen の展開の次数を明示する

  設定(作用素の代数)
  * A は ℂ 上の(非可換な)代数。b = β(b² = 1)、X = 奇の部分 O(bX = −Xb)、Y = 偶の部分 E(bY = Yb)。
    H = m b + X + Y、生成子 T = c b X(c = 1/(2m))。
  * 展開 e^T H e^{−T} = Σ adₜⁿ(H)/n!(Hadamard の補題)は、有界作用素なら収束する級数、
    非有界(p を含む)ときは 1/m の形式的な冪級数(漸近展開)として扱う(外部:Bjorken–Drell §4.3)。
    ここで Lean が示すのは、級数の各項の正確な形(3 次まで)と、その 1/m の次数。
    作用素の定義域:等式はすべて代数の中の恒等式なので、π や Φ が滑らかな係数の微分作用素なら
    C_c^∞ の上でそのまま成り立つ。

  Lean で示すこと
  * 一般の公式(X 奇、Y 偶なら何でもよい):ad_T(m b) = −2mc X、ad_T X = 2c bX²、ad_T Y = c b[X, Y]
    (`ad_beta`、`ad_odd`、`ad_even`)。
  * 3 次までの和の正確な形(`fw_hadamard3`)。c = 1/(2m)(2mc = 1)とすると(`fw_order2`)
      H′ = m b + Y + c X²b + c(YX − XY)b − (4/3)c² X³ − (c²/2)[X, [X, Y]] + c³ R₃
    つまり
      偶:β(m + O²/(2m)) + E − [O, [O, E]]/(8m²)          (1/m² まで)
      奇:β[O, E]/(2m) − O³/(3m²)                           (2 回目の変換で消す)
    R₃ は c³ = 1/(8m³) の項(ad⁴ の寄与も同じ次数なので、この次数は主張しない)。
  * 2 回目の変換:新しい奇の部分 O₁ = c·O₁′ は c に比例する(`odd1_factor`)。O₁ も奇で、新しい偶の部分も偶
    (`odd1_odd`、`even1_even`)。同じ公式を O₁ に当てはめると、偶の部分の変化は c O₁² b = c³ O₁′² b など
    c³ 以上の次数。したがって 1/m² までの偶の部分は 1 回目の結果で確定する。
  * Dirac の場合(2×2 のブロック):O = [[0, S], [S, 0]]、E = diag(Φ, Φ)、S = σ·π。
    - O² = diag(S², S²)、[O, [O, E]] = diag([S, [S, Φ]])(`block_rel`)。
    - Pauli の恒等式(π は非可換):(σ·π)² = π² + iσ·(π × π)(`pauli_nc`)。
      最小結合 [π_j, π_k] = ie ε_jkl B_l なら (σ·π)² = π² − eσ·B(`pauli_minimal`):g = 2 の磁気モーメント。
    - 二重交換子 [S, [S, φ]] = Σ_k [π_k, [π_k, φ]] + iσ·L(`double_comm`)、
      L_l = f_jk − f_kj = −[[π_j, π_k], φ] + 2(π_j g_k − π_k g_j)、g_k = [π_k, φ](`so_form`)。
      [π_k, φ] = −i∂_kφ、Σ[π_k, [π_k, φ]] = −∇²φ、[[π_j, π_k], φ] = 0(B と φ は関数)を入れると
      −[O, [O, eΦ]]/(8m²) は Darwin 項 (e/8m²)∇·𝐄 と スピン軌道項(σ·(𝐄×π − π×𝐄) の形)になる
      (この最後の読み替えは標準的な計算。Bjorken–Drell (4.5))。
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

namespace CFT.FWOrder

/-! ### 一般の FW 展開 -/

section General

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- 交換子 ad_S Z = SZ − ZS -/
def ad (S Z : A) : A := S * Z - Z * S

variable (b X Y : A) (hbb : b * b = 1) (hbX : b * X = -(X * b)) (hbY : b * Y = Y * b)

include hbb in
theorem bb' (z : A) : b * (b * z) = z := by rw [← mul_assoc, hbb, one_mul]

include hbX in
theorem bX' (z : A) : b * (X * z) = -(X * (b * z)) := by rw [← mul_assoc, hbX, neg_mul, mul_assoc]

include hbY in
theorem bY' (z : A) : b * (Y * z) = Y * (b * z) := by rw [← mul_assoc, hbY, mul_assoc]

include hbb hbX in
/-- ad_T(m b) = −2mc X(T = c bX) -/
theorem ad_beta (c m : ℂ) : ad (c • (b * X)) (m • b) = (-(2 * m * c)) • X := by
  have h1 := bb' b hbb
  have h2 := bX' b X hbX
  simp only [ad, smul_mul_assoc, mul_smul_comm, mul_assoc, hbb, hbX, h1, h2, mul_neg, neg_mul,
    smul_neg, one_mul, mul_one]
  module

include hbb hbX in
/-- ad_T X = 2c bX² -/
theorem ad_odd (c : ℂ) : ad (c • (b * X)) X = (2 * c) • (b * (X * X)) := by
  have h1 := bb' b hbb
  have h2 := bX' b X hbX
  simp only [ad, smul_mul_assoc, mul_smul_comm, mul_assoc, hbb, hbX, h1, h2, mul_neg, neg_mul,
    smul_neg, one_mul, mul_one, neg_neg]
  module

include hbb hbX hbY in
/-- ad_T Y = c b[X, Y] -/
theorem ad_even (c : ℂ) : ad (c • (b * X)) Y = c • (b * (X * Y - Y * X)) := by
  have h1 := bb' b hbb
  have h2 := bX' b X hbX
  have h3 := bY' b Y hbY
  simp only [ad, smul_mul_assoc, mul_smul_comm, mul_assoc, mul_sub, smul_sub, hbb, hbX, hbY, h1, h2, h3,
    mul_neg, neg_mul, smul_neg, one_mul, mul_one, neg_neg]
  all_goals module

include hbb hbX hbY in
set_option maxHeartbeats 1000000 in
/-- 【Z17】Hadamard の和の 3 次までの正確な形(b は右端にまとめた) -/
theorem fw_hadamard3 (c m : ℂ) :
    (m • b + X + Y) + ad (c • (b * X)) (m • b + X + Y)
      + (1 / 2 : ℂ) • ad (c • (b * X)) (ad (c • (b * X)) (m • b + X + Y))
      + (1 / 6 : ℂ) • ad (c • (b * X)) (ad (c • (b * X)) (ad (c • (b * X)) (m • b + X + Y)))
    = m • b + Y + (1 - 2 * c * m) • X + (2 * c - 2 * c ^ 2 * m) • (X * (X * b))
      + c • (Y * (X * b)) - c • (X * (Y * b))
      + (-2 * c ^ 2 + 4 / 3 * c ^ 3 * m) • (X * (X * X))
      - (c ^ 2 / 2) • (X * (X * Y)) + c ^ 2 • (X * (Y * X)) - (c ^ 2 / 2) • (Y * (X * X))
      - (4 / 3 * c ^ 3) • (X * (X * (X * (X * b)))) + (c ^ 3 / 6) • (X * (X * (X * (Y * b))))
      - (c ^ 3 / 2) • (X * (X * (Y * (X * b)))) + (c ^ 3 / 2) • (X * (Y * (X * (X * b))))
      - (c ^ 3 / 6) • (Y * (X * (X * (X * b)))) := by
  have h1 := bb' b hbb
  have h2 := bX' b X hbX
  have h3 := bY' b Y hbY
  simp only [ad, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc,
    neg_mul, mul_neg, smul_add, smul_sub, smul_neg, hbb, hbX, hbY, h1, h2, h3, one_mul, mul_one,
    neg_neg]
  module

include hbb hbX hbY in
set_option maxHeartbeats 1000000 in
/-- 【Z17】c = 1/(2m)(2mc = 1)での次数の分類:
偶 m b + Y + c X²b − (c²/2)[X, [X, Y]](1/m² まで)、奇 c(YX − XY)b − (4/3)c²X³、残り c³ R₃ -/
theorem fw_order2 (c m : ℂ) (hc : 2 * m * c = 1) :
    (m • b + X + Y) + ad (c • (b * X)) (m • b + X + Y)
      + (1 / 2 : ℂ) • ad (c • (b * X)) (ad (c • (b * X)) (m • b + X + Y))
      + (1 / 6 : ℂ) • ad (c • (b * X)) (ad (c • (b * X)) (ad (c • (b * X)) (m • b + X + Y)))
    = m • b + Y + c • (X * (X * b))
      - (c ^ 2 / 2) • (X * (X * Y) - (X * (Y * X) + X * (Y * X)) + Y * (X * X))
      + (c • (Y * (X * b) - X * (Y * b)) - (4 / 3 * c ^ 2) • (X * (X * X)))
      + c ^ 3 • (-(4 / 3 : ℂ) • (X * (X * (X * (X * b)))) + (1 / 6 : ℂ) • (X * (X * (X * (Y * b))))
          - (1 / 2 : ℂ) • (X * (X * (Y * (X * b)))) + (1 / 2 : ℂ) • (X * (Y * (X * (X * b))))
          - (1 / 6 : ℂ) • (Y * (X * (X * (X * b))))) := by
  rw [fw_hadamard3 b X Y hbb hbX hbY c m]
  linear_combination (norm := module) ((-1 : ℂ) * hc) • X + ((-c) * hc) • (X * (X * b))
    + ((2 / 3 * c ^ 2) * hc) • (X * (X * X))

/-- 1 回目の後の奇の部分 O₁ = c·O₁′ -/
noncomputable def odd1' (c : ℂ) : A := (Y * (X * b) - X * (Y * b)) - (4 / 3 * c) • (X * (X * X))

theorem odd1_factor (c : ℂ) :
    c • (Y * (X * b) - X * (Y * b)) - (4 / 3 * c ^ 2) • (X * (X * X)) = c • odd1' b X Y c := by
  simp only [odd1']
  module

include hbb hbX hbY in
/-- O₁′ は奇:b O₁′ = −O₁′ b -/
theorem odd1_odd (c : ℂ) : b * odd1' b X Y c = -(odd1' b X Y c * b) := by
  have h1 := bb' b hbb
  have h2 := bX' b X hbX
  have h3 := bY' b Y hbY
  simp only [odd1', mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, neg_mul, mul_neg,
    smul_sub, smul_neg, hbb, hbX, hbY, h1, h2, h3, one_mul, mul_one, neg_neg, neg_sub]
  module

include hbb hbX hbY in
/-- 1 回目の後の偶の部分 Y₁ = Y + c X²b − (c²/2)[X, [X, Y]] は偶:b Y₁ = Y₁ b -/
theorem even1_even (c : ℂ) :
    b * (Y + c • (X * (X * b)) - (c ^ 2 / 2) • (X * (X * Y) - (X * (Y * X) + X * (Y * X)) + Y * (X * X)))
      = (Y + c • (X * (X * b)) - (c ^ 2 / 2) • (X * (X * Y) - (X * (Y * X) + X * (Y * X)) + Y * (X * X))) * b := by
  have h1 := bb' b hbb
  have h2 := bX' b X hbX
  have h3 := bY' b Y hbY
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, neg_mul,
    mul_neg, smul_add, smul_sub, smul_neg, hbb, hbX, hbY, h1, h2, h3, one_mul, mul_one, neg_neg]
  all_goals module

end General

/-! ### Dirac のブロック形 -/

section Blocks

variable {R : Type*} [Ring R]

/-- 【Z17】β = diag(1, −1)、O = [[0, S], [S, 0]]、E = diag(Φ, Φ) は FW の仮定をみたし、
O² = diag(S², S²)、XXY − 2XYX + YXX = diag(SSΦ − 2SΦS + ΦSS) -/
theorem block_rel (S Φ : R) :
    let b : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
    let X : Matrix (Fin 2) (Fin 2) R := !![0, S; S, 0]
    let Y : Matrix (Fin 2) (Fin 2) R := !![Φ, 0; 0, Φ]
    b * b = 1 ∧ b * X = -(X * b) ∧ b * Y = Y * b ∧ X * X = !![S * S, 0; 0, S * S] ∧
      X * (X * Y) - (X * (Y * X) + X * (Y * X)) + Y * (X * X)
        = !![S * (S * Φ) - (S * (Φ * S) + S * (Φ * S)) + Φ * (S * S), 0;
            0, S * (S * Φ) - (S * (Φ * S) + S * (Φ * S)) + Φ * (S * S)] := by
  intro b X Y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [b, X, Y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply])

end Blocks

/-! ### Pauli の恒等式(π は非可換) -/

section Pauli

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- σ·π(成分が非可換な 2×2 行列) -/
def sdR (π : Fin 3 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![π 2, π 0 - Complex.I • π 1; π 0 + Complex.I • π 1, -π 2]

/-- (π × π)_l = π_j π_k − π_k π_j -/
def crossR (π : Fin 3 → R) : Fin 3 → R :=
  ![π 1 * π 2 - π 2 * π 1, π 2 * π 0 - π 0 * π 2, π 0 * π 1 - π 1 * π 0]

/-- diag(x, x) -/
def dg (x : R) : Matrix (Fin 2) (Fin 2) R := !![x, 0; 0, x]

theorem II (x : R) : Complex.I • Complex.I • x = -x := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- 【Z17】(σ·π)² = π² + iσ·(π×π) -/
theorem pauli_nc (π : Fin 3 → R) :
    sdR π * sdR π = dg (π 0 * π 0 + π 1 * π 1 + π 2 * π 2) + Complex.I • sdR (crossR π) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sdR, crossR, dg, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, II] <;>
    module

/-- 【Z17】最小結合 [π_j, π_k] = ie ε_jkl B_l なら (σ·π)² = π² − eσ·B -/
theorem pauli_minimal (π B : Fin 3 → R) (e : ℂ)
    (hcr : crossR π = fun l => Complex.I • (e • B l)) :
    sdR π * sdR π = dg (π 0 * π 0 + π 1 * π 1 + π 2 * π 2) - e • sdR B := by
  rw [pauli_nc, hcr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sdR, dg, smul_add, smul_sub, II] <;>
    module

/-- f_jk = π_jπ_kφ − 2π_jφπ_k + φπ_jπ_k -/
def ff (a c φ : R) : R := a * (c * φ) - (a * (φ * c) + a * (φ * c)) + φ * (a * c)

/-- 【Z17】二重交換子 [S, [S, φ]] = Σ_k f_kk + iσ·L、L_l = f_jk − f_kj -/
theorem double_comm (π : Fin 3 → R) (φ : R) :
    sdR π * (sdR π * dg φ - dg φ * sdR π) - (sdR π * dg φ - dg φ * sdR π) * sdR π
      = dg (ff (π 0) (π 0) φ + ff (π 1) (π 1) φ + ff (π 2) (π 2) φ)
        + Complex.I • sdR ![ff (π 1) (π 2) φ - ff (π 2) (π 1) φ, ff (π 2) (π 0) φ - ff (π 0) (π 2) φ,
            ff (π 0) (π 1) φ - ff (π 1) (π 0) φ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sdR, dg, ff, Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, mul_assoc, II] <;>
    module

/-- 【Z17】スピン軌道の形:f_jk − f_kj = −[[π_j, π_k], φ] + 2(π_j g_k − π_k g_j)、g_k = [π_k, φ] -/
theorem so_form (a c φ : R) :
    ff a c φ - ff c a φ
      = -((a * c - c * a) * φ - φ * (a * c - c * a)) + 2 * (a * (c * φ - φ * c) - c * (a * φ - φ * a)) := by
  simp only [ff]
  noncomm_ring

/-- 【Z17】Darwin の形:f_kk = [π_k, [π_k, φ]] -/
theorem darwin_form (a φ : R) : ff a a φ = a * (a * φ - φ * a) - (a * φ - φ * a) * a := by
  simp only [ff]
  noncomm_ring

end Pauli

end CFT.FWOrder
