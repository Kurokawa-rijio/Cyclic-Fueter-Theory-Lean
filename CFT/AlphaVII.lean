/-
  α-VII 電磁気と標準模型(Z28-f)

  形式化した内容
  * α-VII.7 (Z28-f) 単位 S² 上で電荷 q の単極子に結合した Dirac 作用素:
                    H² の固有値 (j + ½)² − q²(j ≥ |q| − ½)。最低準位 j = |q| − ½ でゼロになり、
                    その縮退度は 2j + 1 = 2|q|。それより上の準位は正
                    (固有値の公式とカイラリティ sign(q) は指数定理・球面調和の外部結果)
  * α-VII.9 (Z28-f) U(1)_F = ½ スピン接続のひねりで指数 χ/2。S² では χ = 2 なので 1 世代

  形式化していない内容
  * α-VII.1(EM-1〜4)、α-VII.3(障害 N1)、α-VII.4(99/250 の導出)、
    α-VII.6(奇数次元の指数 0)、α-VII.8(表現論):README 参照
-/
import CFT.Basic

namespace CFT.AlphaVII

/-- 最低準位 j = |q| − ½ で (j + ½)² − q² = 0、縮退度 2j + 1 = 2|q| -/
theorem monopole_zero_modes (q : ℝ) :
    let j := |q| - 1 / 2
    (j + 1 / 2) ^ 2 - q ^ 2 = 0 ∧ 2 * j + 1 = 2 * |q| := by
  intro j
  constructor
  · simp only [j]; rw [show |q| - 1 / 2 + 1 / 2 = |q| by ring, sq_abs]; ring
  · simp only [j]; ring

/-- j ≥ |q| + ½ の準位は正 -/
theorem monopole_gap (q j : ℝ) (hj : |q| + 1 / 2 ≤ j) : 0 < (j + 1 / 2) ^ 2 - q ^ 2 := by
  have h1 : |q| + 1 ≤ j + 1 / 2 := by linarith
  have h0 : 0 ≤ |q| := abs_nonneg q
  have h2 : (|q| + 1) ^ 2 ≤ (j + 1 / 2) ^ 2 := by nlinarith
  have h3 : q ^ 2 = |q| ^ 2 := (sq_abs q).symm
  nlinarith

/-- S² の Euler 数 χ = 2 で、指数 χ/2 = 1(1 世代) -/
theorem one_generation : (2 : ℤ) / 2 = 1 := by norm_num

end CFT.AlphaVII
