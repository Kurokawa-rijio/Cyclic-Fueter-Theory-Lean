/-
  α-V.1 (Z17):自由 Dirac 作用素の Foldy–Wouthuysen 変換(厳密)

  Dirac 表示の β、αᵢ(4×4)と H = mβ + α·p について、
  U = (E + m) + βα·p、V = (E + m) − βα·p とおくと、E² = m² + |p|² のもとで
    U H V = 2E²(E + m) β、  U V = 2E(E + m)。
  p が実数なら V = U†(βα·p は反エルミート)なので、規格化した
  Û = U/√(2E(E+m)) はユニタリで、Û H Û† = βE(対角化)。
  各成分の等式は、関係式 E² = m² + |p|² と I² = −1 の多項式結合として Lean が検算する
  (係数は sympy の aux/gen_fw.py で求めた)。
-/
import CFT.Basic

namespace CFT.AlphaV

open Matrix

def β : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
def αx : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
def αy : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, -Complex.I, 0, 0; Complex.I, 0, 0, 0]
def αz : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0]

set_option maxHeartbeats 0 in
theorem fw_exact (m E px py pz : ℂ) (hE : E ^ 2 = m ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    let Ap := px • αx + py • αy + pz • αz
    let H := m • β + Ap
    let U := (E + m) • (1 : Matrix (Fin 4) (Fin 4) ℂ) + β * Ap
    let V := (E + m) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - β * Ap
    U * H * V = (2 * E ^ 2 * (E + m)) • β ∧
      U * V = (2 * E * (E + m)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  intro Ap H U V
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, H, Ap, β, αx, αy, αz, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      all_goals (first | ring1 | (linear_combination (-2*E - m) * hE + (-2*E*py^2 - m*py^2) * hI) | (linear_combination (pz) * hE + (py^2*pz) * hI) | (linear_combination (-Complex.I*py + px) * hE + (-Complex.I*py^3 + px*py^2) * hI) | (linear_combination (Complex.I*py + px) * hE + (Complex.I*py^3 + px*py^2) * hI) | (linear_combination (-pz) * hE + (-py^2*pz) * hI) | (linear_combination (2*E + m) * hE + (2*E*py^2 + m*py^2) * hI))
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, H, Ap, β, αx, αy, αz, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      all_goals (first | ring1 | (linear_combination (-1) * hE + (-py^2) * hI))

end CFT.AlphaV
