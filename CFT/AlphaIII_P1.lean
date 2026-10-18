/-
  α-III.2 (Z7, P1):null な弱不連続での応力の跳び

  F を反対称 4×4 行列(下付き添字)、k を null ベクトル(上付き)、α を α·k = 0 の
  共ベクトルとし、[F] = k_μ α_ν − α_μ k_ν とする。Yang–Mills の応力
  T(F) = F η Fᵀ − ¼ (F_{ab}F^{ab}) η について k^μ [T_μν] = 0。

  証明は、各成分が null 条件 N と直交条件 A の多項式結合であることを
  `linear_combination` で示す(係数は sympy で求め、Lean が独立に検算する)。
-/
import CFT.Basic

namespace CFT.AlphaIII

/-- Minkowski 計量 η = diag(−1, 1, 1, 1) -/
def eta : Matrix (Fin 4) (Fin 4) ℝ := !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Yang–Mills の応力テンソル(下付き添字) -/
noncomputable def Tst (G : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  G * eta * G.transpose - ((1 / 4 : ℝ) * ∑ i, ∑ j, G i j * (eta * G * eta) i j) • eta

set_option maxHeartbeats 0 in
theorem null_front (f01 f02 f03 f12 f13 f23 k0 k1 k2 k3 a0 a1 a2 a3 : ℝ)
    (hN : -k0 ^ 2 + k1 ^ 2 + k2 ^ 2 + k3 ^ 2 = 0)
    (hA : a0 * k0 + a1 * k1 + a2 * k2 + a3 * k3 = 0) :
    let F : Matrix (Fin 4) (Fin 4) ℝ :=
      !![0, f01, f02, f03; -f01, 0, f12, f13; -f02, -f12, 0, f23; -f03, -f13, -f23, 0]
    let k : Fin 4 → ℝ := ![k0, k1, k2, k3]
    let α : Fin 4 → ℝ := ![a0, a1, a2, a3]
    let kl := eta.mulVec k
    let J := Matrix.vecMulVec kl α - Matrix.vecMulVec α kl
    Matrix.vecMul k (Tst (F + J) - Tst F) = 0 := by
  intro F k α kl J
  ext ν
  fin_cases ν <;>
    simp [F, k, α, kl, J, Tst, eta, Matrix.vecMul, Matrix.mulVec, Matrix.vecMulVec,
      Matrix.mul_apply, dotProduct, Fin.sum_univ_four, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.transpose_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination (a0^2*k0/2 - a1^2*k0/2 + a1*f01 - a2^2*k0/2 + a2*f02 - a3^2*k0/2 + a3*f03) * hN + (a0*k0^2/2 + a1*k0*k1/2 + a2*k0*k2/2 + a3*k0*k3/2 - f01*k1 - f02*k2 - f03*k3) * hA
  · linear_combination (-a0^2*k1/2 + a0*f01 + a1^2*k1/2 + a2^2*k1/2 + a2*f12 + a3^2*k1/2 + a3*f13) * hN + (-a0*k0*k1/2 - a1*k1^2/2 - a2*k1*k2/2 - a3*k1*k3/2 + f01*k0 - f12*k2 - f13*k3) * hA
  · linear_combination (-a0^2*k2/2 + a0*f02 + a1^2*k2/2 - a1*f12 + a2^2*k2/2 + a3^2*k2/2 + a3*f23) * hN + (-a0*k0*k2/2 - a1*k1*k2/2 - a2*k2^2/2 - a3*k2*k3/2 + f02*k0 + f12*k1 - f23*k3) * hA
  · linear_combination (-a0^2*k3/2 - a0*a3*k0/2 + a0*f03 + a1^2*k3/2 - a1*a3*k1/2 - a1*f13 + a2^2*k3/2 - a2*a3*k2/2 - a2*f23) * hN + (-a0*k0*k3/2 - a1*k1*k3/2 - a2*k2*k3/2 - a3*k0^2/2 + a3*k1^2/2 + a3*k2^2/2 + f03*k0 + f13*k1 + f23*k2) * hA

end CFT.AlphaIII
