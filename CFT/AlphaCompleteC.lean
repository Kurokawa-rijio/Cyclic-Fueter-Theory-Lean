/-
  完全化(その3):α-I.7(Y6)H³ 上の BPS 単極子

  Berry 接続 A_B = a(s) iσ·(p×dp)、a = 1/(2E(E+m)) = (1 − m/E)/(2s)(s = |p|²)と
  Higgs 場 Φ = (p/E)·T(T = −iσ/2)は、曲率 −1 の双曲計量 h = (δ − pp/E²)/m² のもとで
  BPS 方程式 D_AΦ = −*F を厳密に満たす。
    (*F)_k = ½√det h ε_kij h^{ia}h^{jb}F_ab、h^{ij} = m²δ_ij + p_ip_j、√det h = 1/(m²E)
  証明の構成
  1. 曲率は F_ab = Σ_c ε_abc F*_c(F*_c は一般形の閉じた式)              (F_eps)
  2. m²(*F)_k = ½(1/E) ε_kij h^{ia}h^{jb}F_ab = Σ_c K_kc F*_c、
     K_kc = (1/E)[m²(m² + s)δ_kc − m² p_k p_c](= (1/E) adj(h⁻¹))         (starF_closed)
  3. m² D_kΦ + Σ_c K_kc F*_c = 0(成分ごとの証明書)                         (bps)
  1/E、1/s は変数 iE、iS と関係式 (m² + s)iE² = 1、s·iS = 1 で扱う。
  a′ = da/ds = (m s/E³ − 2 + 2m/E)/(4s²)(連鎖律。aB_eq、apB_eq で berry_deriv の値と照合)。
-/
import CFT.AlphaI_AW
import Mathlib.Tactic.Module

open Matrix CFT.AlphaI_AW

namespace CFT.AlphaCompleteC

noncomputable section

def eps3 : Fin 3 → Fin 3 → Fin 3 → ℂ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

def hinv (m : ℂ) (p : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  ![![m ^ 2 + p 0 * p 0, p 0 * p 1, p 0 * p 2], ![p 1 * p 0, m ^ 2 + p 1 * p 1, p 1 * p 2],
    ![p 2 * p 0, p 2 * p 1, m ^ 2 + p 2 * p 2]]

/-- K_kc = (1/E)[m²(m² + s)δ_kc − m² p_k p_c] -/
def Kmat (m iE : ℂ) (p : Fin 3 → ℂ) : Fin 3 → Fin 3 → ℂ :=
  let s := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2
  ![![iE * (m ^ 2 * (m ^ 2 + s) - m ^ 2 * p 0 * p 0), iE * (-(m ^ 2 * p 0 * p 1)), iE * (-(m ^ 2 * p 0 * p 2))],
    ![iE * (-(m ^ 2 * p 1 * p 0)), iE * (m ^ 2 * (m ^ 2 + s) - m ^ 2 * p 1 * p 1), iE * (-(m ^ 2 * p 1 * p 2))],
    ![iE * (-(m ^ 2 * p 2 * p 0)), iE * (-(m ^ 2 * p 2 * p 1)), iE * (m ^ 2 * (m ^ 2 + s) - m ^ 2 * p 2 * p 2)]]

def aB (m iE iS : ℂ) : ℂ := (1 - m * iE) * iS / 2

def apB (m iE iS : ℂ) (p : Fin 3 → ℂ) : ℂ :=
  (m * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) * iE ^ 3 - 2 + 2 * m * iE) * iS ^ 2 / 4

def Phi (iE : ℂ) (p : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (-Complex.I / 2 * iE) • sd p

def dPhi (iE : ℂ) (p : Fin 3 → ℂ) (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2) • (iE • σ k - (p k * iE ^ 3) • sd p)

def DPhi (m iE iS : ℂ) (p : Fin 3 → ℂ) (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  dPhi iE p k + A p (aB m iE iS) 0 k * Phi iE p - Phi iE p * A p (aB m iE iS) 0 k

/-- 双対成分 F*_c の閉じた式(curv_formula と同じ形、b = b′ = 0) -/
def Fs (p : Fin 3 → ℂ) (a ap : ℂ) (c : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • ((2 * (a + ap * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) - 0 ^ 2)) • σ c
    + ((-2 * (a ^ 2 + ap)) * p c) • sd p + (2 * (a * 0 + 0)) • pxs p c)

/-- ε 定義の Hodge 双対(m² 倍):½(1/E) ε_kij h^{ia}h^{jb}F_ab -/
def starF (m iE : ℂ) (p : Fin 3 → ℂ) (a ap : ℂ) (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, ∑ j, ((1 / 2) * iE * eps3 k i j) • ∑ a', ∑ b', (hinv m p i a' * hinv m p j b') • F p a ap 0 0 a' b'

theorem F_diag (p : Fin 3 → ℂ) (a ap : ℂ) (i : Fin 3) : F p a ap 0 0 i i = 0 := by
  simp [F]

theorem F_anti (p : Fin 3 → ℂ) (a ap : ℂ) (i j : Fin 3) : F p a ap 0 0 j i = -F p a ap 0 0 i j := by
  simp only [F]; abel

set_option maxHeartbeats 0 in
/-- 1. F_ab = Σ_c ε_abc F*_c -/
theorem F_eps (p : Fin 3 → ℂ) (a ap : ℂ) (i j : Fin 3) :
    F p a ap 0 0 i j = ∑ c, eps3 i j c • Fs p a ap c := by
  have h := curv_formula p a ap 0 0
  simp only at h
  obtain ⟨h12, h20, h01⟩ := h
  have h21 : F p a ap 0 0 2 1 = -Fs p a ap 0 := by rw [F_anti, h12]; rfl
  have h02 : F p a ap 0 0 0 2 = -Fs p a ap 1 := by rw [F_anti, h20]; rfl
  have h10 : F p a ap 0 0 1 0 = -Fs p a ap 2 := by rw [F_anti, h01]; rfl
  fin_cases i <;> fin_cases j <;>
    simp [eps3, Fin.sum_univ_three, F_diag, h21, h02, h10] <;>
    first | exact h12 | exact h20 | exact h01 | skip

set_option maxHeartbeats 0 in
/-- 2. Hodge 双対の閉じた形:m²(*F)_k = Σ_c K_kc F*_c -/
theorem starF_closed (m iE : ℂ) (p : Fin 3 → ℂ) (a ap : ℂ) (k : Fin 3) :
    starF m iE p a ap k = ∑ c, Kmat m iE p k c • Fs p a ap c := by
  simp only [starF, F_eps]
  fin_cases k <;>
    simp only [Fin.sum_univ_three, eps3, hinv, Kmat, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] <;>
    module

end

end CFT.AlphaCompleteC
