/-
  α-VII.1(Z26):Abelian 射影と 't Hooft テンソル(微分まで含めた定式化)

  R を可換な ℚ 代数(滑らかな関数の環)、∂_μ(μ ∈ Fin 4)を互いに可換な導分、g を定数(∂_μ g = 0)とする。
  SU(2) の随伴表現 R³ で、外積 ×、内積 ·、
    D_μ n = ∂_μ n + g A_μ × n、F_{μν} = ∂_μ A_ν − ∂_ν A_μ + g A_μ × A_ν。
    * ricci:[D_μ, D_ν] n = g F_{μν} × n(微分の可換性と Jacobi 恒等式から。入力ではなく証明)
    * n_dot_dn:n·n = 1 なら n·∂_μ n = 0
    * connection_decomp:D_μ n = 0、n·n = 1 なら g A_μ = g (A_μ·n) n − n × ∂_μ n
      (第二項は一般のゲージで残る。n が定数方向のゲージでだけ A_μ は n の方向だけになる)
    * thooft_identity:n·n = 1 なら
        g·(n·F_{μν}) − n·(D_μ n × D_ν n) = g(∂_μ(n·A_ν) − ∂_ν(n·A_μ)) − n·(∂_μ n × ∂_ν n)
      すなわち 't Hooft テンソル 𝓕 = n·F − (1/g) n·(Dn × Dn) は、U(1) の場 ∂(n·A) とモノポールの項
      −(1/g) n·(∂n × ∂n) の和
  AlphaVII_Abelian の abelian_projection(D n = 0 ⇒ F = (n·F) n)の入力 [D_μ, D_ν]n = F × n は、
  ここで定義から導いたもの(g = 1 の場合)。
  未形式化:'t Hooft テンソルのゲージ不変性、Z26 の原典での n の定義(Higgs 場の向き、S² 値の場など)。
-/
import CFT.Basic
import Mathlib.RingTheory.Derivation.Basic

namespace CFT.Thooft

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def cross (a b : Fin 3 → R) : Fin 3 → R :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def dot (a b : Fin 3 → R) : R := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

variable (d : Fin 4 → Derivation ℚ R R) (g : R) (A : Fin 4 → Fin 3 → R)

/-- 共変微分 D_μ n = ∂_μ n + g A_μ × n -/
def Dcov (μ : Fin 4) (n : Fin 3 → R) : Fin 3 → R := fun i => d μ (n i) + g * cross (A μ) n i

/-- 曲率 F_{μν} = ∂_μ A_ν − ∂_ν A_μ + g A_μ × A_ν -/
def Fcurv (μ ν : Fin 4) : Fin 3 → R := fun i => d μ (A ν i) - d ν (A μ i) + g * cross (A μ) (A ν) i

/-- [D_μ, D_ν] n = g F_{μν} × n -/
theorem ricci (hcomm : ∀ μ ν x, d μ (d ν x) = d ν (d μ x)) (hg : ∀ μ, d μ g = 0)
    (μ ν : Fin 4) (n : Fin 3 → R) (i : Fin 3) :
    Dcov d g A μ (Dcov d g A ν n) i - Dcov d g A ν (Dcov d g A μ n) i = g * cross (Fcurv d g A μ ν) n i := by
  fin_cases i <;>
  simp [Dcov, Fcurv, cross, map_add, map_sub, Derivation.leibniz, smul_eq_mul, hg] <;>
  [linear_combination hcomm μ ν (n 0); linear_combination hcomm μ ν (n 1);
   linear_combination hcomm μ ν (n 2)]

/-- 単位ベクトルの微分は直交する -/
theorem n_dot_dn (n : Fin 3 → R) (hn : dot n n = 1) (μ : Fin 4) :
    dot n (fun j => d μ (n j)) = 0 := by
  have h := congrArg (d μ) hn
  simp only [dot, map_add, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at h
  have h2 : (2 : R) * (n 0 * d μ (n 0) + n 1 * d μ (n 1) + n 2 * d μ (n 2)) = 0 := by
    linear_combination h
  have hu : IsUnit (2 : R) := by
    have : (2 : R) = algebraMap ℚ R 2 := (map_ofNat (algebraMap ℚ R) 2).symm
    rw [this]; exact (isUnit_of_invertible (2 : ℚ)).map _
  simpa [dot] using hu.mul_right_eq_zero.mp h2

/-- D_μ n = 0、n·n = 1 ⇒ g A_μ = g (A_μ·n) n − n × ∂_μ n -/
theorem connection_decomp (n : Fin 3 → R) (hn : dot n n = 1) (μ : Fin 4)
    (hD : ∀ i, Dcov d g A μ n i = 0) (i : Fin 3) :
    g * A μ i = g * dot (A μ) n * n i - cross n (fun j => d μ (n j)) i := by
  have h0 := hD 0; have h1 := hD 1; have h2 := hD 2
  simp only [Dcov, cross, dot] at h0 h1 h2 hn ⊢
  fin_cases i <;> simp at h0 h1 h2 ⊢
  · linear_combination (-n 2) * h1 + n 1 * h2 + (-A μ 0 * g) * hn
  · linear_combination n 2 * h0 + (-n 0) * h2 + (-A μ 1 * g) * hn
  · linear_combination (-n 1) * h0 + n 0 * h1 + (-A μ 2 * g) * hn

/-- 't Hooft テンソルの恒等式 -/
theorem thooft_identity (n : Fin 3 → R) (hn : dot n n = 1) (μ ν : Fin 4) :
    g * dot n (Fcurv d g A μ ν) - dot n (cross (Dcov d g A μ n) (Dcov d g A ν n))
      = g * (d μ (dot n (A ν)) - d ν (dot n (A μ)))
        - dot n (cross (fun j => d μ (n j)) (fun j => d ν (n j))) := by
  have e0 := n_dot_dn d n hn μ
  have e1 := n_dot_dn d n hn ν
  simp only [dot, Fcurv, Dcov, cross, map_add, map_sub, Derivation.leibniz, smul_eq_mul] at e0 e1 hn ⊢
  simp
  linear_combination
    (-A μ 0*A ν 1*g^2*n 2 + A μ 0*A ν 2*g^2*n 1 - A μ 0*d ν (n 0)*g + A μ 1*A ν 0*g^2*n 2
      - A μ 1*A ν 2*g^2*n 0 - A μ 1*d ν (n 1)*g - A μ 2*A ν 0*g^2*n 1 + A μ 2*A ν 1*g^2*n 0
      - A μ 2*d ν (n 2)*g + A ν 0*d μ (n 0)*g + A ν 1*d μ (n 1)*g + A ν 2*d μ (n 2)*g) * hn
    + (-A ν 0*g*n 0 - A ν 1*g*n 1 - A ν 2*g*n 2) * e0
    + (A μ 0*g*n 0 + A μ 1*g*n 1 + A μ 2*g*n 2) * e1

end CFT.Thooft
