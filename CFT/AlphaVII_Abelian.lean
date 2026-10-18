/-
  α-VII.1(Z26):方向場 n による Abelian 射影(標準形での定式化)

  SU(2) の随伴表現(ℝ³、Lie 括弧は外積 ×)で、単位の方向場 n(n·n = 1)、接続 A_μ、
  共変微分 D_μ n = ∂_μ n + A_μ × n、曲率 F_{μν}。Ricci の恒等式 [D_μ, D_ν] n = F_{μν} × n を入力とする。
    * cross_zero_parallel:F × n = 0、n·n = 1 ⇒ F = (F·n) n(n の方向に揃う)
    * abelian_projection:D n = 0 なら([D_μ, D_ν] n = 0 から)F_{μν} = f_{μν} n、f_{μν} = n·F_{μν}:
      非可換な曲率が U(1) の場 f_{μν} に落ちる(Abelian 射影)
    * decomposition:一般に F = (F·n) n + n × (F × n)(n に平行な部分と垂直な部分への分解)
  Z24 の貼り合わせ(AlphaVII_Bundle)と合わせると、f は球面上で c₁ = N の U(1) 束の曲率になる。
    * stabilizer_iff, stabilizer_abelian:n の安定化部分代数は n が張る一次元の可換代数 u(1)
  台帳の Z26 の命題(SU(2) が指定した場の方向のもとで U(1) 接続へ還元される条件、安定化群、
  接続と曲率の対応)はこのファイルと AlphaVII_Thooft で閉じる。[D_μ, D_ν] = gF× は AlphaVII_Thooft で導出。
-/
import CFT.Basic

namespace CFT.Abelian

/-- ℝ³ の外積 -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def dot (a b : Fin 3 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- 分解 F = (F·n)n + n × (F × n)(n·n = 1) -/
theorem decomposition (F n : Fin 3 → ℝ) (hn : dot n n = 1) :
    F = fun i => dot F n * n i + cross n (cross F n) i := by
  funext i
  simp only [dot] at hn
  fin_cases i
  · simp [cross, dot]; linear_combination (-F 0) * hn
  · simp [cross, dot]; linear_combination (-F 1) * hn
  · simp [cross, dot]; linear_combination (-F 2) * hn

/-- F × n = 0 なら F は n に平行 -/
theorem cross_zero_parallel (F n : Fin 3 → ℝ) (hn : dot n n = 1) (h : cross F n = 0) :
    F = fun i => dot F n * n i := by
  have e := decomposition F n hn
  have hc : cross n 0 = 0 := by funext i; fin_cases i <;> simp [cross]
  rw [h, hc] at e
  conv_lhs => rw [e]
  funext i; simp

/-- Abelian 射影:D n = 0 と Ricci の恒等式 [D_μ, D_ν] n = F_{μν} × n から F_{μν} = (n·F_{μν}) n -/
theorem abelian_projection (F : Fin 4 → Fin 4 → Fin 3 → ℝ) (n : Fin 3 → ℝ) (hn : dot n n = 1)
    (commD : Fin 4 → Fin 4 → Fin 3 → ℝ)
    (ricci : ∀ μ ν, commD μ ν = cross (F μ ν) n)
    (covconst : ∀ μ ν, commD μ ν = 0) :
    ∀ μ ν, F μ ν = fun i => dot (F μ ν) n * n i := fun μ ν =>
  cross_zero_parallel _ n hn ((ricci μ ν).symm.trans (covconst μ ν))

/-- 安定化群:無限小回転 v ↦ ω × v が n を動かさない ⇔ ω = (ω·n) n。
  n の安定化部分代数は n が張る一次元(可換、u(1))で、SU(2) は D n = 0 の上で U(1) に還元される -/
theorem stabilizer_iff (ω n : Fin 3 → ℝ) (hn : dot n n = 1) :
    cross ω n = 0 ↔ ω = fun i => dot ω n * n i := by
  constructor
  · exact cross_zero_parallel ω n hn
  · intro h; rw [h]; funext i; fin_cases i <;> simp [cross] <;> ring

/-- 安定化部分代数は可換:n に平行な二つの生成子の括弧は 0 -/
theorem stabilizer_abelian (s t : ℝ) (n : Fin 3 → ℝ) :
    cross (fun i => s * n i) (fun i => t * n i) = 0 := by
  funext i; fin_cases i <;> simp [cross] <;> ring

end CFT.Abelian
