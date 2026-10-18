/-
  α-III.9(Z23):球対称な切り口の Codazzi の式(運動量拘束)

  切り口の計量 ds² + r(s)² (dθ² + sin²θ dφ²)、外曲率 K^i_j = diag(a(s), b(s), b(s))(時間対称でない場合)。
  一点での値:r, r′, sinθ = S, cosθ = C、a, b, a′, b′。
  Christoffel 記号は計量の公式 Γ^k_{ij} = ½ g^{kl}(∂_i g_{jl} + ∂_j g_{il} − ∂_l g_{ij}) から計算する(Gam)。
    * codazzi_s:∇_j K^j_s − ∂_s K = 2(r′/r)(a − b) − 2b′
    * codazzi_theta, codazzi_phi:角度成分は 0
  したがって運動量拘束 ∇_j K^j_i − ∂_i K = 8πG j_i は、球対称では一本 2(r′/r)(a − b) − 2b′ = 8πG j_s。
    * hamiltonian_K:ハミルトン拘束の外曲率の部分 K² − K_ij K^ij = 4ab + 2b²
  ³R(Gauss の式)と表面密度は AlphaIII_Junction、時間的な面の Israel 条件は AlphaIII_Israel、
  ヌルな面は AlphaIII_P1 の null_front、面の型の区別は classify。
-/
import CFT.Basic

namespace CFT.Codazzi

variable (r rp S C a b ap bp : ℝ)

/-- 計量 g = diag(1, r², r²S²) -/
def gm : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = j then ![1, r ^ 2, r ^ 2 * S ^ 2] i else 0

/-- 逆計量 -/
noncomputable def gi : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = j then ![1, 1 / r ^ 2, 1 / (r ^ 2 * S ^ 2)] i else 0

/-- ∂_l g_{ij}(座標 0 = s、1 = θ、2 = φ):∂_s g_θθ = 2rr′、∂_s g_φφ = 2rr′S²、∂_θ g_φφ = 2r²SC -/
def dg : Fin 3 → Fin 3 → Fin 3 → ℝ := fun l i j =>
  if i = j then
    (if l = 0 then ![0, 2 * r * rp, 2 * r * rp * S ^ 2] i
     else if l = 1 then ![0, 0, 2 * r ^ 2 * S * C] i else 0)
  else 0

/-- Γ^k_{ij} = ½ Σ_l g^{kl}(∂_i g_{jl} + ∂_j g_{il} − ∂_l g_{ij}) -/
noncomputable def Gam (k i j : Fin 3) : ℝ :=
  (1 / 2) * ∑ l, gi r S k l * (dg r rp S C i j l + dg r rp S C j i l - dg r rp S C l i j)

/-- K^i_j = diag(a, b, b) とその微分 ∂_k K^i_j(∂_s だけ) -/
def Km : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then ![a, b, b] i else 0
def dK : Fin 3 → Fin 3 → Fin 3 → ℝ := fun k i j =>
  if k = 0 ∧ i = j then ![ap, bp, bp] i else 0

/-- ∇_j K^j_i − ∂_i K -/
noncomputable def momentum (i : Fin 3) : ℝ :=
  (∑ j, dK ap bp j j i) + (∑ j, ∑ l, Gam r rp S C j j l * Km a b l i)
    - (∑ j, ∑ l, Gam r rp S C l j i * Km a b j l) - (∑ j, dK ap bp i j j)

theorem codazzi_s (hr : r ≠ 0) (hS : S ≠ 0) :
    momentum r rp S C a b ap bp 0 = 2 * (rp / r) * (a - b) - 2 * bp := by
  simp [momentum, Gam, gi, dg, Km, dK, Fin.sum_univ_three]
  field_simp; ring

theorem codazzi_theta : momentum r rp S C a b ap bp 1 = 0 := by
  simp [momentum, Gam, gi, dg, Km, dK, Fin.sum_univ_three]

theorem codazzi_phi : momentum r rp S C a b ap bp 2 = 0 := by
  simp [momentum, Gam, gi, dg, Km, dK, Fin.sum_univ_three]

/-- ハミルトン拘束の外曲率の部分:K² − K^i_j K^j_i = 4ab + 2b² -/
theorem hamiltonian_K :
    (∑ i, Km a b i i) ^ 2 - (∑ i, ∑ j, Km a b i j * Km a b j i) = 4 * a * b + 2 * b ^ 2 := by
  simp [Km, Fin.sum_univ_three]; ring

end CFT.Codazzi
