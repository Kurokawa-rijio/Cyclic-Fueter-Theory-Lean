/-
  α-VII.4(Z28-d)の条件つきを閉じる:楕円体族と共形族の 2 次の係数が一致すること

  台帳で核心の仮定だったのは「楕円体族 S⁹_ρ ⊂ R⁴ ⊕ R⁶ に沿った規格化した最低固有値 N = λ Vol^{1/9} の
  2 次の係数は、共形族 e^{2tf}g の 2 次の係数(99/250、AlphaVII_Z28d)と同じ」こと。次の三つから従う。

  (1) 1 次では楕円体 = 微分同相 + 共形変形(`ellipsoid_first_order`)。A = 1 + εB(B は対角)、
      φ_ε(x) = Ax/|Ax|(球面の微分同相)とおくと、接ベクトル v(⟨x, v⟩ = 0、|x| = 1)について
        |Av|² − (1 + 2εu₁)·|dφ_ε v|² = ε²P(ε)/|Ax|⁴、u₁ = ⟨x, Bx⟩
      (`ellipsoid_conformal_first_order` は分母を払った多項式の恒等式)。したがって
      (φ_ε⁻¹)^* g_A = e^{2εu₁} g + O(ε²)。B が R⁴ の部分に 1 なら u₁ = |y_H|² = f + 2/5
      (AlphaVII_Z28Input `ellipsoid_tangent` と同じ結論を、微分同相を明示して示したもの)。
  (2) 丸い S⁹ では N は臨界的:N′[h] = 0(すべての h)。Killing スピノル ∇_Xψ = μX·ψ と
      XY + YX = −2g(X, Y) からエネルギー運動量 T(X, Y) = −2μ g(X, Y)|ψ|²(`killing_stress`):計量に比例。
      Bourguignon–Gauduchon の第一変分 δλ = −½∫⟨T_ψ, h⟩(外部、1992)で δλ は tr h の平均 m だけで決まり、
      相似変換(h = 2g で λ → e^{−1}λ の 1 次)から δλ = −(λ/2n)m(`first_variation_coeff`)。
      δVol/Vol = m/2 と合わせて δN/N = 0(`normalized_first_variation`)。縮退した固有空間でも、異なる
      Killing スピノルの内積は定数(AlphaVII_Z28Input `killing_inner_const`)なので 1 次の分裂はない。
  (3) 2 次の展開(外部:Kato の解析的摂動論)N(g + εh₁ + ε²h₂) = N₀ + ε N′[h₁] + ε²(Q(h₁) + N′[h₂]) + …
      と N′ = 0 から、2 次の係数 Q(h₁) は 1 次の方向 h₁ だけで決まる(`second_order_equal`)。微分同相で
      スペクトルは変わらないので、楕円体族と共形族(同じ h₁ = 2u₁g)の 2 次の係数は等しい。
  外部:Bourguignon–Gauduchon の第一変分の公式、Kato の摂動展開、スペクトルの微分同相不変性。
  これで 99/250 > 0 から ρ = 1 は楕円体族に沿った局所最小(AlphaVII_Z28Input `z28d_local_min`)。
-/
import CFT.AlphaVII_Z28Input
import Mathlib.Algebra.BigOperators.Fin

namespace CFT.FixZ28

open Finset Asymptotics Filter Topology

/-! ### (1) 1 次では楕円体 = 微分同相 + 共形 -/

/-- |(1 + εB)v|² = |v|² + 2ε⟨v, Bv⟩ + ε²|Bv|²(B は対角) -/
theorem norm_sq_expand {N : ℕ} (b v : Fin N → ℝ) (ε : ℝ) :
    ∑ i, ((1 + ε * b i) * v i) ^ 2
      = ∑ i, v i ^ 2 + 2 * ε * ∑ i, b i * v i ^ 2 + ε ^ 2 * ∑ i, b i ^ 2 * v i ^ 2 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- ⟨Ax, Av⟩ = ε·2⟨x, Bv⟩ + ε²⟨Bx, Bv⟩(⟨x, v⟩ = 0) -/
theorem inner_expand {N : ℕ} (b x v : Fin N → ℝ) (ε : ℝ) (hxv : ∑ i, x i * v i = 0) :
    ∑ i, ((1 + ε * b i) * x i) * ((1 + ε * b i) * v i)
      = ε * (2 * ∑ i, b i * x i * v i) + ε ^ 2 * ∑ i, b i ^ 2 * x i * v i := by
  have e : ∑ i, ((1 + ε * b i) * x i) * ((1 + ε * b i) * v i)
      = ∑ i, x i * v i + ε * (2 * ∑ i, b i * x i * v i) + ε ^ 2 * ∑ i, b i ^ 2 * x i * v i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, hxv, zero_add]

/-- 分母を払った恒等式:G = a₀ + 2εa₁ + ε²a₂、K = εc₁ + ε²c₂、D = 1 + 2εu₁ + ε²d₂ で
(G − (1 + 2εu₁)(G − K²/D)/D)·D² = ε²(G D d₂ + (1 + 2εu₁)(c₁ + εc₂)²) -/
theorem ellipsoid_conformal_first_order (a0 a1 a2 c1 c2 u1 d2 ε : ℝ)
    (hD : 1 + 2 * ε * u1 + ε ^ 2 * d2 ≠ 0) :
    ((a0 + 2 * ε * a1 + ε ^ 2 * a2) - (1 + 2 * ε * u1) *
        (((a0 + 2 * ε * a1 + ε ^ 2 * a2) - (ε * c1 + ε ^ 2 * c2) ^ 2 / (1 + 2 * ε * u1 + ε ^ 2 * d2))
          / (1 + 2 * ε * u1 + ε ^ 2 * d2))) * (1 + 2 * ε * u1 + ε ^ 2 * d2) ^ 2
      = ε ^ 2 * ((a0 + 2 * ε * a1 + ε ^ 2 * a2) * (1 + 2 * ε * u1 + ε ^ 2 * d2) * d2
          + (1 + 2 * ε * u1) * (c1 + ε * c2) ^ 2) := by
  field_simp <;> ring

/-- 【α-VII.4 (1)】楕円体の誘導計量 |Av|² と、微分同相 φ_ε(x) = Ax/|Ax| で引き戻した丸い計量
|dφ_ε v|² = (|Av|² − ⟨Ax, Av⟩²/|Ax|²)/|Ax|² の差:|Av|² − (1 + 2εu₁)|dφ_ε v|² は ε² の次数 -/
theorem ellipsoid_first_order {N : ℕ} (b x v : Fin N → ℝ) (ε : ℝ) (hx : ∑ i, x i ^ 2 = 1)
    (hxv : ∑ i, x i * v i = 0) (hD : ∑ i, ((1 + ε * b i) * x i) ^ 2 ≠ 0) :
    ∃ P : ℝ,
      (∑ i, ((1 + ε * b i) * v i) ^ 2 - (1 + 2 * ε * ∑ i, b i * x i ^ 2) *
        ((∑ i, ((1 + ε * b i) * v i) ^ 2
            - (∑ i, ((1 + ε * b i) * x i) * ((1 + ε * b i) * v i)) ^ 2 / ∑ i, ((1 + ε * b i) * x i) ^ 2)
          / ∑ i, ((1 + ε * b i) * x i) ^ 2)) * (∑ i, ((1 + ε * b i) * x i) ^ 2) ^ 2 = ε ^ 2 * P := by
  have hG := norm_sq_expand b v ε
  have hDe : ∑ i, ((1 + ε * b i) * x i) ^ 2
      = 1 + 2 * ε * ∑ i, b i * x i ^ 2 + ε ^ 2 * ∑ i, b i ^ 2 * x i ^ 2 := by
    have := norm_sq_expand b x ε
    rw [hx] at this
    exact this
  have hK := inner_expand b x v ε hxv
  have hD' : 1 + 2 * ε * ∑ i, b i * x i ^ 2 + ε ^ 2 * ∑ i, b i ^ 2 * x i ^ 2 ≠ 0 := by
    rw [← hDe]; exact hD
  rw [hG, hDe, hK]
  exact ⟨_, ellipsoid_conformal_first_order _ _ _ _ _ _ _ ε hD'⟩

/-! ### (2) 丸い S⁹ で規格化した固有値は臨界的 -/

/-- 【α-VII.4 (2)】Killing スピノル:T(X, Y) = μ(⟨XYψ, ψ⟩ + ⟨YXψ, ψ⟩) = −2μ g(X, Y)⟨ψ, ψ⟩
(φ は Clifford の元 a ↦ Re⟨aψ, ψ⟩、XY + YX = −2g) -/
theorem killing_stress {A : Type*} [Ring A] [Algebra ℝ A] (φ : A →ₗ[ℝ] ℝ) (X Y : A) (g μ : ℝ)
    (hcl : X * Y + Y * X = (-2 * g) • (1 : A)) :
    μ * φ (X * Y) + μ * φ (Y * X) = -2 * μ * g * φ 1 := by
  have h := congrArg φ hcl
  rw [map_add, map_smul, smul_eq_mul] at h
  linear_combination μ * h

/-- δλ = c·m(m = tr h の平均)が相似変換 h = 2g(m = 2n、δλ = −λ)でも成り立てば c = −λ/(2n) -/
theorem first_variation_coeff (lam n c : ℝ) (hn : n ≠ 0) (hsc : c * (2 * n) = -lam) :
    c = -(lam / (2 * n)) := by
  field_simp
  linarith

/-- 【α-VII.4 (2)】δN/N = δλ/λ + (1/n)·δVol/Vol = 0(δλ = −(λ/2n)m、δVol/Vol = m/2) -/
theorem normalized_first_variation (lam n m : ℝ) (hl : lam ≠ 0) (hn : n ≠ 0) :
    (-(lam / (2 * n)) * m) / lam + 1 / n * (m / 2) = 0 := by
  field_simp <;> ring

/-! ### (3) 2 次の係数は 1 次の方向だけで決まる -/

/-- 【α-VII.4 (3)】N₂ = Q(h₁) + N′[h₂] で N′ = 0 なら、h₂ によらず 2 次の係数は同じ -/
theorem second_order_equal {H : Type*} (Nd Q : H → ℝ) (hN : ∀ h, Nd h = 0) (h1 h2 h2' : H) :
    Q h1 + Nd h2 = Q h1 + Nd h2' := by
  rw [hN, hN]

/-- 【α-VII.4】まとめ:2 次の係数 99/250 > 0 なら ρ = 1 は楕円体族に沿った局所最小 -/
theorem ellipsoid_local_min (Λ : ℝ → ℝ)
    (hΛ : (fun t => Λ t - Λ 0 - (99 / 250) * t ^ 2) =o[𝓝 0] (fun t => t ^ 2)) :
    ∀ᶠ t in 𝓝 0, Λ 0 ≤ Λ t :=
  CFT.Z28Input.z28d_local_min Λ hΛ

end CFT.FixZ28
