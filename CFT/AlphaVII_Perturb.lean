/-
  α-VII.4(Z28-d):二次の摂動公式(Rayleigh–Schrödinger)の形式化

  実内積空間 E 上の対称作用素 H(ε) = H₀ + εV + ε²W、固有値 E(ε) = E₀ + εE₁ + ε²E₂、
  固有ベクトル ψ(ε) = ψ₀ + εψ₁ + ε²ψ₂(中間規格化 ⟨ψ₀, ψ₁⟩ = 0)を次数ごとに比べる。
    * rs_coefficients:E₁ = ⟨ψ₀, Vψ₀⟩、E₂ = ⟨ψ₀, Wψ₀⟩ + ⟨ψ₀, Vψ₁⟩
    * rs_single_level:E₀ が単純で、(V − E₁)ψ₀ = u が固有値 E₀ + L の固有ベクトルなら
        ψ₁ = −u/L、E₂ = ⟨ψ₀, Wψ₀⟩ − ‖u‖²/L
  Z28-d への適用(z28d_from_rs):S⁹ 上 ψ₀ = 定数、u は 2 次の球面調和関数(L = k(k+n−1) = 20)。
    ‖u‖² = (n²(n−1)/4)·A、⟨ψ₀, Wψ₀⟩ = −(n/4)·A(A = Var X = 1/25)
  を入力として、λ₂ = −207/500、係数 n²A/4 + λ₂ = 99/250 を得る。
  入力のうち「X − E X が 2 次の球面調和関数」は標準的な事実(X = Σ_{i≤4} y_i² と |y|² の組合せが
  ℝ¹⁰ の調和多項式)。V と W の係数 n√(n−1)/2、−n/4 の出所は元の作用素が手元になく未確定。
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import CFT.Basic

namespace CFT.Perturb

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- 一次と二次の係数 -/
theorem rs_coefficients {H₀ V W : E →ₗ[ℝ] E} (hH : H₀.IsSymmetric)
    {ψ₀ ψ₁ ψ₂ : E} {E₀ E₁ E₂ : ℝ} (hn : ⟪ψ₀, ψ₀⟫ = 1)
    (h0 : H₀ ψ₀ = E₀ • ψ₀)
    (h1 : H₀ ψ₁ + V ψ₀ = E₀ • ψ₁ + E₁ • ψ₀)
    (h2 : H₀ ψ₂ + V ψ₁ + W ψ₀ = E₀ • ψ₂ + E₁ • ψ₁ + E₂ • ψ₀)
    (hnorm : ⟪ψ₀, ψ₁⟫ = 0) :
    E₁ = ⟪ψ₀, V ψ₀⟫ ∧ E₂ = ⟪ψ₀, W ψ₀⟫ + ⟪ψ₀, V ψ₁⟫ := by
  have key : ∀ x : E, ⟪ψ₀, H₀ x⟫ = E₀ * ⟪ψ₀, x⟫ := by
    intro x; rw [← hH ψ₀ x, h0, real_inner_smul_left]
  constructor
  · have := congrArg (fun z => ⟪ψ₀, z⟫) h1
    simp only [inner_add_right, real_inner_smul_right, key, hnorm, hn] at this
    linarith
  · have := congrArg (fun z => ⟪ψ₀, z⟫) h2
    simp only [inner_add_right, real_inner_smul_right, key, hnorm, hn] at this
    linarith

/-- 励起準位が一つだけの場合:ψ₁ = −u/L、E₂ = ⟨Wψ₀⟩ − ‖u‖²/L -/
theorem rs_single_level {H₀ V W : E →ₗ[ℝ] E} (hH : H₀.IsSymmetric) (hV : V.IsSymmetric)
    {ψ₀ ψ₁ ψ₂ u : E} {E₀ E₁ E₂ L : ℝ} (hn : ⟪ψ₀, ψ₀⟫ = 1)
    (h0 : H₀ ψ₀ = E₀ • ψ₀)
    (h1 : H₀ ψ₁ + V ψ₀ = E₀ • ψ₁ + E₁ • ψ₀)
    (h2 : H₀ ψ₂ + V ψ₁ + W ψ₀ = E₀ • ψ₂ + E₁ • ψ₁ + E₂ • ψ₀)
    (hnorm : ⟪ψ₀, ψ₁⟫ = 0)
    (hsimple : ∀ x, H₀ x = E₀ • x → ∃ c : ℝ, x = c • ψ₀)
    (hu : V ψ₀ - E₁ • ψ₀ = u) (hexc : H₀ u = (E₀ + L) • u) (hL : L ≠ 0) :
    ψ₁ = -(1 / L) • u ∧ E₂ = ⟪ψ₀, W ψ₀⟫ - ⟪u, u⟫ / L := by
  obtain ⟨_, hE2⟩ := rs_coefficients hH hn h0 h1 h2 hnorm
  -- u ⟂ ψ₀
  have hu0 : ⟪ψ₀, u⟫ = 0 := by
    have e1 : ⟪ψ₀, H₀ u⟫ = (E₀ + L) * ⟪ψ₀, u⟫ := by rw [hexc, real_inner_smul_right]
    have e2 : ⟪ψ₀, H₀ u⟫ = E₀ * ⟪ψ₀, u⟫ := by rw [← hH ψ₀ u, h0, real_inner_smul_left]
    have : L * ⟪ψ₀, u⟫ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hL
  -- y = L•ψ₁ + u は E₀ の固有ベクトル
  have hVψ : V ψ₀ = u + E₁ • ψ₀ := by rw [← hu]; abel
  have h1' : H₀ ψ₁ = E₀ • ψ₁ + E₁ • ψ₀ - V ψ₀ := by rw [← h1]; abel
  have hHy : H₀ (L • ψ₁ + u) = E₀ • (L • ψ₁ + u) := by
    rw [map_add, map_smul, h1', hexc, hVψ]
    module
  obtain ⟨c, hc⟩ := hsimple _ hHy
  have hc0 : c = 0 := by
    have := congrArg (fun z => ⟪ψ₀, z⟫) hc
    simp only [inner_add_right, real_inner_smul_right, hnorm, hu0, hn] at this
    linarith
  have hψ1 : ψ₁ = -(1 / L) • u := by
    have h0' : L • ψ₁ + u = 0 := by rw [hc, hc0, zero_smul]
    have : L • ψ₁ = -u := eq_neg_of_add_eq_zero_left h0'
    calc ψ₁ = (1 / L) • (L • ψ₁) := by rw [smul_smul, one_div, inv_mul_cancel₀ hL, one_smul]
      _ = -(1 / L) • u := by rw [this, smul_neg, neg_smul]
  refine ⟨hψ1, ?_⟩
  have hVu : ⟪ψ₀, V u⟫ = ⟪u, u⟫ := by
    rw [← hV ψ₀ u, hVψ, inner_add_left, real_inner_smul_left, hu0, mul_zero, add_zero]
  rw [hE2, hψ1, map_smul, real_inner_smul_right, hVu]
  ring

/-- Z28-d:入力 ‖u‖² = (n²(n−1)/4)A、⟨Wψ₀⟩ = −(n/4)A、L = k(k+n−1) のもとでの λ₂ と係数 -/
theorem z28d_from_rs (n k A lam2 : ℝ) (hL : k * (k + n - 1) ≠ 0)
    (hlam : lam2 = -(n / 4) * A - (n ^ 2 * (n - 1) / 4 * A) / (k * (k + n - 1))) :
    n ^ 2 / 4 * A + lam2 = n * (n - 1) / 4 * (1 - n / (k * (k + n - 1))) * A := by
  rw [hlam]; field_simp; ring

theorem z28d_values : (-(9 / 4 : ℝ) * (1 / 25) - (9 ^ 2 * (9 - 1) / 4 * (1 / 25)) / (2 * (2 + 9 - 1)))
    = -207 / 500 ∧
    (9 : ℝ) ^ 2 / 4 * (1 / 25) + (-207 / 500) = 99 / 250 := by
  constructor <;> norm_num

end CFT.Perturb
