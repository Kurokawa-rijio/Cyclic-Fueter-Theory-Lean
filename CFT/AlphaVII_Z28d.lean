/-
  α-VII.4(Z28-d):S⁹ の Dirac 作用素の二次摂動(台帳の H(ε) からの導出)

  作用素族:丸い S⁹(n = 9)の共形変形 g_t = e^{2tf}g₀、f = |y_H|² − 2/5(R¹⁰ = R⁴ ⊕ R⁶ の楕円体変形の
  形状部分)。Dirac 作用素の共形共変性で固有値問題は D₀φ = λ e^{tf} φ になる。
  抽象化:実内積空間 E 上の対称作用素 D(= D₀)と M(= f の掛け算)、最低固有値 a = n/2、
  単位の固有ベクトル ψ(Killing スピノル)、u = Mψ(= fψ)、w(= df·ψ、Clifford 積)。
  入力(Killing スピノルと球面調和関数の標準的な事実):
    D u = a u + w、D w = L u − ((n−2)/2) w(L = k(k+n−1) = 20)、⟨u, w⟩ = 0(交差項が消える)、
    固有空間 ker(D − a) の全体で ⟨u, k⟩ = 0(PfP = 0)、⟨u, u⟩ = A(Killing スピノルのノルムは一定)。
  結論:
    * resolvent_formula:(D − a)((n−1)/L·u + (1/L)·w) = u
    * z28d_first:λ₁ = 0
    * z28d_second:λ₂ = −(n²(n−1)/(4L))A − (n/4)A(縮退した固有空間のどのベクトルを φ₁ に足してもよい)
    * vol_root_deriv:x^{1/9} の x = 1 での微分は 1/9(Vol^{1/9} の二次係数 (1/9)(81/2)A = (9/2)A)
    * z28d_normalized:a·(n/2)A + λ₂ = n(n−1)/4·(1 − n/L)·A、n = 9、L = 20、A = 1/25 で 99/250
  楕円体族と共形族の二次係数の一致(微分同相と全体のスケールを除いて一次の接方向が同じ)は
  台帳の論証のままで、ここでは入力。ρ = 1 が大域的な最小点だという主張は撤回済み(局所の主張だけ)。
-/
import CFT.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace CFT.Z28d

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- (D − a)⁻¹ u の明示形 -/
theorem resolvent_formula (D : E →ₗ[ℝ] E) (a n L : ℝ) (u w : E) (hL : L ≠ 0) (ha : a = n / 2)
    (hu : D u = a • u + w) (hw : D w = L • u - ((n - 2) / 2) • w) :
    D (((n - 1) / L) • u + (1 / L) • w) - a • (((n - 1) / L) • u + (1 / L) • w) = u := by
  rw [map_add, map_smul, map_smul, hu, hw, ha]
  simp only [smul_add, smul_sub, smul_smul]
  have e1 : (1 / L) * L = 1 := by field_simp
  rw [e1, one_smul]
  module

variable (D M : E →ₗ[ℝ] E) (hD : D.IsSymmetric) (hM : M.IsSymmetric)

include hD in
/-- 一次:λ₁ = 0 -/
theorem z28d_first (a l1 : ℝ) (ψ φ1 : E) (hn : ⟪ψ, ψ⟫ = 1) (hψ : D ψ = a • ψ)
    (hPfP : ⟪ψ, M ψ⟫ = 0) (hnorm : ⟪ψ, φ1⟫ = 0)
    (h1 : D φ1 = a • φ1 + a • M ψ + l1 • ψ) : l1 = 0 := by
  have := congrArg (fun z => ⟪ψ, z⟫) h1
  simp only [inner_add_right, real_inner_smul_right, hPfP, hn, hnorm] at this
  rw [← hD ψ φ1, hψ, real_inner_smul_left, hnorm] at this
  linarith

include hD hM in
/-- 二次:λ₂ = −a²(n−1)/L·A − (a/2)A -/
theorem z28d_second (a n L A l2 : ℝ) (ψ φ1 φ2 w : E) (hL : L ≠ 0) (ha : a = n / 2)
    (hn : ⟪ψ, ψ⟫ = 1) (hψ : D ψ = a • ψ)
    (hu : D (M ψ) = a • M ψ + w) (hw : D w = L • M ψ - ((n - 2) / 2) • w)
    (hcross : ⟪M ψ, w⟫ = 0) (hker : ∀ k, D k = a • k → ⟪M ψ, k⟫ = 0) (hA : ⟪M ψ, M ψ⟫ = A)
    (h1 : D φ1 = a • φ1 + a • M ψ)
    (h2 : D φ2 = a • φ2 + a • M φ1 + (a / 2) • M (M ψ) + l2 • ψ) :
    l2 = -(a ^ 2 * ((n - 1) / L) * A) - (a / 2) * A := by
  -- φ₁ − a·R u は固有空間に入る
  set R := ((n - 1) / L) • M ψ + (1 / L) • w with hR
  have hres := resolvent_formula D a n L (M ψ) w hL ha hu hw
  have hk : D (φ1 - a • R) = a • (φ1 - a • R) := by
    rw [map_sub, map_smul, h1]
    have : D R = a • R + M ψ := by rw [← hres]; abel
    rw [this]; simp only [smul_add, smul_sub, smul_smul]; abel
  have hk0 := hker _ hk
  have hφ1 : ⟪M ψ, φ1⟫ = a * ((n - 1) / L) * A := by
    have : φ1 = (φ1 - a • R) + a • R := by abel
    rw [this, inner_add_right, hk0, real_inner_smul_right, hR, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, hA, hcross]
    ring
  -- 二次の式を ψ に射影
  have := congrArg (fun z => ⟪ψ, z⟫) h2
  simp only [inner_add_right, real_inner_smul_right, hn] at this
  rw [← hD ψ φ2, hψ, real_inner_smul_left, ← hM ψ φ1, ← hM ψ (M ψ), hφ1, hA] at this
  linarith

/-- 体積の正規化:x ↦ x^{1/9} の x = 1 での微分は 1/9 -/
theorem vol_root_deriv : HasDerivAt (fun x : ℝ => x ^ (1 / 9 : ℝ)) (1 / 9) 1 := by
  have := Real.hasDerivAt_rpow_const (x := 1) (p := 1 / 9) (Or.inl one_ne_zero)
  simpa using this

/-- Vol(g_t) = V₀(1 + (81/2)A t² + …) なら Vol^{1/9} = V₀^{1/9}(1 + (9/2)A t² + …) の係数 -/
theorem vol_coefficient (A : ℝ) : (1 / 9 : ℝ) * (81 / 2 * A) = 9 / 2 * A := by ring

/-- 正規化した不変量の二次係数 -/
theorem z28d_normalized (n L A : ℝ) (hL : L ≠ 0) :
    (n / 2) * (n / 2 * A) + (-((n / 2) ^ 2 * ((n - 1) / L) * A) - (n / 2 / 2) * A)
      = n * (n - 1) / 4 * (1 - n / L) * A := by
  field_simp; ring

/-- n = 9、L = 2(2 + 9 − 1) = 20、A = 1/25 で λ₂ = −207/500、係数 99/250 -/
theorem z28d_values :
    (2 * (2 + 9 - 1) : ℝ) = 20 ∧
    (-((9 / 2 : ℝ) ^ 2 * ((9 - 1) / 20) * (1 / 25)) - (9 / 2 / 2) * (1 / 25)) = -207 / 500 ∧
    (9 : ℝ) * (9 - 1) / 4 * (1 - 9 / 20) * (1 / 25) = 99 / 250 := by
  norm_num

end CFT.Z28d
