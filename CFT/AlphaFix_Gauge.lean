/-
  独立監査(2026-11-04)の指摘を受けた作り直し:α-VIII.2、VII.8-C、VII.9(ゲージ場とスピノル)

  * VIII.2(運動学:Euclid 化したダンベルのスピン接続 Ω ∈ so(4)。作用:ヘテロティックの O(α′) の作用。
      力学:標準埋め込みで α′ 項が消える)
      監査:(i) Lorentz の接続 so(3,1) はコンパクトなゲージ代数に埋め込めない、(ii) ゲージ場の方程式に
      H の Chern–Simons から来る H·F の項がない。
      (i) 埋め込む接続を Euclid 化した断面(α′ の補正を評価する場所、IX.22)のスピン接続 Ω ∈ so(4)
          (反対称な実行列)に定める。ι は反対称性を保つ:Ωᵀ = −Ω ⇒ ι(Ω)ᵀ = −ι(Ω)(`iota_antisymm`)。
          so(4) ⊂ so(4 + m) はコンパクトなので問題は起きない。Lorentz 符号のままでは η ⊕ 1 に関して
          反対称になり、非コンパクトな代数に入る(文献の標準埋め込みも内部空間・Euclid の接続で行う)。
      (ii) F について線形な項 Σ h^{νρσ}F_ρσ を加えた方程式も埋め込みと可換(`ymH_embed`、`ymH_embed_iff`)。
  * VII.8-C(運動学:S⁹ の楕円体 {Σ a_i x_i² = 1}。作用:内部の Dirac 作用。力学:質量ゼロのモード)
      楕円体は凸:第二基本形式 II(v, v) = Σ a_i v_i²/N > 0(`ellipsoid_II_pos`、N = |∇F|/2)。主曲率がすべて
      正なら Gauss の式でスカラー曲率 Σ_{i≠j} κ_iκ_j > 0(`scal_pos_of_convex`)。Lichnerowicz の公式
      ‖Dψ‖² = ‖∇ψ‖² + ∫(scal/4)|ψ|² から ker D = 0(`no_massless_internal`、AlphaVII_Lichnerowicz)。
      結論(否定的):楕円体の族のどの ρ でも、内部の Dirac 作用素の核から質量ゼロのカイラルなモードは出ない。
      カイラルなモードは接合の壁(Jackiw–Rebbi、AlphaVII_Chirality)と ひねりの電荷(VII.9)から来る。
      外部:Gauss の式、II = Hess F/|∇F|、Lichnerowicz の公式(代数の核心は AlphaVII_Lichnerowicz で証明済み)。
  * VII.9(運動学:単位 S² と枠 e¹ = dθ、e² = sin θ dφ。力学:ひねりの電荷とゼロモード)
      スピン接続 ω = −cos θ dφ、曲率 dω = sin θ dθ∧dφ(`spin_curvature`、K = 1)、∫dω = 4π(`spin_flux`)、
      Gauss–Bonnet χ = 2(`euler_char`)。U(1)_F = ½ω でひねると電荷 q = (1/4π)·½·4π = 1/2 = χ/4
      (`twist_charge`)。q = 1/2 の単極子のゼロモード tan(θ/2)^m sin(θ)^q が両端で L² ⇔ m = 0
      (`twist_zero_mode`、AlphaVII ZeroModeL2):ゼロモードはちょうど 1 個。もう一方のカイラリティは空
      (`twist_chirality`)。
-/
import CFT.AlphaVIII_EOM
import CFT.AlphaVII_Lichnerowicz
import CFT.ZeroModeL2
import CFT.AlphaCompleteD
import Mathlib.Analysis.SpecialFunctions.Integrals

open Matrix

namespace CFT.FixGauge

open CFT.Embedding CFT.EmbeddingEOM

/-! ### VIII.2 Euclid の so(4) と H·F の項 -/

section Embed

variable {R : Type*} [CommRing R] [Algebra ℚ R] (d : Fin 4 → Derivation ℚ R R)
variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

set_option linter.unusedSectionVars false

/-- H の Chern–Simons から来る項を含むゲージ場の方程式 D_μ(wF) + Σ h^{νρσ}F_ρσ -/
def ymOpH {p : Type*} [Fintype p] (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) (h : Fin 4 → Fin 4 → Fin 4 → R)
    (A : Fin 4 → Matrix p p R) (ν : Fin 4) : Matrix p p R :=
  ymOp d w A ν + ∑ ρ, ∑ σ, h ν ρ σ • curv d A ρ σ

/-- 【α-VIII.2】H·F の項を含めても埋め込みと可換 -/
theorem ymH_embed (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) (h : Fin 4 → Fin 4 → Fin 4 → R)
    (Ω : Fin 4 → Matrix k k R) (ν : Fin 4) :
    ymOpH d w h (fun a => iota (m := m) (Ω a)) ν = iota (ymOpH d w h Ω ν) := by
  simp only [ymOpH, ym_embed, curvature_embed, ← iota_smul, ← iota_sum, iota_add]

/-- 【α-VIII.2】A = ι(Ω) の方程式 ⇔ Ω の方程式 -/
theorem ymH_embed_iff (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) (h : Fin 4 → Fin 4 → Fin 4 → R)
    (Ω : Fin 4 → Matrix k k R) (ν : Fin 4) :
    ymOpH d w h (fun a => iota (m := m) (Ω a)) ν = 0 ↔ ymOpH d w h Ω ν = 0 := by
  rw [ymH_embed]
  constructor
  · intro h0; exact iota_inj _ _ (h0.trans iota_zero.symm)
  · intro h0; rw [h0, iota_zero]

theorem iota_transpose (X : Matrix k k R) : (iota (m := m) X)ᵀ = iota Xᵀ := by
  simp [iota, Matrix.fromBlocks_transpose]

theorem iota_neg (X : Matrix k k R) : iota (m := m) (-X) = -iota X := by
  ext (i | i) (j | j) <;> simp [iota]

/-- 【α-VIII.2】ι は反対称性を保つ:so(4) の元は so(4 + m) に入る(コンパクト) -/
theorem iota_antisymm (X : Matrix k k R) (hX : Xᵀ = -X) : (iota (m := m) X)ᵀ = -iota X := by
  rw [iota_transpose, hX, iota_neg]

end Embed

/-! ### VII.8-C 内部の Dirac 作用素の核 -/

/-- 凸:主曲率がすべて正なら Σ_{i≠j} κ_iκ_j > 0(n ≥ 2) -/
theorem scal_pos_of_convex {n : ℕ} (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i) (hn : 2 ≤ n) :
    0 < ∑ i, ∑ j, if i = j then (0 : ℝ) else κ i * κ j := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  let i0 : Fin n := ⟨0, h0⟩
  let i1 : Fin n := ⟨1, h1⟩
  have hne : i0 ≠ i1 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  have hterm : ∀ i j : Fin n, 0 ≤ (if i = j then (0 : ℝ) else κ i * κ j) := by
    intro i j
    split_ifs
    · exact le_refl 0
    · exact (mul_pos (hκ i) (hκ j)).le
  apply Finset.sum_pos'
  · intro i _; exact Finset.sum_nonneg fun j _ => hterm i j
  · refine ⟨i0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro j _; exact hterm i0 j
    · refine ⟨i1, Finset.mem_univ _, ?_⟩
      rw [if_neg hne]
      exact mul_pos (hκ _) (hκ _)

/-- 楕円体の第二基本形式 II(v, v) = Σ a_i v_i²/N > 0(v ≠ 0) -/
theorem ellipsoid_II_pos {n : ℕ} (a v : Fin n → ℝ) (N : ℝ) (ha : ∀ i, 0 < a i) (hN : 0 < N) (hv : v ≠ 0) :
    0 < (∑ i, a i * v i ^ 2) / N := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hv
  have hi0' : v i0 ≠ 0 := by simpa using hi0
  refine div_pos ?_ hN
  apply Finset.sum_pos' (fun i _ => mul_nonneg (ha i).le (sq_nonneg _))
  exact ⟨i0, Finset.mem_univ _, mul_pos (ha i0) (by positivity)⟩

/-- 【α-VII.8-C】scal > 0 なら Lichnerowicz の公式から Dψ = 0 ⇒ ψ = 0:質量ゼロのモードはない -/
theorem no_massless_internal (Dpsi2 Npsi2 psi2 scal : ℝ) (hN : 0 ≤ Npsi2) (hp : 0 ≤ psi2) (hs : 0 < scal)
    (hL : Dpsi2 = Npsi2 + scal / 4 * psi2) (hD : Dpsi2 = 0) : psi2 = 0 :=
  CFT.Lichnerowicz.no_zero_mode Dpsi2 Npsi2 psi2 (scal / 4) hN hp (by positivity) hL hD

/-! ### VII.9 ひねりの電荷とゼロモード -/

open Real MeasureTheory Set

/-- 【α-VII.9】スピン接続 ω_φ = −cos θ の曲率 ∂_θω_φ = sin θ(K = 1) -/
theorem spin_curvature (θ : ℝ) : HasDerivAt (fun x => -cos x) (sin θ) θ := by
  simpa using (hasDerivAt_cos θ).neg

/-- Cartan の第一構造式の成分:d(sin θ)/dθ = cos θ(de² = cos θ dθ∧dφ = −ω²₁∧e¹) -/
theorem cartan_first (θ : ℝ) : HasDerivAt sin (cos θ) θ := hasDerivAt_sin θ

/-- 【α-VII.9】∫₀^{2π}∫₀^π sin θ dθ dφ = 4π -/
theorem spin_flux : ∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π, sin θ = 4 * π := by
  simp only [integral_sin, cos_zero, cos_pi, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- Gauss–Bonnet:χ = (1/2π)∫K dA = 2 -/
theorem euler_char : 1 / (2 * π) * ∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π, sin θ = 2 := by
  rw [spin_flux]
  have := pi_ne_zero
  field_simp <;> ring

/-- 【α-VII.9】½ スピン接続のひねり:q = (1/4π)·½·∫dω = 1/2(= χ/4) -/
theorem twist_charge : 1 / (4 * π) * (1 / 2 * ∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..π, sin θ) = 1 / 2 := by
  rw [spin_flux]
  have := pi_ne_zero
  field_simp <;> ring

/-- 【α-VII.9】q = 1/2 のゼロモード tan(θ/2)^m sin(θ)^{1/2} が両端で L² ⇔ m = 0(ちょうど 1 個) -/
theorem twist_zero_mode (m : ℤ) :
    (IntegrableOn (fun θ => (tan (θ / 2) ^ (m : ℝ) * sin θ ^ (1 / 2 : ℝ)) ^ 2) (Ioo 0 (π / 2)) ∧
      IntegrableOn (fun φ => (tan ((π - φ) / 2) ^ (m : ℝ) * sin (π - φ) ^ (1 / 2 : ℝ)) ^ 2) (Ioo 0 (π / 2)))
      ↔ m = 0 := by
  rw [ZeroModeL2.zero_mode_L2, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ← Int.cast_abs]
  constructor
  · intro h
    have h' : |m| < 1 := by exact_mod_cast h
    rw [abs_lt] at h'
    omega
  · rintro rfl
    norm_num

/-- 【α-VII.9】もう一方のカイラリティの分岐は空(q = 1/2) -/
theorem twist_chirality (m : ℝ) : ¬ ((1 : ℝ) / 2 - 1 / 2 < m ∧ m < 1 / 2 - 1 / 2) :=
  CFT.AlphaCompleteD.other_chirality_empty (1 / 2) m (le_refl _)

end CFT.FixGauge
