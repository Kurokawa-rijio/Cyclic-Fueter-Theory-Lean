/-
  α-VI.6 (Z35) 物理的な内積 / α-VI.8 (Z37) 半古典極限

  首の縮約模型の位相空間は (a, b, p_a, p_b)、拘束は Hfun = 0。
  * K = (p_a² + 4c²(b² + ℓ²))/b は Dirac 観測量({K, H} = 0、AlphaVI `bracket_KH`)。
  * T = ab/(2p_a) も拘束面の上で Dirac 観測量:{T, H} = (b/2p_a²)·Hfun(`bracket_TH`)。
  * {T, K} = 1(AlphaVI `bracket_TK`)。したがって (K, T) は 2 次元の簡約位相空間の正準座標。

  量子化(簡約位相空間の量子化):
  * WDW の厳密解 Ψ_C = e^{iaσ_C/ħ}/σ_C(AlphaIV_WKB)は K̂ の固有関数で、固有値は C(`K_eigen`)。
    分離定数 C は Dirac 観測量 K の値そのもの。
  * Ψ_C が定義域 Q > 0 を持つのは C² > 64c⁴ℓ² のときに限る(`domain_nonempty_iff`)。
    物理的な状態は C の関数 f(C)(C > 8c²ℓ)、内積は ⟨f, g⟩ = ∫ f̄ g dC。
    正値性と規格化は L² の内積から(`phys_inner_nonneg`、`phys_inner_eq_zero`)。
    ゲージの冗長性(拘束が生成する時間の取り直し)は、Dirac 観測量 K の値で状態を表すことで除かれる。
    時間は関係的:T̂ = iħ ∂/∂C が K̂ に共役な時計。
  * 半古典極限:S_C = aσ_C(b) について ∂S/∂C = T(`dS_dC`)。波束 ∫ f(C) e^{i(S_C − CT₀)/ħ} dC の
    停留位相の条件 ∂S/∂C = T₀ は古典軌道 T = T₀ を与える(Jacobi の定理)。
    確率解釈は |f(C)|² dC(K の値の分布)、拘束の保存は {K, H} = 0 と {T, H} ≈ 0。
-/
import CFT.AlphaVI
import CFT.AlphaCompleteA
import CFT.AlphaIV_WKB

namespace CFT.Phys

open CFT.AlphaVI CFT.AlphaCompleteA Complex MeasureTheory

noncomputable section

/-- 【α-VI.8】T は拘束面の上で Dirac 観測量:{T, H} = (b/2p_a²) · Hfun -/
theorem bracket_TH (a b pa pb c l : ℝ) (hb : b ≠ 0) (hpa : pa ≠ 0) (hc : c ≠ 0) :
    Ta b pa * Hpa a b pa pb c + Tb a pa * Hpb b pa c - Tpa a b pa * Ha b pa c l - Tpb * Hb a b pa pb c l
      = b / (2 * pa ^ 2) * Hfun a b pa pb c l := by
  simp only [Ta, Tb, Tpa, Tpb, Ha, Hb, Hpa, Hpb, Hfun]
  field_simp
  ring

/-- 拘束面 Hfun = 0 の上で {T, H} = 0 -/
theorem bracket_TH_weak (a b pa pb c l : ℝ) (hb : b ≠ 0) (hpa : pa ≠ 0) (hc : c ≠ 0)
    (hH : Hfun a b pa pb c l = 0) :
    Ta b pa * Hpa a b pa pb c + Tb a pa * Hpb b pa c - Tpa a b pa * Ha b pa c l - Tpb * Hb a b pa pb c l
      = 0 := by
  rw [bracket_TH a b pa pb c l hb hpa hc, hH, mul_zero]

/-- 【α-VI.6】K̂ = (−ħ²∂_a² + 4c²(b² + ℓ²))/b について K̂Ψ_C = C Ψ_C(σ² = Cb − 4c²(b² + ℓ²) のとき)。
Ψ_aa は実際の a についての 2 階微分。 -/
theorem K_eigen (κ hb : ℝ) (hhb : hb * κ = 1) (c l C : ℝ) (A σ : ℝ → ℝ) (a b : ℝ) (hb0 : b ≠ 0)
    (hσ2 : σ b ^ 2 = C * b - 4 * c ^ 2 * (b ^ 2 + l ^ 2)) (Daa : ℂ)
    (hDaa : HasDerivAt (fun x => CFT.WKB.Psia κ A σ x b) Daa a) :
    (-(hb : ℂ) ^ 2 * Daa + 4 * (c : ℂ) ^ 2 * ((b : ℂ) ^ 2 + (l : ℂ) ^ 2) * CFT.WKB.Psi κ A σ a b) / b
      = (C : ℂ) * CFT.WKB.Psi κ A σ a b := by
  rw [hDaa.unique (CFT.WKB.hasDerivAt_Psia_a κ A σ a b)]
  have hu : (hb : ℂ) * (κ : ℂ) = 1 := by exact_mod_cast hhb
  have hI : I ^ 2 = -1 := I_sq
  have hσC : (σ b : ℂ) ^ 2 = (C : ℂ) * b - 4 * (c : ℂ) ^ 2 * ((b : ℂ) ^ 2 + (l : ℂ) ^ 2) := by
    exact_mod_cast hσ2
  have hb0' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
  rw [div_eq_iff hb0']
  generalize CFT.WKB.Psi κ A σ a b = P
  linear_combination (-(σ b : ℂ) ^ 2 * P * I ^ 2 * ((hb : ℂ) * κ + 1)) * hu
    + (-(σ b : ℂ) ^ 2 * P) * hI + P * hσC

/-- Q(b) > 0 となる b が存在する ⇔ C² > 64c⁴ℓ²(16c²Q(b) = C² − 64c⁴ℓ² − (8c²b − C)²) -/
theorem domain_nonempty_iff (c l C : ℝ) (hc : c ≠ 0) :
    (∃ b, 0 < CFT.WKB.Q c l C b) ↔ 64 * c ^ 4 * l ^ 2 < C ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have key : ∀ b, 16 * c ^ 2 * CFT.WKB.Q c l C b = C ^ 2 - 64 * c ^ 4 * l ^ 2 - (8 * c ^ 2 * b - C) ^ 2 := by
    intro b; simp only [CFT.WKB.Q]; ring
  constructor
  · rintro ⟨b, hb⟩
    have := key b
    nlinarith [sq_nonneg (8 * c ^ 2 * b - C), mul_pos hc2 hb]
  · intro h
    refine ⟨C / (8 * c ^ 2), ?_⟩
    have := key (C / (8 * c ^ 2))
    have h8 : 8 * c ^ 2 * (C / (8 * c ^ 2)) - C = 0 := by field_simp
    rw [h8] at this
    nlinarith

/-- 【α-VI.8】∂S/∂C = T:S_C = a√(Cb − 4c²(b² + ℓ²)) の C 微分は ab/(2σ) = T(a, b, p_a = σ) -/
theorem dS_dC (a b c l C : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) :
    HasDerivAt (fun C' => a * Real.sqrt (CFT.WKB.Q c l C' b))
      (a * b / (2 * Real.sqrt (CFT.WKB.Q c l C b))) C := by
  have hlin : HasDerivAt (fun C' => CFT.WKB.Q c l C' b) b C := by
    have h := ((hasDerivAt_id C).mul_const b).sub_const (4 * c ^ 2 * (b ^ 2 + l ^ 2))
    convert h using 1
    simp
  have h := (hlin.sqrt hQ.ne').const_mul a
  convert h using 1
  ring

/-- 物理的な状態空間:K の値 C > 8c²ℓ の上の L² 関数 -/
abbrev Hphys (c l : ℝ) := Lp ℂ 2 (volume.restrict (Set.Ioi (8 * c ^ 2 * l)))

/-- 【α-VI.6】物理的な内積は正値:⟨f, f⟩ ≥ 0 -/
theorem phys_inner_nonneg (c l : ℝ) (f : Hphys c l) : 0 ≤ RCLike.re (inner f f : ℂ) :=
  inner_self_nonneg

/-- 【α-VI.6】⟨f, f⟩ = 0 ⇔ f = 0(内積は非退化) -/
theorem phys_inner_eq_zero (c l : ℝ) (f : Hphys c l) : (inner f f : ℂ) = 0 ↔ f = 0 :=
  inner_self_eq_zero

end

end CFT.Phys
