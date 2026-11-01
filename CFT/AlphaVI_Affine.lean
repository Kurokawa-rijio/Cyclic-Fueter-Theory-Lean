/-
  α-VI.6 (Z35):物理的な内積を、実の Dirac 観測量が自己共役になる条件(Ashtekar の reality conditions)から決める

  簡約位相空間の座標:K(Dirac 観測量、K > K₀ = 8c²ℓ)と D = (K − K₀)T({D, K} = K − K₀、AlphaVI_Physical2)。
  (K − K₀, D) は affine 群「ax + b」の Lie 代数を張る。

  物理的な内積の要請(標準的な基準。Ashtekar–Tate 1991、Isham 1984)
    (P1) 実の Dirac 観測量 K、D は自己共役な作用素で表す。
    (P2) K のスペクトルは古典的な値域と一致:K̂ − K₀ > 0。
    (P3) 各セクターで既約。
  (P1)〜(P3) をみたす affine 群のユニタリ表現は、同値を除いてただ一つ(Gel'fand–Naimark 1947、
  "Unitary representations of the group of linear transformations of the straight line"、
  Doklady 55, 567–570。正の軌道の既約表現の一意性。Stone の定理で自己共役な生成子と強連続な
  ユニタリ群が一対一に対応)。その実現を Lean で作り、性質を確かめる:
  * H = L²((0, ∞), dk)、k = K − K₀。U(α, τ)ψ(k) = e^{iτkκ} √α ψ(αk)(κ = 1/ħ)
  * 群の法則 U(α, τ)U(β, σ) = U(αβ, τ + ασ)(`affine_group_law`)
  * ユニタリ:∫|U(α, τ)ψ|² = ∫|ψ|²(`affine_unitary`)
  * K̂ψ = (K₀ + k)ψ、D̂ψ = iħ(kψ′ + ½ψ) は交換関係 [D̂, K̂] = iħ(K̂ − K₀) をみたす(`affine_commutator`)。
    これは古典の {D, K} = K − K₀ の量子化。
  * K̂ − K₀ ≥ 0:⟨ψ, (K̂ − K₀)ψ⟩ = ∫ k|ψ|² ≥ 0(`K_positive`)
  したがって物理的な内積 ⟨f, g⟩ = ∫₀^∞ f̄ g dk は (P1)〜(P3) から一意に決まる。

  セクター:WDW の二つの枝 p_a = ±√Q は affine 群の正負の軌道ではない(K − K₀ > 0 は p_a の符号によらない)。
  a, b > 0 では T = ab/(2p_a) の符号 = p_a の符号(`sector_sign`)で、T は保存するので符号は軌道に沿って
  変わらない(AlphaVI_Physical `bracket_TH_weak`)。したがって
    H_phys = L²((0, ∞), dk) ⊗ ℂ²(多重度 2、超選択則で分かれる二つのセクター)
  で、各セクターに上の表現が一つずつ乗る(Klein–Gordon の正負の周波数と同じ構造)。
  T̂ = iħ∂_K は半直線上で自己共役にならないので、時計としては使わない。
-/
import CFT.AlphaVI_Physical2

namespace CFT.Affine

open MeasureTheory Set Complex

noncomputable section

/-- affine 群のユニタリ表現 U(α, τ)ψ(k) = e^{iτkκ} √α ψ(αk) -/
def U (κ α τ : ℝ) (ψ : ℝ → ℂ) (k : ℝ) : ℂ :=
  Complex.exp (((τ * k * κ : ℝ) : ℂ) * I) * ((Real.sqrt α : ℝ) : ℂ) * ψ (α * k)

/-- 【α-VI.6】群の法則:U(α, τ)U(β, σ) = U(αβ, τ + ασ)(α, β > 0) -/
theorem affine_group_law (κ α β τ σ : ℝ) (hα : 0 < α) (hβ : 0 < β) (ψ : ℝ → ℂ) :
    U κ α τ (U κ β σ ψ) = U κ (α * β) (τ + α * σ) ψ := by
  funext k
  simp only [U]
  rw [Real.sqrt_mul hα.le β, show β * (α * k) = α * β * k by ring]
  have e : Complex.exp (((τ * k * κ : ℝ) : ℂ) * I) * Complex.exp (((σ * (α * k) * κ : ℝ) : ℂ) * I)
      = Complex.exp ((((τ + α * σ) * k * κ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← e]
  push_cast
  ring

/-- 【α-VI.6】ユニタリ:U(α, τ) は L²((0, ∞), dk) のノルムを保つ -/
theorem affine_unitary (κ α τ : ℝ) (hα : 0 < α) (ψ : ℝ → ℂ) :
    ∫ k in Ioi (0 : ℝ), ‖U κ α τ ψ k‖ ^ 2 = ∫ k in Ioi (0 : ℝ), ‖ψ k‖ ^ 2 := by
  have h : ∀ k, ‖U κ α τ ψ k‖ = ‖((Real.sqrt α : ℝ) : ℂ) * ψ (α * k)‖ := by
    intro k
    simp only [U]
    rw [mul_assoc, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simp_rw [h]
  exact CFT.Phys2.dilation_isometry ψ α hα

/-- 【α-VI.6】交換関係:K̂ψ = (K₀ + k)ψ、D̂ψ = iħ(kψ′ + ½ψ) について
D̂(K̂ψ) − K̂(D̂ψ) = iħ(K̂ − K₀)ψ(各点 k で、ψ′ = ψ の微分) -/
theorem affine_commutator (hb K0 k : ℝ) (ψ : ℝ → ℂ) (ψ' : ℂ) (hψ : HasDerivAt ψ ψ' k) :
    HasDerivAt (fun x => ((K0 + x : ℝ) : ℂ) * ψ x) (ψ k + ((K0 + k : ℝ) : ℂ) * ψ') k ∧
    I * hb * ((k : ℂ) * (ψ k + ((K0 + k : ℝ) : ℂ) * ψ') + 1 / 2 * (((K0 + k : ℝ) : ℂ) * ψ k))
      - ((K0 + k : ℝ) : ℂ) * (I * hb * ((k : ℂ) * ψ' + 1 / 2 * ψ k))
      = I * hb * ((k : ℂ) * ψ k) := by
  constructor
  · have h1 : HasDerivAt (fun x : ℝ => ((K0 + x : ℝ) : ℂ)) 1 k := by
      have := ((hasDerivAt_id k).const_add K0).ofReal_comp
      simpa using this
    have h := h1.mul hψ
    simpa using h
  · push_cast
    ring

/-- 【α-VI.6】K̂ − K₀ は正:⟨ψ, (K̂ − K₀)ψ⟩ = ∫₀^∞ k|ψ|² dk ≥ 0 -/
theorem K_positive (ψ : ℝ → ℂ) : 0 ≤ ∫ k in Ioi (0 : ℝ), k * ‖ψ k‖ ^ 2 :=
  setIntegral_nonneg measurableSet_Ioi (fun k hk => mul_nonneg (le_of_lt hk) (sq_nonneg _))

/-- 【α-VI.6】セクター:a, b > 0 なら T = ab/(2p_a) の符号は p_a の符号 -/
theorem sector_sign (a b pa : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (0 < a * b / (2 * pa) ↔ 0 < pa) := by
  have hab : 0 < a * b := mul_pos ha hb
  constructor
  · intro h
    by_contra hp
    push_neg at hp
    have : a * b / (2 * pa) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hab.le (by linarith)
    linarith
  · intro hp
    positivity

end

end CFT.Affine
