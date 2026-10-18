/-
  作用原理を幾何から導く(α-II.1 の作り直しの後半)

  原理 1(群):ゲージ群は量子球面 Q そのもの、単位四元数 = SU(2) = Spin(3)。
  原理 2(自然さ):微分は 2 階まで、座標変換とゲージ変換で不変。四次元ではこれで作用は
    R/(16πG) − Λ/(8πG) − (1/2g²) tr F²(+ 運動方程式に効かない θ 項)に限られる
    (Lovelock の定理と Yang–Mills の一意性、外部定理)。
  原理 3(U21′):ゲージ場 = 空間の切り口のスピン接続。
    * spin_torsion_free:ds² + r²dΩ² の正規直交枠 e^s = ds、e^θ = r dθ、e^φ = r sinθ dφ に対し、
      ω^θ_s = r′dθ、ω^φ_s = r′ sinθ dφ、ω^φ_θ = cosθ dφ は捩れがない(Cartan の第一構造式、27 成分すべて)
    * spin_is_witten:so(3) ≅ su(2) で、このスピン接続は Witten の球対称な形
      A = W(τ₁dθ + τ₂ sinθ dφ) + τ₃ cosθ dφ の W = r′ に当たる
      ⇒ U21′ の W = r′ は「Yang–Mills 場 = 空間のスピン接続」と同値
    * s3_spin_connection:半径 1 の S³ = SU(2) の左不変な枠(de^a = −ε_abc e^b∧e^c)では
      ω^a_b = −ε_abc e^c が捩れなし・反対称(A_F = ½U⁻¹dU、λ = ½ のメロン)
  原理 2 の残りの自由度 Λ は、帽子と首の貼り合わせで 0 に決まる:
    * lambda_zero:³R = 16πGρ + 2Λ を帽子(³R = 6/ℓ²、16πGρ = 3k/ℓ⁴)と首(³R = 2/ℓ²、16πGρ = k/ℓ⁴)
      で同時に満たすなら Λ = 0、k = 2ℓ²(k = 8πG/g²、つまり ℓ² = 4πG/g²)
  結論:S = ∫√−g [R/(16πG) − (1/2g²) tr F²] + (1/8πG)∮ε√|h| K(Gibbons–Hawking–York 項)、ℓ² = 4πG/g²。
  YM の部分は A を境界で固定する変分では境界項が要らない(1 階微分の作用、磁荷は位相的に固定)。
    * coupling_size、strong_or_classical:α·ℓ² = ℓ_P²(α = g²/4π)。強い結合と古典的な大きさは両立しない
    * junction_ghy:接合部では両側で K_ab = 0、GHY 項の寄与は 0、Israel 条件は殻なし、lapse も C¹ でつながる
  W = r′ は作用に代入するのではなく(代入すると高階微分の別の理論になる)、初期データの条件として課す。
  それが力学で保たれるのは三つの相(AlphaII_EYM)。
-/
import CFT.Basic

namespace CFT.Action

/-! ### スピン接続(座標 0 = s、1 = θ、2 = φ、枠 0 = s、1 = θ、2 = φ) -/

variable (r rp S C : ℝ)

/-- e^a_i -/
def e : Fin 3 → Fin 3 → ℝ := fun a i => if a = i then ![1, r, r * S] a else 0

/-- (de^a)_{ij} = ∂_i e^a_j − ∂_j e^a_i:非零は (de^θ)_{sθ} = r′、(de^φ)_{sφ} = r′S、(de^φ)_{θφ} = rC -/
def de : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a i j =>
  if a = 1 ∧ i = 0 ∧ j = 1 then rp else if a = 1 ∧ i = 1 ∧ j = 0 then -rp
  else if a = 2 ∧ i = 0 ∧ j = 2 then rp * S else if a = 2 ∧ i = 2 ∧ j = 0 then -(rp * S)
  else if a = 2 ∧ i = 1 ∧ j = 2 then r * C else if a = 2 ∧ i = 2 ∧ j = 1 then -(r * C) else 0

/-- ω^a_{b,i}:ω^θ_s = r′dθ、ω^φ_s = r′S dφ、ω^φ_θ = C dφ と反対称 -/
def om : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b i =>
  if a = 1 ∧ b = 0 ∧ i = 1 then rp else if a = 0 ∧ b = 1 ∧ i = 1 then -rp
  else if a = 2 ∧ b = 0 ∧ i = 2 then rp * S else if a = 0 ∧ b = 2 ∧ i = 2 then -(rp * S)
  else if a = 2 ∧ b = 1 ∧ i = 2 then C else if a = 1 ∧ b = 2 ∧ i = 2 then -C else 0

/-- 捩れ T^a_{ij} = (de^a)_{ij} + Σ_b (ω^a_{b,i} e^b_j − ω^a_{b,j} e^b_i) -/
def torsion (a i j : Fin 3) : ℝ :=
  de r rp S C a i j + ∑ b, (om rp S C a b i * e r S b j - om rp S C a b j * e r S b i)

theorem spin_torsion_free : ∀ a i j, torsion r rp S C a i j = 0 := by
  intro a i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [torsion, de, om, e, Fin.sum_univ_three] <;> ring

theorem spin_antisymmetric : ∀ a b i, om rp S C a b i = -om rp S C b a i := by
  intro a b i
  fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [om]

/-- Witten の形との対応:(ω^θ_s, ω^φ_s, ω^φ_θ) の係数は (W dθ, W sinθ dφ, cosθ dφ) で W = r′ -/
theorem spin_is_witten :
    (om rp S C 1 0 1, om rp S C 2 0 2, om rp S C 2 1 2) = (rp * 1, rp * S, C) := by
  simp [om]

/-! ### S³ = SU(2) のスピン接続 -/

/-- Levi-Civita 記号 -/
noncomputable def eps (a b c : Fin 3) : ℝ :=
  ((b.val : ℝ) - a.val) * ((c.val : ℝ) - a.val) * ((c.val : ℝ) - b.val) / 2

/-- 左不変な枠で de^a = −ε_abc e^b∧e^c、成分 (de^a)_{bc} = −2ε_abc;ω^a_{b,c} = −ε_abc。
    捩れ (de^a)_{ij} + ω^a_{b,i}δ^b_j − ω^a_{b,j}δ^b_i = 0 -/
theorem s3_spin_connection :
    (∀ a i j, -2 * eps a i j + (-eps a j i) - (-eps a i j) = 0) ∧
    (∀ a b c, -eps a b c = -(-eps b a c)) := by
  constructor <;> intro a b c <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [eps] <;> norm_num

/-! ### Λ は貼り合わせで 0 -/

theorem lambda_zero (l k Λ : ℝ) (hl : l ≠ 0)
    (hcap : 6 / l ^ 2 = 3 * k / l ^ 4 + 2 * Λ) (hneck : 2 / l ^ 2 = k / l ^ 4 + 2 * Λ) :
    Λ = 0 ∧ k = 2 * l ^ 2 := by
  have e1 : 3 * k / l ^ 4 = 3 * (k / l ^ 4) := by ring
  have e2 : 6 / l ^ 2 = 3 * (2 / l ^ 2) := by ring
  have hΛ : Λ = 0 := by rw [e1, e2] at hcap; linarith
  refine ⟨hΛ, ?_⟩
  rw [hΛ] at hneck
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  field_simp at hneck
  have : l ^ 2 * (2 * l ^ 2 - k) = 0 := by nlinarith [hneck]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hl2
  · linarith

/-! ### 境界項(Gibbons–Hawking–York)と接合 -/

/-- 計量 −N²dt² + ds² + r²dΩ² の面 s = 一定(法線 ∂_s)の外曲率は K_tt = −NN′、K_θθ = rr′、K_φφ = rr′sin²θ、
    跡 K = N′/N + 2r′/r。接合 s = πℓ/2(首側は s′ = 0):帽子は測地的な時間 N = 1、首は N = cosh(s′/ℓ)。
    両側で N = 1、N′ = 0、r′ = 0 なので K_ab = 0 と K = 0:GHY 項の寄与は 0、
    二つの側の GHY 項から出る Israel 条件は [K_ab] = 0(殻なし)。lapse も C¹ でつながる -/
theorem junction_ghy (l θ : ℝ) (hl : l ≠ 0) :
    -- 帽子側(N = 1、N′ = 0、r = ℓ sin(π/2)、r′ = cos(π/2))
    (-(1 : ℝ) * 0 = 0 ∧ l * Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) = 0 ∧
      0 / 1 + 2 * Real.cos (Real.pi / 2) / (l * Real.sin (Real.pi / 2)) = 0) ∧
    -- 首側(N = cosh 0、N′ = sinh 0 / ℓ、r = ℓ、r′ = 0)
    (-(Real.cosh 0) * (Real.sinh 0 / l) = 0 ∧ l * 0 * Real.sin θ ^ 2 = 0 ∧
      (Real.sinh 0 / l) / Real.cosh 0 + 2 * 0 / l = 0) ∧
    -- lapse の C¹ 接続
    (Real.cosh 0 = 1 ∧ Real.sinh 0 / l = 0) := by
  simp [Real.cos_pi_div_two]

/-! ### 結合の強さと大きさの両立しない関係 -/

/-- ℓ² = 4πG/g²、ℓ_P² = G(ħ = c = 1)、α = g²/(4π) なら α·ℓ² = ℓ_P²:結合定数 = (ℓ_P/ℓ)² -/
theorem coupling_size (G g l lP α : ℝ) (hg : g ≠ 0) (hl : l ^ 2 = 4 * Real.pi * G / g ^ 2)
    (hP : lP ^ 2 = G) (hα : α = g ^ 2 / (4 * Real.pi)) : α * l ^ 2 = lP ^ 2 := by
  have hπ := Real.pi_ne_zero
  rw [hα, hl, hP]; field_simp; ring

/-- 強い結合(α ≥ α₀ > 0)なら ℓ² ≤ ℓ_P²/α₀(Planck 長さ程度)、
    古典的に大きい(ℓ² ≥ L² > 0)なら α ≤ ℓ_P²/L²(弱い結合):二つは同時に成り立たない -/
theorem strong_or_classical (α l lP α0 L : ℝ) (h : α * l ^ 2 = lP ^ 2) (hα0 : 0 < α0) (hL : 0 < L) :
    (α0 ≤ α → l ^ 2 ≤ lP ^ 2 / α0) ∧ (L ^ 2 ≤ l ^ 2 → 0 ≤ α → α ≤ lP ^ 2 / L ^ 2) := by
  constructor
  · intro hα
    rw [le_div_iff hα0]
    nlinarith [sq_nonneg l]
  · intro hl hα
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg L]

end CFT.Action
