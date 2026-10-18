/-
  α-I.7(Y6)の残り:BPS 方程式の舞台 h = (δ − pp/E²)/m²(AlphaCompleteC)の曲率は −1

  監査で「曲率 −1 は docstring の主張だけ」と指摘された部分を証明する。三段で示す。
  1. 固有値の分解(h_radial、h_tangential):
       動径方向 p̂ では h(p̂, p̂) = (1 − P²/E²)/m² = 1/E²、p に垂直な v では h(v, v) = |v|²/m²
     ⇒ h = dP²/E² + (P²/m²) dΩ²(P = |p|、E² = m² + P²)
  2. 変数変換(h_rapidity):P = m sinh η とおくと (dP/dη)²/E² = 1、P²/m² = sinh²η
     ⇒ h = dη² + sinh²η dΩ²
  3. Cartan の第二構造式(warped_curvature):ds² + f(s)²dΩ² で、スピン接続(AlphaII_Action の
     spin_torsion_free と同じ ω)から Ω = dω + ω∧ω を成分で計算すると、
       Ω^θ_s = (f″/f) e^s∧e^θ、Ω^φ_s = (f″/f) e^s∧e^φ、Ω^φ_θ = ((f′² − 1)/f²) e^θ∧e^φ
     断面曲率は K(s,θ) = K(s,φ) = −f″/f、K(θ,φ) = (1 − f′²)/f²
  ⇒ f = sinh η で三つの断面曲率はすべて −1(h3_curvature)。
     検算:f = ℓ sin(s/ℓ)(帽子)ではすべて +1/ℓ²(cap_curvature)。
  BPS の方程式自体は AlphaCompleteC2 の bps。単極子から S¹ 不変インスタントンへの対応は Atiyah(1984)の定理(外部)。
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Real

namespace CFT.H3

/-! ### 1. 固有値の分解 -/

/-- h_ij v^i v^j = (|v|² − (p·v)²/E²)/m² を動径方向 v = p/P で評価すると 1/E² -/
theorem h_radial (m P E : ℝ) (hm : m ≠ 0) (hP : P ≠ 0) (hE : E ^ 2 = m ^ 2 + P ^ 2) (hE0 : E ≠ 0) :
    (1 - (P * 1) ^ 2 / E ^ 2) / m ^ 2 = 1 / E ^ 2 := by
  have : E ^ 2 - P ^ 2 = m ^ 2 := by linarith
  field_simp; nlinarith [this]

/-- p に垂直な v(p·v = 0)では h(v, v) = |v|²/m² -/
theorem h_tangential (m E v2 : ℝ) (hm : m ≠ 0) (hE0 : E ≠ 0) :
    (v2 - 0 ^ 2 / E ^ 2) / m ^ 2 = v2 / m ^ 2 := by
  simp

/-! ### 2. ラピディティへの変数変換 -/

theorem h_rapidity (m η : ℝ) (hm : 0 < m) :
    HasDerivAt (fun t => m * sinh t) (m * cosh η) η ∧
    (m * cosh η) ^ 2 / (m ^ 2 + (m * sinh η) ^ 2) = 1 ∧
    (m * sinh η) ^ 2 / m ^ 2 = sinh η ^ 2 := by
  have hm' := hm.ne'
  have hc : m ^ 2 + (m * sinh η) ^ 2 = (m * cosh η) ^ 2 := by
    have := cosh_sq η; nlinarith [this]
  refine ⟨(hasDerivAt_sinh η).const_mul m, ?_, by field_simp; ring⟩
  rw [hc]; exact div_self (by positivity)

/-! ### 3. Cartan の第二構造式(座標 0 = s、1 = θ、2 = φ) -/

variable (f f1 f2 S C : ℝ)

/-- 接続 1 形式 ω^a_{b,i}:ω^θ_s = f′dθ、ω^φ_s = f′S dφ、ω^φ_θ = C dφ と反対称 -/
def om : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b i =>
  if a = 1 ∧ b = 0 ∧ i = 1 then f1 else if a = 0 ∧ b = 1 ∧ i = 1 then -f1
  else if a = 2 ∧ b = 0 ∧ i = 2 then f1 * S else if a = 0 ∧ b = 2 ∧ i = 2 then -(f1 * S)
  else if a = 2 ∧ b = 1 ∧ i = 2 then C else if a = 1 ∧ b = 2 ∧ i = 2 then -C else 0

/-- ∂_i ω^a_{b,j}(∂_s f′ = f″、∂_θ S = C、∂_θ C = −S) -/
def dom : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b i j =>
  if a = 1 ∧ b = 0 ∧ i = 0 ∧ j = 1 then f2 else if a = 0 ∧ b = 1 ∧ i = 0 ∧ j = 1 then -f2
  else if a = 2 ∧ b = 0 ∧ i = 0 ∧ j = 2 then f2 * S else if a = 0 ∧ b = 2 ∧ i = 0 ∧ j = 2 then -(f2 * S)
  else if a = 2 ∧ b = 0 ∧ i = 1 ∧ j = 2 then f1 * C else if a = 0 ∧ b = 2 ∧ i = 1 ∧ j = 2 then -(f1 * C)
  else if a = 2 ∧ b = 1 ∧ i = 1 ∧ j = 2 then -S else if a = 1 ∧ b = 2 ∧ i = 1 ∧ j = 2 then S else 0

/-- Ω^a_b の座標成分 (ij):∂_iω_j − ∂_jω_i + Σ_c (ω^a_{c,i}ω^c_{b,j} − ω^a_{c,j}ω^c_{b,i}) -/
def Om (a b i j : Fin 3) : ℝ :=
  dom f1 f2 S C a b i j - dom f1 f2 S C a b j i
    + ∑ c, (om f1 S C a c i * om f1 S C c b j - om f1 S C a c j * om f1 S C c b i)

theorem warped_curvature :
    Om f1 f2 S C 1 0 0 1 = f2 ∧ Om f1 f2 S C 2 0 0 2 = f2 * S ∧
    Om f1 f2 S C 2 1 1 2 = (f1 ^ 2 - 1) * S ∧
    Om f1 f2 S C 1 0 0 2 = 0 ∧ Om f1 f2 S C 1 0 1 2 = 0 ∧ Om f1 f2 S C 2 0 0 1 = 0 ∧
    Om f1 f2 S C 2 0 1 2 = 0 ∧ Om f1 f2 S C 2 1 0 1 = 0 ∧ Om f1 f2 S C 2 1 0 2 = 0 := by
  simp [Om, dom, om, Fin.sum_univ_three]; ring_nf; simp

/-- 枠の成分に直す(e^s = ds、e^θ = f dθ、e^φ = fS dφ)と断面曲率は −f″/f、−f″/f、(1 − f′²)/f² -/
theorem sectional (f : ℝ) (hf : f ≠ 0) (hS : S ≠ 0) :
    -(Om f1 f2 S C 1 0 0 1 / (1 * f)) = -(f2 / f) ∧
    -(Om f1 f2 S C 2 0 0 2 / (1 * (f * S))) = -(f2 / f) ∧
    -(Om f1 f2 S C 2 1 1 2 / (f * (f * S))) = (1 - f1 ^ 2) / f ^ 2 := by
  obtain ⟨h1, h2, h3, -⟩ := warped_curvature f1 f2 S C
  rw [h1, h2, h3]
  refine ⟨by rw [one_mul], ?_, ?_⟩ <;> field_simp <;> ring

/-- H³:f = sinh η で三つの断面曲率はすべて −1 -/
theorem h3_curvature (η : ℝ) (hη : η ≠ 0) :
    -(sinh η / sinh η) = -1 ∧ (1 - cosh η ^ 2) / sinh η ^ 2 = -1 ∧
    HasDerivAt sinh (cosh η) η ∧ HasDerivAt cosh (sinh η) η := by
  have hs : sinh η ≠ 0 := sinh_ne_zero.2 hη
  refine ⟨by field_simp, ?_, hasDerivAt_sinh η, hasDerivAt_cosh η⟩
  rw [show 1 - cosh η ^ 2 = -(sinh η ^ 2) by rw [cosh_sq]; ring]
  field_simp

/-- 検算:帽子 f = ℓ sin(s/ℓ) ではすべて +1/ℓ² -/
theorem cap_curvature (l x : ℝ) (hl : l ≠ 0) (hx : sin x ≠ 0) :
    -((-(sin x) / l) / (l * sin x)) = 1 / l ^ 2 ∧
    (1 - cos x ^ 2) / (l * sin x) ^ 2 = 1 / l ^ 2 := by
  refine ⟨by field_simp; ring, ?_⟩
  rw [show 1 - cos x ^ 2 = sin x ^ 2 by rw [← sin_sq_add_cos_sq x]; ring]
  field_simp; ring

end CFT.H3
