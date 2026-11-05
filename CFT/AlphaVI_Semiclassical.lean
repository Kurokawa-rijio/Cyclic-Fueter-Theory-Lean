/-
  α-VI.8 (Z37):停留位相の定理の適用条件をすべてそろえる

  波束 Ψ_g(a, b) = ∫ g(C) e^{i(a√Q_C(b) − C T₀)/ħ}/√Q_C(b) dC(正の枝)。位相 Φ(C) = a√Q_C(b) − C T₀。
  停留位相の定理(Hörmander, The Analysis of Linear Partial Differential Operators I, Thm 7.7.5)の条件:
    (H1) 振幅 g/√Q_C(b) と位相 Φ が g の台の近くでなめらか、g はコンパクトな台をもつ
    (H2) 台の中の停留点で Φ″ ≠ 0
    (H3) 台の中の停留点は有限個(ここでは高々一つ)
  ここで Lean で示すこと:
  * 許される C の範囲:b > 0 なら Q_C(b) > 0 ⇔ C > C_min(b) = 4c²(b² + ℓ²)/b(`Q_pos_iff`)。
    相加相乗平均で C_min(b) ≥ 8c²ℓ = K₀(`Cmin_ge`)。したがって C > K₀ だけでは足りない。
    波束の振幅は g ∈ C_c^∞((C_min(b), ∞)) とする:台が [C₁, C₂] で C₁ > C_min(b) なら台の上で Q > 0
    (`support_condition`)。b を動かすときは、C_min(b) < C₁ をみたす b の範囲(古典的に許される領域)で考える。
    (H1) は Q > 0 で √ がなめらかなことから従う(`d2S_dC2` など)。
  * 停留点の存在と位置:a, b, T₀ > 0 なら C* = C_min(b) + a²b/(4T₀²) で
    Q_{C*}(b) = (ab/(2T₀))² > 0、∂_C(a√Q_C)|_{C*} = T₀(`stationary_point`)。
  * (H2) 非退化:Φ″(C*) = −ab²/(4Q^{3/2}) ≠ 0(AlphaVI_Physical2 `stationary_nondegenerate`)。
  * (H3) 一意性:AlphaVI_Physical2 `stationary_unique`。
  結論(外部定理の適用):C* が g の台の内部にあれば
    Ψ_g(a, b) = e^{iΦ(C*)/ħ} g(C*) √(2πħ/|Φ″(C*)|) e^{−iπ/4}/√Q_{C*}(b) + O(ħ^{3/2})、
  台の外なら O(ħ^∞)。|Ψ_g|² は {T(a, b) = T₀、K = C*} の近くに集中し、これは保存量 (K, T) で
  ラベルされた古典軌道(AlphaVI `bracket_KH`、AlphaVI_Physical `bracket_TH_weak`)。
-/
import CFT.AlphaVI_Physical2

namespace CFT.Semi

open CFT.WKB CFT.Phys2 Real Set

noncomputable section

/-- C_min(b) = 4c²(b² + ℓ²)/b -/
def Cmin (c l b : ℝ) : ℝ := 4 * c ^ 2 * (b ^ 2 + l ^ 2) / b

/-- b > 0 なら Q_C(b) > 0 ⇔ C > C_min(b) -/
theorem Q_pos_iff (c l b C : ℝ) (hb : 0 < b) : 0 < Q c l C b ↔ Cmin c l b < C := by
  simp only [Cmin, Q]
  rw [div_lt_iff₀ hb]
  constructor <;> intro h <;> linarith

/-- C_min(b) ≥ 8c²ℓ = K₀(相加相乗平均) -/
theorem Cmin_ge (c l b : ℝ) (hb : 0 < b) : 8 * c ^ 2 * l ≤ Cmin c l b := by
  simp only [Cmin]
  rw [le_div_iff₀ hb]
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (b - l))]

/-- 【α-VI.8】台の条件:C ≥ C₁ > C_min(b) なら Q_C(b) > 0 -/
theorem support_condition (c l b C₁ C : ℝ) (hb : 0 < b) (h1 : Cmin c l b < C₁) (hC : C₁ ≤ C) :
    0 < Q c l C b :=
  (Q_pos_iff c l b C hb).mpr (lt_of_lt_of_le h1 hC)

/-- 【α-VI.8】停留点の存在:C* = C_min(b) + a²b/(4T₀²) で Q = (ab/(2T₀))²、∂_C(a√Q) = T₀ -/
theorem stationary_point (a b c l T0 : ℝ) (ha : 0 < a) (hb : 0 < b) (hT : 0 < T0) :
    Q c l (Cmin c l b + a ^ 2 * b / (4 * T0 ^ 2)) b = (a * b / (2 * T0)) ^ 2 ∧
    0 < Q c l (Cmin c l b + a ^ 2 * b / (4 * T0 ^ 2)) b ∧
    a * b / (2 * Real.sqrt (Q c l (Cmin c l b + a ^ 2 * b / (4 * T0 ^ 2)) b)) = T0 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hT0 : T0 ≠ 0 := hT.ne'
  have hQ : Q c l (Cmin c l b + a ^ 2 * b / (4 * T0 ^ 2)) b = (a * b / (2 * T0)) ^ 2 := by
    simp only [Q, Cmin]
    field_simp <;> ring
  have hpos : 0 < a * b / (2 * T0) := by positivity
  refine ⟨hQ, by rw [hQ]; positivity, ?_⟩
  rw [hQ, Real.sqrt_sq hpos.le]
  field_simp <;> ring

end

end CFT.Semi
