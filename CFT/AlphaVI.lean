/-
  α-VI 重力と量子重力(Z33, Z35, Z37, U21′ 監査)

  形式化した内容
  * α-VI.3 (U21′ 監査) S³ 相は宇宙定数なしでは静的解にならない:
                  超静的(N = 1)なら R_tt = 0 だが、トレースのない YM 応力では R_tt = 8πGρ > 0
  * α-VI.4 (Z33) 首の Wheeler–DeWitt 方程式の厳密解(α-IV.12 wdw_exact と同じ式)
  * α-VI.6 (Z35) 縮約位相空間:K = (p_a² + 4c²(b² + ℓ²))/b、T = ab/(2p_a) について
                  {T, K} = 1、{K, H} = 0(偏微分は明示式。sympy で導出、Lean で括弧を検算)
  * α-VI.8 (Z37) 縮約模型 a″ = −a、W″ = 2W(1 − W²) で
                  拘束 C = a′² + a² − ℓ²(W′² + (1 − W²)²) は保存。
                  インスタントン作用 3π² · 8/3 = 8π²
-/
import CFT.AlphaIV

open Real

namespace CFT.AlphaVI

/-! ### α-VI.3 S³ 相は静的でない -/

theorem s3_not_ultrastatic (G l : ℝ) (hG : 0 < G) (hl : l ≠ 0) :
    (0 : ℝ) ≠ 8 * π * G * (3 / (8 * π * G * l ^ 2)) := by
  have : 0 < 8 * π * G * (3 / (8 * π * G * l ^ 2)) := by positivity
  exact this.ne

/-! ### α-VI.4 Wheeler–DeWitt の厳密解 -/

alias wdw_exact := CFT.AlphaIV.wdw_exact

/-! ### α-VI.6 Poisson 括弧 -/

section Bracket

variable (a b pa pb c l : ℝ)

/-- K, T, H の偏微分(順に ∂_a, ∂_b, ∂_{p_a}, ∂_{p_b}) -/
noncomputable def Ka : ℝ := 0
noncomputable def Kb : ℝ := (4 * b ^ 2 * c ^ 2 - 4 * c ^ 2 * l ^ 2 - pa ^ 2) / b ^ 2
noncomputable def Kpa : ℝ := 2 * pa / b
noncomputable def Kpb : ℝ := 0
noncomputable def Ta : ℝ := b / (2 * pa)
noncomputable def Tb : ℝ := a / (2 * pa)
noncomputable def Tpa : ℝ := -(a * b) / (2 * pa ^ 2)
noncomputable def Tpb : ℝ := 0
noncomputable def Ha : ℝ := -c + c * l ^ 2 / b ^ 2 + pa ^ 2 / (4 * b ^ 2 * c)
noncomputable def Hb : ℝ := (-4 * a * c ^ 2 * l ^ 2 + pa * (-a * pa + b * pb)) / (2 * b ^ 3 * c)
noncomputable def Hpa : ℝ := (a * pa - b * pb) / (2 * b ^ 2 * c)
noncomputable def Hpb : ℝ := -pa / (2 * b * c)

/-- {T, K} = 1 -/
theorem bracket_TK (hb : b ≠ 0) (hpa : pa ≠ 0) :
    Ta b pa * Kpa b pa - Tpa a b pa * Ka + Tb a pa * Kpb - Tpb * Kb b pa c l = 1 := by
  simp only [Ta, Kpa, Tpa, Ka, Tb, Kpb, Tpb, Kb]
  field_simp

/-- {K, H} = 0(K は Dirac 観測量) -/
theorem bracket_KH (hb : b ≠ 0) (hc : c ≠ 0) :
    Ka * Hpa a b pa pb c - Kpa b pa * Ha b pa c l + Kb b pa c l * Hpb b pa c
      - Kpb * Hb a b pa pb c l = 0 := by
  simp only [Ka, Hpa, Kpa, Ha, Kb, Hpb, Kpb, Hb]
  field_simp
  ring

/-- 偏微分の検算(K について):∂K/∂p_a = 2p_a/b -/
theorem K_pa_deriv (hb : b ≠ 0) :
    HasDerivAt (fun x => (x ^ 2 + 4 * c ^ 2 * (b ^ 2 + l ^ 2)) / b) (Kpa b pa) pa := by
  have h := (((hasDerivAt_id pa).pow 2).add_const (4 * c ^ 2 * (b ^ 2 + l ^ 2))).div_const b
  convert h using 1
  simp [Kpa]

/-- 偏微分の検算(K について):∂K/∂b -/
theorem K_b_deriv (hb : b ≠ 0) :
    HasDerivAt (fun x => (pa ^ 2 + 4 * c ^ 2 * (x ^ 2 + l ^ 2)) / x) (Kb b pa c l) b := by
  have hnum := (((hasDerivAt_id b).pow 2).add_const (l ^ 2)).const_mul (4 * c ^ 2) |>.const_add (pa ^ 2)
  have h := hnum.div (hasDerivAt_id b) hb
  convert h using 1
  simp [Kb]
  field_simp
  ring

/-- 偏微分の検算(T について) -/
theorem T_a_deriv (hpa : pa ≠ 0) :
    HasDerivAt (fun x => x * b / (2 * pa)) (Ta b pa) a := by
  have h := ((hasDerivAt_id a).mul_const b).div_const (2 * pa)
  convert h using 1
  simp [Ta]

theorem T_pa_deriv (hpa : pa ≠ 0) :
    HasDerivAt (fun x => a * b / (2 * x)) (Tpa a b pa) pa := by
  have h2 : HasDerivAt (fun x => 2 * x) 2 pa := by
    simpa using (hasDerivAt_id pa).const_mul 2
  have h := (hasDerivAt_const pa (a * b)).div h2 (by positivity)
  convert h using 1
  simp [Tpa]
  field_simp
  ring

end Bracket

/-! ### α-VI.8 縮約模型の拘束の保存 -/

theorem constraint_conserved (a da W dW : ℝ → ℝ) (l η : ℝ)
    (ha : HasDerivAt a (da η) η) (hda : HasDerivAt da (-a η) η)
    (hW : HasDerivAt W (dW η) η) (hdW : HasDerivAt dW (2 * W η * (1 - W η ^ 2)) η) :
    HasDerivAt (fun η => da η ^ 2 + a η ^ 2 - l ^ 2 * (dW η ^ 2 + (1 - W η ^ 2) ^ 2)) 0 η := by
  have h := ((hda.pow 2).add (ha.pow 2)).sub
    (((hdW.pow 2).add (((hW.pow 2).const_sub 1).pow 2)).const_mul (l ^ 2))
  convert h using 1
  simp
  ring

/-- インスタントンの作用:g²S = 3π² × ∫2 sech⁴ = 3π² × 8/3 = 8π² -/
theorem instanton_action : 3 * π ^ 2 * (8 / 3) = 8 * π ^ 2 := by ring

end CFT.AlphaVI
