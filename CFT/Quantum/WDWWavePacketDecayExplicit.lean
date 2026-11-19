/-
  命題集 `LEAN_GAP_TREES.md` 5-8（波動関数の境界条件）の残り：波束版 Ψ_f の非消滅、
  大きな |T₀| に対する評価（第六段：具体的な重みに対する f′ の計算と明示定数）。

  第五段では f′ を仮定として置く抽象形で 1/|T₀| 減衰評価を得た。ここでは端点で
  消える具体的な bump 重み

    g(C) = (C − C₁)(C₂ − C)·√(C − 8c²ℓ)

  を取る。首 b = ℓ では Q c l C l = ℓ(C − 8c²ℓ) なので、被積分関数は

    f(C) = g(C)/√(Q c l C l) = (C − C₁)(C₂ − C)/√ℓ

  と多項式になり、f′(C) = (C₁ + C₂ − 2C)/√ℓ、‖f′‖ ≤ (C₂ − C₁)/√ℓ。
  第五段の適用により明示定数つきの減衰評価

    ‖Ψ_f(T₀)‖ ≤ (C₂ − C₁)²·|ħ|/(√ℓ·|T₀|)

  が得られる。具体例 c = ℓ = 1、C ∈ [9, 10] では ‖Ψ_f(T₀)‖ ≤ |ħ|/|T₀|。
  （sympy による明示計算でも f・f′・端点値を照合済み。）

  残り：非消滅への組み立て（大きな |T₀| での下限評価）。減衰評価は上界であり、
  非消滅には別途下限が要る。置換 y = √(C − 8) により積分はフレネル型になり、
  初等的な閉形式が無いため次の段に残る。
-/
import CFT.Quantum.WDWWavePacketDecay

namespace CFT.WDWWavePacketDecayExplicit

open CFT.WKB CFT.WDWBoundary CFT.WDWWavePacket CFT.WDWWavePacketGen CFT.WDWWavePacketPhase
  CFT.WDWWavePacketSymm CFT.WDWWavePacketDecay MeasureTheory intervalIntegral

noncomputable section

variable (c l : ℝ)

/-- 端点で消える bump 重み：g(C) = (C − C₁)(C₂ − C)·√(C − 8c²ℓ)。-/
def bumpG (C₁ C₂ : ℝ) (C : ℝ) : ℝ := (C - C₁) * (C₂ - C) * Real.sqrt (C - 8 * c ^ 2 * l)

/-- bump 重みは左端点で消える。-/
theorem bumpG_vanish_left (C₁ C₂ : ℝ) : bumpG c l C₁ C₂ C₁ = 0 := by
  simp [bumpG]

/-- bump 重みは右端点で消える。-/
theorem bumpG_vanish_right (C₁ C₂ : ℝ) : bumpG c l C₁ C₂ C₂ = 0 := by
  simp [bumpG]

/-- 首では被積分関数は多項式になる：g(C)/√Q = (C − C₁)(C₂ − C)/√ℓ。-/
theorem bumpG_div_sqrt_eq {C₁ C₂ C : ℝ} (ha : 8 * c ^ 2 * l < C) (hl : 0 < l) :
    bumpG c l C₁ C₂ C / Real.sqrt (Q c l C l) = (C - C₁) * (C₂ - C) / Real.sqrt l := by
  rw [Q_neck, Real.sqrt_mul hl.le]
  unfold bumpG
  exact mul_div_mul_right _ _ (Real.sqrt_pos.mpr (sub_pos.mpr ha)).ne'

/-- 被積分関数 f(C) = g(C)/√Q の導関数：f′(C) = (C₁ + C₂ − 2C)/√ℓ。-/
theorem hasDerivAt_bumpF {C₁ C₂ : ℝ} (hlt : C₁ < C₂) (hC₁ : 8 * c ^ 2 * l < C₁)
    (hl : 0 < l) {C : ℝ} (hC : C ∈ Set.uIcc C₁ C₂) :
    HasDerivAt (fun C => ((bumpG c l C₁ C₂ C / Real.sqrt (Q c l C l) : ℝ) : ℂ))
      (((C₁ + C₂ - 2 * C) / Real.sqrt l : ℝ) : ℂ) C := by
  have hCa : 8 * c ^ 2 * l < C := by
    rcases Set.mem_uIcc.mp hC with h | h
    · exact lt_of_lt_of_le hC₁ h.1
    · exact lt_of_lt_of_le hC₁ (le_trans hlt.le h.1)
  have hpoly : HasDerivAt (fun C => (C - C₁) * (C₂ - C) / Real.sqrt l)
      ((C₁ + C₂ - 2 * C) / Real.sqrt l) C := by
    have h1 : HasDerivAt (fun C => C - C₁) 1 C := (hasDerivAt_id C).sub_const C₁
    have h2 : HasDerivAt (fun C => C₂ - C) (-1) C := by
      simpa using (hasDerivAt_const C C₂).sub (hasDerivAt_id C)
    have hdiv := (h1.mul h2).div_const (Real.sqrt l)
    convert hdiv using 1
    ring
  have hpolyC := hpoly.ofReal_comp
  apply hpolyC.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hCa] with y hy
  rw [bumpG_div_sqrt_eq c l hy hl]

/-- f′ は区間上で連続。-/
theorem bumpF'_continuousOn {C₁ C₂ : ℝ} :
    ContinuousOn (fun C => (((C₁ + C₂ - 2 * C) / Real.sqrt l : ℝ) : ℂ))
      (Set.uIcc C₁ C₂) := by
  fun_prop

/-- f′ の上界：‖f′(C)‖ ≤ (C₂ − C₁)/√ℓ。-/
theorem bumpF'_norm_le {C₁ C₂ : ℝ} (hlt : C₁ < C₂) (hl : 0 < l)
    {C : ℝ} (hC : C ∈ Set.uIoc C₁ C₂) :
    ‖(((C₁ + C₂ - 2 * C) / Real.sqrt l : ℝ) : ℂ)‖ ≤ (C₂ - C₁) / Real.sqrt l := by
  rw [Set.uIoc_of_le hlt.le] at hC
  have hbound : |C₁ + C₂ - 2 * C| ≤ C₂ - C₁ := by
    rw [abs_le]
    constructor <;> linarith [hC.1, hC.2]
  calc ‖(((C₁ + C₂ - 2 * C) / Real.sqrt l : ℝ) : ℂ)‖
      = |C₁ + C₂ - 2 * C| / Real.sqrt l := by
        rw [Complex.norm_eq_abs, Complex.abs_ofReal, abs_div,
          abs_of_nonneg (Real.sqrt_nonneg l)]
    _ ≤ (C₂ - C₁) / Real.sqrt l :=
        (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hl)).mpr hbound

/-- 明示定数つきの減衰評価：bump 重みに対して
    ‖Ψ_f(T₀)‖ ≤ (C₂ − C₁)²·|ħ|/(√ℓ·|T₀|)。-/
theorem packetPhase_bump_norm_le {C₁ C₂ T₀ hbar : ℝ} (hlt : C₁ < C₂)
    (hC₁ : 8 * c ^ 2 * l < C₁) (hl : 0 < l) (hT₀ : T₀ ≠ 0) (hhbar : hbar ≠ 0) :
    ‖packetPhase c l C₁ C₂ T₀ hbar (bumpG c l C₁ C₂)‖
      ≤ (C₂ - C₁) ^ 2 * |hbar| / (Real.sqrt l * |T₀|) := by
  have h := packetPhase_norm_le_of_vanish c l hlt hT₀ hhbar
    (f' := fun C => (((C₁ + C₂ - 2 * C) / Real.sqrt l : ℝ) : ℂ))
    (M := (C₂ - C₁) / Real.sqrt l)
    (fun C hC => hasDerivAt_bumpF c l hlt hC₁ hl hC)
    (bumpF'_continuousOn l)
    (bumpG_vanish_left c l C₁ C₂)
    (bumpG_vanish_right c l C₁ C₂)
    (fun C hC => bumpF'_norm_le l hlt hl hC)
  have hstep : (C₂ - C₁) * ((C₂ - C₁) / Real.sqrt l) = (C₂ - C₁) ^ 2 / Real.sqrt l := by
    rw [← mul_div_assoc, ← pow_two]
  have heq : (C₂ - C₁) * ((C₂ - C₁) / Real.sqrt l) * |hbar| / |T₀|
      = (C₂ - C₁) ^ 2 * |hbar| / (Real.sqrt l * |T₀|) := by
    rw [hstep, div_mul_eq_mul_div, div_div]
  rwa [heq] at h

/-- 具体例：c = ℓ = 1、C ∈ [9, 10] の bump 波束は ‖Ψ_f(T₀)‖ ≤ |ħ|/|T₀|。-/
theorem packetPhase_bump_example {T₀ hbar : ℝ} (hT₀ : T₀ ≠ 0) (hhbar : hbar ≠ 0) :
    ‖packetPhase 1 1 9 10 T₀ hbar (bumpG 1 1 9 10)‖ ≤ |hbar| / |T₀| := by
  have h := packetPhase_bump_norm_le (c := 1) (l := 1)
    (by norm_num : (9 : ℝ) < 10)
    (by norm_num : 8 * (1 : ℝ) ^ 2 * 1 < 9)
    (by norm_num : (0 : ℝ) < 1) hT₀ hhbar
  rw [show ((10 : ℝ) - 9) ^ 2 = 1 by norm_num] at h
  simpa using h

end

end CFT.WDWWavePacketDecayExplicit
