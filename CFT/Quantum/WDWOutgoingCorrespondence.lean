/-
  5-8 の残り：枝と古典的「外向き」の対応付け（(C5)、`GAP_5-8_prep.md` §2）

  厳密解 Ψ₊ = e^{iaσ/ħ}/σ、Ψ₋ = e^{−iaσ/ħ}/(−σ) の位相は Hamilton–Jacobi
  関数 S = aσ(b) から来る（`CFT.WKB.wdw_exact_sqrt`）。古典の運動量は
  p_a = ∂S/∂a = σ(b)、p_b = ∂S/∂b = aσ′(b) で、Hamilton 方程式より
  ȧ = N·∂Hfun/∂p_a（`CFT.AlphaCompleteA.H_pa`）。このモジュールは
  ȧ の符号が因子 σ − bσ′ = (Cb − 8c²ℓ²)/(2σ) で決まることと、
  首 b = ℓ（物理的枝 C > 8c²ℓ）では正の枝が膨張（ȧ > 0）、負の枝が収縮
  （ȧ < 0）になることを証明する。すなわち N > 0 のゲージで Ψ₊ が
  「外向き」（首の伸長）、Ψ₋ が「内向き」に対応する。Vilenkin のトンネル
  条件の「規約つき」の部分がこれで外れる。波束版 Ψ_f の非消滅は
  C 積分の下限評価が要るため 5-8 の残りとして残る。
-/
import CFT.Quantum.WDWExactWKB
import CFT.Spherical.CompletionNeckDynamics

namespace CFT.WDWOutgoing

variable (c l : ℝ)

/-- σ(b) = √Q(b)、Q(b) = Cb − 4c²(b² + ℓ²) -/
noncomputable def sig (C b : ℝ) : ℝ := Real.sqrt (CFT.WKB.Q c l C b)

theorem sig_pos (C b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) : 0 < sig c l C b := by
  have h : sig c l C b = Real.sqrt (CFT.WKB.Q c l C b) := rfl
  rw [h]; exact Real.sqrt_pos.mpr hQ

theorem sig_ne_zero (C b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) : sig c l C b ≠ 0 :=
  ne_of_gt (sig_pos c l C b hQ)

/-- (C5) の微分：σ′(b) = (C − 8c²b)/(2σ(b)) -/
theorem hasDerivAt_sig (C b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) :
    HasDerivAt (sig c l C) ((C - 8 * c ^ 2 * b) / (2 * sig c l C b)) b := by
  have h := (CFT.WKB.hasDerivAt_Q c l C b).sqrt (ne_of_gt hQ)
  have hsig : (fun x => Real.sqrt (CFT.WKB.Q c l C x)) = sig c l C := rfl
  rw [hsig] at h
  exact h

/-- (C5)：σ − bσ′ = (Cb − 8c²ℓ²)/(2σ) -/
theorem sigma_sub_b_sigma'_eq (C b : ℝ) (hQ : 0 < CFT.WKB.Q c l C b) :
    sig c l C b - b * deriv (sig c l C) b
      = (C * b - 8 * c ^ 2 * l ^ 2) / (2 * sig c l C b) := by
  have hd := (hasDerivAt_sig c l C b hQ).deriv
  have hsig2 : (sig c l C b) ^ 2 = CFT.WKB.Q c l C b := Real.sq_sqrt (le_of_lt hQ)
  have hQdef : CFT.WKB.Q c l C b = C * b - 4 * c ^ 2 * (b ^ 2 + l ^ 2) := rfl
  have hsig0 : sig c l C b ≠ 0 := sig_ne_zero c l C b hQ
  rw [hQdef] at hsig2
  rw [hd]
  field_simp
  nlinarith [hsig2]

/-- 首 b = ℓ での因子の因数分解 -/
theorem neck_factor (C : ℝ) : C * l - 8 * c ^ 2 * l ^ 2 = l * (C - 8 * c ^ 2 * l) := by
  ring

/-- 物理的枝 C > 8c²ℓ では首での因子は正 -/
theorem neck_factor_pos (C : ℝ) (hl : 0 < l) (hC : 8 * c ^ 2 * l < C) :
    0 < C * l - 8 * c ^ 2 * l ^ 2 := by
  rw [neck_factor]
  exact mul_pos hl (by linarith)

/-- 正の枝での古典速度：ȧ = N·a·(σ − bσ′)/(2b²c)
    （p_a = σ、p_b = aσ′ を `H_pa` に代入） -/
theorem velocity_plus (N a b C : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    N * deriv (fun x => CFT.AlphaCompleteA.Hfun a b x (a * deriv (sig c l C) b) c l)
        (sig c l C b)
      = N * a * (sig c l C b - b * deriv (sig c l C) b) / (2 * b ^ 2 * c) := by
  have h := (CFT.AlphaCompleteA.H_pa a b (sig c l C b) (a * deriv (sig c l C) b) c l
    hb hc).deriv
  rw [h]
  field_simp
  ring

/-- 負の枝での古典速度：符号が反転する（p_a = −σ、p_b = −aσ′） -/
theorem velocity_minus (N a b C : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) :
    N * deriv (fun x => CFT.AlphaCompleteA.Hfun a b x (-(a * deriv (sig c l C) b)) c l)
        (-(sig c l C b))
      = -(N * a * (sig c l C b - b * deriv (sig c l C) b) / (2 * b ^ 2 * c)) := by
  have h := (CFT.AlphaCompleteA.H_pa a b (-(sig c l C b)) (-(a * deriv (sig c l C) b)) c l
    hb hc).deriv
  rw [h]
  field_simp
  ring

/-- 首での正の枝は膨張（ȧ > 0）：Ψ₊ は「外向き」 -/
theorem outgoing_plus_neck (N a C : ℝ) (hN : 0 < N) (ha : 0 < a) (hl : 0 < l)
    (hc : 0 < c) (hC : 8 * c ^ 2 * l < C) (hQ : 0 < CFT.WKB.Q c l C l) :
    0 < N * deriv (fun x => CFT.AlphaCompleteA.Hfun a l x (a * deriv (sig c l C) l) c l)
        (sig c l C l) := by
  rw [velocity_plus c l N a l C (ne_of_gt hl) (ne_of_gt hc),
    sigma_sub_b_sigma'_eq c l C l hQ]
  have hsig : 0 < sig c l C l := sig_pos c l C l hQ
  have hfac : 0 < C * l - 8 * c ^ 2 * l ^ 2 := neck_factor_pos c l C hl hC
  positivity

/-- 首での負の枝は収縮（ȧ < 0）：Ψ₋ は「内向き」 -/
theorem incoming_minus_neck (N a C : ℝ) (hN : 0 < N) (ha : 0 < a) (hl : 0 < l)
    (hc : 0 < c) (hC : 8 * c ^ 2 * l < C) (hQ : 0 < CFT.WKB.Q c l C l) :
    N * deriv (fun x => CFT.AlphaCompleteA.Hfun a l x (-(a * deriv (sig c l C) l)) c l)
        (-(sig c l C l)) < 0 := by
  rw [velocity_minus c l N a l C (ne_of_gt hl) (ne_of_gt hc),
    sigma_sub_b_sigma'_eq c l C l hQ]
  have hsig : 0 < sig c l C l := sig_pos c l C l hQ
  have hfac : 0 < C * l - 8 * c ^ 2 * l ^ 2 := neck_factor_pos c l C hl hC
  have hpos : 0 < N * a * ((C * l - 8 * c ^ 2 * l ^ 2) / (2 * sig c l C l))
      / (2 * l ^ 2 * c) := by positivity
  linarith

/-- まとめ：首では正の枝が膨張・負の枝が収縮する（外向き／内向きの同定） -/
theorem outgoing_correspondence_neck (N a C : ℝ) (hN : 0 < N) (ha : 0 < a)
    (hl : 0 < l) (hc : 0 < c) (hC : 8 * c ^ 2 * l < C)
    (hQ : 0 < CFT.WKB.Q c l C l) :
    0 < N * deriv (fun x => CFT.AlphaCompleteA.Hfun a l x (a * deriv (sig c l C) l) c l)
        (sig c l C l)
      ∧ N * deriv (fun x => CFT.AlphaCompleteA.Hfun a l x (-(a * deriv (sig c l C) l)) c l)
        (-(sig c l C l)) < 0 :=
  ⟨outgoing_plus_neck c l N a C hN ha hl hc hC hQ,
    incoming_minus_neck c l N a C hN ha hl hc hC hQ⟩

end CFT.WDWOutgoing
