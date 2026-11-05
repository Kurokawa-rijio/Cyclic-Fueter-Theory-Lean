/-
  新しい柱 3:共形の枠 ——「物理の時空 = Ω² × 量子の球(静的宇宙 ℝ × S³)」(2026-11-06)

  v6 では「相対論の計量 = 量子の計量 × 共形因子」(g_Q = h_ms/(2E²))だった。同じ関係を時空に置く。
  ĝ = −dη² + du² + sin²u dΩ²(静的宇宙、S³ の半径 1)、物理の計量 g = Ω²ĝ。YM は 4 次元で共形不変なので
  ĝ の上にそのまま住み、エネルギー運動量のトレースは 0。Einstein の方程式のトレースは R[g] = 0、
  共形変換の公式 R[Ω²ĝ] = Ω⁻²R̂ − 6Ω⁻³□̂Ω(外部:Wald 付録 D)と R̂ = 6 から **□̂Ω = Ω**(線形)。

  古典
  * 帽子 Ω = ℓ cos η(時間だけ)、首 Ω = ℓ/sin u(場所だけ)は、どちらも □̂Ω = Ω をみたす
    (`cap_box`、`neck_box`)。首の座標 x = ℓ log tan(u/2) で dx = ℓ du/sin u(`neck_coordinate`)、
    円柱 dx² + ℓ²dΩ² = (ℓ²/sin²u)(du² + sin²u dΩ²):首の両端の無限遠は S³ の極(点)。
  * 静的な解の全体は Ω = (A + Bu)/sin u(`static_general`)。
  * 接合の跳び(X.14)は、倍率の 2 階微分の縫い目:u = π/2 で Ω = ℓ、Ω′ = 0 は両側で一致し、
    Ω″ は 0(帽子)と ℓ(首)(`junction_seam`)。物理の W = r′ は W = cos u + (Ω′/Ω) sin u(`r_prime_conformal`)。
  * Einstein の ηη 成分:首 Ω² + Ω′² = ℓ²/sin⁴u、帽子 3(Ω² + Ω̇²) = 3ℓ²。どちらも YM のエネルギーと
    ℓ² = 4πG/g² で一致(`eta_neck`、`eta_cap`)。
  量子(ミニ超空間、テスト C の候補)
  * 一様な Ω(η) の作用 S = (3π/4G)∫(Ω² − Ω̇²)dη(Einstein–Hilbert を共形変換し S³ で積分、外部)。
    運動方程式 Ω̈ = −Ω、すべての解は周期 2π(`periodic`:**巡回**)。エネルギー H_Ω = −(3π/4G)(Ω̇² + Ω²)
    は負で、帽子では −(3π/4G)ℓ²(`cap_energy`)。YM の帽子のエネルギー 3π²/g² との和が 0
    (ハミルトン拘束)⇔ ℓ² = 4πG/g²(`energy_balance`、IX.11・IX.17 と同じ)。
  * 量子化:Ω は振動数 1 の(負のエネルギーの)調和振動子。基底状態 e^{−MΩ²/2} の固有値 ½
    (`ground_state`、M = 3π/2G、ħ = 1)。準位 n + ½ は外部(調和振動子)。YM を古典の帽子の値のまま
    拘束 3π²/g² = n + ½ を課すと ℓ²/ℓ_P² = 4(n + ½)/(3π)、α = g²/4π = 3π/(4n + 2)(`quantized`)。
    注意:演算子の順序で ½ はずれうる、YM の量子化はしていない、ミニ超空間への切り詰め。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace CFT.Conformal

open Real

/-- 【柱 3】帽子 Ω = ℓ cos η:□̂Ω = −Ω̈ = Ω -/
theorem cap_box (l η : ℝ) :
    HasDerivAt (fun e => l * cos e) (-(l * sin η)) η ∧
    HasDerivAt (fun e => -(l * sin e)) (-(l * cos η)) η ∧ -(-(l * cos η)) = l * cos η := by
  refine ⟨?_, ?_, by ring⟩
  · have h := (hasDerivAt_cos η).const_mul l
    convert h using 1; ring
  · have h := ((hasDerivAt_sin η).const_mul l).neg
    convert h using 1

/-- 首 Ω = ℓ/sin u の 1 階と 2 階の微分 -/
theorem neck_derivs (l u : ℝ) (hs : sin u ≠ 0) :
    HasDerivAt (fun v => l / sin v) (-(l * cos u) / sin u ^ 2) u ∧
    HasDerivAt (fun v => -(l * cos v) / sin v ^ 2) (l * (1 + cos u ^ 2) / sin u ^ 3) u := by
  constructor
  · have h := (hasDerivAt_const u l).div (hasDerivAt_sin u) hs
    convert h using 1; ring
  · have h := ((hasDerivAt_cos u).const_mul l).neg.div ((hasDerivAt_sin u).pow 2) (pow_ne_zero 2 hs)
    convert h using 1
    have h1 := sin_sq_add_cos_sq u
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [show (1 : ℝ) + cos u ^ 2 = sin u ^ 2 + 2 * cos u ^ 2 by linarith]
    field_simp
    ring

/-- 【柱 3】首 Ω = ℓ/sin u:□̂Ω = Ω″ + 2 cot u Ω′ = Ω -/
theorem neck_box (l u : ℝ) (hs : sin u ≠ 0) :
    l * (1 + cos u ^ 2) / sin u ^ 3 + 2 * (cos u / sin u) * (-(l * cos u) / sin u ^ 2) = l / sin u := by
  have h1 := sin_sq_add_cos_sq u
  rw [show (1 : ℝ) + cos u ^ 2 = sin u ^ 2 + 2 * cos u ^ 2 by linarith]
  field_simp
  ring

/-- 【柱 3】静的な解の全体 Ω = f/sin u(f = A + Bu)は □̂Ω = Ω をみたす:
Ω′ = (B sin u − f cos u)/sin²u、Ω″ = (f sin²u − 2cos u(B sin u − f cos u))/sin³u -/
theorem static_general (A B u : ℝ) (hs : sin u ≠ 0) :
    ((A + B * u) * sin u ^ 2 - 2 * cos u * (B * sin u - (A + B * u) * cos u)) / sin u ^ 3
      + 2 * (cos u / sin u) * ((B * sin u - (A + B * u) * cos u) / sin u ^ 2) = (A + B * u) / sin u := by
  field_simp
  ring

/-- 静的な一般解の 1 階微分 -/
theorem static_general_deriv (A B u : ℝ) (hs : sin u ≠ 0) :
    HasDerivAt (fun v => (A + B * v) / sin v) ((B * sin u - (A + B * u) * cos u) / sin u ^ 2) u := by
  have h := (((hasDerivAt_id' u).const_mul B).const_add A).div (hasDerivAt_sin u) hs
  convert h using 1; ring

/-- 【柱 3】接合の跳び = 倍率の縫い目:u = π/2 で首は Ω = ℓ、Ω′ = 0、Ω″ = ℓ、帽子(時間対称)は Ω = ℓ、
Ω′ = Ω″ = 0 -/
theorem junction_seam (l : ℝ) :
    l / sin (π / 2) = l ∧ -(l * cos (π / 2)) / sin (π / 2) ^ 2 = 0 ∧
    l * (1 + cos (π / 2) ^ 2) / sin (π / 2) ^ 3 = l := by
  simp [sin_pi_div_two, cos_pi_div_two]

/-- 【柱 3】物理の W = r′(r = Ω sin u、dρ = Ω du):r′ = (Ω′ sin u + Ω cos u)/Ω。首では 0、帽子では cos u -/
theorem r_prime_conformal (l u : ℝ) (hl : l ≠ 0) (hs : sin u ≠ 0) :
    ((-(l * cos u) / sin u ^ 2) * sin u + l / sin u * cos u) / (l / sin u) = 0 ∧
    (0 * sin u + l * cos u) / l = cos u := by
  constructor
  · field_simp <;> ring
  · rw [zero_mul, zero_add, mul_div_cancel_left₀ _ hl]

/-- 【柱 3】Einstein の ηη 成分(首):Ω² + Ω′² = ℓ²/sin⁴u、8πG·1/(2g²sin⁴u) と一致 ⇔ ℓ² = 4πG/g² -/
theorem eta_neck (G g l u : ℝ) (hg : g ≠ 0) (hs : sin u ≠ 0) :
    (l / sin u) ^ 2 + (-(l * cos u) / sin u ^ 2) ^ 2 = l ^ 2 / sin u ^ 4 ∧
    (l ^ 2 / sin u ^ 4 = 8 * π * G * (1 / (2 * g ^ 2 * sin u ^ 4)) ↔ l ^ 2 = 4 * π * G / g ^ 2) := by
  have h1 := sin_sq_add_cos_sq u
  have hs4 : sin u ^ 4 ≠ 0 := pow_ne_zero 4 hs
  constructor
  · have e : l ^ 2 / sin u ^ 4 = l ^ 2 * (sin u ^ 2 + cos u ^ 2) / sin u ^ 4 := by rw [h1, mul_one]
    rw [e]
    field_simp
    ring
  · have e : 8 * π * G * (1 / (2 * g ^ 2 * sin u ^ 4)) = (4 * π * G / g ^ 2) / sin u ^ 4 := by
      field_simp <;> ring
    rw [e]
    constructor
    · intro h; exact (div_left_inj' hs4).mp h
    · intro h; rw [h]

/-- 【柱 3】Einstein の ηη 成分(帽子):3(Ω² + Ω̇²) = 3ℓ²、8πG·3/(2g²) と一致 ⇔ ℓ² = 4πG/g² -/
theorem eta_cap (G g l η : ℝ) (hg : g ≠ 0) :
    3 * ((l * cos η) ^ 2 + (-(l * sin η)) ^ 2) = 3 * l ^ 2 ∧
    (3 * l ^ 2 = 8 * π * G * (3 / (2 * g ^ 2)) ↔ l ^ 2 = 4 * π * G / g ^ 2) := by
  constructor
  · have h := sin_sq_add_cos_sq η
    linear_combination (3 * l ^ 2) * h
  · constructor
    · intro h
      have h' : l ^ 2 = 8 * π * G * (3 / (2 * g ^ 2)) / 3 := by linarith
      rw [h']; field_simp; ring
    · intro h; rw [h]; field_simp; ring

/-! ### ミニ超空間と量子化 -/

/-- 【柱 3】Ω̈ = −Ω の解 Ω = A cos η + B sin η は周期 2π(巡回) -/
theorem periodic (A B η : ℝ) :
    A * cos (η + 2 * π) + B * sin (η + 2 * π) = A * cos η + B * sin η := by
  rw [cos_add_two_pi, sin_add_two_pi]

/-- 【柱 3】Ω のエネルギー H_Ω = −(3π/4G)(Ω̇² + Ω²) は帽子 Ω = ℓ cos η で −(3π/4G)ℓ²(一定) -/
theorem cap_energy (G l η : ℝ) :
    -(3 * π / (4 * G)) * ((-(l * sin η)) ^ 2 + (l * cos η) ^ 2) = -(3 * π / (4 * G)) * l ^ 2 := by
  have h := sin_sq_add_cos_sq η
  linear_combination (-(3 * π / (4 * G)) * l ^ 2) * h

/-- 【柱 3】ハミルトン拘束 H_Ω + E_YM = 0(E_YM = 3π²/g²、帽子の YM の S³ 上のエネルギー)⇔ ℓ² = 4πG/g² -/
theorem energy_balance (G g l : ℝ) (hG : G ≠ 0) (hg : g ≠ 0) :
    -(3 * π / (4 * G)) * l ^ 2 + 3 * π ^ 2 / g ^ 2 = 0 ↔ l ^ 2 = 4 * π * G / g ^ 2 := by
  have hπ := pi_pos.ne'
  have hc : 3 * π / (4 * G) ≠ 0 := div_ne_zero (mul_ne_zero three_ne_zero hπ) (mul_ne_zero four_ne_zero hG)
  have e : -(3 * π / (4 * G)) * l ^ 2 + 3 * π ^ 2 / g ^ 2 = (3 * π / (4 * G)) * (4 * π * G / g ^ 2 - l ^ 2) := by
    field_simp; ring
  rw [e, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hc
    · linarith
  · intro h; right; linarith

/-- 【柱 3】量子化:基底状態 ψ = e^{−MΩ²/2} は −(1/2M)ψ″ + (M/2)Ω²ψ = ½ψ(ħ = 1、振動数 1)。
負のエネルギーの振動子なので H_Ω の準位は −(n + ½)(外部:調和振動子の準位) -/
theorem ground_state (M x : ℝ) (hM : M ≠ 0) :
    HasDerivAt (fun y => rexp (-(M * y ^ 2) / 2)) (-(M * x) * rexp (-(M * x ^ 2) / 2)) x ∧
    HasDerivAt (fun y => -(M * y) * rexp (-(M * y ^ 2) / 2))
      ((M ^ 2 * x ^ 2 - M) * rexp (-(M * x ^ 2) / 2)) x ∧
    -(1 / (2 * M)) * ((M ^ 2 * x ^ 2 - M) * rexp (-(M * x ^ 2) / 2)) + M / 2 * x ^ 2 * rexp (-(M * x ^ 2) / 2)
      = 1 / 2 * rexp (-(M * x ^ 2) / 2) := by
  have hq : HasDerivAt (fun y : ℝ => -(M * y ^ 2) / 2) (-(M * x)) x := by
    have := (((hasDerivAt_pow 2 x).const_mul M).neg).div_const 2
    convert this using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  have he := hq.exp
  refine ⟨?_, ?_, ?_⟩
  · convert he using 1; ring
  · have h := ((hasDerivAt_id' x).const_mul M).neg.mul he
    convert h using 1; ring
  · field_simp <;> ring

/-- 【柱 3】拘束の量子化(半古典):3π²/g² = n + ½ なら ℓ² = 4πG/g² = (4G/3π)(n + ½)、α = g²/4π = 3π/(4n + 2) -/
theorem quantized (G g n : ℝ) (hg : g ≠ 0) (hn : 0 ≤ n) (h : 3 * π ^ 2 / g ^ 2 = n + 1 / 2) :
    4 * π * G / g ^ 2 = 4 * G / (3 * π) * (n + 1 / 2) ∧ g ^ 2 / (4 * π) = 3 * π / (4 * n + 2) := by
  have hπ := pi_pos.ne'
  have hn' : n + 1 / 2 ≠ 0 := by linarith
  have hg2 : g ^ 2 = 3 * π ^ 2 / (n + 1 / 2) := by
    rw [eq_div_iff hn', ← h]
    field_simp
  constructor
  · rw [← h]; field_simp; ring
  · rw [hg2]
    have : (4 * n + 2) ≠ 0 := by linarith
    field_simp; ring

end CFT.Conformal
