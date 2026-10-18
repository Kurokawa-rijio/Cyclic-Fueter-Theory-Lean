/-
  α-II.1(Z2)の作り直し:ダンベルは SU(2) の Einstein–Yang–Mills(EYM)理論の初期データであり、
  U21′ の条件 W = r′ は、三つの相の上でだけ時間発展で保たれる

  入力(標準の公式):
    * 球対称な SU(2) の磁気的な配位(Witten の形)の場の強さは、正規直交枠で
      動径成分 B_r = (1 − W²)/r²(一成分)、接線成分 B_t = W′/r(二成分)
    * Yang–Mills の応力(電場 0):ρ = (1/2g²)ΣB²、p_i = (1/g²)(½ΣB² − B_i²)
    * ADM の発展式(時間対称 K_ij = 0 の瞬間、∂_tγ = −2NK):
        ∂_t K_ij = −D_iD_jN + N(³R_ij − 8πG(S_ij − ½γ_ij(S − ρ)))
    * 縮約した YM 方程式(a₀ = 0、W_t = 0 の瞬間):W_tt = N(N W′)′ + N² W(1 − W²)/r²
  A. 応力:
    * ym_stress:ρ = (W′²/r² + (1 − W²)²/(2r⁴))/g²、p_r = (W′²/r² − (1 − W²)²/(2r⁴))/g²、
      p_T = (1 − W²)²/(2r⁴)/g²、跡ゼロ −ρ + p_r + 2p_T = 0
    * cap_stress:帽子 r = ℓ sin x、W = r′ = cos x で ρ = 3/(2g²ℓ⁴)、p_r = p_T = 1/(2g²ℓ⁴)(放射 p = ρ/3)
    * neck_stress:首 r = ℓ、W = 0 で ρ = 1/(2g²ℓ⁴)、p_r = −ρ、p_T = ρ(Bertotti–Robinson)
    * ell_cap、ell_neck:ハミルトン拘束 16πGρ = ³R は帽子でも首でも ℓ² = 4πG/g² と同値
    * flux_cap:帽子の球面を貫く磁束 4πr²B_r = 4π sin²x(接合 x = π/2 で首の 4π と一致、磁荷は不要)
    * riem_identity:W = r′ なら g²ρ = |Riem₃|²/8(|Riem₃|² = 4(2K₁² + K₂²)、K₁ = −r″/r、K₂ = (1 − r′²)/r²)
      ⇒ ハミルトン拘束は純粋に幾何の式 ³R = (ℓ²/2)|Riem₃|²
  B. W = r′ が保たれるか(時間対称な瞬間での 2 階の時間微分、κ = 8πG/g²):
    * sector_delta:W_tt − (r′)_tt = κN²r′(rr″ + 1 − r′²)²/r⁴
        − N′(κNr(1 − r′²)² + Nr³(2rr″ + 2r′² − 2) + r⁴N′r′)/r⁴
    * sector_geodesic:測地的な時間(N′ = 0)では、保たれる ⇔ r′ = 0 または rr″ + 1 − r′² = 0
    * phase_neck:r′ = r″ = 0 とハミルトン拘束 ⇒ r² = ℓ²(首)
    * phase_form:rr″ + 1 − r′² = 0 とハミルトン拘束 ⇒ 1 − r′² = 0(平坦)か 1 − r′² = r²/ℓ²(S³(ℓ))
      ⇒ W = r′ が力学と両立する切り口は、平坦・S³(ℓ)・S²×ℝ(ℓ) の三つの相だけで、半径は ℓ に決まる
      (双曲空間 rr″ + 1 − r′² = 0、1 − r′² < 0 はハミルトン拘束で除外される)
    * neck_any_lapse:首では任意の lapse で保たれる
    * frw_exact:帽子は閉じた FRW(共形時間 N = A = a(η))で、W = cos χ は任意の a(η) で YM 方程式を満たし、
      r′ = ∂_s(a sin χ) = cos χ:帽子の中では W = r′ が厳密に全時間で保たれる
    * neck_W_slope、neck_W_unstable:首の W = 0 のまわりの揺らぎは m²ℓ² = −1 で AdS₂ の BF 境界 −1/4 を下回る(不安定)
  残り:接合部の影響が届く領域(接合から出る光円錐の内側)で W = r′ が保たれるかは未確認(数値計算が必要)。
-/
import CFT.Basic
import CFT.AlphaVIII_BF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Real

namespace CFT.EYM

/-! ### A. 応力 -/

noncomputable def rho (g W W1 r : ℝ) : ℝ := (1 / (2 * g ^ 2)) * (((1 - W ^ 2) / r ^ 2) ^ 2 + 2 * (W1 / r) ^ 2)
noncomputable def pr (g W W1 r : ℝ) : ℝ :=
  (1 / g ^ 2) * ((1 / 2) * (((1 - W ^ 2) / r ^ 2) ^ 2 + 2 * (W1 / r) ^ 2) - ((1 - W ^ 2) / r ^ 2) ^ 2)
noncomputable def pT (g W W1 r : ℝ) : ℝ :=
  (1 / g ^ 2) * ((1 / 2) * (((1 - W ^ 2) / r ^ 2) ^ 2 + 2 * (W1 / r) ^ 2) - (W1 / r) ^ 2)

theorem ym_stress (g W W1 r : ℝ) (hg : g ≠ 0) (hr : r ≠ 0) :
    rho g W W1 r = (W1 ^ 2 / r ^ 2 + (1 - W ^ 2) ^ 2 / (2 * r ^ 4)) / g ^ 2 ∧
    pr g W W1 r = (W1 ^ 2 / r ^ 2 - (1 - W ^ 2) ^ 2 / (2 * r ^ 4)) / g ^ 2 ∧
    pT g W W1 r = (1 - W ^ 2) ^ 2 / (2 * r ^ 4) / g ^ 2 ∧
    -rho g W W1 r + pr g W W1 r + 2 * pT g W W1 r = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · simp only [rho, pr, pT]; field_simp; ring

theorem cap_stress (g l x : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) (hx : sin x ≠ 0) :
    rho g (cos x) (-(sin x) / l) (l * sin x) = 3 / (2 * g ^ 2 * l ^ 4) ∧
    pr g (cos x) (-(sin x) / l) (l * sin x) = 1 / (2 * g ^ 2 * l ^ 4) ∧
    pT g (cos x) (-(sin x) / l) (l * sin x) = 1 / (2 * g ^ 2 * l ^ 4) := by
  have h1 : 1 - cos x ^ 2 = sin x ^ 2 := by rw [← sin_sq_add_cos_sq x]; ring
  refine ⟨?_, ?_, ?_⟩ <;> · simp only [rho, pr, pT]; rw [h1]; field_simp; ring

theorem neck_stress (g l : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) :
    rho g 0 0 l = 1 / (2 * g ^ 2 * l ^ 4) ∧ pr g 0 0 l = -(1 / (2 * g ^ 2 * l ^ 4)) ∧
    pT g 0 0 l = 1 / (2 * g ^ 2 * l ^ 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> · simp only [rho, pr, pT]; field_simp; ring

/-- 帽子:16πG·3/(2g²ℓ⁴) = 6/ℓ² ⇔ ℓ² = 4πG/g² -/
theorem ell_cap (G g l : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) (hG : G ≠ 0) :
    16 * π * G * (3 / (2 * g ^ 2 * l ^ 4)) = 6 / l ^ 2 ↔ l ^ 2 = 4 * π * G / g ^ 2 := by
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  constructor
  · intro h; field_simp at h ⊢; nlinarith [h, sq_nonneg l, pow_pos (sq_pos_of_ne_zero hl) 2]
  · intro h; have hπ := pi_ne_zero; rw [show l ^ 4 = l ^ 2 * l ^ 2 by ring, h]; field_simp; ring

theorem ell_neck (G g l : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) (hG : G ≠ 0) :
    16 * π * G * (1 / (2 * g ^ 2 * l ^ 4)) = 2 / l ^ 2 ↔ l ^ 2 = 4 * π * G / g ^ 2 := by
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  constructor
  · intro h; field_simp at h ⊢; nlinarith [h, sq_nonneg l, pow_pos (sq_pos_of_ne_zero hl) 2]
  · intro h; have hπ := pi_ne_zero; rw [show l ^ 4 = l ^ 2 * l ^ 2 by ring, h]; field_simp; ring

/-- 磁束:4πr²B_r = 4π(1 − W²)、帽子で 4π sin²x、接合 x = π/2 で 4π -/
theorem flux_cap (l x : ℝ) (hl : l ≠ 0) (hx : sin x ≠ 0) :
    4 * π * (l * sin x) ^ 2 * ((1 - cos x ^ 2) / (l * sin x) ^ 2) = 4 * π * sin x ^ 2 ∧
    4 * π * sin (π / 2) ^ 2 = 4 * π * (1 - 0 ^ 2) ∧ cos (π / 2) = 0 := by
  have h1 : 1 - cos x ^ 2 = sin x ^ 2 := by rw [← sin_sq_add_cos_sq x]; ring
  refine ⟨?_, by simp, cos_pi_div_two⟩
  rw [h1]; field_simp; ring

/-- W = r′ なら g²ρ = |Riem₃|²/8 -/
theorem riem_identity (g r r1 r2 : ℝ) (hg : g ≠ 0) (hr : r ≠ 0) :
    g ^ 2 * rho g r1 r2 r = 4 * (2 * (-r2 / r) ^ 2 + ((1 - r1 ^ 2) / r ^ 2) ^ 2) / 8 := by
  unfold rho; field_simp; ring

/-- ハミルトン拘束 ³R = 16πGρ は ³R = (ℓ²/2)|Riem₃|²(ℓ² = 4πG/g²) -/
theorem geometric_constraint (G g r r1 r2 : ℝ) (hg : g ≠ 0) (hr : r ≠ 0) :
    16 * π * G * rho g r1 r2 r
      = ((4 * π * G / g ^ 2) / 2) * (4 * (2 * (-r2 / r) ^ 2 + ((1 - r1 ^ 2) / r ^ 2) ^ 2)) := by
  have := riem_identity g r r1 r2 hg hr
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have e : rho g r1 r2 r = 4 * (2 * (-r2 / r) ^ 2 + ((1 - r1 ^ 2) / r ^ 2) ^ 2) / 8 / g ^ 2 := by
    rw [← this]; field_simp
  rw [e]; field_simp; ring

/-! ### B. W = r′ は保たれるか -/

/-- W_tt(YM 方程式、W = r′、W′ = r″、W″ = r‴) -/
noncomputable def Wtt (r0 r1 r2 r3 n0 n1 : ℝ) : ℝ := n0 * (n1 * r2 + n0 * r3) + n0 ^ 2 * r1 * (1 - r1 ^ 2) / r0 ^ 2

/-- R_tt = −N ∂_tK_θθ/r(YM の跡ゼロ S = ρ を使った ADM の式) -/
noncomputable def Rtt (K r0 r1 r2 n0 n1 : ℝ) : ℝ :=
  -n0 * (-r0 * r1 * n1 + n0 * (1 - r1 ^ 2 - r0 * r2) - K * n0 * (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 2)) / r0

/-- A_tt = −N ∂_tK_ss -/
noncomputable def Att (K r0 r1 r2 n0 n2 : ℝ) : ℝ :=
  -n0 * (-n2 + n0 * (-2 * r2 / r0) - K * n0 * (r2 ^ 2 / r0 ^ 2 - (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 4)))

theorem Rtt_deriv (K : ℝ) (r r1 r2 n n1 : ℝ → ℝ) (r3 n2 : ℝ → ℝ) (s : ℝ) (hr : r s ≠ 0)
    (d0 : HasDerivAt r (r1 s) s) (d1 : HasDerivAt r1 (r2 s) s) (d2 : HasDerivAt r2 (r3 s) s)
    (e0 : HasDerivAt n (n1 s) s) (e1 : HasDerivAt n1 (n2 s) s) :
    HasDerivAt (fun t => Rtt K (r t) (r1 t) (r2 t) (n t) (n1 t))
      ((K * (n s) ^ 2 * (r1 s) * (-(r1 s) ^ 4 + 2 * (r1 s) ^ 2 - 1)
        + K * (n s) * (r s) * (2 * (n s) * (r1 s) ^ 3 * (r2 s) - 2 * (n s) * (r1 s) * (r2 s)
          + (n1 s) * (r1 s) ^ 4 - 2 * (n1 s) * (r1 s) ^ 2 + (n1 s))
        + (n s) ^ 2 * (r s) ^ 2 * (r1 s) * (-K * (r2 s) ^ 2 - (r1 s) ^ 2 + 1)
        + 2 * (n s) * (n1 s) * (r s) ^ 3 * ((r1 s) ^ 2 - 1)
        + (r s) ^ 4 * ((n s) ^ 2 * (r3 s) + 3 * (n s) * (n1 s) * (r2 s) + (n1 s) ^ 2 * (r1 s))) / (r s) ^ 4
        + (r1 s) * Att K (r s) (r1 s) (r2 s) (n s) (n2 s)) s := by
  have hr2 : (r s) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hA := (d0.mul d1).mul e1
  have hB := e0.mul (((d1.pow 2).const_sub 1).sub (d0.mul d2))
  have hC := ((e0.const_mul K).mul (((d1.pow 2).const_sub 1).pow 2)).div ((d0.pow 2).const_mul 2)
    (by simpa using hr2)
  have hX := (hA.neg.add hB).sub hC
  have h := (e0.neg.mul hX).div d0 hr
  convert h using 1
  · funext t; simp only [Rtt]; ring
  · simp only [Att, Nat.cast_ofNat]; field_simp; ring

/-- W_tt − (r′)_tt の公式((r′)_tt = ∂_s R_tt − r′ A_tt) -/
theorem sector_delta (K r0 r1 r2 r3 n0 n1 n2 : ℝ) (hr : r0 ≠ 0) :
    Wtt r0 r1 r2 r3 n0 n1 -
      (((K * n0 ^ 2 * r1 * (-r1 ^ 4 + 2 * r1 ^ 2 - 1)
        + K * n0 * r0 * (2 * n0 * r1 ^ 3 * r2 - 2 * n0 * r1 * r2 + n1 * r1 ^ 4 - 2 * n1 * r1 ^ 2 + n1)
        + n0 ^ 2 * r0 ^ 2 * r1 * (-K * r2 ^ 2 - r1 ^ 2 + 1) + 2 * n0 * n1 * r0 ^ 3 * (r1 ^ 2 - 1)
        + r0 ^ 4 * (n0 ^ 2 * r3 + 3 * n0 * n1 * r2 + n1 ^ 2 * r1)) / r0 ^ 4
        + r1 * Att K r0 r1 r2 n0 n2) - r1 * Att K r0 r1 r2 n0 n2)
    = K * n0 ^ 2 * r1 * (r0 * r2 + 1 - r1 ^ 2) ^ 2 / r0 ^ 4
      - n1 * (K * n0 * r0 * (1 - r1 ^ 2) ^ 2 + n0 * r0 ^ 3 * (2 * r0 * r2 + 2 * r1 ^ 2 - 2)
        + r0 ^ 4 * n1 * r1) / r0 ^ 4 := by
  unfold Wtt; field_simp; ring

/-- 測地的な時間(N′ = 0):差は κN²r′(rr″ + 1 − r′²)²/r⁴、0 ⇔ r′ = 0 ∨ rr″ + 1 − r′² = 0 -/
theorem sector_geodesic (K r0 r1 r2 n0 : ℝ) (hK : K ≠ 0) (hn : n0 ≠ 0) (hr : r0 ≠ 0) :
    K * n0 ^ 2 * r1 * (r0 * r2 + 1 - r1 ^ 2) ^ 2 / r0 ^ 4
      - 0 * (K * n0 * r0 * (1 - r1 ^ 2) ^ 2 + n0 * r0 ^ 3 * (2 * r0 * r2 + 2 * r1 ^ 2 - 2) + r0 ^ 4 * 0 * r1) / r0 ^ 4
      = 0 ↔ r1 = 0 ∨ r0 * r2 + 1 - r1 ^ 2 = 0 := by
  have hr4 : r0 ^ 4 ≠ 0 := pow_ne_zero 4 hr
  rw [zero_mul, zero_div, sub_zero, div_eq_zero_iff, or_iff_left hr4]
  constructor
  · intro h
    have h' : (K * n0 ^ 2) * (r1 * (r0 * r2 + 1 - r1 ^ 2) ^ 2) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 (mul_ne_zero hK (pow_ne_zero 2 hn))
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ((pow_eq_zero_iff two_ne_zero).mp h2)
  · rintro (h | h) <;> simp [h]

/-- ハミルトン拘束(W = r′、κ = 8πG/g²):2(1 − r′² − 2rr″)/r² = κ(r″²/r² + (1 − r′²)²/(2r⁴))·2/2 -/
def hamC (K r0 r1 r2 : ℝ) : Prop :=
  2 * (1 - r1 ^ 2 - 2 * r0 * r2) / r0 ^ 2 = 2 * K * (r2 ^ 2 / r0 ^ 2 + (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 4))

/-- 首の相:r′ = r″ = 0 なら r² = κ/2 = ℓ² -/
theorem phase_neck (K r0 : ℝ) (hr : r0 ≠ 0) (h : hamC K r0 0 0) : r0 ^ 2 = K / 2 := by
  unfold hamC at h
  have hr2 : r0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp at h
  nlinarith [h, pow_pos (sq_pos_of_ne_zero hr) 2, sq_nonneg r0]

/-- 空間形の相:rr″ + 1 − r′² = 0 なら 1 − r′² = 0(平坦)か 1 − r′² = 2r²/κ = r²/ℓ²(S³(ℓ)) -/
theorem phase_form (K r0 r1 r2 : ℝ) (hK : K ≠ 0) (hr : r0 ≠ 0) (hf : r0 * r2 + 1 - r1 ^ 2 = 0)
    (h : hamC K r0 r1 r2) : 1 - r1 ^ 2 = 0 ∨ 1 - r1 ^ 2 = 2 * r0 ^ 2 / K := by
  unfold hamC at h
  have hr2' : r2 = -(1 - r1 ^ 2) / r0 := by field_simp; linarith
  rw [hr2'] at h
  have h2 : 6 * (1 - r1 ^ 2) / r0 ^ 2 = 3 * K * (1 - r1 ^ 2) ^ 2 / r0 ^ 4 := by
    have e1 : 2 * (1 - r1 ^ 2 - 2 * r0 * (-(1 - r1 ^ 2) / r0)) / r0 ^ 2 = 6 * (1 - r1 ^ 2) / r0 ^ 2 := by
      field_simp; ring
    have e2 : 2 * K * ((-(1 - r1 ^ 2) / r0) ^ 2 / r0 ^ 2 + (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 4))
        = 3 * K * (1 - r1 ^ 2) ^ 2 / r0 ^ 4 := by field_simp; ring
    rw [← e1, ← e2]; exact h
  rw [div_eq_div_iff (pow_ne_zero 2 hr) (pow_ne_zero 4 hr)] at h2
  have h3 : r0 ^ 2 * ((1 - r1 ^ 2) * (3 * K * (1 - r1 ^ 2) - 6 * r0 ^ 2)) = 0 := by
    linear_combination (-1 : ℝ) * h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (pow_ne_zero 2 hr)
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact Or.inl h5
  · right; field_simp; linarith

/-- 双曲空間の除外:1 − r′² = 2r²/κ > 0(κ > 0)なので 1 − r′² < 0 の空間形は拘束を満たさない -/
theorem no_hyperbolic (K r0 r1 r2 : ℝ) (hK : 0 < K) (hr : r0 ≠ 0) (hf : r0 * r2 + 1 - r1 ^ 2 = 0)
    (h : hamC K r0 r1 r2) (hneg : 1 - r1 ^ 2 < 0) : False := by
  rcases phase_form K r0 r1 r2 hK.ne' hr hf h with h0 | h1
  · linarith
  · have : 0 < 2 * r0 ^ 2 / K := by positivity
    linarith

/-- 首では任意の lapse で差は 0(r′ = r″ = 0、r² = κ/2) -/
theorem neck_any_lapse (K r0 n0 n1 : ℝ) (hr : r0 ≠ 0) (h : r0 ^ 2 = K / 2) :
    K * n0 ^ 2 * 0 * (r0 * 0 + 1 - 0 ^ 2) ^ 2 / r0 ^ 4
      - n1 * (K * n0 * r0 * (1 - 0 ^ 2) ^ 2 + n0 * r0 ^ 3 * (2 * r0 * 0 + 2 * 0 ^ 2 - 2) + r0 ^ 4 * n1 * 0) / r0 ^ 4
      = 0 := by
  have hK : K = 2 * r0 ^ 2 := by linarith
  rw [hK]; field_simp; ring

/-- 帽子の FRW:共形時間で N = A = a、R = a sin χ、W = cos χ は YM 方程式
    ∂_χ(N W_χ/A) + NA W(1 − W²)/R² = 0 を任意の a で満たし、r′ = ∂_χ(a sin χ)/a = cos χ -/
theorem frw_exact (a χ : ℝ) (ha : a ≠ 0) (hs : sin χ ≠ 0) :
    HasDerivAt (fun x => a * (-(sin x)) / a) (a * (-(cos χ)) / a) χ ∧
    a * (-(cos χ)) / a + a * a * cos χ * (1 - cos χ ^ 2) / (a * sin χ) ^ 2 = 0 ∧
    a * cos χ / a = cos χ := by
  have h1 : 1 - cos χ ^ 2 = sin χ ^ 2 := by rw [← sin_sq_add_cos_sq χ]; ring
  refine ⟨((hasDerivAt_sin χ).neg.const_mul a).div_const a, ?_, by field_simp⟩
  rw [h1]; field_simp; ring

/-! ### C. 首の不安定性(W の凝縮)

  首(AdS₂ × S²、N = cosh(x/ℓ)、R = ℓ)で W = 0 のまわりの線形化:YM 方程式
  ∂_t(W_t/N) = ∂_x(N W_x) + N W(1 − W²)/ℓ² の右辺の W(1 − W²) の W = 0 での傾きは 1 なので
  □_{AdS₂} W = −W/ℓ²、つまり m²ℓ² = −1。AdS₂ の BF 境界 −1/4 より下で、W は指数的に育つ(不安定)。
  ⇒ 単位磁荷の極限ブラックホールの喉は、電荷を持つ質量ゼロの W ボソンの凝縮で崩れる
  (弱い重力予想が要請する「極限ブラックホールが崩壊できる」ことの、この理論での具体的な現れ) -/

theorem neck_W_slope : HasDerivAt (fun W : ℝ => W * (1 - W ^ 2)) 1 0 := by
  have h := (hasDerivAt_id (0 : ℝ)).mul (((hasDerivAt_id (0 : ℝ)).pow 2).const_sub 1)
  convert h using 1; simp

theorem neck_W_unstable : -(1 : ℝ) < -(1 / 4) ∧ ¬ ∃ α : ℝ, α ^ 2 - 1 * α - (-1) = 0 := by
  refine ⟨by norm_num, fun h => ?_⟩
  have := (CFT.BF.bf_ads2 (-1)).1 h
  norm_num at this

end CFT.EYM
