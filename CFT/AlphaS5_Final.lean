/-
  段階 5 の最終定理を、場の方程式から結論まで一つの定理で通す(2026-10-21 の評価基準 D)

  * wave_jump_final(α-IV.2、Z8):両側の YM 方程式(F = dA + A∧A)、波面 u = u₀ に沿う実現、波面の上で
    Ω, W, r が連続 ⇒ 跳び [W_u] は波面に沿って一定(goursat_W、fym_eq を呼ぶ)
  * cap_crunch_final(α-IV.5、Z9):帽子の EYM 方程式(tt、θθ 成分)と時間対称な初期値 a(0) = ℓ、a′(0) = 0、
    中心の世界線に沿う実現 ⇒ a(η) = ℓ cos η、Kretschmann スカラー K = 24ℓ⁴/(ℓ cos η)⁸、η → π/2⁻ で K → ∞
    (cap_00、cap_22、kret_cap、kret_blowup を呼ぶ)。中心の固有時は ℓ sin η → ℓ < πℓ/2(cap_proper_time、t_sing_lt)
-/
import CFT.AlphaS4_Final
import CFT.AlphaS5_Curvature

open Real Set Filter Topology

namespace CFT.S5F

open CFT.S4 CFT.S5 CFT.S5K CFT.S4F

/-- α-IV.2:波面に沿う [W_u] の一定性 -/
theorem wave_jump_final {S₁ S₂ : Type*} [Field S₁] [CharZero S₁] [Field S₂] [CharZero S₂]
    (d₁ : Fin 4 → Derivation ℤ S₁ S₁) (d₂ : Fin 4 → Derivation ℤ S₂ S₂)
    (Om₁ r₁ s₁ c₁ W₁ : S₁) (Om₂ r₂ s₂ c₂ W₂ : S₂)
    (H₁ : SphN d₁ Om₁ r₁ s₁ c₁) (H₂ : SphN d₂ Om₂ r₂ s₂ c₂)
    (W2₁ : d₁ 2 W₁ = 0) (W3₁ : d₁ 3 W₁ = 0) (W2₂ : d₂ 2 W₂ = 0) (W3₂ : d₂ 3 W₂ = 0)
    (Y₁ : YMeq d₁ (giN Om₁ r₁ s₁) (Om₁ * r₁ ^ 2 * s₁) (Aym W₁ s₁ c₁) (Fym d₁ (Aym W₁ s₁ c₁)) 0 2 = 0)
    (Y₂ : YMeq d₂ (giN Om₂ r₂ s₂) (Om₂ * r₂ ^ 2 * s₂) (Aym W₂ s₂ c₂) (Fym d₂ (Aym W₂ s₂ c₂)) 0 2 = 0)
    {v0 v1 : ℝ} {fv₁ : ℝ → S₁ →+* ℝ} {fv₂ : ℝ → S₂ →+* ℝ}
    (F₁ : RealLine (d₁ 1) fv₁ (Icc v0 v1)) (F₂ : RealLine (d₂ 1) fv₂ (Icc v0 v1))
    (cr : ∀ v ∈ Icc v0 v1, fv₁ v r₁ = fv₂ v r₂) (cO : ∀ v ∈ Icc v0 v1, fv₁ v Om₁ = fv₂ v Om₂)
    (cW : ∀ v ∈ Icc v0 v1, fv₁ v W₁ = fv₂ v W₂) :
    ∀ v ∈ Icc v0 v1, fv₂ v (d₂ 0 W₂) - fv₁ v (d₁ 0 W₁) = fv₂ v0 (d₂ 0 W₂) - fv₁ v0 (d₁ 0 W₁) := by
  rw [fymN d₁ W₁ Om₁ r₁ s₁ c₁ H₁ W2₁ W3₁] at Y₁
  rw [fymN d₂ W₂ Om₂ r₂ s₂ c₂ H₂ W2₂ W3₂] at Y₂
  have g₁ := goursat_W d₁ W₁ Om₁ r₁ s₁ c₁ H₁ W2₁ W3₁ Y₁
  have g₂ := goursat_W d₂ W₂ Om₂ r₂ s₂ c₂ H₂ W2₂ W3₂ Y₂
  have hd : ∀ v ∈ Icc v0 v1, HasDerivWithinAt (fun v => fv₂ v (d₂ 0 W₂) - fv₁ v (d₁ 0 W₁)) 0 (Icc v0 v1) v := by
    intro v hv'
    have h := (F₂.deriv (d₂ 0 W₂) v hv').sub (F₁.deriv (d₁ 0 W₁) v hv')
    convert h using 1
    rw [H₂.comm 1 0 W₂, H₁.comm 1 0 W₁, g₁, g₂]
    simp only [map_mul, map_sub, map_pow, map_inv₀, map_one, map_ofNat]
    rw [cr v hv', cO v hv', cW v hv']; ring
  have hc : ContinuousOn (fun v => fv₂ v (d₂ 0 W₂) - fv₁ v (d₁ 0 W₁)) (Icc v0 v1) :=
    fun v hv' => (hd v hv').continuousWithinAt
  exact constant_of_has_deriv_right_zero hc (fun v hv' =>
    (hd v (Ico_subset_Icc_self hv')).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv'))

/-- α-IV.5:帽子の崩壊を場の方程式から曲率の不変量の発散まで -/
theorem cap_crunch_final {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)
    (a X Y s c lS : S) (H : CapData d a X Y s c) (Y2 : d 2 Y = 0) (Y3 : d 3 Y = 0)
    (E00 : Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 0 0
      = 2 * lS ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (Fym d (Aym Y s c)) 0 0)
    (E22 : Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 2 2
      = 2 * lS ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (Fym d (Aym Y s c)) 2 2)
    {ev : ℝ → S →+* ℝ} (L : RealLine (d 0) ev (Ico 0 (π / 2))) {l : ℝ} (hl : 0 < l)
    (hlS : ∀ η ∈ Ico 0 (π / 2), ev η lS = l) (ha0 : ev 0 a = l) (hda0 : ev 0 (d 0 a) = 0) :
    (∀ η ∈ Ico 0 (π / 2), ev η a = l * cos η) ∧
    (∀ η ∈ Ico 0 (π / 2), ev η (KretD d ![-a ^ 2, a ^ 2, (a * X) ^ 2, (a * X) ^ 2 * s ^ 2]
      ![-(a⁻¹ ^ 2), a⁻¹ ^ 2, (a * X)⁻¹ ^ 2, (a * X)⁻¹ ^ 2 * s⁻¹ ^ 2] (GD d a a (a * X) s c))
        = 24 * l ^ 4 * ((l * cos η)⁻¹) ^ 8) ∧
    Tendsto (fun η => ev η (KretD d ![-a ^ 2, a ^ 2, (a * X) ^ 2, (a * X) ^ 2 * s ^ 2]
      ![-(a⁻¹ ^ 2), a⁻¹ ^ 2, (a * X)⁻¹ ^ 2, (a * X)⁻¹ ^ 2 * s⁻¹ ^ 2] (GD d a a (a * X) s c)))
      (𝓝[<] (π / 2)) atTop := by
  have HS := capSph d a X Y s c H
  rw [fymD d Y a a (a * X) s c HS Y2 Y3] at E00 E22
  have h00 := (cap_00 d a X Y s c lS H).mp E00
  have h22 := (cap_22 d a X Y s c lS H).mp E22
  have ha := H.ha
  have hacc : d 0 (d 0 a) = -a := by
    have : 2 * a * (d 0 (d 0 a) + a) = 0 := by linear_combination h22 + h00
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero ha)
    linear_combination this
  have hK := kret_cap d a X Y s c lS H h00 hacc
  -- 中心の世界線に沿う常微分方程式 a″ = −a と一意性
  have hcos : ∀ η ∈ Ico 0 (π / 2), ev η a = l * cos η := by
    intro η hη
    let E : ℝ → ℝ := fun t => (ev t a - l * cos t) ^ 2 + (ev t (d 0 a) + l * sin t) ^ 2
    have hE : ∀ t ∈ Icc 0 η, HasDerivWithinAt E 0 (Icc 0 η) t := by
      intro t ht
      have htI : t ∈ Ico 0 (π / 2) := ⟨ht.1, lt_of_le_of_lt ht.2 hη.2⟩
      have sub : Icc 0 η ⊆ Ico 0 (π / 2) := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hη.2⟩
      have d1 := (L.deriv a t htI).mono sub
      have d2 := (L.deriv (d 0 a) t htI).mono sub
      rw [hacc, map_neg] at d2
      have h := ((d1.sub ((hasDerivAt_cos t).const_mul l).hasDerivWithinAt).pow 2).add
        ((d2.add ((hasDerivAt_sin t).const_mul l).hasDerivWithinAt).pow 2)
      convert h using 1
      push_cast; ring
    have hc : ContinuousOn E (Icc 0 η) := fun t ht => (hE t ht).continuousWithinAt
    have hconst := constant_of_has_deriv_right_zero hc (fun t ht =>
      (hE t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    have e := hconst η ⟨hη.1, le_refl _⟩
    simp only [E, ha0, hda0, cos_zero, sin_zero, mul_one, mul_zero, sub_self, add_zero] at e
    have h3 : (ev η a - l * cos η) ^ 2 = 0 := by
      have := sq_nonneg (ev η (d 0 a) + l * sin η); nlinarith [sq_nonneg (ev η a - l * cos η)]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  have hKv : ∀ η ∈ Ico 0 (π / 2), ev η (KretD d ![-a ^ 2, a ^ 2, (a * X) ^ 2, (a * X) ^ 2 * s ^ 2]
      ![-(a⁻¹ ^ 2), a⁻¹ ^ 2, (a * X)⁻¹ ^ 2, (a * X)⁻¹ ^ 2 * s⁻¹ ^ 2] (GD d a a (a * X) s c))
        = 24 * l ^ 4 * ((l * cos η)⁻¹) ^ 8 := by
    intro η hη
    rw [hK]
    simp only [map_mul, map_pow, map_inv₀, map_ofNat]
    rw [hlS η hη, hcos η hη]
  refine ⟨hcos, hKv, ?_⟩
  refine (kret_blowup l hl).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < π / 2)] with η hη
  exact (hKv η ⟨hη.1.le, hη.2⟩).symm

end CFT.S5F
