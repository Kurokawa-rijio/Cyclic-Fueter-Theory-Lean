/-! ### C. 外側の厳密解:帽子(閉じた放射 FRW)と首(AdS₂ × S²)を EYM の式から -/

section Exact
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- 帽子:共形時間 η(座標 0)と χ(座標 1)、N = A = a(η)、R = a(η) X(X = sin χ、Y = cos χ)、W = Y -/
structure CapData (a X Y s c : S) : Prop where
  ha : a ≠ 0
  hX : X ≠ 0
  hs : s ≠ 0
  a1 : d 1 a = 0
  a2 : d 2 a = 0
  a3 : d 3 a = 0
  X0 : d 0 X = 0
  X1 : d 1 X = Y
  X2 : d 2 X = 0
  X3 : d 3 X = 0
  Y0 : d 0 Y = 0
  Y1 : d 1 Y = -X
  hXY : X ^ 2 + Y ^ 2 = 1
  s0 : d 0 s = 0
  s1 : d 1 s = 0
  s2 : d 2 s = c
  s3 : d 3 s = 0
  c0 : d 0 c = 0
  c1 : d 1 c = 0
  c2 : d 2 c = -s
  c3 : d 3 c = 0
  comm : ∀ i j f, d i (d j f) = d j (d i f)

theorem capSph (a X Y s c : S) (H : CapData d a X Y s c) : SphD d a a (a * X) s c := by
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  refine ⟨ha, ha, mul_ne_zero ha hX, hs, a2, a3, a2, a3, ?_, ?_, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ <;>
    simp [Derivation.leibniz, a2, a3, X2, X3]

set_option maxHeartbeats 0 in
/-- 帽子の tt 成分 ⇔ Friedmann の式 a′² + a² = ℓ²(閉じた放射 FRW、共形時間) -/
theorem cap_00 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 0 0
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 0 0 ↔ (d 0 a) ^ 2 + a ^ 2 = l ^ 2 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_00 d a a (a * X) s c HS, tymD_00 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  constructor
  · intro h
    linear_combination ((1/3 : S) * a ^ 2) * h + ((-1/3 : S) * X ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1/3 : S) * Y ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1/3 : S) * a ^ 6 * iX ^ 2 * ia ^ 4 + (-1/3 : S) * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2) * hXY + ((1/3 : S) * X ^ 3 * a ^ 4 * iX ^ 3 * ia ^ 4 * l ^ 2 + (1/3 : S) * X ^ 2 * a ^ 4 * iX ^ 2 * ia ^ 4 * l ^ 2 + (-1/3 : S) * X * a ^ 6 * iX * ia ^ 4 + (1 : S) * X * a ^ 4 * iX * ia ^ 4 * l ^ 2 + (-1/3 : S) * X * a ^ 2 * (d 0 a) ^ 2 * iX * ia ^ 2 + (-1/3 : S) * a ^ 6 * ia ^ 4 + (-2/3 : S) * a ^ 5 * ia ^ 3 + (1 : S) * a ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 2) * hiX + ((1/3 : S) * a ^ 5 * iX ^ 2 * ia ^ 3 + (-1/3 : S) * a ^ 5 * ia ^ 3 + (1/3 : S) * a ^ 4 * iX ^ 2 * ia ^ 2 + (-1 : S) * a ^ 4 * ia ^ 2 + (1 : S) * a ^ 3 * ia ^ 3 * l ^ 2 + (-1 : S) * a ^ 3 * ia + (1 : S) * a ^ 2 * ia ^ 2 * l ^ 2 + (-1 : S) * a ^ 2 + (-1 : S) * a * (d 0 a) ^ 2 * ia + (1 : S) * a * ia * l ^ 2 + (-1 : S) * (d 0 a) ^ 2 + (1 : S) * l ^ 2) * hia
  · intro h
    linear_combination ((3 : S) * ia ^ 2) * h + ((1 : S) * X ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * Y ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 4 * iX ^ 2 * ia ^ 4 + (1 : S) * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2) * hXY + ((-1 : S) * X ^ 3 * a ^ 2 * iX ^ 3 * ia ^ 4 * l ^ 2 + (-1 : S) * X ^ 2 * a ^ 2 * iX ^ 2 * ia ^ 4 * l ^ 2 + (1 : S) * X * a ^ 4 * iX * ia ^ 4 + (-3 : S) * X * a ^ 2 * iX * ia ^ 4 * l ^ 2 + (1 : S) * X * (d 0 a) ^ 2 * iX * ia ^ 2 + (1 : S) * a ^ 4 * ia ^ 4 + (2 : S) * a ^ 3 * ia ^ 3 + (-3 : S) * a ^ 2 * ia ^ 4 * l ^ 2 + (3 : S) * (d 0 a) ^ 2 * ia ^ 2) * hiX + ((-1 : S) * a ^ 3 * iX ^ 2 * ia ^ 3 + (1 : S) * a ^ 3 * ia ^ 3 + (-1 : S) * a ^ 2 * iX ^ 2 * ia ^ 2 + (3 : S) * a ^ 2 * ia ^ 2 + (-3 : S) * a * ia ^ 3 * l ^ 2 + (-3 : S) * ia ^ 2 * l ^ 2) * hia

set_option maxHeartbeats 0 in
/-- 帽子の χχ 成分 ⇔ 2aa″ − a′² + a² + ℓ² = 0 -/
theorem cap_11 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 1 1
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 1 1 ↔ 2 * a * d 0 (d 0 a) - (d 0 a) ^ 2 + a ^ 2 + l ^ 2 = 0 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_11 d a a (a * X) s c HS, tymD_11 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  constructor
  · intro h
    linear_combination ((-1 : S) * a ^ 2) * h + ((-1 : S) * X ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * Y ^ 2 * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 4 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * a ^ 4 * iX ^ 2 * ia ^ 2) * hXY + ((1 : S) * X ^ 3 * a ^ 4 * iX ^ 3 * ia ^ 4 * l ^ 2 + (1 : S) * X ^ 2 * a ^ 4 * iX ^ 2 * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 4 * (d 0 a) ^ 2 * iX * ia ^ 4 + (1 : S) * X * a ^ 4 * iX * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 4 * iX * ia ^ 2 + (-2 : S) * X * a ^ 2 * iX * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 4 * (d 0 a) ^ 2 * ia ^ 4 + (-2 : S) * a ^ 4 * (d 0 (d 0 a)) * ia ^ 3 + (1 : S) * a ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 4 * ia ^ 2 + (-2 : S) * a ^ 2 * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * a ^ 3 * (d 0 a) ^ 2 * ia ^ 3 + (-2 : S) * a ^ 3 * (d 0 (d 0 a)) * ia ^ 2 + (1 : S) * a ^ 3 * ia ^ 3 * l ^ 2 + (-1 : S) * a ^ 3 * ia + (1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 2 + (-2 : S) * a ^ 2 * (d 0 (d 0 a)) * ia + (1 : S) * a ^ 2 * ia ^ 2 * l ^ 2 + (-1 : S) * a ^ 2 + (1 : S) * a * (d 0 a) ^ 2 * ia + (-2 : S) * a * (d 0 (d 0 a)) + (-1 : S) * a * ia * l ^ 2 + (1 : S) * (d 0 a) ^ 2 + (-1 : S) * l ^ 2) * hia
  · intro h
    linear_combination ((-1 : S) * ia ^ 2) * h + ((-1 : S) * X ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * Y ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 2 * iX ^ 4 * ia ^ 4 * l ^ 2 + (1 : S) * a ^ 2 * iX ^ 2 * ia ^ 2) * hXY + ((1 : S) * X ^ 3 * a ^ 2 * iX ^ 3 * ia ^ 4 * l ^ 2 + (1 : S) * X ^ 2 * a ^ 2 * iX ^ 2 * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 2 * (d 0 a) ^ 2 * iX * ia ^ 4 + (1 : S) * X * a ^ 2 * iX * ia ^ 4 * l ^ 2 + (-1 : S) * X * a ^ 2 * iX * ia ^ 2 + (-2 : S) * X * iX * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 4 + (-2 : S) * a ^ 2 * (d 0 (d 0 a)) * ia ^ 3 + (1 : S) * a ^ 2 * ia ^ 4 * l ^ 2 + (-1 : S) * a ^ 2 * ia ^ 2 + (-2 : S) * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * a * (d 0 a) ^ 2 * ia ^ 3 + (-2 : S) * a * (d 0 (d 0 a)) * ia ^ 2 + (1 : S) * a * ia ^ 3 * l ^ 2 + (1 : S) * (d 0 a) ^ 2 * ia ^ 2 + (1 : S) * ia ^ 2 * l ^ 2) * hia

set_option maxHeartbeats 0 in
/-- 帽子の θθ 成分 ⇔ 2aa″ − a′² + a² + ℓ² = 0(等方) -/
theorem cap_22 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 2 2
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 2 2 ↔ 2 * a * d 0 (d 0 a) - (d 0 a) ^ 2 + a ^ 2 + l ^ 2 = 0 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_22 d a a (a * X) s c HS, tymD_22 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  constructor
  · intro h
    linear_combination ((-1 : S) * a ^ 2 * iX ^ 2) * h + ((1 : S) * X ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 2 * l ^ 2 + (-1 : S) * Y ^ 2 * a ^ 2 * iX ^ 4 * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 2 * iX ^ 4 * ia ^ 2 * l ^ 2) * hXY + ((-1 : S) * X ^ 3 * a ^ 2 * iX ^ 3 * ia ^ 2 * l ^ 2 + (-1 : S) * X ^ 2 * a ^ 2 * iX ^ 2 * ia ^ 2 * l ^ 2 + (1 : S) * X * a ^ 4 * (d 0 a) ^ 2 * iX * ia ^ 4 + (-1 : S) * X * a ^ 4 * (d 0 (d 0 a)) * iX * ia ^ 3 + (-1 : S) * X * a ^ 4 * iX * ia ^ 2 + (-1 : S) * X * a ^ 3 * (d 0 (d 0 a)) * iX * ia ^ 2 + (-1 : S) * X * a ^ 2 * iX * ia ^ 2 * l ^ 2 + (1 : S) * a ^ 4 * (d 0 a) ^ 2 * ia ^ 4 + (-1 : S) * a ^ 4 * (d 0 (d 0 a)) * ia ^ 3 + (-1 : S) * a ^ 4 * ia ^ 2 + (-1 : S) * a ^ 3 * (d 0 (d 0 a)) * ia ^ 2 + (-1 : S) * a ^ 2 * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * a ^ 3 * (d 0 a) ^ 2 * ia ^ 3 + (-1 : S) * a ^ 3 * (d 0 (d 0 a)) * ia ^ 2 + (-1 : S) * a ^ 3 * ia + (1 : S) * a ^ 2 * (d 0 a) ^ 2 * ia ^ 2 + (-2 : S) * a ^ 2 * (d 0 (d 0 a)) * ia + (-1 : S) * a ^ 2 + (1 : S) * a * (d 0 a) ^ 2 * ia + (-2 : S) * a * (d 0 (d 0 a)) + (-1 : S) * a * ia * l ^ 2 + (1 : S) * (d 0 a) ^ 2 + (-1 : S) * l ^ 2) * hia
  · intro h
    linear_combination ((-1 : S) * X ^ 2 * ia ^ 2) * h + ((1 : S) * X ^ 2 * iX ^ 2 * ia ^ 2 * l ^ 2 + (-1 : S) * Y ^ 2 * iX ^ 2 * ia ^ 2 * l ^ 2 + (1 : S) * iX ^ 2 * ia ^ 2 * l ^ 2) * hXY + ((-1 : S) * X ^ 3 * iX * ia ^ 2 * l ^ 2 + (-1 : S) * X ^ 2 * ia ^ 2 * l ^ 2) * hiX + ((1 : S) * X ^ 2 * a * (d 0 a) ^ 2 * ia ^ 3 + (-1 : S) * X ^ 2 * a * (d 0 (d 0 a)) * ia ^ 2 + (1 : S) * X ^ 2 * (d 0 a) ^ 2 * ia ^ 2) * hia

set_option maxHeartbeats 0 in
/-- 帽子の tχ 成分は恒等的に成り立つ(W_η = 0) -/
theorem cap_01 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 0 1
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 0 1 := by
  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_01 d a a (a * X) s c HS, tymD_01 d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  linear_combination ((2 : S) * Y * (d 0 a) * iX * ia) * hia

/-- 首:時間 t(座標 0)と z(座標 1)、N = 1、A = C(C = cos(t/ℓ)、S = sin(t/ℓ))、R = ℓ、W = 0 -/
structure NeckData (C Sn l s c : S) : Prop where
  hC : C ≠ 0
  hl : l ≠ 0
  hs : s ≠ 0
  dl : ∀ i, d i l = 0
  C0 : d 0 C = -(Sn * l⁻¹)
  C1 : d 1 C = 0
  C2 : d 2 C = 0
  C3 : d 3 C = 0
  S0 : d 0 Sn = C * l⁻¹
  S1 : d 1 Sn = 0
  s0 : d 0 s = 0
  s1 : d 1 s = 0
  s2 : d 2 s = c
  s3 : d 3 s = 0
  c0 : d 0 c = 0
  c1 : d 1 c = 0
  c2 : d 2 c = -s
  c3 : d 3 c = 0
  comm : ∀ i j f, d i (d j f) = d j (d i f)

theorem neckSph (C Sn l s c : S) (H : NeckData d C Sn l s c) : SphD d 1 C l s c := by
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  exact ⟨one_ne_zero, hC, hl, hs, Derivation.map_one_eq_zero _, Derivation.map_one_eq_zero _, C2, C3,
    dl 2, dl 3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (0,0) 成分を満たす -/
theorem neck_00 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 0 0
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 0 0 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_00 d 1 C l s c HS, tymD_00 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination ((-1 : S) * il ^ 3 * l + (-1 : S) * il ^ 2) * hil

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (1,1) 成分を満たす -/
theorem neck_11 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 1 1
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 1 1 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_11 d 1 C l s c HS, tymD_11 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination ((1 : S) * C ^ 2 * il ^ 3 * l + (1 : S) * C ^ 2 * il ^ 2) * hil

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (2,2) 成分を満たす -/
theorem neck_22 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 2 2
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 2 2 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_22 d 1 C l s c HS, tymD_22 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination ((1 : S) * il ^ 2 * l ^ 2) * hiC

set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の (0,1) 成分を満たす -/
theorem neck_01 (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) 0 1
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) 0 1 := by
  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_01 d 1 C l s c HS, tymD_01 d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
  linear_combination 0

end Exact
