import pickle
Y=pickle.load(open('ym_eq.pkl','rb')); C6=pickle.load(open('cert6.pkl','rb')); C7=pickle.load(open('cert7.pkl','rb'))
MAT="Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons"
def lc(qs,names):
    parts=['(%s) * %s'%(q,n) for q,n in zip(qs,names) if q not in('0','(0 : S)')]
    return ' + '.join(parts) if parts else '0'
L=[]
L.append('''/-! ### A. 二重ヌル座標の YM 方程式(Z8 の W_uv の式を F = dA + A∧A から導く) -/

section YMEq
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

theorem eps3_table : (eps3 : Fin 3 → Fin 3 → Fin 3 → S) =
    ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]], ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
      ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]] := by
  funext a b e
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp [eps3]

/-- 上付きの F^{aμν} = g^{μα} g^{νβ} F^a_αβ -/
def Fup (gi : Fin 4 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S) (a : Fin 3) (m n : Fin 4) : S :=
  ∑ al, ∑ be, gi m al * gi n be * F a al be

/-- YM 方程式 √−g D_μ F^{aμν} = ∂_μ(√−g F^{aμν}) + √−g ε_abc A^b_μ F^{cμν} -/
def YMeq (gi : Fin 4 → Fin 4 → S) (sg : S) (Aa : Fin 3 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S)
    (a : Fin 3) (n : Fin 4) : S :=
  ∑ m, d m (sg * Fup gi F a m n) + sg * ∑ m, ∑ b, ∑ e, eps3 a b e * Aa b m * Fup gi F e m n
''')
PRE='''  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  rw [eps3_table]
  simp only [YMeq, Fup, giN, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, ''' + MAT + ''',
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
'''
for a in range(3):
    for n in range(4):
        rhs,qs=Y[a,n]
        L.append(f'''set_option maxHeartbeats 0 in
theorem ymN_{a}{n} (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) {a} {n} = {rhs} := by
{PRE}  linear_combination {lc(qs,['hiOm','hir','his'])}
''')
L.append("end YMEq\n")
open('ymeq.lean','w').write('\n'.join(L))
print('ok')
M=[]
M.append('''/-! ### B. Goursat の形と拘束の伝播 -/

section Goursat
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- uu の拘束(Raychaudhuri):C_u = r_uu − (Ω_u/Ω) r_u + 2ℓ² W_u²/r -/
def Cu (Om r W l : S) : S := d 0 (d 0 r) - d 0 Om * Om⁻¹ * d 0 r + 2 * l ^ 2 * (d 0 W) ^ 2 * r⁻¹
/-- vv の拘束 -/
def Cv (Om r W l : S) : S := d 1 (d 1 r) - d 1 Om * Om⁻¹ * d 1 r + 2 * l ^ 2 * (d 1 W) ^ 2 * r⁻¹

theorem constraint_uu (W Om r s c l : S) (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 0 - 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 0
      = -(2 * r⁻¹) * Cu d Om r W l := by
  rw [einN_00 d Om r s c H, tymN_00 d W s H.hO H.hr H.hs, Cu]; ring

theorem constraint_vv (W Om r s c l : S) (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 1 1 - 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 1 1
      = -(2 * r⁻¹) * Cv d Om r W l := by
  rw [einN_11 d Om r s c H, tymN_11 d W s H.hO H.hr H.hs, Cv]; ring

/-- Goursat の形(r):uv 成分の Einstein 方程式から r_uv を 1 階微分で書く -/
theorem goursat_r (W Om r s c l : S) (H : SphN d Om r s c)
    (hE : Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 1 = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 1) :
    d 0 (d 1 r) = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹ := by
  have hm := (CFT.S4J.mixed_eq d W Om r s c l H).mp hE
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ H.hr
  generalize r⁻¹ = ir at hir hm ⊢
  linear_combination ir * hm + ''' + C6['gr'] + '''

/-- Goursat の形(Ω):θθ 成分の Einstein 方程式から Ω_uv -/
theorem goursat_Om (W Om r s c l : S) (H : SphN d Om r s c)
    (hE : Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 2 2 = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 2 2) :
    d 0 (d 1 Om) = d 0 Om * d 1 Om * Om⁻¹ - 2 * Om * d 0 (d 1 r) * r⁻¹ - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4 := by
  rw [einN_22 d Om r s c H, tymN_22 d W s H.hO H.hr H.hs] at hE
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ H.hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ H.hr
  generalize Om⁻¹ = iOm at hiOm hE ⊢
  generalize r⁻¹ = ir at hir hE ⊢
  linear_combination (''' + C6['gO_c'] + ''') * hE + ''' + C6['gO'] + '''

/-- Goursat の形(W):YM 方程式から W_uv = ½ Ω W(1 − W²)/r²(Z8 の式) -/
theorem goursat_W (W Om r s c : S) (H : SphN d Om r s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0)
    (hY : YMeq d (giN Om r s) (Om * r ^ 2 * s) (Aym W s c) (FT d W s) 0 2 = 0) :
    d 0 (d 1 W) = 2⁻¹ * Om * W * (1 - W ^ 2) * r⁻¹ ^ 2 := by
  rw [ymN_02 d W Om r s c H W2 W3] at hY
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ H.hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ H.hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ H.hs
  generalize Om⁻¹ = iOm at hiOm hY ⊢
  generalize r⁻¹ = ir at hir hY ⊢
  generalize s⁻¹ = is at his hY ⊢
  linear_combination (-(2⁻¹ : S) * is) * hY + ''' + C6['gW'] + '''
''')
PROP='''  obtain ⟨hO, hr', hs, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr'
  have d2 : ∀ i, d i (2 : S) = 0 := fun i => deriv_ofNat (d i) 2
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, d2 i]; ring
  have kr := comm 1 0 r
  have kO := comm 1 0 Om
  have kW := comm 1 0 W
'''
SIMP='''map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, iO, ir, dl, d2, d2i,
    kr, kO, kW, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul'''
M.append('''/-- 拘束の伝播(u の拘束を v の方向に):Goursat の三つの式のもとで ∂_v C_u = −(r_v/r) C_u -/
theorem constraint_prop_u (W Om r s c l : S) (H : SphN d Om r s c) (dl : ∀ i, d i l = 0)
    (hr : d 0 (d 1 r) = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹)
    (hO : d 0 (d 1 Om) = d 0 Om * d 1 Om * Om⁻¹ - 2 * Om * d 0 (d 1 r) * r⁻¹ - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4)
    (hW : d 0 (d 1 W) = 2⁻¹ * Om * W * (1 - W ^ 2) * r⁻¹ ^ 2) :
    d 1 (Cu d Om r W l) = -(d 1 r * r⁻¹) * Cu d Om r W l := by
''' + PROP + '''  have k1 : d 1 (d 0 (d 0 r)) = d 0 (d 0 (d 1 r)) := by rw [comm 1 0 (d 0 r), kr]
  have hr1 : d 0 (d 0 (d 1 r)) = d 0 (2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹) := by
    rw [hr]
  simp only [Cu, k1, ''' + SIMP + '''] at hr1 ⊢
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr'
  generalize Om⁻¹ = iOm at hiOm hr hO hW hr1 ⊢
  generalize r⁻¹ = ir at hir hr hO hW hr1 ⊢
  linear_combination ''' + C6['cu'] + '''

/-- 拘束の伝播(v の拘束を u の方向に):∂_u C_v = −(r_u/r) C_v -/
theorem constraint_prop_v (W Om r s c l : S) (H : SphN d Om r s c) (dl : ∀ i, d i l = 0)
    (hr : d 0 (d 1 r) = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹)
    (hO : d 0 (d 1 Om) = d 0 Om * d 1 Om * Om⁻¹ - 2 * Om * d 0 (d 1 r) * r⁻¹ - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4)
    (hW : d 0 (d 1 W) = 2⁻¹ * Om * W * (1 - W ^ 2) * r⁻¹ ^ 2) :
    d 0 (Cv d Om r W l) = -(d 0 r * r⁻¹) * Cv d Om r W l := by
''' + PROP + '''  have k1 : d 0 (d 1 (d 1 r)) = d 1 (d 0 (d 1 r)) := by rw [comm 0 1 (d 1 r)]
  have hr1 : d 1 (d 0 (d 1 r)) = d 1 (2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) * r⁻¹ - d 0 r * d 1 r * r⁻¹) := by
    rw [hr]
  simp only [Cv, k1, ''' + SIMP.replace("kr, kO, kW, ","kr, ") + '''] at hr1 ⊢
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr'
  generalize Om⁻¹ = iOm at hiOm hr hO hW hr1 ⊢
  generalize r⁻¹ = ir at hir hr hO hW hr1 ⊢
  linear_combination ''' + C6['cv'] + '''

end Goursat
''')
open('goursat.lean','w').write('\n'.join(M))
print('ok')
K=[]
K.append('''/-! ### C. 外側の厳密解:帽子(閉じた放射 FRW)と首(AdS₂ × S²)を EYM の式から -/

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
''')
CAPPRE='''  have HS := capSph d a X Y s c H
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  rw [einD_{ij} d a a (a * X) s c HS, tymD_{ij} d Y s ha ha (mul_ne_zero ha hX) hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
'''
tg={(0,0):'(d 0 a) ^ 2 + a ^ 2 = l ^ 2',(1,1):'2 * a * d 0 (d 0 a) - (d 0 a) ^ 2 + a ^ 2 + l ^ 2 = 0',(2,2):'2 * a * d 0 (d 0 a) - (d 0 a) ^ 2 + a ^ 2 + l ^ 2 = 0'}
doc={(0,0):'帽子の tt 成分 ⇔ Friedmann の式 a′² + a² = ℓ²(閉じた放射 FRW、共形時間)',(1,1):'帽子の χχ 成分 ⇔ 2aa″ − a′² + a² + ℓ² = 0',(2,2):'帽子の θθ 成分 ⇔ 2aa″ − a′² + a² + ℓ² = 0(等方)'}
for ij in [(0,0),(1,1),(2,2)]:
    i,j=ij; kinv,cf,k,cb=C7[ij]
    K.append(f'''set_option maxHeartbeats 0 in
/-- {doc[ij]} -/
theorem cap_{i}{j} (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) {i} {j}
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) {i} {j} ↔ {tg[ij]} := by
{CAPPRE.replace('{ij}',f'{i}{j}')}  constructor
  · intro h
    linear_combination ({kinv}) * h + {cf}
  · intro h
    linear_combination ({k}) * h + {cb}
''')
K.append(f'''set_option maxHeartbeats 0 in
/-- 帽子の tχ 成分は恒等的に成り立つ(W_η = 0) -/
theorem cap_01 (a X Y s c l : S) (H : CapData d a X Y s c) :
    Ein d (gD a a (a * X) s) (giD a a (a * X) s) (GD d a a (a * X) s c) 0 1
      = 2 * l ^ 2 * Tym (gD a a (a * X) s) (giD a a (a * X) s) (FT d Y s) 0 1 := by
{CAPPRE.replace('{ij}','01')}  linear_combination {C7[(0,1)]}
''')
K.append('''/-- 首:時間 t(座標 0)と z(座標 1)、N = 1、A = C(C = cos(t/ℓ)、S = sin(t/ℓ))、R = ℓ、W = 0 -/
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
''')
NPRE='''  have HS := neckSph d C Sn l s c H
  obtain ⟨hC, hl, hs, dl, C0, C1, C2, C3, S0, S1, -, -, -, -, -, -, -, -, comm⟩ := H
  have il := fun i => deriv_inv (d i) l hl
  rw [einD_{ij} d 1 C l s c HS, tymD_{ij} d 0 s one_ne_zero hC hl hs]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, inv_one, one_pow, il, dl, C0, C1, S0, S1, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  have hiC : C * C⁻¹ = 1 := mul_inv_cancel₀ hC
  have hil : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  generalize C⁻¹ = iC at hiC ⊢
  generalize l⁻¹ = il at hil ⊢
'''
for (i,j) in [(0,0),(1,1),(2,2),(0,1)]:
    K.append(f'''set_option maxHeartbeats 0 in
/-- 首(AdS₂ × S² の同期座標 −dt² + cos²(t/ℓ)dz² + ℓ²dΩ²)は EYM の ({i},{j}) 成分を満たす -/
theorem neck_{i}{j} (C Sn l s c : S) (H : NeckData d C Sn l s c) :
    Ein d (gD 1 C l s) (giD 1 C l s) (GD d 1 C l s c) {i} {j}
      = 2 * l ^ 2 * Tym (gD 1 C l s) (giD 1 C l s) (FT d 0 s) {i} {j} := by
{NPRE.replace('{ij}',f'{i}{j}')}  linear_combination {C7[('neck',i,j)]}
''')
K.append("end Exact\n")
open('exact.lean','w').write('\n'.join(K))
print('ok3')
