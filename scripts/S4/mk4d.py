import pickle
C4=pickle.load(open('cert4dall.pkl','rb')); Y=pickle.load(open('ymdall.pkl','rb'))
allL=open('all.lean').read()
def lc(qs,names):
    parts=['(%s) * %s'%(q,n) for q,n in zip(qs,names) if q not in('0','(0 : S)')]
    return ' + '.join(parts) if parts else '0'
MAT="Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons"
ric_ein=allL[:allL.index("set_option maxHeartbeats 0 in\ntheorem tymA_00")]
tym=allL[allL.index("set_option maxHeartbeats 0 in\ntheorem tymA_00"):]
hdr='''/-
  段階 2 の補い:縮約した方程式と 4 次元の EYM 方程式の全成分の直接の照合(Palais の対称臨界性を使わない)

  同期ゲージ N = 1、シフト 0、計量 −dt² + A²dx² + R²dΩ²、YM の接続 A = Wτ₁dθ + (Wsτ₂ + cτ₃)dφ。
  E_μν := G_μν − 2ℓ²T̂_μν(4 次元の Einstein テンソルは Levi-Civita の公式から、T̂ は F = dA + A∧A から)。
  縮約の残差 H = Hα、M = Mα、X = eKxα、T = eKTα、eP = ePα(AlphaS2_Match)について
    E₀₀ = H/2、E₀₁ = E₁₀ = −A M、E₁₁ = A²(2T + H/2)、E₂₂ = R²(X + T + H/2)、E₃₃ = s² E₂₂、他の 10 成分は 0
    YM の (1,θ) 成分 = −s eP、(2,φ) 成分 = −eP、他の 10 成分は 0
  (sync_ij、ym_all)。したがって
  * full_4d_iff_alpha:4 次元の EYM 方程式の全成分(Einstein 16、YM 12)⇔ α の五つの方程式
  * palais_free:4 次元の EYM 方程式の全成分 ⇔ 縮約した作用の五つの Euler–Lagrange 方程式(el_iff_alpha と合成)
  この ansatz について、縮約してから変分してよいこと(Palais)を外部定理として使わずに済む。
  補題 ricA_ij、einA_ij(全 16 成分の Ricci と Einstein)、tymA_ij(全 16 成分の YM の応力)、ymA_an(YM 方程式の全 12 成分)。
-/
import CFT.AlphaS4_Distrib
import CFT.AlphaS2_Match

namespace CFT.S2M

open CFT.S4 CFT.S5 CFT.S2
open CFT.Propagation (deriv_inv deriv_ofNat)

section Curv
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S) (N A R s c : S)

'''
mid='''
end Curv

section Stress
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S) (W s : S)

'''
# YM all components
YPRE='''  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zW20, zW30⟩ := z W W2 W3 0
  obtain ⟨zW21, zW31⟩ := z W W2 W3 1
  have kW := comm 1 0 W
  simp only [eps3_table, YMeq, Fup, giD, FT, Aym, Fin.sum_univ_three, Fin.sum_univ_four, '''+MAT+''',
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3, W2, W3, s0, s1, s2, s3, c0, c1, c2, c3, zW20, zW30, zW21, zW31, kW,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul, neg_mul, mul_neg]
  all_goals
    have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize N⁻¹ = iN at hiN ⊢
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
'''
ym=['\nend Stress\n\nsection YMall\nvariable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)\n']
for a in range(3):
    for n in range(4):
        rhs,qs=Y[a,n]
        ym.append(f'''set_option maxHeartbeats 0 in
theorem ymA_{a}{n} (W N A R s c : S) (H : SphD d N A R s c) (W2 : d 2 W = 0) (W3 : d 3 W = 0) :
    YMeq d (giD N A R s) (N * A * R ^ 2 * s) (Aym W s c) (FT d W s) {a} {n} = {rhs} := by
{YPRE}    linear_combination {lc(qs,['hiN','hiA','hiR','his'])}
''')
ym.append("end YMall\n")
# sync theorems
tg={(0,0):'2⁻¹ * Hα (d 0) (d 1) A R W l',(0,1):'-(A * Mα (d 0) (d 1) A R W l)',(1,0):'-(A * Mα (d 0) (d 1) A R W l)',
    (1,1):'A ^ 2 * (2 * eKTα (d 0) (d 1) A R W l + 2⁻¹ * Hα (d 0) (d 1) A R W l)',
    (2,2):'R ^ 2 * (eKxα (d 0) (d 1) A R W l + eKTα (d 0) (d 1) A R W l + 2⁻¹ * Hα (d 0) (d 1) A R W l)',
    (3,3):'s ^ 2 * (R ^ 2 * (eKxα (d 0) (d 1) A R W l + eKTα (d 0) (d 1) A R W l + 2⁻¹ * Hα (d 0) (d 1) A R W l))'}
SYNC=['\nsection Sync\nvariable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)\n']
for i in range(4):
    for j in range(4):
        rhs=tg.get((i,j),'0')
        qs=C4[(i,j)]
        SYNC.append(f'''set_option maxHeartbeats 0 in
theorem sync_{i}{j} (W A R s c l : S) (H : SphD d 1 A R s c) (hl0 : d 0 l = 0) (hl1 : d 1 l = 0) :
    Ein d (gD 1 A R s) (giD 1 A R s) (GD d 1 A R s c) {i} {j}
      - 2 * l ^ 2 * Tym (gD 1 A R s) (giD 1 A R s) (FT d W s) {i} {j} = {rhs} := by
  have hE := einA_{i}{j} d 1 A R s c H
  have hT := tymA_{i}{j} d W s one_ne_zero H.hA H.hR H.hs
  rw [hE, hT]
  obtain ⟨-, hA, hR, hs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, comm⟩ := H
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have kA := comm 1 0 A
  have kR := comm 1 0 R
  have kW := comm 1 0 W
  have d2i : ∀ i, d i (2⁻¹ : S) = 0 := fun i => by rw [deriv_inv (d i) 2 two_ne_zero, deriv_ofNat (d i) 2]; ring
  simp only [Hα, Mα, ePα, eKxα, eKTα, CFT.Propagation.Hc, CFT.Propagation.Mc, CFT.Propagation.Dx,
    map_add, map_sub, map_neg, map_mul, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, inv_one, one_pow,
    iA, iR, kA, kR, kW, hl0, hl1, d2i, deriv_ofNat (d 0) 2, deriv_ofNat (d 1) 2,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, mul_one, one_mul]
  all_goals
    have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
    have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    generalize A⁻¹ = iA at hiA ⊢
    generalize R⁻¹ = iR at hiR ⊢
    generalize s⁻¹ = is at his ⊢
    linear_combination {lc(qs,['hiA','hiR','his'])}
''')
SYNC.append("end Sync\n")
open('/home/claude/lean/CFT/CFT/AlphaS2_4DMatch.lean','w').write(hdr+ric_ein+mid+tym+''.join(ym)+''.join(SYNC)+"\nend CFT.S2M\n")
print('written')
