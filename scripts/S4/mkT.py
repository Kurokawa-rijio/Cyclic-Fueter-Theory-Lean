import pickle
r=pickle.load(open('certT.pkl','rb'))
def g(s):
    for f in ['Om','N','A','R','r']: s=s.replace('%s⁻¹'%f,'i'+f)
    return s.replace('s⁻¹','is')
def lc(qs,names):
    parts=['(%s) * %s'%(g(q),n) for q,n in zip(qs,names) if q not in('0','(0 : S)')]
    return ' + '.join(parts) if parts else '0'
F=r['D','F']
FT='![' + ',\n    '.join('![' + ', '.join('!['+', '.join(F[a][m])+']' for m in range(4))+']' for a in range(3))+']'
MAT="Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons"
L=[]
L.append(f'''/-! ### Yang–Mills の場の強さと応力(球対称な磁気的な仮定 A = W τ₁ dθ + (W s τ₂ + c τ₃) dφ) -/

section YM
variable (W s c : S)

/-- Levi-Civita 記号 ε_abc(su(2) の構造定数) -/
def eps3 (a b e : Fin 3) : S :=
  if (a, b, e) = (0, 1, 2) ∨ (a, b, e) = (1, 2, 0) ∨ (a, b, e) = (2, 0, 1) then 1
  else if (a, b, e) = (0, 2, 1) ∨ (a, b, e) = (2, 1, 0) ∨ (a, b, e) = (1, 0, 2) then -1 else 0

/-- 接続 A^a_μ(座標 0, 1 は (t, x) または (u, v)、2 = θ、3 = φ) -/
def Aym : Fin 3 → Fin 4 → S := ![![0, 0, W, 0], ![0, 0, 0, W * s], ![0, 0, 0, c]]

/-- 場の強さ F^a_μν = ∂_μ A^a_ν − ∂_ν A^a_μ + ε_abc A^b_μ A^c_ν -/
def Fym (Aa : Fin 3 → Fin 4 → S) (a : Fin 3) (m n : Fin 4) : S :=
  d m (Aa a n) - d n (Aa a m) + ∑ b, ∑ e, eps3 a b e * Aa b m * Aa e n

/-- F の表 -/
def FT : Fin 3 → Fin 4 → Fin 4 → S :=
  {FT}

/-- YM の応力 T̂_μν = F^a_μλ F^a_ν^λ − ¼ g_μν F^a_αβ F^{{aαβ}}(T = T̂/g²、8πG T = 2ℓ² T̂) -/
def Tym (g gi : Fin 4 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S) (m n : Fin 4) : S :=
  ∑ a, ∑ l, ∑ k, F a m l * gi l k * F a n k
    - 4⁻¹ * g m n * ∑ a, ∑ al, ∑ be, ∑ ga, ∑ de, F a al be * gi al ga * gi be de * F a ga de

set_option maxHeartbeats 0 in
theorem fym_eq (W2 : d 2 W = 0) (W3 : d 3 W = 0) (s0 : d 0 s = 0) (s1 : d 1 s = 0) (s2 : d 2 s = c)
    (s3 : d 3 s = 0) (c0 : d 0 c = 0) (c1 : d 1 c = 0) (c2 : d 2 c = -s) (c3 : d 3 c = 0) :
    Fym d (Aym W s c) = FT d W s c := by
  funext a m n
  fin_cases a <;> fin_cases m <;> fin_cases n <;>
    simp [Fym, Aym, FT, eps3, Fin.sum_univ_three, Derivation.leibniz, smul_eq_mul, W2, W3, s0, s1, s2, s3,
      c0, c1, c2, c3] <;> ring
''')
for kind in ['D','N']:
    gargs='N A R s' if kind=='D' else 'Om r s'
    nz=[('N','hN'),('A','hA'),('R','hR'),('s','hs')] if kind=='D' else [('Om','hO'),('r','hr'),('s','hs')]
    hyps=' '.join(f'({h} : {v} ≠ 0)' for v,h in nz)
    gen=''.join(f"  have hi{v} : {v} * {v}⁻¹ = 1 := mul_inv_cancel₀ {h}\n" for v,h in nz)+''.join(f"  generalize {v}⁻¹ = i{v if v!='s' else 's'} at hi{v} ⊢\n" for v,h in nz)
    gen=gen.replace('generalize s⁻¹ = is at his','generalize s⁻¹ = is at his').replace('= is at his','= is at his')
    names=[f'hi{v}' for v,h in nz]
    for (m,n) in [(0,0),(1,1),(0,1),(2,2)]+([(1,2),(1,3)] if kind=='N' else []):
        rhs,qs,_=r[kind,'T',m,n]
        L.append(f'''set_option maxHeartbeats 0 in
theorem tym{kind}_{m}{n} {hyps} :
    Tym (g{kind} {gargs}) (gi{kind} {gargs}) (FT d W s c) {m} {n} =
    {rhs} := by
  simp only [Tym, g{kind}, gi{kind}, FT, Fin.sum_univ_three, Fin.sum_univ_four, {MAT},
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
{gen}  linear_combination {lc(qs,names)}
''')
L.append("end YM\n")
open('ym.lean','w').write('\n'.join(L))
