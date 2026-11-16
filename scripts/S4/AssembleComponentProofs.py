import pickle
C=pickle.load(open('cert.pkl','rb'))
def lc(qs,names):
    parts=[]
    for q,n in zip(qs,names):
        if q!='(0 : S)' and q!='0': parts.append('(%s) * %s'%(q,n))
    return ' + '.join(parts) if parts else '0'
def gens(kind):
    if kind=='D':
        return ("""  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
""",['hiN','hiA','hiR','his'])
    return ("""  have hiO : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize Om⁻¹ = iOm at hiO ⊢
  generalize r⁻¹ = ir at hir ⊢
  generalize s⁻¹ = is at his ⊢
""",['hiO','hir','his'])
SIMPD="""  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
"""
PRED="""  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iN := fun i => deriv_inv (d i) N hN
  have iA := fun i => deriv_inv (d i) A hA
  have iR := fun i => deriv_inv (d i) R hR
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zN20, zN30⟩ := z N N2 N3 0
  obtain ⟨zN21, zN31⟩ := z N N2 N3 1
  obtain ⟨zA20, zA30⟩ := z A A2 A3 0
  obtain ⟨zA21, zA31⟩ := z A A2 A3 1
  obtain ⟨zR20, zR30⟩ := z R R2 R3 0
  obtain ⟨zR21, zR31⟩ := z R R2 R3 1
  have kN := comm 1 0 N
  have kA := comm 1 0 A
  have kR := comm 1 0 R
"""
PREN="""  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
  have iO := fun i => deriv_inv (d i) Om hO
  have ir := fun i => deriv_inv (d i) r hr
  have is := fun i => deriv_inv (d i) s hs
  have z : ∀ f, d 2 f = 0 → d 3 f = 0 → ∀ j, d 2 (d j f) = 0 ∧ d 3 (d j f) = 0 := fun f h2 h3 j =>
    ⟨by rw [comm 2 j f, h2, map_zero], by rw [comm 3 j f, h3, map_zero]⟩
  obtain ⟨zO20, zO30⟩ := z Om O2 O3 0
  obtain ⟨zO21, zO31⟩ := z Om O2 O3 1
  obtain ⟨zr20, zr30⟩ := z r r2 r3 0
  obtain ⟨zr21, zr31⟩ := z r r2 r3 1
  have kO := comm 1 0 Om
  have kr := comm 1 0 r
"""
SIMPN="""  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
"""
MAT="Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons"
out={}
for kind in ['D','N']:
    c=C[kind]; L=[]
    args='N A R s c' if kind=='D' else 'Om r s c'
    gargs='N A R s' if kind=='D' else 'Om r s'
    hyp='SphD d N A R s c' if kind=='D' else 'SphN d Om r s c'
    g,names=gens(kind)
    nz='hN, hA, hR, hs' if kind=='D' else 'hO, hr, hs'
    comps=[(0,0),(1,1),(2,2),(3,3),(0,1)]+([(1,0)] if kind=='N' else [])
    for (i,j) in comps:
        rhs,qs=c[('ric',i,j)]
        L.append(f"""set_option maxHeartbeats 0 in
theorem ric{kind}_{i}{j} (H : {hyp}) : Ric d (G{kind} d {args}) {i} {j} =
    {rhs} := by
{PRED if kind=='D' else PREN}{SIMPD if kind=='D' else SIMPN}{g}  linear_combination {lc(qs,names)}
""")
    rhs,qs=c['rsc']
    rw='rw [h00, h11, h22, h33]' if kind=='D' else 'rw [h01, h10, h22, h33]'
    hs_=''.join(f"  have h{i}{j} := ric{kind}_{i}{j} d {args} H\n" for (i,j) in comps)
    L.append(f"""set_option maxHeartbeats 0 in
theorem rsc{kind} (H : {hyp}) : Rsc d (gi{kind} {gargs}) (G{kind} d {args}) =
    {rhs} := by
{hs_}  obtain ⟨{nz}, -⟩ := H
  simp only [Rsc, gi{kind}, Fin.sum_univ_four, {MAT}, zero_mul, add_zero, zero_add]
  {rw}
{g}  linear_combination {lc(qs,names)}
""")
    for (i,j) in [(0,0),(1,1),(2,2),(0,1)]:
        rhs,qs,_=c[('ein',i,j)]
        L.append(f"""set_option maxHeartbeats 0 in
theorem ein{kind}_{i}{j} (H : {hyp}) :
    Ein d (g{kind} {gargs}) (gi{kind} {gargs}) (G{kind} d {args}) {i} {j} =
    {rhs} := by
  have hR' := ric{kind}_{i}{j} d {args} H
  have hS := rsc{kind} d {args} H
  obtain ⟨{nz}, -⟩ := H
  rw [Ein, hR', hS]
  simp only [g{kind}, {MAT}]
{g}  linear_combination {lc(qs,names)}
""")
    out[kind]='\n'.join(L)
pickle.dump(out,open('lean.pkl','wb'))
print(len(out['D']),len(out['N']))
