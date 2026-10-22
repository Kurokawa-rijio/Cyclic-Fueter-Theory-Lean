import pickle
o=pickle.load(open('closed.pkl','rb'))
def fix(e): return e
L=[]
def prelude(kind):
    if kind=='D':
        return """  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
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
  simp only [Ric, GD, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring"""
    else:
        return """  obtain ⟨hO, hr, hs, O2, O3, r2, r3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
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
  simp only [Ric, GN, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, iO, ir, is, O2, O3, r2, r3,
    s0, s1, s2, s3, c0, c1, c2, c3, zO20, zO30, zO21, zO31, zr20, zr30, zr21, zr31,
    kO, kr, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  field_simp
  ring"""
for kind,args,hyp in [('D','N A R s c','SphD d N A R s c'),('N','Om r s c','SphN d Om r s c')]:
    gargs='N A R s' if kind=='D' else 'Om r s'
    for (i,j) in [(0,0),(1,1),(2,2),(3,3),(0,1)]+([(1,0)] if kind=='N' else []):
        key='Ric%s%d%d'%(kind,min(i,j),max(i,j))
        L.append(f"""set_option maxHeartbeats 0 in
theorem ric{kind}_{i}{j} (H : {hyp}) : Ric d (G{kind} d {args}) {i} {j} = {o[key]} := by
{prelude(kind)}
""")
    L.append(f"""theorem rsc{kind} (H : {hyp}) :
    Rsc d (gi{kind} {gargs}) (G{kind} d {args}) = {o['Rsc'+kind]} := by
  have h00 := ric{kind}_00 d {args} H
  have h11 := ric{kind}_11 d {args} H
  have h22 := ric{kind}_22 d {args} H
  have h33 := ric{kind}_33 d {args} H
  have h01 := ric{kind}_01 d {args} H
  have H0 := H
  obtain ⟨{'hN, hA, hR, hs' if kind=='D' else 'hO, hr, hs'}, -⟩ := H
  simp only [Rsc, gi{kind}, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, zero_mul, add_zero, zero_add]
  {'rw [h00, h11, h22, h33]' if kind=='D' else 'rw [h01, ricN_10 d Om r s c H0, h22, h33]'}
  field_simp
  ring
""")
    for (i,j) in [(0,0),(1,1),(2,2),(0,1)]:
        L.append(f"""theorem ein{kind}_{i}{j} (H : {hyp}) :
    Ein d (g{kind} {gargs}) (gi{kind} {gargs}) (G{kind} d {args}) {i} {j} = {o['Ein%s%d%d'%(kind,i,j)]} := by
  have hR := ric{kind}_{i}{j} d {args} H
  have hS := rsc{kind} d {args} H
  obtain ⟨{'hN, hA, hR0, hs' if kind=='D' else 'hO, hr, hs'}, -⟩ := H
  rw [Ein, hR, hS]
  simp only [g{kind}, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring
""")
open('ric.lean','w').write('\n'.join(L))
