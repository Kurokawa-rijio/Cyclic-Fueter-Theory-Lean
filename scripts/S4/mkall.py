import pickle,re
C=pickle.load(open('certall.pkl','rb')); T=pickle.load(open('certTall.pkl','rb'))
src=open('mklean.py').read()
ns={}
exec(src.split("out={}")[0],ns)   # get lc, gens, SIMPD, PRED
lc=ns['lc']; gens=ns['gens']; SIMPD=ns['SIMPD']; PRED=ns['PRED']
def wrap(block):
    return "  all_goals\n"+''.join('  '+ln+'\n' for ln in block.rstrip('\n').split('\n'))
g,names=gens('D')
L=[]
for i in range(4):
    for j in range(4):
        rhs,qs=C[('ric',i,j)]
        L.append(f"""set_option maxHeartbeats 0 in
theorem ricA_{i}{j} (H : SphD d N A R s c) : Ric d (GD d N A R s c) {i} {j} =
    {rhs} := by
{PRED}{SIMPD}{wrap(g+'  linear_combination '+lc(qs,names))}""")
for i in range(4):
    for j in range(4):
        rhs,qs,_=C[('ein',i,j)]
        L.append(f"""set_option maxHeartbeats 0 in
theorem einA_{i}{j} (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) {i} {j} =
    {rhs} := by
  have hR' := ricA_{i}{j} d N A R s c H
  have hS := rscD d N A R s c H
  obtain ⟨hN, hA, hR, hs, -⟩ := H
  rw [Ein, hR', hS]
  simp only [gD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_zero, zero_mul, sub_zero]
{wrap(g+'  linear_combination '+lc(qs,names))}""")
MAT="Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons"
def gT(st):
    for f in ['N','A','R']: st=st.replace('%s⁻¹'%f,'i'+f)
    return st.replace('s⁻¹','is')
genT="""have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
generalize N⁻¹ = iN at hiN ⊢
generalize A⁻¹ = iA at hiA ⊢
generalize R⁻¹ = iR at hiR ⊢
generalize s⁻¹ = is at his ⊢
"""
for i in range(4):
    for j in range(4):
        rhs,qs,_=T[('D','T',i,j)]
        qs=[gT(q) for q in qs]
        L.append(f"""set_option maxHeartbeats 0 in
theorem tymA_{i}{j} {{N A R : S}} (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) {i} {j} =
    {rhs} := by
  simp only [Tym, gD, giD, FT, Fin.sum_univ_three, Fin.sum_univ_four, {MAT},
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, neg_mul, mul_neg]
{wrap(genT+'linear_combination '+lc(qs,['hiN','hiA','hiR','his']))}""")
open('all.lean','w').write('\n'.join(L))
print(len(L))
