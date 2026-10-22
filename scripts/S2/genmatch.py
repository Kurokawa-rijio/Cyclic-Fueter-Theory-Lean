import sympy as sp, pickle
exec(open('gen.py').read().split("import pickle")[0].replace('print("formal identity residual:",check)',''))
certs=pickle.load(open('certs.pkl','rb'))
def leanC(e):
    s=lean(e)
    return s.replace('A⁻¹','a').replace('R⁻¹','r').replace('N⁻¹','1')
P='CFT.Propagation'
args="dx A R (-(dt A * A⁻¹)) (-(dt R * R⁻¹)) W (A * dt W) (2 * l ^ 2)"
Hs=f"{P}.Hc {args}"; Ms=f"{P}.Mc {args}"
DxR=f"{P}.Dx dx A R"; DDR=f"{P}.Dx dx A ({DxR})"; DxW=f"{P}.Dx dx A W"
Kx="(-(dt A * A⁻¹))"; KT="(-(dt R * R⁻¹))"; Pp="(A * dt W)"; k="(2 * l ^ 2)"
eP=f"(dt {Pp} - (dx (dx W * A⁻¹) + A * W * (1 - W ^ 2) * R⁻¹ ^ 2))"
eKx=f"(dt {Kx} - (-2 * ({DDR}) * R⁻¹ + ({Kx} + 2 * {KT}) * {Kx} - {k} * ((({Pp} * A⁻¹) ^ 2 + ({DxW}) ^ 2) * R⁻¹ ^ 2 - (1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 * 2⁻¹)))"
eKT=f"(dt {KT} - ((1 - ({DxR}) ^ 2 - R * ({DDR})) * R⁻¹ ^ 2 + ({Kx} + 2 * {KT}) * {KT} - {k} * ((1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 * 2⁻¹)))"
H_='Hα dt dx A R W l'; M_='Mα dt dx A R W l'; eP_='ePα dt dx A R W l'; eKx_='eKxα dt dx A R W l'; eKT_='eKTα dt dx A R W l'
rhs={'N':f"A * R ^ 2 * {H_}",'b':f"-2 * A ^ 2 * R ^ 2 * {M_}",'W':f"-8 * l ^ 2 * {eP_}",
     'A':f"-4 * R ^ 2 * {eKT_} - R ^ 2 * {H_}",'R':f"-4 * A * R * ({eKx_} + {eKT_}) - 2 * A * R * {H_}"}
sig='(dt dx : Derivation ℤ S S) (A R W l : S) : S'
defs=f'''
/-- α の拘束と発展方程式(同期ゲージ、K_x = −∂_tA/A、K_T = −∂_tR/R、P = A∂_tW、κ = 2ℓ²) -/
def Hα {sig} := {Hs}
def Mα {sig} := {Ms}
def ePα {sig} := {eP}
def eKxα {sig} := {eKx}
def eKTα {sig} := {eKT}
'''
hdr='''/-
  段階 2(その 2):同期ゲージ N = 1、β = 0 で、作用の Euler–Lagrange の式は α の方程式の一次結合
    E_N = A R² · H(ハミルトン拘束、AlphaIV_Propagation の Hc)
    E_β = −2A²R² · M(運動量拘束、Mc)
    E_W = −8ℓ² ·(YM の発展方程式 ∂_t P = ∂_x(∂_xW/A) + AW(1 − W²)/R²、P = A∂_tW)
    E_A = −4R² ·(K_T の発展方程式) − R² · H
    E_R = −4AR ·(K_x の発展方程式 + K_T の発展方程式) − 2AR · H
  ここで K_x = −∂_tA/A、K_T = −∂_tR/R、P = A∂_tW、κ = 2ℓ²(拘束の伝播 AlphaIV_Propagation の変数)。
  * el_iff_alpha:A, R, ℓ ≠ 0 なら、五つの EL の式がすべて 0 ⇔ α の五つの方程式(H = M = 0 と三つの発展方程式)。
  したがって α で入力としてきた場の方程式は、段階 1 で導いた作用の帰結である(仮定ではない)。
  証明:aux/S2/match.py が A·A⁻¹ = 1、R·R⁻¹ = 1 に関する一次結合の係数を出し、linear_combination で閉じる。
-/
import CFT.AlphaS2_Action

namespace CFT.S2

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {S : Type*} [Field S] [CharZero S]
'''
body=defs
names={'N':'EN','b':'Eb','W':'EW','A':'EA','R':'ER'}
for f in ['N','b','W','A','R']:
    Q=certs[f]
    lc=' + '.join(f'({leanC(q)}) * {h}' for q,h in zip(Q,['ha','hb'])) if Q else '0'
    body+=f'''
theorem match_{f} (dt dx : Derivation ℤ S S) (A R W l : S) (hA : A ≠ 0) (hR : R ≠ 0)
    (hc : ∀ f, dt (dx f) = dx (dt f)) (hlt : dt l = 0) (hlx : dx l = 0) :
    {names[f]} dt dx 1 A R 0 W l = {rhs[f]} := by
  have ha : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hb : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have i2t : dt (2⁻¹ : S) = 0 := by rw [{P}.deriv_inv _ _ two_ne_zero, {P}.deriv_ofNat dt 2]; ring
  have i2x : dx (2⁻¹ : S) = 0 := by rw [{P}.deriv_inv _ _ two_ne_zero, {P}.deriv_ofNat dx 2]; ring
  simp only [{names[f]}, Hα, Mα, ePα, eKxα, eKTα, {P}.Hc, {P}.Mc, {P}.Dx, map_add, map_sub, map_neg, map_zero, inv_one,
    Derivation.map_one_eq_zero, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    {P}.deriv_inv _ _ hA, {P}.deriv_inv _ _ hR, {P}.deriv_ofNat dt 2, {P}.deriv_ofNat dx 2,
    {P}.deriv_ofNat dt 4, {P}.deriv_ofNat dx 4, {P}.deriv_ofNat dt 8, {P}.deriv_ofNat dx 8,
    hc, hlt, hlx, i2t, i2x, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, zero_mul, add_zero, sub_zero, mul_one, one_mul]
  generalize A⁻¹ = a at ha ⊢
  generalize R⁻¹ = r at hb ⊢
  linear_combination {lc}
'''
final='''
/-- 抽象的な形:五つの一次の関係と A, R, ℓ ≠ 0 から、EL の式がすべて 0 ⇔ α の方程式がすべて成り立つ -/
theorem el_iff_abstract (A R l EN Eb EW EA ER H M eP eKx eKT : S) (hA : A ≠ 0) (hR : R ≠ 0) (hl : l ≠ 0)
    (h1 : EN = A * R ^ 2 * H) (h2 : Eb = -2 * A ^ 2 * R ^ 2 * M) (h3 : EW = -8 * l ^ 2 * eP)
    (h4 : EA = -4 * R ^ 2 * eKT - R ^ 2 * H) (h5 : ER = -4 * A * R * (eKx + eKT) - 2 * A * R * H) :
    (EN = 0 ∧ Eb = 0 ∧ EW = 0 ∧ EA = 0 ∧ ER = 0) ↔ (H = 0 ∧ M = 0 ∧ eP = 0 ∧ eKx = 0 ∧ eKT = 0) := by
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  constructor
  · rintro ⟨e1, e2, e3, e4, e5⟩
    have hH : H = 0 := by
      rw [h1] at e1; rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h (mul_ne_zero hA hR2)
      · exact h
    have hM : M = 0 := by
      rw [h2] at e2; rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h (by simp [hA, hR])
      · exact h
    have hP : eP = 0 := by
      rw [h3] at e3; rcases mul_eq_zero.mp e3 with h | h
      · exact absurd h (by simp [hl])
      · exact h
    have hT : eKT = 0 := by
      rw [h4, hH] at e4
      have : R ^ 2 * eKT = 0 := by linear_combination (-1/4 : S) * e4
      exact (mul_eq_zero.mp this).resolve_left hR2
    have hX : eKx = 0 := by
      rw [h5, hH, hT] at e5
      have : (A * R) * eKx = 0 := by linear_combination (-1/4 : S) * e5
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hA hR)
    exact ⟨hH, hM, hP, hX, hT⟩
  · rintro ⟨hH, hM, hP, hX, hT⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, hH, mul_zero]
    · rw [h2, hM, mul_zero]
    · rw [h3, hP, mul_zero]
    · rw [h4, hT, hH]; ring
    · rw [h5, hX, hT, hH]; ring

/-- 段階 2 の結論:縮約した作用の Euler–Lagrange 方程式 ⇔ α の場の方程式(同期ゲージ) -/
theorem el_iff_alpha (dt dx : Derivation ℤ S S) (A R W l : S) (hA : A ≠ 0) (hR : R ≠ 0) (hl : l ≠ 0)
    (hc : ∀ f, dt (dx f) = dx (dt f)) (hlt : dt l = 0) (hlx : dx l = 0) :
    (EN dt dx 1 A R 0 W l = 0 ∧ Eb dt dx 1 A R 0 W l = 0 ∧ EW dt dx 1 A R 0 W l = 0 ∧
      EA dt dx 1 A R 0 W l = 0 ∧ ER dt dx 1 A R 0 W l = 0) ↔
    (Hα dt dx A R W l = 0 ∧ Mα dt dx A R W l = 0 ∧ ePα dt dx A R W l = 0 ∧
      eKxα dt dx A R W l = 0 ∧ eKTα dt dx A R W l = 0) :=
  el_iff_abstract A R l _ _ _ _ _ _ _ _ _ _ hA hR hl
    (match_N dt dx A R W l hA hR hc hlt hlx) (match_b dt dx A R W l hA hR hc hlt hlx)
    (match_W dt dx A R W l hA hR hc hlt hlx) (match_A dt dx A R W l hA hR hc hlt hlx)
    (match_R dt dx A R W l hA hR hc hlt hlx)
'''
open('/home/claude/lean/CFT/CFT/AlphaS2_Match.lean','w').write(hdr+body+final+'\nend CFT.S2\n')
print("ok")
