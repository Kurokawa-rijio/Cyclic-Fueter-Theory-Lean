import pickle
K=pickle.load(open('kret_cert.pkl','rb')); KC=pickle.load(open('kret_cap.pkl','rb'))
def lc(qs,names):
    parts=['(%s) * %s'%(q,n) for q,n in zip(qs,names) if q not in('0','(0 : S)')]
    return ' + '.join(parts) if parts else '0'
MAT="Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons"
s=f'''/-
  段階 5 の補い(2026-10-21 の外部レビュー):帽子の崩壊を曲率の不変量で直接示す、波面の軌道を導く

  * Riem:Riemann テンソル R^a_bce = ∂_c Γ^a_eb − ∂_e Γ^a_cb + Γ^a_cf Γ^f_eb − Γ^a_ef Γ^f_cb
  * KretD:対角な計量での全縮約 K = R_abce R^abce = Σ g_aa g^bb g^cc g^ee (R^a_bce)²(gD_diag で計量は対角)
  * kretD:一般の球対称な計量 −N²dt² + A²dx² + R²dΩ² の K を計算(Christoffel の表 GD から)
  * kret_cap:帽子(閉じた放射 FRW)で、場の方程式 a′² + a² = ℓ²、a″ = −a(cap_00、cap_22、cap_accel)のもとで
    K = 24ℓ⁴/a⁸(外部レビューの値と一致。共形時間で計算、固有時 τ = ℓ sin η で a² = ℓ² − τ²)
  * kret_blowup:a = ℓ cos η で η → π/2⁻ のとき K → ∞(密度の発散 cap_crunch とは別に、曲率の不変量の発散)
  * kret_center、density_center:K と ρ̂ は χ によらない(一様)ので、極座標の中心 χ → 0 でも同じ値
  * front_null、front_sign、front_inward、front_hits_center:共形計量 a²(−dη² + dχ²) のヌル曲線は χ′² = 1、
    連続な χ′ で χ′(0) = −1 なら至る所 −1、χ(0) = π/2 から χ = π/2 − η、中心 χ = 0 に着くのは η = π/2 だけ
-/
import CFT.AlphaS5_Evolution

namespace CFT.S5K

open CFT.S4 CFT.S5
open CFT.Propagation (deriv_inv deriv_ofNat)

section Curv
variable {{S : Type*}} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- Riemann テンソル R^a_bce -/
def Riem (Γ : Fin 4 → Fin 4 → Fin 4 → S) (a b c e : Fin 4) : S :=
  d c (Γ a e b) - d e (Γ a c b) + ∑ f, (Γ a c f * Γ f e b - Γ a e f * Γ f c b)

/-- 対角な計量(成分 gd、逆 gid)での Kretschmann スカラー R_abce R^abce -/
def KretD (gd gid : Fin 4 → S) (Γ : Fin 4 → Fin 4 → Fin 4 → S) : S :=
  ∑ a, ∑ b, ∑ c, ∑ e, gd a * gid b * gid c * gid e * Riem d Γ a b c e ^ 2

/-- gD は対角で、成分は ![−N², A², R², R²s²](giD も同様) -/
theorem gD_diag (N A R s : S) :
    (∀ i j, gD N A R s i j = if i = j then ![-N ^ 2, A ^ 2, R ^ 2, R ^ 2 * s ^ 2] i else 0) ∧
    (∀ i j, giD N A R s i j = if i = j then ![-(N⁻¹ ^ 2), A⁻¹ ^ 2, R⁻¹ ^ 2, R⁻¹ ^ 2 * s⁻¹ ^ 2] i else 0) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [gD, giD]

set_option maxHeartbeats 0 in
/-- 一般の球対称な計量の Kretschmann スカラー -/
theorem kretD (N A R s c : S) (H : SphD d N A R s c) :
    KretD d ![-N ^ 2, A ^ 2, R ^ 2, R ^ 2 * s ^ 2] ![-(N⁻¹ ^ 2), A⁻¹ ^ 2, R⁻¹ ^ 2, R⁻¹ ^ 2 * s⁻¹ ^ 2]
      (GD d N A R s c) = {K['rhs']} := by
  obtain ⟨hN, hA, hR, hs, N2, N3, A2, A3, R2, R3, s0, s1, s2, s3, c0, c1, c2, c3, comm⟩ := H
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
  simp only [KretD, Riem, GD, Fin.sum_univ_four, {MAT}, map_add, map_sub, map_neg, map_mul, map_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    iN, iA, iR, is, N2, N3, A2, A3, R2, R3,
    s0, s1, s2, s3, c0, c1, c2, c3, zN20, zN30, zN21, zN31, zA20, zA30, zA21, zA31, zR20, zR30, zR21, zR31,
    kN, kA, kR, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  have his : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  generalize s⁻¹ = is at his ⊢
  linear_combination {lc(K['q'][:4],['hiN','hiA','hiR','his'])}

set_option maxHeartbeats 0 in
/-- 帽子(閉じた放射 FRW):場の方程式のもとで K = 24ℓ⁴/a⁸ -/
theorem kret_cap (a X Y s c l : S) (H : CapData d a X Y s c)
    (h00 : (d 0 a) ^ 2 + a ^ 2 = l ^ 2) (h22 : d 0 (d 0 a) = -a) :
    KretD d ![-a ^ 2, a ^ 2, (a * X) ^ 2, (a * X) ^ 2 * s ^ 2]
      ![-(a⁻¹ ^ 2), a⁻¹ ^ 2, (a * X)⁻¹ ^ 2, (a * X)⁻¹ ^ 2 * s⁻¹ ^ 2] (GD d a a (a * X) s c)
      = 24 * l ^ 4 * a⁻¹ ^ 8 := by
  have HS := capSph d a X Y s c H
  rw [kretD d a a (a * X) s c HS]
  obtain ⟨ha, hX, hs, a1, a2, a3, X0, X1, X2, X3, Y0, Y1, hXY, -, -, -, -, -, -, -, -, comm⟩ := H
  have za : d 1 (d 0 a) = 0 := by rw [comm 1 0 a, a1, map_zero]
  simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, smul_eq_mul, mul_inv,
    a1, X0, X1, Y0, Y1, za, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hiX : X * X⁻¹ = 1 := mul_inv_cancel₀ hX
  generalize a⁻¹ = ia at hia ⊢
  generalize X⁻¹ = iX at hiX ⊢
  linear_combination {KC}

end Curv
'''
open('kret.lean','w').write(s)
