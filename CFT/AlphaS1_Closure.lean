/-
  段階 0・1 の範囲を閉じる三つの定理(2026-10-21 の外部検算の指摘への対応)

  指摘 (a):巡回族 D_m は定義として置かれ、幾何から導かれていない。
  指摘 (b):Maxwell の一意性は指定した二次形式の類の中、非可換の部分は不変性だけ。
  指摘 (c):GHY 項は FRW の恒等式だけ。

  A. 巡回族の導出
    * factorization_iff:一階の定数係数の作用素 D = Σ c_a ∂_a(c_a ∈ ℍ)が Laplacian を因数分解する
      (記号で (Σ c̄_a ξ_a)(Σ c_b ξ_b) = |ξ|²)⇔ c̄_a c_b + c̄_b c_a = 2δ_ab(係数が ℍ の正規直交基底)。
      したがって D̄D = Δ を満たす作用素は、正規直交基底 (1, i, j, k) の並べ替え(と O(4) の作用)で尽くされる
    * 四つの作用素の族を「添字の上に推移的に働く位数 4 の群」の軌道として作ると、群は巡回群 ℤ₄(4-cycle が生成、
      共役が三つ)か Klein の四元群 V₄ のどちらか(S₄ の推移的な位数 4 の部分群の分類、初等的な既知の事実)。
      - ℤ₄(巡回族):係数行列は特異で、共通の解の直線 γ(−k)ℍ を持つ(α-I.2 の right_kernel、null_solution)
      - V₄(Klein の族):klein_family_regular:右核は 0。共通の解はない
      つまり「Laplacian の因数分解 + 推移的な最小の並べ替え + 共通の解(特異性)」から巡回族が選ばれる
  B. ゲージ場の作用の完全性
    * maxwell_mass:質量項 m²(ξ·ξ) を含めた一般の記号 a(k·k)(ξ·ξ) + b(k·ξ)² + m²(ξ·ξ) がゲージ不変 ⇔ a + b = 0 かつ m² = 0
    * ym_coupling:曲率 F_c = ∂A − ∂A + c ε^{abc}A^bA^c の変換は δF_c = ε^{abc}F_c^b ε^c + (c − 1)X(X は明示)
    * ym_coupling_forced:座標関数がある環で、共変性がすべての配位で成り立つなら c = 1。
      非可換の結合定数(曲率の二次の項の係数)はゲージ変換の形から強制される(Utiyama の主張の核心)
  C. 境界項(球対称の一般の計量)
    * ghy_spherical:ds² = −N²dt² + A²dx² + R²dΩ²(N, A, R は (t, x) の任意の関数)で
        √−g R / sin θ = L₁ + ∂_t(2√h K_t) + ∂_x(−2√−γ K_x)
      L₁ = 2AN − 2AṘ²/N − 4RȦṘ/N + 2NR′²/A + 4RN′R′/A は一階の微分だけ。
      √h K_t = (ȦR² + 2ARṘ)/N(t 一定の面)、√−γ K_x = (N′R² + 2NRR′)/A(x 一定の面)。
      GHY 項 (1/8πG)∮εK√|h| がちょうど二つの全微分を消すので、EH + GHY = (1/16πG)∫L₁:
      Dirichlet の変分問題が球対称の全体(ダンベルのすべての配位)で立つ
  外部に残るもの:スカラー曲率の公式そのもの(計量からの曲率の計算、aux/S1/ghy.py の sympy で確認)、
  S₄ の推移的な位数 4 の部分群の分類(初等的)、Lovelock の定理(非線形への延長)。
-/
import CFT.AlphaS1_Derivation
import Mathlib.Tactic.FieldSimp
import CFT.AlphaIV_Propagation
import CFT.AlphaI_C

open Quaternion

namespace CFT.S1C

set_option maxHeartbeats 4000000

/-! ### A. 巡回族の導出 -/

/-- 記号の積 (Σ ξ_a c̄_a)(Σ ξ_b c_b)(実数 ξ_a は ℍ の中心) -/
def symProd (c : Fin 4 → ℍ[ℝ]) (ξ : Fin 4 → ℝ) : ℍ[ℝ] :=
  (∑ a, (ξ a : ℍ[ℝ]) * star (c a)) * (∑ b, (ξ b : ℍ[ℝ]) * c b)

theorem symProd_expand (c : Fin 4 → ℍ[ℝ]) (ξ : Fin 4 → ℝ) :
    symProd c ξ = ∑ a, ∑ b, ((ξ a * ξ b : ℝ) : ℍ[ℝ]) * (star (c a) * c b) := by
  rw [symProd, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Quaternion.coe_mul, mul_assoc, ← mul_assoc (star (c a)), ← Quaternion.coe_commutes, mul_assoc,
    mul_assoc]

/-- 記号の因数分解 ⇔ 係数の正規直交性 -/
theorem factorization_iff (c : Fin 4 → ℍ[ℝ]) :
    (∀ ξ : Fin 4 → ℝ, symProd c ξ = ((∑ a, ξ a ^ 2 : ℝ) : ℍ[ℝ])) ↔
      ∀ a b, star (c a) * c b + star (c b) * c a = ((if a = b then 2 else 0 : ℝ) : ℍ[ℝ]) := by
  constructor
  · intro H a b
    have hd : ∀ a, star (c a) * c a = 1 := by
      intro a
      have := H (Pi.single a 1)
      rw [symProd_expand] at this
      fin_cases a <;> simpa [Fin.sum_univ_four, Pi.single_apply] using this
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, hd]; ext <;> simp; norm_num
    · rw [if_neg hab]
      have := H (Pi.single a 1 + Pi.single b 1)
      rw [symProd_expand] at this
      fin_cases a <;> fin_cases b <;> simp_all [Fin.sum_univ_four, Pi.single_apply] <;>
        (have h' := sub_eq_zero.mpr this; abel_nf at h' ⊢; first | exact h' | (rw [← h']; abel))
  · intro H ξ
    have hd : ∀ a, star (c a) * c a = 1 := by
      intro a
      have h := H a a
      rw [if_pos rfl] at h
      have h0 := congrArg (fun q : ℍ[ℝ] => q.re) h; have h1 := congrArg (fun q : ℍ[ℝ] => q.imI) h
      have h2 := congrArg (fun q : ℍ[ℝ] => q.imJ) h; have h3 := congrArg (fun q : ℍ[ℝ] => q.imK) h
      simp only [Quaternion.add_re, Quaternion.add_imI, Quaternion.add_imJ, Quaternion.add_imK,
        Quaternion.coe_re, Quaternion.coe_imI, Quaternion.coe_imJ, Quaternion.coe_imK] at h0 h1 h2 h3
      ext <;> simp only [Quaternion.one_re, Quaternion.one_imI, Quaternion.one_imJ, Quaternion.one_imK] <;>
        linarith
    have ha : ∀ a b, a ≠ b → star (c b) * c a = -(star (c a) * c b) := by
      intro a b hab; have h := H a b; rw [if_neg hab, Quaternion.coe_zero] at h
      exact eq_neg_of_add_eq_zero_right h
    rw [symProd_expand]
    simp only [Fin.sum_univ_four, hd, ha 0 1 (by decide), ha 0 2 (by decide), ha 0 3 (by decide),
      ha 1 2 (by decide), ha 1 3 (by decide), ha 2 3 (by decide)]
    simp only [Quaternion.coe_add, sq]
    rw [mul_comm (ξ 1) (ξ 0), mul_comm (ξ 2) (ξ 0), mul_comm (ξ 3) (ξ 0), mul_comm (ξ 2) (ξ 1),
      mul_comm (ξ 3) (ξ 1), mul_comm (ξ 3) (ξ 2)]
    simp only [mul_neg, mul_one]
    abel

/-- 巡回族の各作用素の係数 e_{m+a} は正規直交:D̄_m D_m = Δ(v6 の命題 8.2) -/
theorem cyclic_factorizes (m : Fin 4) :
    ∀ a b, star ((CFT.FueterC.e (m + a))) * CFT.FueterC.e (m + b)
      + star (CFT.FueterC.e (m + b)) * CFT.FueterC.e (m + a) = ((if a = b then 2 else 0 : ℝ) : ℍ[ℝ]) := by
  intro a b
  fin_cases m <;> fin_cases a <;> fin_cases b <;>
    simp [CFT.FueterC.e, CFT.FueterC.qi, CFT.FueterC.qj, CFT.FueterC.qk] <;> ext <;> simp <;> norm_num

/-- Klein の四元群による族:行は (1,i,j,k)、(i,1,k,j)、(j,k,1,i)、(k,j,i,1) -/
def kleinRow : Fin 4 → Fin 4 → ℍ[ℝ] :=
  ![![1, ⟨0,1,0,0⟩, ⟨0,0,1,0⟩, ⟨0,0,0,1⟩],
    ![⟨0,1,0,0⟩, 1, ⟨0,0,0,1⟩, ⟨0,0,1,0⟩],
    ![⟨0,0,1,0⟩, ⟨0,0,0,1⟩, 1, ⟨0,1,0,0⟩],
    ![⟨0,0,0,1⟩, ⟨0,0,1,0⟩, ⟨0,1,0,0⟩, 1]]

/-- Klein の族は正則:右核は 0(共通の解がない) -/
theorem klein_family_regular (y : Fin 4 → ℍ[ℝ]) (h : ∀ r, ∑ a, kleinRow r a * y a = 0) : y = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [kleinRow, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Quaternion.ext_iff] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  obtain ⟨a0, a1, a2, a3⟩ := h0; obtain ⟨b0, b1, b2, b3⟩ := h1
  obtain ⟨c0, c1, c2, c3⟩ := h2; obtain ⟨d0, d1, d2, d3⟩ := h3
  funext r
  fin_cases r <;> ext <;> simp <;> linarith

/-! ### B. ゲージ場の作用の完全性 -/

open CFT.S1 in
/-- 質量項を含めた記号:ゲージ不変 ⇔ a + b = 0 かつ m² = 0 -/
theorem maxwell_mass (a b m2 : ℝ) :
    (∀ k ξ (t : ℝ), vecQ a b k (fun i => ξ i + t * k i) + m2 * dot (fun i => ξ i + t * k i) (fun i => ξ i + t * k i)
        = vecQ a b k ξ + m2 * dot ξ ξ) ↔ (a + b = 0 ∧ m2 = 0) := by
  constructor
  · intro h
    have e1 := h ![-1, 0, 0, 0] ![0, 0, 0, 0] 1
    have e2 := h ![0, 1, 0, 0] ![0, 0, 0, 0] 1
    simp [vecQ, dot, eta, Fin.sum_univ_four] at e1 e2
    constructor <;> linarith
  · rintro ⟨hab, hm⟩ k ξ t
    have hb : b = -a := by linarith
    subst hb hm
    simp only [vecQ, dot, Fin.sum_univ_four]
    ring

section YM
variable {S : Type*} [CommRing S]
variable (D : Fin 4 → Derivation ℤ S S) (A : Fin 3 → Fin 4 → S) (ε : Fin 3 → S) (c : S)

open CFT.S1 in
/-- 結合定数 c を持つ曲率 -/
def Fc (a : Fin 3) (μ ν : Fin 4) : S :=
  D μ (A a ν) - D ν (A a μ) + c * ∑ b, ∑ e, f3 a b e * A b μ * A e ν

open CFT.S1 in
/-- δF_c の Leibniz 展開(δA は通常のゲージ変換) -/
def dFc (a : Fin 3) (μ ν : Fin 4) : S :=
  D μ (dA D A ε a ν) - D ν (dA D A ε a μ)
    + c * ∑ b, ∑ e, f3 a b e * (dA D A ε b μ * A e ν + A b μ * dA D A ε e ν)

open CFT.S1 in
/-- 余り Y^a_{μν} = Σ ε^{abe}(A^b_μ ∂_ν ε^e − A^b_ν ∂_μ ε^e) -/
def Yrem (a : Fin 3) (μ ν : Fin 4) : S :=
  ∑ b, ∑ e, f3 a b e * (A b μ * D ν (ε e) - A b ν * D μ (ε e))

open CFT.S1 in
theorem ym_coupling (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (hcc : ∀ μ, D μ c = 0)
    (a : Fin 3) (μ ν : Fin 4) :
    dFc D A ε c a μ ν = ∑ b, ∑ e, f3 a b e * Fc D A c b μ ν * ε e + (c - 1) * Yrem D A ε a μ ν := by
  have h := hc μ ν
  fin_cases a <;>
  simp [dFc, dA, Fc, Yrem, f3, Fin.sum_univ_three, map_add, map_sub, map_neg, Derivation.leibniz,
    smul_eq_mul, h, hcc] <;> ring

open CFT.S1 in
/-- 共変性がすべての配位で成り立つなら c = 1 -/
theorem ym_coupling_forced (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x)) (hcc : ∀ μ, D μ c = 0)
    (x : Fin 4 → S) (hx : ∀ a b, D a (x b) = if a = b then 1 else 0)
    (H : ∀ (A : Fin 3 → Fin 4 → S) (ε : Fin 3 → S),
      dFc D A ε c 0 0 1 = ∑ b, ∑ e, f3 0 b e * Fc D A c b 0 1 * ε e) : c = 1 := by
  set A0 : Fin 3 → Fin 4 → S := fun b μ => if b = 1 ∧ μ = 0 then 1 else 0
  set e0 : Fin 3 → S := fun e => if e = 2 then x 1 else 0
  have h1 := ym_coupling D A0 e0 c hc hcc 0 0 1
  rw [H A0 e0] at h1
  have hY : Yrem D A0 e0 0 0 1 = 1 := by
    simp [Yrem, A0, e0, f3, Fin.sum_univ_three, hx]
  rw [hY] at h1
  have : c - 1 = 0 := by linear_combination -h1
  linear_combination this

end YM

/-! ### C. 境界項(球対称の一般の計量) -/

section GHY
variable {S : Type*} [Field S] [CharZero S] (dt dx : Derivation ℤ S S) (N A R : S)

/-- √−g R / sin θ(計量 −N²dt² + A²dx² + R²dΩ²、aux/S1/ghy.py の sympy の公式) -/
def sqrtgR : S :=
  2*A*N + 4*A*R*dt (dt R)*N⁻¹ + 2*A*(dt R)^2*N⁻¹ - 4*A*R*dt N*dt R*N⁻¹^2
  + 2*R^2*dt (dt A)*N⁻¹ + 4*R*dt A*dt R*N⁻¹ - 2*R^2*dt A*dt N*N⁻¹^2
  - 4*N*R*dx (dx R)*A⁻¹ - 2*N*(dx R)^2*A⁻¹ - 2*R^2*dx (dx N)*A⁻¹ - 4*R*dx N*dx R*A⁻¹
  + 4*N*R*dx A*dx R*A⁻¹^2 + 2*R^2*dx A*dx N*A⁻¹^2

/-- t 一定の面の √h K = (ȦR² + 2ARṘ)/N -/
def hKt : S := (dt A * R^2 + 2*A*R*dt R) * N⁻¹
/-- x 一定の面の √−γ K = (N′R² + 2NRR′)/A -/
def hKx : S := (dx N * R^2 + 2*N*R*dx R) * A⁻¹
/-- 一階のラグランジアン -/
def L1 : S :=
  2*A*N - 2*A*(dt R)^2*N⁻¹ - 4*R*dt A*dt R*N⁻¹ + 2*N*(dx R)^2*A⁻¹ + 4*R*dx N*dx R*A⁻¹

theorem ghy_spherical (hN : N ≠ 0) (hA : A ≠ 0) (hc : ∀ f, dt (dx f) = dx (dt f)) :
    sqrtgR dt dx N A R = L1 dt dx N A R + dt (2 * hKt dt N A R) + dx (-(2 * hKx dx N A R)) := by
  have iN := CFT.Propagation.deriv_inv dt N hN
  have iA := CFT.Propagation.deriv_inv dx A hA
  have iN' := CFT.Propagation.deriv_inv dx N hN
  have iA' := CFT.Propagation.deriv_inv dt A hA
  simp only [sqrtgR, hKt, hKx, L1, map_add, map_sub, map_neg, map_mul, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, iN, iA, iN', iA', CFT.Propagation.deriv_ofNat dt 2,
    CFT.Propagation.deriv_ofNat dx 2, nsmul_eq_mul, Nat.cast_ofNat, hc]
  ring

end GHY

end CFT.S1C
