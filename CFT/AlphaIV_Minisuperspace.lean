/-
  α-IV.12 / α-VI.4 の土台:首の縮約作用を 4 次元の作用から導く

  計量 −N²dt² + a²dx² + b²dΩ²(N, a, b は t だけの関数)と、首の YM 場 W = 0(単極子)について
  * F̂² = F^a_μν F^{aμν} = 2/b⁴(`fsq_W0`)
  * √−g (R − ℓ² F̂²) = sin θ · { 2 [−(a ḃ² + 2b ȧ ḃ)/N + N a (1 − ℓ²/b²)]
                                 + d/dt(2 ȧ b²/N) + d/dt(4 a b ḃ/N) }(`reduced_density`)
  全微分を落とし、角度と x で積分した係数を c とおくと、縮約 Lagrangian
    L = c [−(a ḃ² + 2b ȧ ḃ)/N + N a (1 − ℓ²/b²)]
  が得られる(作用の規格化 (1/16πG)∫√−g(R − ℓ²F̂²) は、Einstein 方程式 G = 2ℓ² T̂ と同じ)。
  * Legendre 変換 p_a = ∂L/∂ȧ、p_b = ∂L/∂ḃ で H = p_a ȧ + p_b ḃ − L = N · Hfun(`legendre`)
  * ∂L/∂N = −Hfun(拘束 Hfun = 0 は N の運動方程式)(`L_N`)
  ここで Hfun は AlphaCompleteA の首の Hamiltonian。これで Hamiltonian が作用から導かれる。
-/
import CFT.AlphaS4_Curv
import CFT.AlphaCompleteA

namespace CFT.Mini

open CFT.S4 CFT.Propagation

section Density

variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- F̂² = Σ F^a_αβ g^{αγ} g^{βδ} F^a_γδ(Tym の第 2 項と同じ和) -/
def Fsq (gi : Fin 4 → Fin 4 → S) (F : Fin 3 → Fin 4 → Fin 4 → S) : S :=
  ∑ a, ∑ al, ∑ be, ∑ ga, ∑ de, F a al be * gi al ga * gi be de * F a ga de

set_option maxHeartbeats 4000000 in
/-- 首の単極子 W = 0 では F̂² = 2/R⁴ -/
theorem fsq_W0 (N A R s : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Fsq (giD N A R s) (FT d 0 s) = 2 * R⁻¹ ^ 4 := by
  simp [Fsq, FT, giD, Fin.sum_univ_three, Fin.sum_univ_four]
  field_simp
  ring

set_option maxHeartbeats 4000000 in
/-- 【α-IV.12】縮約作用の密度:√−g (R − ℓ² F̂²) = 2 sin θ · L/c + 全微分 -/
theorem reduced_density (N a b s c l : S) (H : SphD d N a b s c)
    (hN1 : d 1 N = 0) (ha1 : d 1 a = 0) (hb1 : d 1 b = 0) :
    N * a * b ^ 2 * s * (Rsc d (giD N a b s) (GD d N a b s c) - l ^ 2 * Fsq (giD N a b s) (FT d 0 s))
      = s * (2 * (-(a * d 0 b ^ 2 + 2 * b * d 0 a * d 0 b) * N⁻¹ + N * a * (1 - l ^ 2 * b⁻¹ ^ 2))
          + 2 * d 0 (d 0 a * b ^ 2 * N⁻¹) + 4 * d 0 (a * b * d 0 b * N⁻¹)) := by
  have hN := H.hN
  have ha := H.hA
  have hb := H.hR
  have hs := H.hs
  rw [rscD d N a b s c H, fsq_W0 d N a b s hN ha hb hs]
  have iN := deriv_inv (d 0) N hN
  simp only [hN1, ha1, hb1, map_zero, zero_mul, mul_zero, zero_add, add_zero, sub_zero,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, iN]
  field_simp
  ring

end Density

/-! ### 縮約 Lagrangian と Legendre 変換(実数) -/

section Legendre

open CFT.AlphaCompleteA

/-- 縮約 Lagrangian L(a, b, ȧ, ḃ, N) = c[−(a ḃ² + 2b ȧ ḃ)/N + N a (1 − ℓ²/b²)] -/
noncomputable def Lfun (a b ad bd N c l : ℝ) : ℝ :=
  c * (-(a * bd ^ 2 + 2 * b * ad * bd) / N + N * a * (1 - l ^ 2 / b ^ 2))

/-- p_a = ∂L/∂ȧ = −2c b ḃ/N -/
theorem L_ad (a b ad bd N c l : ℝ) :
    HasDerivAt (fun x => Lfun a b x bd N c l) (-2 * c * b * bd / N) ad := by
  have hf : (fun x => Lfun a b x bd N c l) =
      fun x => (-2 * c * b * bd / N) * x + c * (-(a * bd ^ 2) / N + N * a * (1 - l ^ 2 / b ^ 2)) := by
    funext x; simp only [Lfun]; ring
  rw [hf]
  simpa using ((hasDerivAt_id ad).const_mul (-2 * c * b * bd / N)).add_const
    (c * (-(a * bd ^ 2) / N + N * a * (1 - l ^ 2 / b ^ 2)))

/-- p_b = ∂L/∂ḃ = −2c(a ḃ + b ȧ)/N -/
theorem L_bd (a b ad bd N c l : ℝ) :
    HasDerivAt (fun y => Lfun a b ad y N c l) (-2 * c * (a * bd + b * ad) / N) bd := by
  have hf : (fun y => Lfun a b ad y N c l) =
      fun y => (-(c * a) / N) * y ^ 2 + (-(2 * c * b * ad) / N) * y
        + c * (N * a * (1 - l ^ 2 / b ^ 2)) := by
    funext y; simp only [Lfun]; ring
  rw [hf]
  have h := ((((hasDerivAt_pow 2 bd).const_mul (-(c * a) / N)).add
    ((hasDerivAt_id bd).const_mul (-(2 * c * b * ad) / N))).add_const (c * (N * a * (1 - l ^ 2 / b ^ 2))))
  convert h using 1
  simp only [id, Nat.cast_ofNat]
  ring

/-- 【α-IV.12】Legendre 変換:H = p_a ȧ + p_b ḃ − L = N · Hfun(a, b, p_a, p_b) -/
theorem legendre (a b ad bd N c l : ℝ) (hN : N ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (-2 * c * b * bd / N) * ad + (-2 * c * (a * bd + b * ad) / N) * bd - Lfun a b ad bd N c l
      = N * Hfun a b (-2 * c * b * bd / N) (-2 * c * (a * bd + b * ad) / N) c l := by
  simp only [Lfun, Hfun]
  field_simp
  ring

/-- 【α-IV.12】∂L/∂N = −Hfun:N の運動方程式が Hamiltonian 拘束 Hfun = 0 -/
theorem L_N (a b ad bd N c l : ℝ) (hN : N ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    HasDerivAt (fun n => Lfun a b ad bd n c l)
      (-Hfun a b (-2 * c * b * bd / N) (-2 * c * (a * bd + b * ad) / N) c l) N := by
  have hf : (fun n => Lfun a b ad bd n c l) =
      fun n => (-(c * (a * bd ^ 2 + 2 * b * ad * bd))) * n⁻¹ + (c * a * (1 - l ^ 2 / b ^ 2)) * n := by
    funext n; simp only [Lfun]; ring
  rw [hf]
  have h := ((hasDerivAt_inv hN).const_mul (-(c * (a * bd ^ 2 + 2 * b * ad * bd)))).add
    ((hasDerivAt_id N).const_mul (c * a * (1 - l ^ 2 / b ^ 2)))
  convert h using 1
  simp only [Hfun, id]
  field_simp
  ring

end Legendre

end CFT.Mini
