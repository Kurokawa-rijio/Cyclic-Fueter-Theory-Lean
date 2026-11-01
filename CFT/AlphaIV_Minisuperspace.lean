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
/-- 縮約作用の密度の恒等式の最後の段(逆元を変数 iN、ia、ib にした多項式の恒等式) -/
theorem density_aux (N a b s l Nd ad bd add bdd iN ia ib : S)
    (hiN : N * iN = 1) (hia : a * ia = 1) (hib : b * ib = 1) :
    N * a * b ^ 8 * s * iN ^ 2 * ib ^ 7 * bdd * 4 - N ^ 3 * a * b ^ 5 * s * iN ^ 2 * ib ^ 7 * l ^ 2 * 2 + (N ^ 3 * a * b ^ 7 * s * iN ^ 2 * ib ^ 7 * 2 - N ^ 7 * a ^ 2 * b ^ 11 * s * Nd * bd * iN ^ 9 * ia * ib ^ 10 * 4) + N ^ 8 * a * b ^ 12 * s * iN ^ 9 * ia * ib ^ 10 * add * 2 + (N ^ 8 * a ^ 2 * b ^ 10 * s * bd ^ 2 * iN ^ 9 * ia * ib ^ 10 * 2 - N ^ 12 * a ^ 3 * b ^ 13 * s * ad * Nd * iN ^ 14 * ia ^ 3 * ib ^ 11 * 2) + N ^ 13 * a ^ 3 * b ^ 12 * s * ad * bd * iN ^ 14 * ia ^ 3 * ib ^ 11 * 4 = -(N ^ 5 * a * b ^ 3 * s * Nd * bd * iN ^ 7 * ib ^ 2 * 4) - N ^ 5 * b ^ 4 * s * ad * Nd * iN ^ 7 * ib ^ 2 * 2 + N ^ 6 * a * b ^ 2 * s * bd ^ 2 * iN ^ 7 * ib ^ 2 * 2 + N ^ 6 * a * b ^ 3 * s * iN ^ 7 * ib ^ 2 * bdd * 4 + N ^ 6 * b ^ 3 * s * ad * bd * iN ^ 7 * ib ^ 2 * 4 + N ^ 6 * b ^ 4 * s * iN ^ 7 * ib ^ 2 * add * 2 + (N ^ 8 * a * b ^ 2 * s * iN ^ 7 * ib ^ 2 * 2 - N ^ 8 * a * s * iN ^ 7 * ib ^ 2 * l ^ 2 * 2) := by
  linear_combination ((-2 : S) * add * b ^ 4 * iN * ib ^ 2 * s + (-4 : S) * ad * b ^ 3 * bd * iN * ib ^ 2 * s + (-2 : S) * a * b ^ 2 * bd ^ 2 * iN * ib ^ 2 * s + (-4 : S) * a * b ^ 3 * bdd * iN * ib ^ 2 * s + (4 : S) * a * b ^ 8 * bdd * iN * ib ^ 7 * s + (2 : S) * a * add * b ^ 12 * iN * ia * ib ^ 10 * s + (2 : S) * a ^ 2 * b ^ 10 * bd ^ 2 * iN * ia * ib ^ 10 * s + (4 : S) * a ^ 3 * ad * b ^ 12 * bd * iN * ia ^ 3 * ib ^ 11 * s + (2 : S) * Nd * ad * b ^ 4 * iN ^ 2 * ib ^ 2 * s + (4 : S) * Nd * a * b ^ 3 * bd * iN ^ 2 * ib ^ 2 * s + (-4 : S) * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 2 * ia * ib ^ 10 * s + (-2 : S) * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 2 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N * add * b ^ 4 * iN ^ 2 * ib ^ 2 * s + (-4 : S) * N * ad * b ^ 3 * bd * iN ^ 2 * ib ^ 2 * s + (2 : S) * N * a * ib ^ 2 * l ^ 2 * s + (-2 : S) * N * a * b ^ 2 * ib ^ 2 * s + (-2 : S) * N * a * b ^ 2 * bd ^ 2 * iN ^ 2 * ib ^ 2 * s + (-4 : S) * N * a * b ^ 3 * bdd * iN ^ 2 * ib ^ 2 * s + (-2 : S) * N * a * b ^ 5 * ib ^ 7 * l ^ 2 * s + (2 : S) * N * a * b ^ 7 * ib ^ 7 * s + (2 : S) * N * a * add * b ^ 12 * iN ^ 2 * ia * ib ^ 10 * s + (2 : S) * N * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 2 * ia * ib ^ 10 * s + (4 : S) * N * a ^ 3 * ad * b ^ 12 * bd * iN ^ 2 * ia ^ 3 * ib ^ 11 * s + (2 : S) * N * Nd * ad * b ^ 4 * iN ^ 3 * ib ^ 2 * s + (4 : S) * N * Nd * a * b ^ 3 * bd * iN ^ 3 * ib ^ 2 * s + (-4 : S) * N * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 3 * ia * ib ^ 10 * s + (-2 : S) * N * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 3 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 2 * add * b ^ 4 * iN ^ 3 * ib ^ 2 * s + (-4 : S) * N ^ 2 * ad * b ^ 3 * bd * iN ^ 3 * ib ^ 2 * s + (2 : S) * N ^ 2 * a * iN * ib ^ 2 * l ^ 2 * s + (-2 : S) * N ^ 2 * a * b ^ 2 * iN * ib ^ 2 * s + (-2 : S) * N ^ 2 * a * b ^ 2 * bd ^ 2 * iN ^ 3 * ib ^ 2 * s + (-4 : S) * N ^ 2 * a * b ^ 3 * bdd * iN ^ 3 * ib ^ 2 * s + (-2 : S) * N ^ 2 * a * b ^ 5 * iN * ib ^ 7 * l ^ 2 * s + (2 : S) * N ^ 2 * a * b ^ 7 * iN * ib ^ 7 * s + (2 : S) * N ^ 2 * a * add * b ^ 12 * iN ^ 3 * ia * ib ^ 10 * s + (2 : S) * N ^ 2 * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 3 * ia * ib ^ 10 * s + (4 : S) * N ^ 2 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 3 * ia ^ 3 * ib ^ 11 * s + (2 : S) * N ^ 2 * Nd * ad * b ^ 4 * iN ^ 4 * ib ^ 2 * s + (4 : S) * N ^ 2 * Nd * a * b ^ 3 * bd * iN ^ 4 * ib ^ 2 * s + (-4 : S) * N ^ 2 * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 4 * ia * ib ^ 10 * s + (-2 : S) * N ^ 2 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 4 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 3 * add * b ^ 4 * iN ^ 4 * ib ^ 2 * s + (-4 : S) * N ^ 3 * ad * b ^ 3 * bd * iN ^ 4 * ib ^ 2 * s + (2 : S) * N ^ 3 * a * iN ^ 2 * ib ^ 2 * l ^ 2 * s + (-2 : S) * N ^ 3 * a * b ^ 2 * iN ^ 2 * ib ^ 2 * s + (-2 : S) * N ^ 3 * a * b ^ 2 * bd ^ 2 * iN ^ 4 * ib ^ 2 * s + (-4 : S) * N ^ 3 * a * b ^ 3 * bdd * iN ^ 4 * ib ^ 2 * s + (2 : S) * N ^ 3 * a * add * b ^ 12 * iN ^ 4 * ia * ib ^ 10 * s + (2 : S) * N ^ 3 * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 4 * ia * ib ^ 10 * s + (4 : S) * N ^ 3 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 4 * ia ^ 3 * ib ^ 11 * s + (2 : S) * N ^ 3 * Nd * ad * b ^ 4 * iN ^ 5 * ib ^ 2 * s + (4 : S) * N ^ 3 * Nd * a * b ^ 3 * bd * iN ^ 5 * ib ^ 2 * s + (-4 : S) * N ^ 3 * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 5 * ia * ib ^ 10 * s + (-2 : S) * N ^ 3 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 5 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 4 * add * b ^ 4 * iN ^ 5 * ib ^ 2 * s + (-4 : S) * N ^ 4 * ad * b ^ 3 * bd * iN ^ 5 * ib ^ 2 * s + (2 : S) * N ^ 4 * a * iN ^ 3 * ib ^ 2 * l ^ 2 * s + (-2 : S) * N ^ 4 * a * b ^ 2 * iN ^ 3 * ib ^ 2 * s + (-2 : S) * N ^ 4 * a * b ^ 2 * bd ^ 2 * iN ^ 5 * ib ^ 2 * s + (-4 : S) * N ^ 4 * a * b ^ 3 * bdd * iN ^ 5 * ib ^ 2 * s + (2 : S) * N ^ 4 * a * add * b ^ 12 * iN ^ 5 * ia * ib ^ 10 * s + (2 : S) * N ^ 4 * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 5 * ia * ib ^ 10 * s + (4 : S) * N ^ 4 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 5 * ia ^ 3 * ib ^ 11 * s + (2 : S) * N ^ 4 * Nd * ad * b ^ 4 * iN ^ 6 * ib ^ 2 * s + (4 : S) * N ^ 4 * Nd * a * b ^ 3 * bd * iN ^ 6 * ib ^ 2 * s + (-4 : S) * N ^ 4 * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 6 * ia * ib ^ 10 * s + (-2 : S) * N ^ 4 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 6 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 5 * add * b ^ 4 * iN ^ 6 * ib ^ 2 * s + (-4 : S) * N ^ 5 * ad * b ^ 3 * bd * iN ^ 6 * ib ^ 2 * s + (2 : S) * N ^ 5 * a * iN ^ 4 * ib ^ 2 * l ^ 2 * s + (-2 : S) * N ^ 5 * a * b ^ 2 * iN ^ 4 * ib ^ 2 * s + (-2 : S) * N ^ 5 * a * b ^ 2 * bd ^ 2 * iN ^ 6 * ib ^ 2 * s + (-4 : S) * N ^ 5 * a * b ^ 3 * bdd * iN ^ 6 * ib ^ 2 * s + (2 : S) * N ^ 5 * a * add * b ^ 12 * iN ^ 6 * ia * ib ^ 10 * s + (2 : S) * N ^ 5 * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 6 * ia * ib ^ 10 * s + (4 : S) * N ^ 5 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 6 * ia ^ 3 * ib ^ 11 * s + (-4 : S) * N ^ 5 * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 7 * ia * ib ^ 10 * s + (-2 : S) * N ^ 5 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 7 * ia ^ 3 * ib ^ 11 * s + (2 : S) * N ^ 6 * a * iN ^ 5 * ib ^ 2 * l ^ 2 * s + (-2 : S) * N ^ 6 * a * b ^ 2 * iN ^ 5 * ib ^ 2 * s + (2 : S) * N ^ 6 * a * add * b ^ 12 * iN ^ 7 * ia * ib ^ 10 * s + (2 : S) * N ^ 6 * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 7 * ia * ib ^ 10 * s + (4 : S) * N ^ 6 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 7 * ia ^ 3 * ib ^ 11 * s + (-4 : S) * N ^ 6 * Nd * a ^ 2 * b ^ 11 * bd * iN ^ 8 * ia * ib ^ 10 * s + (-2 : S) * N ^ 6 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 8 * ia ^ 3 * ib ^ 11 * s + (2 : S) * N ^ 7 * a * iN ^ 6 * ib ^ 2 * l ^ 2 * s + (-2 : S) * N ^ 7 * a * b ^ 2 * iN ^ 6 * ib ^ 2 * s + (2 : S) * N ^ 7 * a * add * b ^ 12 * iN ^ 8 * ia * ib ^ 10 * s + (2 : S) * N ^ 7 * a ^ 2 * b ^ 10 * bd ^ 2 * iN ^ 8 * ia * ib ^ 10 * s + (4 : S) * N ^ 7 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 8 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 7 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 9 * ia ^ 3 * ib ^ 11 * s + (4 : S) * N ^ 8 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 9 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 8 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 10 * ia ^ 3 * ib ^ 11 * s + (4 : S) * N ^ 9 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 10 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 9 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 11 * ia ^ 3 * ib ^ 11 * s + (4 : S) * N ^ 10 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 11 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 10 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 12 * ia ^ 3 * ib ^ 11 * s + (4 : S) * N ^ 11 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 12 * ia ^ 3 * ib ^ 11 * s + (-2 : S) * N ^ 11 * Nd * a ^ 3 * ad * b ^ 13 * iN ^ 13 * ia ^ 3 * ib ^ 11 * s + (4 : S) * N ^ 12 * a ^ 3 * ad * b ^ 12 * bd * iN ^ 13 * ia ^ 3 * ib ^ 11 * s) * hiN
    + ((2 : S) * add * b ^ 12 * iN * ib ^ 10 * s + (4 : S) * ad * b ^ 12 * bd * iN * ib ^ 11 * s + (2 : S) * a * b ^ 10 * bd ^ 2 * iN * ib ^ 10 * s + (4 : S) * a * ad * b ^ 12 * bd * iN * ia * ib ^ 11 * s + (4 : S) * a ^ 2 * ad * b ^ 12 * bd * iN * ia ^ 2 * ib ^ 11 * s + (-2 : S) * Nd * ad * b ^ 13 * iN ^ 2 * ib ^ 11 * s + (-4 : S) * Nd * a * b ^ 11 * bd * iN ^ 2 * ib ^ 10 * s + (-2 : S) * Nd * a * ad * b ^ 13 * iN ^ 2 * ia * ib ^ 11 * s + (-2 : S) * Nd * a ^ 2 * ad * b ^ 13 * iN ^ 2 * ia ^ 2 * ib ^ 11 * s) * hia
    + ((2 : S) * add * b ^ 4 * iN * ib ^ 2 * s + (2 : S) * add * b ^ 5 * iN * ib ^ 3 * s + (2 : S) * add * b ^ 6 * iN * ib ^ 4 * s + (2 : S) * add * b ^ 7 * iN * ib ^ 5 * s + (2 : S) * add * b ^ 8 * iN * ib ^ 6 * s + (2 : S) * add * b ^ 9 * iN * ib ^ 7 * s + (2 : S) * add * b ^ 10 * iN * ib ^ 8 * s + (2 : S) * add * b ^ 11 * iN * ib ^ 9 * s + (4 : S) * ad * b ^ 3 * bd * iN * ib ^ 2 * s + (4 : S) * ad * b ^ 4 * bd * iN * ib ^ 3 * s + (4 : S) * ad * b ^ 5 * bd * iN * ib ^ 4 * s + (4 : S) * ad * b ^ 6 * bd * iN * ib ^ 5 * s + (4 : S) * ad * b ^ 7 * bd * iN * ib ^ 6 * s + (4 : S) * ad * b ^ 8 * bd * iN * ib ^ 7 * s + (4 : S) * ad * b ^ 9 * bd * iN * ib ^ 8 * s + (4 : S) * ad * b ^ 10 * bd * iN * ib ^ 9 * s + (4 : S) * ad * b ^ 11 * bd * iN * ib ^ 10 * s + (2 : S) * a * b ^ 2 * bd ^ 2 * iN * ib ^ 2 * s + (4 : S) * a * b ^ 3 * bdd * iN * ib ^ 2 * s + (2 : S) * a * b ^ 3 * bd ^ 2 * iN * ib ^ 3 * s + (4 : S) * a * b ^ 4 * bdd * iN * ib ^ 3 * s + (2 : S) * a * b ^ 4 * bd ^ 2 * iN * ib ^ 4 * s + (4 : S) * a * b ^ 5 * bdd * iN * ib ^ 4 * s + (2 : S) * a * b ^ 5 * bd ^ 2 * iN * ib ^ 5 * s + (4 : S) * a * b ^ 6 * bdd * iN * ib ^ 5 * s + (2 : S) * a * b ^ 6 * bd ^ 2 * iN * ib ^ 6 * s + (4 : S) * a * b ^ 7 * bdd * iN * ib ^ 6 * s + (2 : S) * a * b ^ 7 * bd ^ 2 * iN * ib ^ 7 * s + (2 : S) * a * b ^ 8 * bd ^ 2 * iN * ib ^ 8 * s + (2 : S) * a * b ^ 9 * bd ^ 2 * iN * ib ^ 9 * s + (-2 : S) * Nd * ad * b ^ 4 * iN ^ 2 * ib ^ 2 * s + (-2 : S) * Nd * ad * b ^ 5 * iN ^ 2 * ib ^ 3 * s + (-2 : S) * Nd * ad * b ^ 6 * iN ^ 2 * ib ^ 4 * s + (-2 : S) * Nd * ad * b ^ 7 * iN ^ 2 * ib ^ 5 * s + (-2 : S) * Nd * ad * b ^ 8 * iN ^ 2 * ib ^ 6 * s + (-2 : S) * Nd * ad * b ^ 9 * iN ^ 2 * ib ^ 7 * s + (-2 : S) * Nd * ad * b ^ 10 * iN ^ 2 * ib ^ 8 * s + (-2 : S) * Nd * ad * b ^ 11 * iN ^ 2 * ib ^ 9 * s + (-2 : S) * Nd * ad * b ^ 12 * iN ^ 2 * ib ^ 10 * s + (-4 : S) * Nd * a * b ^ 3 * bd * iN ^ 2 * ib ^ 2 * s + (-4 : S) * Nd * a * b ^ 4 * bd * iN ^ 2 * ib ^ 3 * s + (-4 : S) * Nd * a * b ^ 5 * bd * iN ^ 2 * ib ^ 4 * s + (-4 : S) * Nd * a * b ^ 6 * bd * iN ^ 2 * ib ^ 5 * s + (-4 : S) * Nd * a * b ^ 7 * bd * iN ^ 2 * ib ^ 6 * s + (-4 : S) * Nd * a * b ^ 8 * bd * iN ^ 2 * ib ^ 7 * s + (-4 : S) * Nd * a * b ^ 9 * bd * iN ^ 2 * ib ^ 8 * s + (-4 : S) * Nd * a * b ^ 10 * bd * iN ^ 2 * ib ^ 9 * s + (-2 : S) * N * a * ib ^ 2 * l ^ 2 * s + (-2 : S) * N * a * b * ib ^ 3 * l ^ 2 * s + (2 : S) * N * a * b ^ 2 * ib ^ 2 * s + (-2 : S) * N * a * b ^ 2 * ib ^ 4 * l ^ 2 * s + (2 : S) * N * a * b ^ 3 * ib ^ 3 * s + (-2 : S) * N * a * b ^ 3 * ib ^ 5 * l ^ 2 * s + (2 : S) * N * a * b ^ 4 * ib ^ 4 * s + (-2 : S) * N * a * b ^ 4 * ib ^ 6 * l ^ 2 * s + (2 : S) * N * a * b ^ 5 * ib ^ 5 * s + (2 : S) * N * a * b ^ 6 * ib ^ 6 * s) * hib

/-- s⁴R⁸ s⁻⁴R⁻⁸ · 2 = 2 -/
theorem fsq_aux (s R iS iR : S) (his : s * iS = 1) (hiR : R * iR = 1) :
    s ^ 4 * R ^ 8 * iS ^ 4 * iR ^ 8 * 2 = 2 := by
  linear_combination ((2 : S) * R ^ 8 * iR ^ 8 + (2 : S) * R ^ 8 * iR ^ 8 * iS * s
      + (2 : S) * R ^ 8 * iR ^ 8 * iS ^ 2 * s ^ 2 + (2 : S) * R ^ 8 * iR ^ 8 * iS ^ 3 * s ^ 3) * his
    + ((2 : S) + (2 : S) * R * iR + (2 : S) * R ^ 2 * iR ^ 2 + (2 : S) * R ^ 3 * iR ^ 3
      + (2 : S) * R ^ 4 * iR ^ 4 + (2 : S) * R ^ 5 * iR ^ 5 + (2 : S) * R ^ 6 * iR ^ 6
      + (2 : S) * R ^ 7 * iR ^ 7) * hiR

set_option maxHeartbeats 4000000 in
/-- 首の単極子 W = 0 では F̂² = 2/R⁴ -/
theorem fsq_W0 (N A R s : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Fsq (giD N A R s) (FT d 0 s) = 2 * R⁻¹ ^ 4 := by
  simp [Fsq, FT, giD, Fin.sum_univ_three, Fin.sum_univ_four]
  field_simp
  exact fsq_aux s R s⁻¹ R⁻¹ (mul_inv_cancel₀ hs) (mul_inv_cancel₀ hR)

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
  exact density_aux N a b s l (d 0 N) (d 0 a) (d 0 b) (d 0 (d 0 a)) (d 0 (d 0 b)) N⁻¹ a⁻¹ b⁻¹
    (mul_inv_cancel₀ hN) (mul_inv_cancel₀ ha) (mul_inv_cancel₀ hb)

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
