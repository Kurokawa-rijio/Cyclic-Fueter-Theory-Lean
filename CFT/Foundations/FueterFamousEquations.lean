/-
  有名方程式を Fueter 作用素で書き直す橋渡し(2026-11-18)

  `FueterOperatorSquares`(α-I.1)の作用素 Vec = i∂₁ + j∂₂ + k∂₃(空間の Fueter 作用素)、
  Box = ∂₀² − Σ∂ᵢ²、双四元数の D = ∂₀ + I·Vec(D̄D = □)を使い、今日示した有名方程式の仮定や結論が
  この幾何学の言葉そのものであることを示す。
  * `vec_vector`:純虚の場 u = u₁i + u₂j + u₃k に対し Vec u = −div u + curl u(四元数の積から)。
    系 `fueter_regular_iff`:Vec u = 0 ⇔ div u = 0 かつ curl u = 0。
  * `vec_vec`:Vec(Vec f) = −(∂₁² + ∂₂² + ∂₃²) f(空間の Laplacian の因数分解)。
  * 流体:`bernoulli_fueter`:Fueter 正則な流れ(Vec u = 0、つまり非圧縮かつ渦なし)では Bernoulli の定理が成り立つ。
    `ns_viscous_fueter`:Navier–Stokes の粘性項 μΔu は −μ Vec(Vec u) の虚部。
  * 静電場:`coulomb_fueter`:Coulomb ポテンシャル φ = q/r について、電場 ∇φ = Vec φ は Fueter 正則(Vec(Vec φ) = 0)。
  * 電磁場:`maxwell_biquaternion`:F = E + I B(純虚の双四元数)について
      D F = (div B − I div E) + (∂₀E − curl B) + I(∂₀B + curl E)。
    系 `maxwell_single_equation`:Maxwell 方程式(源 ρ, j)⇒ D F = −(Iρ + j)(1 本の双四元数の式)。
    `em_square`:F² = −(|E|² − |B|²) − 2I(E·B)(電磁場の 2 つの不変量は F² のスカラー部)。
    `em_square_invariant`:F² がスカラーなら、可逆な q による変換 F ↦ qFq⁻¹ で F² は不変
    (Lorentz 変換は双四元数の共役で書けるので、`SpecialRelativityLaws.em_invariant_*` はこの特別な場合)。
  * 特殊相対論:`mass_shell_biquaternion`:P = p₀ + I(p₁i + p₂j + p₃k) について P P̄ = p₀² − |p|²
    (Minkowski のノルムは双四元数のノルム。質量殻 E² = |p|² + m² は P P̄ = m²)。
  * 重力:`box_bridge`:線形化重力の □(η = diag(−1,1,1,1))は −Box のスカラー部。
    系 `lorenz_gauge_fueter`:Lorenz ゲージで G_μν = ½ (Box h̄_μν) のスカラー部(Box = D̄D)。
  * ゲージ場:`quaternion_gauge_bianchi`:四元数に値をとる接続(SU(2) ⊂ ℍ)でも Bianchi 恒等式 DF = 0
    (`BianchiSecond.gauge_bianchi` の ℍ[S] への当てはめ)。
-/
import CFT.Foundations.FueterOperatorSquares
import CFT.Foundations.ContinuumFieldLaws
import CFT.Foundations.LinearizedGravity
import CFT.Foundations.BianchiSecond

open Quaternion CFT.Operators

namespace CFT.FueterBridge

set_option maxHeartbeats 2000000

section Ring

variable {R : Type*} [CommRing R] (d : Fin 4 → Derivation ℤ R R)

/-- 純虚の場 u₁i + u₂j + u₃k -/
def vecQ (u : Fin 4 → R) : ℍ[R] := ⟨0, u 1, u 2, u 3⟩

/-- Vec u = −div u + curl u -/
theorem vec_vector (u : Fin 4 → R) :
    Vec d (vecQ u) = ⟨-(d 1 (u 1) + d 2 (u 2) + d 3 (u 3)), d 2 (u 3) - d 3 (u 2),
      d 3 (u 1) - d 1 (u 3), d 1 (u 2) - d 2 (u 1)⟩ := by
  ext <;> simp [Vec, vecQ, dq, e] <;> ring

/-- Fueter 正則 ⇔ 発散も回転も 0 -/
theorem fueter_regular_iff (u : Fin 4 → R) :
    Vec d (vecQ u) = 0 ↔ (d 1 (u 1) + d 2 (u 2) + d 3 (u 3) = 0 ∧ d 2 (u 3) = d 3 (u 2)
      ∧ d 3 (u 1) = d 1 (u 3) ∧ d 1 (u 2) = d 2 (u 1)) := by
  rw [vec_vector]
  constructor
  · intro h
    have h0 := congrArg Quaternion.re h
    have h1 := congrArg Quaternion.imI h
    have h2 := congrArg Quaternion.imJ h
    have h3 := congrArg Quaternion.imK h
    simp only [Quaternion.zero_re, Quaternion.zero_imI, Quaternion.zero_imJ,
      Quaternion.zero_imK] at h0 h1 h2 h3
    exact ⟨neg_eq_zero.mp h0, sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    ext <;> simp [h0, h1, h2, h3]

/-- Vec(Vec f) = −(∂₁² + ∂₂² + ∂₃²) f -/
theorem vec_vec (hc : ∀ a b x, d a (d b x) = d b (d a x)) (f : ℍ[R]) :
    Vec d (Vec d f) = -(dq (d 1) (dq (d 1) f) + dq (d 2) (dq (d 2) f) + dq (d 3) (dq (d 3) f)) := by
  have c21 := hc 2 1
  have c31 := hc 3 1
  have c32 := hc 3 2
  ext <;> simp [Vec, dq, e, map_add, map_sub, map_neg, c21, c31, c32] <;> ring

/-- 電磁場 F = E + I B の Fueter 方程式 -/
theorem maxwell_biquaternion (I : R) (hI : I * I = -1) (hdI : ∀ a, d a I = 0) (E B : Fin 4 → R) :
    DB d I (vecQ (fun a => E a + I * B a))
      = ⟨(d 1 (B 1) + d 2 (B 2) + d 3 (B 3)) - I * (d 1 (E 1) + d 2 (E 2) + d 3 (E 3)),
          (d 0 (E 1) - (d 2 (B 3) - d 3 (B 2))) + I * (d 0 (B 1) + (d 2 (E 3) - d 3 (E 2))),
          (d 0 (E 2) - (d 3 (B 1) - d 1 (B 3))) + I * (d 0 (B 2) + (d 3 (E 1) - d 1 (E 3))),
          (d 0 (E 3) - (d 1 (B 2) - d 2 (B 1))) + I * (d 0 (B 3) + (d 1 (E 2) - d 2 (E 1)))⟩ := by
  have hd : ∀ a x, d a (I * x) = I * d a x := by
    intro a x; rw [Derivation.leibniz, hdI a]; simp [smul_eq_mul]
  ext
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (-(d 1 (B 1) + d 2 (B 2) + d 3 (B 3))) * hI
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (d 2 (B 3) - d 3 (B 2)) * hI
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (d 3 (B 1) - d 1 (B 3)) * hI
  · simp [DB, Vec, vecQ, dq, e, map_add, hd]
    linear_combination (d 1 (B 2) - d 2 (B 1)) * hI

/-- Maxwell 方程式 ⇒ 1 本の双四元数の式 D F = −(Iρ + j) -/
theorem maxwell_single_equation (I : R) (hI : I * I = -1) (hdI : ∀ a, d a I = 0)
    (E B j : Fin 4 → R) (ρ : R)
    (gaussE : d 1 (E 1) + d 2 (E 2) + d 3 (E 3) = ρ) (gaussB : d 1 (B 1) + d 2 (B 2) + d 3 (B 3) = 0)
    (ampere1 : d 2 (B 3) - d 3 (B 2) - d 0 (E 1) = j 1)
    (ampere2 : d 3 (B 1) - d 1 (B 3) - d 0 (E 2) = j 2)
    (ampere3 : d 1 (B 2) - d 2 (B 1) - d 0 (E 3) = j 3)
    (faraday1 : d 2 (E 3) - d 3 (E 2) + d 0 (B 1) = 0)
    (faraday2 : d 3 (E 1) - d 1 (E 3) + d 0 (B 2) = 0)
    (faraday3 : d 1 (E 2) - d 2 (E 1) + d 0 (B 3) = 0) :
    DB d I (vecQ (fun a => E a + I * B a)) = ⟨-(I * ρ), -(j 1), -(j 2), -(j 3)⟩ := by
  rw [maxwell_biquaternion d I hI hdI E B]
  ext
  · simp only; rw [gaussB, gaussE]; ring
  · simp only; linear_combination -ampere1 + I * faraday1
  · simp only; linear_combination -ampere2 + I * faraday2
  · simp only; linear_combination -ampere3 + I * faraday3

/-- 電磁場の 2 つの不変量は F² のスカラー部 -/
theorem em_square (I : R) (hI : I * I = -1) (E B : Fin 4 → R) :
    vecQ (fun a => E a + I * B a) * vecQ (fun a => E a + I * B a)
      = ⟨-((E 1 ^ 2 + E 2 ^ 2 + E 3 ^ 2) - (B 1 ^ 2 + B 2 ^ 2 + B 3 ^ 2))
          - 2 * I * (E 1 * B 1 + E 2 * B 2 + E 3 * B 3), 0, 0, 0⟩ := by
  ext
  · simp [vecQ]
    linear_combination (-(B 1 ^ 2 + B 2 ^ 2 + B 3 ^ 2)) * hI
  · simp [vecQ]; ring
  · simp [vecQ]; ring
  · simp [vecQ]; ring

/-- F² がスカラーなら、可逆な q による変換 F ↦ qFq⁻¹ で F² は不変 -/
theorem em_square_invariant (F q q' : ℍ[R]) (s : R) (hFF : F * F = (s : ℍ[R]))
    (hq : q' * q = 1) (hq' : q * q' = 1) :
    (q * F * q') * (q * F * q') = (s : ℍ[R]) := by
  have e1 : (q * F * q') * (q * F * q') = q * (F * (q' * q) * F) * q' := by noncomm_ring
  rw [e1, hq, mul_one, hFF, ← Quaternion.coe_commutes s q, mul_assoc, hq', mul_one]

/-- 4 元運動量の双四元数 P = p₀ + I(p₁i + p₂j + p₃k) のノルム P P̄ = p₀² − |p|² -/
theorem mass_shell_biquaternion (I : R) (hI : I * I = -1) (p0 p1 p2 p3 : R) :
    (⟨p0, I * p1, I * p2, I * p3⟩ : ℍ[R]) * star (⟨p0, I * p1, I * p2, I * p3⟩ : ℍ[R])
      = ((p0 ^ 2 - (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) : R) : ℍ[R]) := by
  ext
  · simp
    linear_combination (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) * hI
  · simp; ring
  · simp; ring
  · simp; ring

end Ring


section Field

variable {S : Type*} [Field S] [CharZero S] (D : Fin 4 → Derivation ℤ S S)

/-- Fueter 正則な流れ(非圧縮かつ渦なし)では Bernoulli の定理が成り立つ -/
theorem bernoulli_fueter (ρ p Φ : S) (u : Fin 4 → S) (hreg : Vec D (vecQ u) = 0) (i : Fin 4)
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (hρ : ρ ≠ 0) (hρc : D i ρ = 0)
    (heuler : ρ * CFT.Continuum.ssum (fun j => u j * D j (u i)) = -(D i p) - ρ * D i Φ) :
    D i ((1/2 : S) * CFT.Continuum.ssum (fun j => u j * u j) + p * ρ⁻¹ + Φ) = 0 := by
  obtain ⟨_, h1, h2, h3⟩ := (fueter_regular_iff D u).mp hreg
  rcases hi with rfl | rfl | rfl
  · exact CFT.Continuum.bernoulli D ρ p Φ u 1 hρ hρc rfl h3 h2.symm heuler
  · exact CFT.Continuum.bernoulli D ρ p Φ u 2 hρ hρc h3.symm rfl h1 heuler
  · exact CFT.Continuum.bernoulli D ρ p Φ u 3 hρ hρc h2 h1.symm rfl heuler

/-- Navier–Stokes の粘性項:Vec(Vec u) = −Δu -/
theorem ns_viscous_fueter (hc : ∀ a b x, D a (D b x) = D b (D a x)) (u : Fin 4 → S) :
    Vec D (Vec D (vecQ u)) = -(⟨0, CFT.Continuum.ssum (fun j => D j (D j (u 1))),
      CFT.Continuum.ssum (fun j => D j (D j (u 2))),
      CFT.Continuum.ssum (fun j => D j (D j (u 3)))⟩ : ℍ[S]) := by
  rw [vec_vec D hc]
  ext <;> simp [dq, vecQ, CFT.Continuum.ssum]

/-- Coulomb の電場 ∇φ = Vec φ は Fueter 正則:Vec(Vec φ) = 0 -/
theorem coulomb_fueter (hc : ∀ a b x, D a (D b x) = D b (D a x)) (q ri : S) (x : Fin 4 → S)
    (hq : ∀ j, D j q = 0) (hx : ∀ j, D j (x j) = 1)
    (hri : ∀ j, D j ri = -(x j * (ri * ri * ri)))
    (hnorm : (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * ri ^ 2 = 1) :
    Vec D (Vec D (⟨q * ri, 0, 0, 0⟩ : ℍ[S])) = 0 := by
  have h := CFT.Continuum.coulomb_harmonic D q ri x hq hx hri hnorm
  unfold CFT.Continuum.ssum at h
  rw [vec_vec D hc]
  ext
  · simp only [dq, Quaternion.neg_re, Quaternion.add_re, Quaternion.zero_re]
    rw [h, neg_zero]
  all_goals simp [dq]

/-- 線形化重力の □(η = diag(−1,1,1,1))は −Box のスカラー部 -/
theorem box_bridge (s : S) :
    CFT.LinGrav.box D s = -(Box D (⟨s, 0, 0, 0⟩ : ℍ[S])).re := by
  simp (config := { decide := true }) [CFT.LinGrav.box, CFT.LinGrav.eta, Box, dq,
    Fin.sum_univ_four] <;> ring

/-- Lorenz ゲージで G_μν = ½ (Box h̄_μν) のスカラー部(Box = D̄D、`biquaternion_box`) -/
theorem lorenz_gauge_fueter (hc : ∀ μ ν x, D μ (D ν x) = D ν (D μ x))
    (h : Fin 4 → Fin 4 → S) (hL : ∀ ν, CFT.LinGrav.Lg D h ν = 0) (μ ν : Fin 4) :
    CFT.LinGrav.Gt D h μ ν
      = (1/2 : S) * (Box D (⟨CFT.LinGrav.hbar h μ ν, 0, 0, 0⟩ : ℍ[S])).re := by
  rw [CFT.LinGrav.G_lorenz_gauge D h hc hL μ ν, box_bridge]
  ring

end Field

/-- 四元数に値をとる接続(SU(2) ⊂ ℍ)の Bianchi 恒等式 DF = 0 -/
theorem quaternion_gauge_bianchi {ι S : Type*} [CommRing S] (A : ι → ℍ[S])
    (dA : ι → ι → ℍ[S]) (ddA : ι → ι → ι → ℍ[S]) (hsym : ∀ i j k, ddA i j k = ddA j i k)
    (e c d : ι) :
    CFT.Classical.Dcurv A dA ddA e c d + CFT.Classical.Dcurv A dA ddA c d e
      + CFT.Classical.Dcurv A dA ddA d e c = 0 :=
  CFT.Classical.gauge_bianchi A dA ddA hsym e c d

end CFT.FueterBridge
