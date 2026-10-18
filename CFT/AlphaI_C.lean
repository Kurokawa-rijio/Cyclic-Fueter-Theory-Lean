/-
  α-I.2(Y2):巡回 Fueter 係数行列 C の階数と左右の核

  基本の右 Fueter 作用素 D_R = ∂₀ + i∂₁ + j∂₂ + k∂₃ の係数 e = (1, i, j, k) を巡回させた
    D_r = Σ_a e_{r+a} ∂_a(添字は 4 を法とする)
  の係数行列 C_{ra} = e_{r+a}(4×4、四元数成分)。係数は左から作用させる規約。
  γ(q) = (1, q, q², q³)。
  台帳の主張(rank_ℍ C = 3、ker_R C = γ(−k)ℍ、ker_L C = ℍγ(i))をこの C で証明する:
    * left_kernel :Σ_r x_r C_{ra} = 0(全 a)⇔ x = q·γ(i)
    * right_kernel:Σ_a C_{ra} y_a = 0(全 r)⇔ y = γ(−k)·q
    * rank_three  :列 0, 1, 2 は右一次独立で、列 3 = 列0·k + 列1 − 列2·k
                   (右 ℍ 加群としての列階数 3。右核の次元 1 と合わせて rank-nullity 4 = 3 + 1)
  注意:C の成分そのものは台帳の記述(巡回 Fueter、γ の左右の核)から再構成した。
  上の二つの核がちょうど台帳の主張と一致することが、この再構成の検算になっている。
-/
import CFT.Basic

open Quaternion

namespace CFT.FueterC

noncomputable section

/-- 四元数の単位 -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

/-- 右 Fueter 作用素の係数 e = (1, i, j, k) -/
def e : Fin 4 → ℍ[ℝ] := ![1, qi, qj, qk]

/-- 巡回係数行列 C_{ra} = e_{r+a} -/
def C (r a : Fin 4) : ℍ[ℝ] := e (r + a)

/-- γ(q) = (1, q, q², q³) -/
def gam (q : ℍ[ℝ]) : Fin 4 → ℍ[ℝ] := ![1, q, q * q, q * q * q]

theorem gam_i : (gam qi 0, gam qi 1, gam qi 2, gam qi 3) = (1, qi, -1, -qi) := by
  simp only [gam, Prod.mk.injEq]; refine ⟨by simp, by simp, ?_, ?_⟩ <;> ext <;> simp [qi]

theorem gam_mk : (gam (-qk) 0, gam (-qk) 1, gam (-qk) 2, gam (-qk) 3) = (1, -qk, -1, qk) := by
  simp only [gam, Prod.mk.injEq]; refine ⟨by simp, by simp, ?_, ?_⟩ <;> ext <;> simp [qk]

/-- C の成分表 -/
theorem C_table (r a : Fin 4) : C r a = e (r + a) := rfl

/-- 右核:C y = 0 ⇔ y = γ(−k) q -/
theorem right_kernel (y : Fin 4 → ℍ[ℝ]) :
    (∀ r, ∑ a, C r a * y a = 0) ↔ ∃ q : ℍ[ℝ], ∀ a, y a = gam (-qk) a * q := by
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [Fin.sum_univ_four, C, e] at h0 h1 h2 h3
    norm_num [Fin.isValue] at h0 h1 h2 h3
    refine ⟨y 0, fun a => ?_⟩
    have e0 := congrArg QuaternionAlgebra.re h0; have e1 := congrArg QuaternionAlgebra.imI h0
    have e2 := congrArg QuaternionAlgebra.imJ h0; have e3 := congrArg QuaternionAlgebra.imK h0
    have f0 := congrArg QuaternionAlgebra.re h1; have f1 := congrArg QuaternionAlgebra.imI h1
    have f2 := congrArg QuaternionAlgebra.imJ h1; have f3 := congrArg QuaternionAlgebra.imK h1
    have g0 := congrArg QuaternionAlgebra.re h2; have g1 := congrArg QuaternionAlgebra.imI h2
    have g2 := congrArg QuaternionAlgebra.imJ h2; have g3 := congrArg QuaternionAlgebra.imK h2
    have k0 := congrArg QuaternionAlgebra.re h3; have k1 := congrArg QuaternionAlgebra.imI h3
    have k2 := congrArg QuaternionAlgebra.imJ h3; have k3 := congrArg QuaternionAlgebra.imK h3
    simp [qi, qj, qk] at e0 e1 e2 e3 f0 f1 f2 f3 g0 g1 g2 g3 k0 k1 k2 k3
    fin_cases a <;> ext <;> simp [gam, qk, mul_assoc] <;> linarith
  · rintro ⟨q, hq⟩ r
    simp only [Fin.sum_univ_four, hq]
    fin_cases r <;> ext <;> simp [C, e, gam, qi, qj, qk, mul_assoc] <;> ring

/-- 左核:x C = 0 ⇔ x = q γ(i) -/
theorem left_kernel (x : Fin 4 → ℍ[ℝ]) :
    (∀ a, ∑ r, x r * C r a = 0) ↔ ∃ q : ℍ[ℝ], ∀ r, x r = q * gam qi r := by
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [Fin.sum_univ_four, C, e] at h0 h1 h2 h3
    norm_num [Fin.isValue] at h0 h1 h2 h3
    refine ⟨x 0, fun r => ?_⟩
    have e0 := congrArg QuaternionAlgebra.re h0; have e1 := congrArg QuaternionAlgebra.imI h0
    have e2 := congrArg QuaternionAlgebra.imJ h0; have e3 := congrArg QuaternionAlgebra.imK h0
    have f0 := congrArg QuaternionAlgebra.re h1; have f1 := congrArg QuaternionAlgebra.imI h1
    have f2 := congrArg QuaternionAlgebra.imJ h1; have f3 := congrArg QuaternionAlgebra.imK h1
    have g0 := congrArg QuaternionAlgebra.re h2; have g1 := congrArg QuaternionAlgebra.imI h2
    have g2 := congrArg QuaternionAlgebra.imJ h2; have g3 := congrArg QuaternionAlgebra.imK h2
    have k0 := congrArg QuaternionAlgebra.re h3; have k1 := congrArg QuaternionAlgebra.imI h3
    have k2 := congrArg QuaternionAlgebra.imJ h3; have k3 := congrArg QuaternionAlgebra.imK h3
    simp [qi, qj, qk] at e0 e1 e2 e3 f0 f1 f2 f3 g0 g1 g2 g3 k0 k1 k2 k3
    fin_cases r <;> ext <;> simp [gam, qi, mul_assoc] <;> linarith
  · rintro ⟨q, hq⟩ a
    simp only [Fin.sum_univ_four, hq]
    fin_cases a <;> ext <;> simp [C, e, gam, qi, qj, qk, mul_assoc] <;> ring

/-- 階数 3:列 0, 1, 2 は右一次独立、列 3 はその右一次結合 -/
theorem rank_three :
    (∀ y : Fin 3 → ℍ[ℝ], (∀ r, C r 0 * y 0 + C r 1 * y 1 + C r 2 * y 2 = 0) → y = 0) ∧
    (∀ r, C r 3 = C r 0 * qk + C r 1 - C r 2 * qk) := by
  constructor
  · intro y hy
    have h := (right_kernel ![y 0, y 1, y 2, 0]).mp (fun r => by
      simp only [Fin.sum_univ_four]; simpa using hy r)
    obtain ⟨q, hq⟩ := h
    have h3 := hq 3
    have hq0 : q = 0 := by
      have : gam (-qk) 3 * q = 0 := by rw [← h3]; rfl
      have hg : gam (-qk) 3 = qk := by ext <;> simp [gam, qk, mul_assoc]
      rw [hg] at this
      have hk : qk ≠ 0 := by intro h0; have := congrArg QuaternionAlgebra.imK h0; simp [qk] at this
      exact (mul_eq_zero.mp this).resolve_left hk
    funext a
    have := hq (Fin.castSucc a)
    fin_cases a <;> simpa [hq0] using this
  · intro r
    fin_cases r <;> ext <;> simp [C, e, qi, qj, qk]

/-- 行列は特異(非自明な右核を持つ) -/
theorem singular : ∃ y : Fin 4 → ℍ[ℝ], y ≠ 0 ∧ ∀ r, ∑ a, C r a * y a = 0 := by
  refine ⟨gam (-qk), ?_, (right_kernel _).mpr ⟨1, fun a => by rw [mul_one]⟩⟩
  intro h
  have := congrFun h 0
  simp [gam] at this

/-! ### 実数化:ℝ 線形写像としての階数 12 -/

/-- y ↦ C y(ℝ 線形) -/
def Cmap : (Fin 4 → ℍ[ℝ]) →ₗ[ℝ] (Fin 4 → ℍ[ℝ]) where
  toFun y := fun r => ∑ a, C r a * y a
  map_add' y z := by funext r; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext r
    simp only [RingHom.id_apply, Pi.smul_apply]
    calc ∑ x : Fin 4, C r x * c • y x = ∑ x : Fin 4, c • (C r x * y x) :=
          Finset.sum_congr rfl fun a _ => Algebra.mul_smul_comm c (C r a) (y a)
      _ = c • ∑ a : Fin 4, C r a * y a :=
          (Finset.smul_sum (s := Finset.univ) (r := c) (f := fun a => C r a * y a)).symm

/-- q ↦ γ(−k) q(ℝ 線形、単射) -/
def kerParam : ℍ[ℝ] →ₗ[ℝ] (Fin 4 → ℍ[ℝ]) where
  toFun q := fun a => gam (-qk) a * q
  map_add' p q := by funext a; simp [mul_add]
  map_smul' c q := by funext a; simp

theorem kerParam_injective : Function.Injective kerParam := by
  intro p q h
  have := congrFun h 0
  simpa [kerParam, gam] using this

theorem ker_eq_range : LinearMap.ker Cmap = LinearMap.range kerParam := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := (right_kernel y).mp (fun r => congrFun h r)
    exact ⟨q, funext fun a => (hq a).symm⟩
  · rintro ⟨q, rfl⟩
    funext r
    exact (right_kernel (kerParam q)).mpr ⟨q, fun a => rfl⟩ r

/-- 実数化した写像の階数は 12(= 16 − 4)、四元数の右加群としての階数 3 に対応 -/
theorem real_rank_twelve : Module.finrank ℝ (LinearMap.range Cmap) = 12 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker Cmap
  have h2 : Module.finrank ℝ (LinearMap.ker Cmap) = 4 := by
    rw [ker_eq_range, LinearMap.finrank_range_of_inj kerParam_injective, Quaternion.finrank_eq_four]
  have h3 : Module.finrank ℝ (Fin 4 → ℍ[ℝ]) = 16 := by
    rw [Module.finrank_pi_fintype, Quaternion.finrank_eq_four]; simp
  omega

end

end CFT.FueterC
