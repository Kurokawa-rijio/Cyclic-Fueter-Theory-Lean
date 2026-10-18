/-
  α-VIII.2(Z39, Z40):標準埋め込みで Green–Schwarz の Bianchi 恒等式の右辺が消えること(代数的な部分)

  R を関数の環、∂_μ を導分、接続を行列値 A_μ(成分ごとに微分)として
    F_{μν}(A) = ∂_μ A_ν − ∂_ν A_μ + A_μ A_ν − A_ν A_μ。
  標準埋め込み ι(X) = X ⊕ 0(スピン接続 Ω の値を、より大きいゲージ代数のブロックに置く)について:
    * curvature_embed:F(ι Ω) = ι(F(Ω))(曲率は埋め込みと可換)
    * trace_embed:tr(ι X · ι Y) = tr(X Y)(この ι はトレースの規格化を保つ)
    * pontryagin_match:tr(F_{μν}(ιΩ) F_{ρσ}(ιΩ)) = tr(R_{μν} R_{ρσ})、したがって
      dH ∝ Tr F∧F − tr R∧R の各成分が 0(gs_rhs_vanishes)
  注意:これは Bianchi 恒等式の右辺の相殺だけで、全場の方程式や SUSY 条件が満たされることではない。
  また実際のヘテロティック弦では Tr(E₈ または SO(32))と tr(SO(9,1))の規格化の比が規約で入る。
    * z40_alpha_term_vanishes(Z40 の障害):切り詰めた有効作用の α′ 項 −(α′/4)(Tr F² − tr R²)
      は A = ι(Ω) の上で恒等的に 0。U21′ に必要な Yang–Mills の源はこの切り詰め・この埋め込みでは得られない
      (台帳の条件つきの障害。非標準埋め込み、H 場・ディラトンを含む縮約は別の経路)。
-/
import CFT.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace CFT.Embedding

variable {R : Type*} [CommRing R] [Algebra ℚ R] (d : Fin 4 → Derivation ℚ R R)
set_option linter.unusedSectionVars false

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

/-- 成分ごとの微分 -/
def dM (μ : Fin 4) {p : Type*} (X : Matrix p p R) : Matrix p p R := X.map (d μ)

/-- 曲率 -/
def curv {p : Type*} [Fintype p] (A : Fin 4 → Matrix p p R) (μ ν : Fin 4) : Matrix p p R :=
  dM d μ (A ν) - dM d ν (A μ) + (A μ * A ν - A ν * A μ)

/-- 標準埋め込み ι(X) = X ⊕ 0 -/
def iota (X : Matrix k k R) : Matrix (k ⊕ m) (k ⊕ m) R := fromBlocks X 0 0 0

theorem iota_mul (X Y : Matrix k k R) : iota (m := m) X * iota Y = iota (X * Y) := by
  simp [iota, fromBlocks_multiply]

theorem iota_sub (X Y : Matrix k k R) : iota (m := m) X - iota Y = iota (X - Y) := by
  ext (i | i) (j | j) <;> simp [iota]

theorem iota_add (X Y : Matrix k k R) : iota (m := m) X + iota Y = iota (X + Y) := by
  simp [iota, fromBlocks_add]

theorem dM_iota (μ : Fin 4) (X : Matrix k k R) : dM d μ (iota (m := m) X) = iota (dM d μ X) := by
  ext (i | i) (j | j) <;> simp [dM, iota]

/-- 曲率は埋め込みと可換 -/
theorem curvature_embed (Ω : Fin 4 → Matrix k k R) (μ ν : Fin 4) :
    curv d (fun a => iota (m := m) (Ω a)) μ ν = iota (curv d Ω μ ν) := by
  simp only [curv, dM_iota, iota_mul, iota_sub, iota_add]

/-- トレースの規格化を保つ -/
theorem trace_embed (X Y : Matrix k k R) : (iota (m := m) X * iota Y).trace = (X * Y).trace := by
  rw [iota_mul]; simp [iota, Matrix.trace, Fintype.sum_sum_type]

/-- Pontryagin 密度の成分が一致 -/
theorem pontryagin_match (Ω : Fin 4 → Matrix k k R) (μ ν ρ σ : Fin 4) :
    (curv d (fun a => iota (m := m) (Ω a)) μ ν * curv d (fun a => iota (m := m) (Ω a)) ρ σ).trace
      = (curv d Ω μ ν * curv d Ω ρ σ).trace := by
  rw [curvature_embed, curvature_embed, trace_embed]

/-- 標準埋め込み A = ι(Ω) では Bianchi 恒等式の右辺 Tr F F − tr R R の各成分が 0 -/
theorem gs_rhs_vanishes (Ω : Fin 4 → Matrix k k R) (μ ν ρ σ : Fin 4) :
    (curv d (fun a => iota (m := m) (Ω a)) μ ν * curv d (fun a => iota (m := m) (Ω a)) ρ σ).trace
      - (curv d Ω μ ν * curv d Ω ρ σ).trace = 0 := by
  rw [pontryagin_match, sub_self]

/-- 計量で縮約した曲率の二乗 g^{μρ}g^{νσ} tr(F_{μν}F_{ρσ}) -/
def sqDensity {p : Type*} [Fintype p] (gi : Fin 4 → Fin 4 → R) (A : Fin 4 → Matrix p p R) : R :=
  ∑ μ, ∑ ν, ∑ ρ, ∑ σ, gi μ ρ * gi ν σ * (curv d A μ ν * curv d A ρ σ).trace

/-- Z40:切り詰めた有効作用の α′ 項 −(α′/4)(Tr F² − tr R²) は、標準埋め込み A = ι(Ω) の上で
  恒等的に 0(cα = −α′/4、Ω に依らない)。したがってこの切り詰めでは、U21′ に必要な Yang–Mills の項が残らない -/
theorem z40_alpha_term_vanishes (gi : Fin 4 → Fin 4 → R) (cα : R) (Ω : Fin 4 → Matrix k k R) :
    cα * (sqDensity d gi (fun a => iota (m := m) (Ω a)) - sqDensity d gi Ω) = 0 := by
  have : sqDensity d gi (fun a => iota (m := m) (Ω a)) = sqDensity d gi Ω := by
    unfold sqDensity
    simp only [pontryagin_match]
  rw [this, sub_self, mul_zero]

end CFT.Embedding
