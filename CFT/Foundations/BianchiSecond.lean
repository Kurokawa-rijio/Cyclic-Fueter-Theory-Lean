/-
  命題集 `LEAN_GAP_TREES.md` 13-2(第 2 Bianchi 恒等式)の代数の核(2026-11-18)

  ゲージ理論の形で示してから、Riemann テンソルの成分の形に落とす。
  * 一般の(非可換)環の上で、接続 A_c、その微分 ∂_e A_c、2 階微分 ∂_e∂_f A_c(e, f について対称)から
    曲率 F_cd = ∂_c A_d − ∂_d A_c + [A_c, A_d] と共変微分 D_e F_cd = ∂_e F_cd + [A_e, F_cd] を作ると、
      D_e F_cd + D_c F_de + D_d F_ec = 0(`gauge_bianchi`、Yang–Mills の Bianchi 恒等式 DF = 0)。
    証明は 2 階微分の対称性で 2 階の項を消したあと、非可換多項式の恒等式(`noncomm_ring`)。
  * 成分では (A_c)^a_b = Γ^a_cb とおくと F_cd の (a,b) 成分が Riemann テンソル R^a_bcd になる(`curv_apply`)。
    Riemann の共変微分 ∇_e R^a_bcd は D_e F_cd の成分から、下の添字 c, d に掛かる 2 項を引いたもの
    (`nablaR`、展開形 `nablaR_explicit`)。
  * `bianchi_second`:Γ が下の 2 添字で対称(ねじれがない)なら
      ∇_e R^a_bcd + ∇_c R^a_bde + ∇_d R^a_bec = 0。
    ゲージ版に、余分な 6 項が Γ の対称性と R の反対称性で 2 つずつ打ち消すことを足す。
  計量は使わない(任意のねじれのない接続で成り立つ)。縮約した形 ∇^a G_ab = 0 は計量との両立が要るので次の段。
-/
import Mathlib
import CFT.Foundations.CurvatureJetAlgebra

open Finset BigOperators

namespace CFT.Classical

/-! ### ゲージ理論の形(非可換環) -/

section Gauge

variable {ι R : Type*} [Ring R]

/-- 曲率 F_cd = ∂_c A_d − ∂_d A_c + A_c A_d − A_d A_c -/
def curv (A : ι → R) (dA : ι → ι → R) (c d : ι) : R :=
  dA c d - dA d c + A c * A d - A d * A c

/-- 曲率の微分 ∂_e F_cd -/
def dcurv (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R) (e c d : ι) : R :=
  ddA e c d - ddA e d c + (dA e c * A d + A c * dA e d) - (dA e d * A c + A d * dA e c)

/-- 共変微分 D_e F_cd = ∂_e F_cd + A_e F_cd − F_cd A_e -/
def Dcurv (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R) (e c d : ι) : R :=
  dcurv A dA ddA e c d + (A e * curv A dA c d - curv A dA c d * A e)

/-- Yang–Mills の Bianchi 恒等式 D_e F_cd + D_c F_de + D_d F_ec = 0 -/
theorem gauge_bianchi (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R)
    (hsym : ∀ i j k, ddA i j k = ddA j i k) (e c d : ι) :
    Dcurv A dA ddA e c d + Dcurv A dA ddA c d e + Dcurv A dA ddA d e c = 0 := by
  unfold Dcurv dcurv curv
  rw [hsym e c d, hsym c d e, hsym d e c]
  noncomm_ring

end Gauge

/-! ### 成分の形 -/

section Components

variable {n : ℕ}

/-- 接続行列 (A_c)^a_b = Γ^a_cb -/
def Amat (Γ : Fin n → Fin n → Fin n → ℝ) (c : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => Γ a c b

/-- (∂_e A_c)^a_b = ∂_e Γ^a_cb(dΓ e a c b) -/
def dAmat (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (e c : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => dΓ e a c b

/-- (∂_e∂_f A_c)^a_b = ∂_e∂_f Γ^a_cb(ddΓ e f a c b) -/
def ddAmat (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (e f c : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => ddΓ e f a c b

/-- 曲率行列の成分は Riemann テンソル -/
theorem curv_apply (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (c d a b : Fin n) : curv (Amat Γ) (dAmat dΓ) c d a b = riemann Γ dΓ a b c d := by
  simp only [curv, Amat, dAmat, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.of_apply, riemann, Finset.sum_sub_distrib]
  ring

/-- Riemann テンソルの共変微分 ∇_e R^a_bcd -/
noncomputable def nablaR (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (e a b c d : Fin n) : ℝ :=
  Dcurv (Amat Γ) (dAmat dΓ) (ddAmat ddΓ) e c d a b
    - ∑ f, Γ f e c * riemann Γ dΓ a b f d - ∑ f, Γ f e d * riemann Γ dΓ a b c f

/-- 展開形:∇_e R^a_bcd = ∂_e R^a_bcd + Γ^a_ef R^f_bcd − Γ^f_eb R^a_fcd − Γ^f_ec R^a_bfd − Γ^f_ed R^a_bcf -/
theorem nablaR_explicit (Γ : Fin n → Fin n → Fin n → ℝ)
    (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (e a b c d : Fin n) :
    nablaR Γ dΓ ddΓ e a b c d
      = (ddΓ e c a d b - ddΓ e d a c b
          + ∑ g, (dΓ e a c g * Γ g d b + Γ a c g * dΓ e g d b)
          - ∑ g, (dΓ e a d g * Γ g c b + Γ a d g * dΓ e g c b))
        + ∑ f, Γ a e f * riemann Γ dΓ f b c d - ∑ f, riemann Γ dΓ a f c d * Γ f e b
        - ∑ f, Γ f e c * riemann Γ dΓ a b f d - ∑ f, Γ f e d * riemann Γ dΓ a b c f := by
  simp only [nablaR, Dcurv, dcurv, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    curv_apply]
  simp only [Amat, dAmat, ddAmat, Matrix.of_apply, Finset.sum_add_distrib]
  ring

/-- 第 2 Bianchi 恒等式:ねじれのない接続について ∇_e R^a_bcd + ∇_c R^a_bde + ∇_d R^a_bec = 0 -/
theorem bianchi_second (Γ : Fin n → Fin n → Fin n → ℝ)
    (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdd : ∀ e f a b c, ddΓ e f a b c = ddΓ f e a b c)
    (e a b c d : Fin n) :
    nablaR Γ dΓ ddΓ e a b c d + nablaR Γ dΓ ddΓ c a b d e + nablaR Γ dΓ ddΓ d a b e c = 0 := by
  have hsym : ∀ i j k, ddAmat ddΓ i j k = ddAmat ddΓ j i k := fun i j k => by
    ext x y
    simp only [ddAmat, Matrix.of_apply]
    exact hdd i j x k y
  have hg := congrFun (congrFun
    (gauge_bianchi (Amat Γ) (dAmat dΓ) (ddAmat ddΓ) hsym e c d) a) b
  simp only [Matrix.add_apply, Matrix.zero_apply] at hg
  have hx : ∑ f, (Γ f e c * riemann Γ dΓ a b f d + Γ f e d * riemann Γ dΓ a b c f
      + Γ f c d * riemann Γ dΓ a b f e + Γ f c e * riemann Γ dΓ a b d f
      + Γ f d e * riemann Γ dΓ a b f c + Γ f d c * riemann Γ dΓ a b e f) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    rw [hΓ f c e, hΓ f d e, hΓ f d c, riemann_antisymm Γ dΓ a b d f,
      riemann_antisymm Γ dΓ a b f c, riemann_antisymm Γ dΓ a b e f]
    ring
  simp only [Finset.sum_add_distrib] at hx
  unfold nablaR
  linarith

end Components

end CFT.Classical
