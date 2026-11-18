/-
  古典物理の土台 第 0 段:座標成分による曲率の代数(2026-11-18)

  n 次元の座標成分で、計量の微分の値(jet)から Christoffel 記号と Riemann テンソルを組み立てる。
  微分は「値」として与える:dg c a b = ∂_c g_ab、ddg e c a b = ∂_e ∂_c g_ab、dginv c a b = ∂_c g^ab。
  実際の関数から作るときの橋渡し(Schwarz の定理など)は次の段で行う。

  * `riemann`:R^a_bcd = ∂_c Γ^a_db − ∂_d Γ^a_cb + Σ_e (Γ^a_ce Γ^e_db − Γ^a_de Γ^e_cb)。
    Γ と ∂Γ を与えれば定義できる一般の形。
  * `riemann_antisymm`:R^a_bcd = −R^a_bdc。
  * `bianchi_first`:Γ が下の 2 つの添字で対称、∂Γ も同じ添字で対称なら、
    R^a_bcd + R^a_cdb + R^a_dbc = 0(第 1 Bianchi 恒等式)。
  * `christoffel1_symm`:第 1 種の Christoffel 記号 Γ_abc = ½(∂_b g_ac + ∂_c g_ab − ∂_a g_bc) は b, c について対称。
  * `metric_compat`:∂_c g_ab = Γ_abc + Γ_bac(計量との両立、∇g = 0 の成分の形)。
  * `christoffel2_symm`、`dchristoffel2_symm`:Γ^a_bc = g^ad Γ_dbc とその微分は b, c について対称。
  * `bianchi_first_metric`:計量から作った Riemann テンソルは第 1 Bianchi 恒等式をみたす。
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset BigOperators

namespace CFT.Classical

variable {n : ℕ}

section General

variable {R : Type*} [CommRing R]

/-- Γ(a, b, c) = Γ^a_bc、dΓ(c, a, b, d) = ∂_c Γ^a_bd から作る Riemann テンソル R^a_bcd -/
def riemann (Γ : Fin n → Fin n → Fin n → R) (dΓ : Fin n → Fin n → Fin n → Fin n → R)
    (a b c d : Fin n) : R :=
  dΓ c a d b - dΓ d a c b + ∑ e, (Γ a c e * Γ e d b - Γ a d e * Γ e c b)

theorem riemann_antisymm (Γ : Fin n → Fin n → Fin n → R)
    (dΓ : Fin n → Fin n → Fin n → Fin n → R) (a b c d : Fin n) :
    riemann Γ dΓ a b c d = -riemann Γ dΓ a b d c := by
  simp only [riemann, Finset.sum_sub_distrib]
  ring

theorem bianchi_first (Γ : Fin n → Fin n → Fin n → R)
    (dΓ : Fin n → Fin n → Fin n → Fin n → R)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (hdΓ : ∀ c a b d, dΓ c a b d = dΓ c a d b)
    (a b c d : Fin n) :
    riemann Γ dΓ a b c d + riemann Γ dΓ a c d b + riemann Γ dΓ a d b c = 0 := by
  have s : ∀ x y z w : Fin n,
      ∑ e, Γ x y e * Γ e z w = ∑ e, Γ x y e * Γ e w z :=
    fun x y z w => Finset.sum_congr rfl (fun e _ => by rw [hΓ e z w])
  simp only [riemann, Finset.sum_sub_distrib]
  rw [hdΓ d a b c, hdΓ b a c d, hdΓ c a b d, s a d c b, s a b d c, s a c b d]
  ring

end General

section Metric

/-- 計量の 2 階までの jet。dg c a b = ∂_c g_ab、ddg e c a b = ∂_e ∂_c g_ab、
ginv a b = g^ab、dginv c a b = ∂_c g^ab -/
structure MetricJet (n : ℕ) where
  ginv : Fin n → Fin n → ℝ
  dginv : Fin n → Fin n → Fin n → ℝ
  dg : Fin n → Fin n → Fin n → ℝ
  ddg : Fin n → Fin n → Fin n → Fin n → ℝ
  dg_symm : ∀ c a b, dg c a b = dg c b a
  ddg_symm : ∀ e c a b, ddg e c a b = ddg e c b a

namespace MetricJet

variable (J : MetricJet n)

/-- 第 1 種の Christoffel 記号 Γ_abc = ½(∂_b g_ac + ∂_c g_ab − ∂_a g_bc) -/
noncomputable def chr1 (a b c : Fin n) : ℝ := (J.dg b a c + J.dg c a b - J.dg a b c) / 2

/-- その微分 ∂_e Γ_abc -/
noncomputable def dchr1 (e a b c : Fin n) : ℝ := (J.ddg e b a c + J.ddg e c a b - J.ddg e a b c) / 2

/-- 第 2 種の Christoffel 記号 Γ^a_bc = g^ad Γ_dbc -/
noncomputable def chr2 (a b c : Fin n) : ℝ := ∑ d, J.ginv a d * J.chr1 d b c

/-- その微分 ∂_e Γ^a_bc = (∂_e g^ad) Γ_dbc + g^ad ∂_e Γ_dbc -/
noncomputable def dchr2 (e a b c : Fin n) : ℝ :=
  ∑ d, (J.dginv e a d * J.chr1 d b c + J.ginv a d * J.dchr1 e d b c)

theorem chr1_symm (a b c : Fin n) : J.chr1 a b c = J.chr1 a c b := by
  unfold chr1
  rw [J.dg_symm a b c]
  ring

theorem metric_compat (a b c : Fin n) : J.dg c a b = J.chr1 a b c + J.chr1 b a c := by
  unfold chr1
  rw [J.dg_symm b a c, J.dg_symm a b c]
  ring

theorem dchr1_symm (e a b c : Fin n) : J.dchr1 e a b c = J.dchr1 e a c b := by
  unfold dchr1
  rw [J.ddg_symm e a b c]
  ring

theorem chr2_symm (a b c : Fin n) : J.chr2 a b c = J.chr2 a c b := by
  unfold chr2
  exact Finset.sum_congr rfl (fun d _ => by rw [J.chr1_symm d b c])

theorem dchr2_symm (e a b c : Fin n) : J.dchr2 e a b c = J.dchr2 e a c b := by
  unfold dchr2
  exact Finset.sum_congr rfl (fun d _ => by rw [J.chr1_symm d b c, J.dchr1_symm e d b c])

/-- 計量から作った Riemann テンソル R^a_bcd -/
noncomputable def riem (a b c d : Fin n) : ℝ := riemann J.chr2 J.dchr2 a b c d

theorem bianchi_first_metric (a b c d : Fin n) :
    J.riem a b c d + J.riem a c d b + J.riem a d b c = 0 :=
  bianchi_first J.chr2 J.dchr2 J.chr2_symm J.dchr2_symm a b c d

theorem riem_antisymm (a b c d : Fin n) : J.riem a b c d = -J.riem a b d c :=
  riemann_antisymm J.chr2 J.dchr2 a b c d

end MetricJet

end Metric

end CFT.Classical
