import CFT.Spherical.WedgeEYMSystem
import CFT.Spherical.WedgeEnergyBalance
import Mathlib.Tactic

/-
  命題集 `LEAN_GAP_TREES.md` 4-5（エネルギー恒等式）の残り：フラックス恒等式そのものの
  解析的 `deriv` 版への移行。
  `WedgeEnergyIdentity.lean` の恒等式は導分代数の流儀で、矩形上の収支
  （`WedgeEnergyBalance.lean`）はフラックス恒等式を各点の仮定として受け取っていた。
  このモジュールでは、実際の関数 W, Om, r : ℝ → ℝ → ℝ と `CFT.Wedge.Du` / `Dv`
  （スライスの `deriv`）で、v 方向・u 方向のエネルギー恒等式とフラックス形
    ∂_u F^u + ∂_v F^v = -V (∂_u A + ∂_v A)
  を証明する。W 方程式は `Duv W = rhsW` の形で仮定し、v 方向の恒等式では
  混合偏微分の可換性 Dv (Du W) = Duv W を仮定する（導分代数版の hc に対応。
  u 方向は可換性を使わない）。さらに解析版フラックスから矩形上の収支
  （`wedge_energy_balance`）への組み込みも行う（dFu・dFv の連続性は仮定）。
  これで 4-5 は、微分恒等式・矩形上の積分収支・解析版の移行まですべて閉じる。
-/

open CFT.Wedge
open CFT.WedgeBalance

namespace CFT.WedgeEnergyAnalytic

noncomputable section

/-- ポテンシャル V(W) = W²/2 - W⁴/4 の u 偏微分：V_u = (W - W³) W_u。 -/
theorem wedgePotFun_deriv_u {W : ℝ → ℝ → ℝ} {u v : ℝ}
    (hW : Differentiable ℝ (fun u' => W u' v)) :
    deriv (fun u' => wedgePotFun W u' v) u
      = (W u v - (W u v) ^ 3) * (Du W u v) := by
  have h : HasDerivAt (fun u' => wedgePotFun W u' v)
      ((2 : ℝ) * (W u v) ^ (2 - 1) * (Du W u v) / 2
        - (4 : ℝ) * (W u v) ^ (4 - 1) * (Du W u v) / 4) u := by
    have h1 := (hW u).hasDerivAt
    have h2 := (h1.pow 2).div_const 2
    have h3 := (h1.pow 4).div_const 4
    exact h2.sub h3
  rw [h.deriv]
  ring

/-- ポテンシャル V(W) の v 偏微分：V_v = (W - W³) W_v。 -/
theorem wedgePotFun_deriv_v {W : ℝ → ℝ → ℝ} {u v : ℝ}
    (hW : Differentiable ℝ (fun v' => W u v')) :
    deriv (fun v' => wedgePotFun W u v') v
      = (W u v - (W u v) ^ 3) * (Dv W u v) := by
  have h : HasDerivAt (fun v' => wedgePotFun W u v')
      ((2 : ℝ) * (W u v) ^ (2 - 1) * (Dv W u v) / 2
        - (4 : ℝ) * (W u v) ^ (4 - 1) * (Dv W u v) / 4) v := by
    have h1 := (hW v).hasDerivAt
    have h2 := (h1.pow 2).div_const 2
    have h3 := (h1.pow 4).div_const 4
    exact h2.sub h3
  rw [h.deriv]
  ring

/-- 係数 A = Ω/(2r²) の u スライスの微分可能性（r ≠ 0 のもと）。 -/
theorem wedgeAFun_diff_u {Om r : ℝ → ℝ → ℝ} {v : ℝ}
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hr0 : ∀ u, r u v ≠ 0) :
    Differentiable ℝ (fun u' => wedgeAFun Om r u' v) := by
  show Differentiable ℝ (fun u' => Om u' v / (2 * (r u' v) ^ 2))
  apply Differentiable.div hOm ((hr.pow 2).const_mul 2)
  intro x
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (hr0 x))

/-- 係数 A = Ω/(2r²) の v スライスの微分可能性（r ≠ 0 のもと）。 -/
theorem wedgeAFun_diff_v {Om r : ℝ → ℝ → ℝ} {u : ℝ}
    (hOm : Differentiable ℝ (fun v' => Om u v'))
    (hr : Differentiable ℝ (fun v' => r u v'))
    (hr0 : ∀ v, r u v ≠ 0) :
    Differentiable ℝ (fun v' => wedgeAFun Om r u v') := by
  show Differentiable ℝ (fun v' => Om u v' / (2 * (r u v') ^ 2))
  apply Differentiable.div hOm ((hr.pow 2).const_mul 2)
  intro x
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (hr0 x))

/-- ポテンシャル V(W) の u スライスの微分可能性。 -/
theorem wedgePotFun_diff_u {W : ℝ → ℝ → ℝ} {v : ℝ}
    (hW : Differentiable ℝ (fun u' => W u' v)) :
    Differentiable ℝ (fun u' => wedgePotFun W u' v) := by
  show Differentiable ℝ (fun u' => (W u' v) ^ 2 / 2 - (W u' v) ^ 4 / 4)
  exact ((hW.pow 2).div_const 2).sub ((hW.pow 4).div_const 4)

/-- ポテンシャル V(W) の v スライスの微分可能性。 -/
theorem wedgePotFun_diff_v {W : ℝ → ℝ → ℝ} {u : ℝ}
    (hW : Differentiable ℝ (fun v' => W u v')) :
    Differentiable ℝ (fun v' => wedgePotFun W u v') := by
  show Differentiable ℝ (fun v' => (W u v') ^ 2 / 2 - (W u v') ^ 4 / 4)
  exact ((hW.pow 2).div_const 2).sub ((hW.pow 4).div_const 4)

/-- フラックスの u 成分 F^u = W_v²/2 - A V の解析版。 -/
noncomputable def wedgeFuFun (W Om r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Dv W u v) ^ 2 / 2 - wedgeAFun Om r u v * wedgePotFun W u v

/-- フラックスの v 成分 F^v = W_u²/2 - A V の解析版。 -/
noncomputable def wedgeFvFun (W Om r : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  (Du W u v) ^ 2 / 2 - wedgeAFun Om r u v * wedgePotFun W u v

/-- 4-5（v 方向のエネルギー恒等式の解析版）：
    ∂_v (W_u²/2) - ∂_u (A V) = -V ∂_u A。
    混合偏微分の可換性 Dv (Du W) = Duv W を仮定する（導分代数版の hc に対応）。 -/
theorem wedge_energy_v_analytic {W Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hDuW : Differentiable ℝ (fun v' => Du W u v'))
    (hW : Differentiable ℝ (fun u' => W u' v))
    (hOm : Differentiable ℝ (fun u' => Om u' v))
    (hr : Differentiable ℝ (fun u' => r u' v))
    (hr0 : ∀ u, r u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hcomm : Dv (Du W) u v = Duv W u v) :
    Dv (fun u v => (Du W u v) ^ 2 / 2) u v
      - Du (fun u v => wedgeAFun Om r u v * wedgePotFun W u v) u v
      = - wedgePotFun W u v * Du (wedgeAFun Om r) u v := by
  have hA : Differentiable ℝ (fun u' => wedgeAFun Om r u' v) :=
    wedgeAFun_diff_u hOm hr hr0
  have hV : Differentiable ℝ (fun u' => wedgePotFun W u' v) :=
    wedgePotFun_diff_u hW
  have h1 : deriv (fun v' => (Du W u v') ^ 2 / 2) v
      = (Du W u v) * (Dv (Du W) u v) := by
    have h : HasDerivAt (fun v' => (Du W u v') ^ 2 / 2)
        ((2 : ℝ) * (Du W u v) ^ (2 - 1) * (Dv (Du W) u v) / 2) v :=
      ((hDuW v).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : deriv (fun u' => wedgeAFun Om r u' v * wedgePotFun W u' v) u
      = deriv (fun u' => wedgeAFun Om r u' v) u * wedgePotFun W u v
        + wedgeAFun Om r u v * ((W u v - (W u v) ^ 3) * (Du W u v)) := by
    rw [deriv_mul (hA u) (hV u), wedgePotFun_deriv_u hW]
  have h3 : Dv (Du W) u v = wedgeAFun Om r u v * (W u v - (W u v) ^ 3) := by
    rw [hcomm, hWuv]
    show (1 / 2) * Om u v * W u v * (1 - (W u v) ^ 2) / (r u v) ^ 2
      = (Om u v / (2 * (r u v) ^ 2)) * (W u v - (W u v) ^ 3)
    field_simp
    ring
  show deriv (fun v' => (Du W u v') ^ 2 / 2) v
      - deriv (fun u' => wedgeAFun Om r u' v * wedgePotFun W u' v) u
      = - wedgePotFun W u v * deriv (fun u' => wedgeAFun Om r u' v) u
  rw [h1, h2, h3]
  ring

/-- 4-5（u 方向のエネルギー恒等式の解析版）：
    ∂_u (W_v²/2) - ∂_v (A V) = -V ∂_v A。
    こちらは可換性を仮定しない（W 方程式を Duv の形で直接使う）。 -/
theorem wedge_energy_u_analytic {W Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hDvW : Differentiable ℝ (fun u' => Dv W u' v))
    (hW : Differentiable ℝ (fun v' => W u v'))
    (hOm : Differentiable ℝ (fun v' => Om u v'))
    (hr : Differentiable ℝ (fun v' => r u v'))
    (hr0 : ∀ v, r u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v)) :
    Du (fun u v => (Dv W u v) ^ 2 / 2) u v
      - Dv (fun u v => wedgeAFun Om r u v * wedgePotFun W u v) u v
      = - wedgePotFun W u v * Dv (wedgeAFun Om r) u v := by
  have hA : Differentiable ℝ (fun v' => wedgeAFun Om r u v') :=
    wedgeAFun_diff_v hOm hr hr0
  have hV : Differentiable ℝ (fun v' => wedgePotFun W u v') :=
    wedgePotFun_diff_v hW
  have h1 : deriv (fun u' => (Dv W u' v) ^ 2 / 2) u
      = (Dv W u v) * (Du (Dv W) u v) := by
    have h : HasDerivAt (fun u' => (Dv W u' v) ^ 2 / 2)
        ((2 : ℝ) * (Dv W u v) ^ (2 - 1) * (Du (Dv W) u v) / 2) u :=
      ((hDvW u).hasDerivAt.pow 2).div_const 2
    rw [h.deriv]
    ring_nf
  have h2 : deriv (fun v' => wedgeAFun Om r u v' * wedgePotFun W u v') v
      = deriv (fun v' => wedgeAFun Om r u v') v * wedgePotFun W u v
        + wedgeAFun Om r u v * ((W u v - (W u v) ^ 3) * (Dv W u v)) := by
    rw [deriv_mul (hA v) (hV v), wedgePotFun_deriv_v hW]
  have h3 : Du (Dv W) u v = wedgeAFun Om r u v * (W u v - (W u v) ^ 3) := by
    have hWuv' : Du (Dv W) u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v) := hWuv
    rw [hWuv']
    show (1 / 2) * Om u v * W u v * (1 - (W u v) ^ 2) / (r u v) ^ 2
      = (Om u v / (2 * (r u v) ^ 2)) * (W u v - (W u v) ^ 3)
    field_simp
    ring
  show deriv (fun u' => (Dv W u' v) ^ 2 / 2) u
      - deriv (fun v' => wedgeAFun Om r u v' * wedgePotFun W u v') v
      = - wedgePotFun W u v * deriv (fun v' => wedgeAFun Om r u v') v
  rw [h1, h2, h3]
  ring

/-- 4-5（フラックス恒等式の解析版）：
    ∂_u F^u + ∂_v F^v = -V (∂_u A + ∂_v A)。 -/
theorem wedge_energy_flux_analytic {W Om r : ℝ → ℝ → ℝ} {u v : ℝ}
    (hDuW : Differentiable ℝ (fun v' => Du W u v'))
    (hDvW : Differentiable ℝ (fun u' => Dv W u' v))
    (hWu : Differentiable ℝ (fun u' => W u' v))
    (hWv : Differentiable ℝ (fun v' => W u v'))
    (hOmu : Differentiable ℝ (fun u' => Om u' v))
    (hOmv : Differentiable ℝ (fun v' => Om u v'))
    (hru : Differentiable ℝ (fun u' => r u' v))
    (hrv : Differentiable ℝ (fun v' => r u v'))
    (hr0 : ∀ u v, r u v ≠ 0)
    (hWuv : Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hcomm : Dv (Du W) u v = Duv W u v) :
    Du (wedgeFuFun W Om r) u v + Dv (wedgeFvFun W Om r) u v
      = - wedgePotFun W u v
        * (Du (wedgeAFun Om r) u v + Dv (wedgeAFun Om r) u v) := by
  have hAu : Differentiable ℝ (fun u' => wedgeAFun Om r u' v) :=
    wedgeAFun_diff_u hOmu hru (fun x => hr0 x v)
  have hAv : Differentiable ℝ (fun v' => wedgeAFun Om r u v') :=
    wedgeAFun_diff_v hOmv hrv (fun x => hr0 u x)
  have hVu : Differentiable ℝ (fun u' => wedgePotFun W u' v) :=
    wedgePotFun_diff_u hWu
  have hVv : Differentiable ℝ (fun v' => wedgePotFun W u v') :=
    wedgePotFun_diff_v hWv
  have hFu : Du (wedgeFuFun W Om r) u v
      = Du (fun u v => (Dv W u v) ^ 2 / 2) u v
        - Du (fun u v => wedgeAFun Om r u v * wedgePotFun W u v) u v := by
    show deriv (fun u' => (Dv W u' v) ^ 2 / 2
        - wedgeAFun Om r u' v * wedgePotFun W u' v) u
      = deriv (fun u' => (Dv W u' v) ^ 2 / 2) u
        - deriv (fun u' => wedgeAFun Om r u' v * wedgePotFun W u' v) u
    rw [deriv_sub ((((hDvW.pow 2).div_const 2)) u) ((hAu.mul hVu) u)]
  have hFv : Dv (wedgeFvFun W Om r) u v
      = Dv (fun u v => (Du W u v) ^ 2 / 2) u v
        - Dv (fun u v => wedgeAFun Om r u v * wedgePotFun W u v) u v := by
    show deriv (fun v' => (Du W u v') ^ 2 / 2
        - wedgeAFun Om r u v' * wedgePotFun W u v') v
      = deriv (fun v' => (Du W u v') ^ 2 / 2) v
        - deriv (fun v' => wedgeAFun Om r u v' * wedgePotFun W u v') v
    rw [deriv_sub ((((hDuW.pow 2).div_const 2)) v) ((hAv.mul hVv) v)]
  rw [hFu, hFv]
  have hu := wedge_energy_u_analytic hDvW hWv hOmv hrv (fun x => hr0 u x) hWuv
  have hv := wedge_energy_v_analytic hDuW hWu hOmu hru (fun x => hr0 x v) hWuv hcomm
  linear_combination hu + hv

/-- 4-5（解析版フラックスからの矩形上のエネルギー収支）：
    フラックス恒等式の解析版と矩形上の発散定理を組み合わせ、境界フラックス =
    源 -V (∂_u A + ∂_v A) の二重積分を得る。dFu・dFv の連続性は仮定する。 -/
theorem wedge_energy_balance_analytic {W Om r : ℝ → ℝ → ℝ} {u0 u1 v0 v1 : ℝ}
    (hu : u0 ≤ u1) (hv : v0 ≤ v1)
    (hDuW : ∀ u, Differentiable ℝ (fun v' => Du W u v'))
    (hDvW : ∀ v, Differentiable ℝ (fun u' => Dv W u' v))
    (hWu : ∀ v, Differentiable ℝ (fun u' => W u' v))
    (hWv : ∀ u, Differentiable ℝ (fun v' => W u v'))
    (hOmu : ∀ v, Differentiable ℝ (fun u' => Om u' v))
    (hOmv : ∀ u, Differentiable ℝ (fun v' => Om u v'))
    (hru : ∀ v, Differentiable ℝ (fun u' => r u' v))
    (hrv : ∀ u, Differentiable ℝ (fun v' => r u v'))
    (hr0 : ∀ u v, r u v ≠ 0)
    (hWuv : ∀ u v, Duv W u v = CFT.Wedge.rhsW (Om u v) (W u v) (r u v))
    (hcomm : ∀ u v, Dv (Du W) u v = Duv W u v)
    (hFu_c : Continuous (Function.uncurry fun u v => Du (wedgeFuFun W Om r) u v))
    (hFv_c : Continuous (Function.uncurry fun u v => Dv (wedgeFvFun W Om r) u v)) :
    (∫ v in v0..v1, (wedgeFuFun W Om r u1 v - wedgeFuFun W Om r u0 v))
      + (∫ u in u0..u1, (wedgeFvFun W Om r u v1 - wedgeFvFun W Om r u v0))
      = ∫ u in u0..u1, ∫ v in v0..v1,
          -(wedgePotFun W u v)
            * (Du (wedgeAFun Om r) u v + Dv (wedgeAFun Om r) u v) := by
  have hFu_diff : ∀ v, Differentiable ℝ (fun u' => wedgeFuFun W Om r u' v) := by
    intro v
    show Differentiable ℝ (fun u' => (Dv W u' v) ^ 2 / 2
      - wedgeAFun Om r u' v * wedgePotFun W u' v)
    exact (((hDvW v).pow 2).div_const 2).sub
      ((wedgeAFun_diff_u (hOmu v) (hru v) (fun x => hr0 x v)).mul
        (wedgePotFun_diff_u (hWu v)))
  have hFv_diff : ∀ u, Differentiable ℝ (fun v' => wedgeFvFun W Om r u v') := by
    intro u
    show Differentiable ℝ (fun v' => (Du W u v') ^ 2 / 2
      - wedgeAFun Om r u v' * wedgePotFun W u v')
    exact (((hDuW u).pow 2).div_const 2).sub
      ((wedgeAFun_diff_v (hOmv u) (hrv u) (fun x => hr0 u x)).mul
        (wedgePotFun_diff_v (hWv u)))
  exact CFT.WedgeBalance.wedge_energy_balance hu hv
    (fun v u => (hFu_diff v u).hasDerivAt)
    (fun u v => (hFv_diff u v).hasDerivAt)
    hFu_c hFv_c
    (fun u v => wedge_energy_flux_analytic (hDuW u) (hDvW v) (hWu v) (hWv u)
      (hOmu v) (hOmv u) (hru v) (hrv u) hr0 (hWuv u v) (hcomm u v))

end

end CFT.WedgeEnergyAnalytic
