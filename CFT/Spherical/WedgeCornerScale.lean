import Mathlib
import CFT.Spherical.WedgeEYMSystem
import CFT.Spherical.WedgeCornerConditions

/-!
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (a)：特性データと角条件による二重ヌルゲージの固定。
  特性データによる部分は `CFT.Spherical.WedgeGaugeFixing` で閉じている
  （帽子・首データが再パラメータ化を恒等写像に固定する）。ここでは角条件に
  よる部分、すなわち角のデータが残余自由度のうち相対スケールを固定する
  ことを証明する。

  二重ヌル座標の残余自由度のうち相対スケール (u, v) ↦ (a·u, v/a) は、
  計量係数 Ω を不変に保つ（ũ'ṽ' = a·(1/a) = 1）が、角の傾きを変える：
  Du W ↦ (1/a)·Du W、Dv W ↦ a·Dv W。角条件 W_u = 1/√2 は
  (1/a)·(1/√2) = 1/√2 を強制するので a = 1 になる（主結果
  `corner_slope_fixes_scale`）。2階の角条件 r_uu = −1 も
  (1/a)²·(−1) = −1 を強制するので、a > 0 の範囲で a = 1 になる
  （`corner_ruu_fixes_scale`）。

  一方、角の値（r = Ω = 1、W = 0）・Ω の角の値・r の角の傾き（0）は
  相対スケールで不変であり、スケールを固定しない。すなわち角条件のうち
  相対スケールを固定するのは W_u = 1/√2（と r_uu = −1）であり、
  他の角条件はスケール不変である。

  角条件 W_u = 1/√2 は特性データから従う（`CFT.WedgeCorner.data_W_u`）
  ので、まとめとして特性データを持つ場では角条件を満たす相対スケールは
  a = 1 のみである（`corner_data_fixes_relative_scale`）。これで
  12-8 (a) の角条件による部分が閉じた。

  残り：(b) のくさび EYM 系の形での分類（近地平線極限 AdS₂ × S² など。
  温度の側は 6-2・9-3・`RNExtremalDoubleZero` で証明済み）。
-/

open Real

namespace CFT.WedgeCornerScale

open CFT.Wedge

/-- 相対スケール (u, v) ↦ (a·u, v/a) による場の引き戻し。
    計量係数 Ω は ũ'ṽ' = a·(1/a) = 1 により不変なので、スカラーとしての引き戻しが
    正しい Ω の変換である。 -/
noncomputable def scaleFields (a : ℝ) (F : WedgeFields) : WedgeFields where
  r u v := F.r (u / a) (a * v)
  Om u v := F.Om (u / a) (a * v)
  W u v := F.W (u / a) (a * v)

/-- 一般補題：u 方向の微分は引き戻しで 1/a 倍される。 -/
theorem scale_du {a : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : DifferentiableAt ℝ (fun u => G u 0) 0) :
    Du (fun u v => G (u / a) (a * v)) 0 0 = (1 / a) * Du G 0 0 := by
  have h1 : HasDerivAt (fun u : ℝ => u / a) (1 / a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const a
  have h2 : HasDerivAt (fun x : ℝ => G x 0) (Du G 0 0) (0 / a) := by
    rw [zero_div]; exact hG.hasDerivAt
  have hcomp := h2.comp 0 h1
  have hder : deriv (fun u' : ℝ => G (u' / a) 0) 0 = Du G 0 0 * (1 / a) := hcomp.deriv
  show deriv (fun u' : ℝ => G (u' / a) (a * 0)) 0 = (1 / a) * Du G 0 0
  simp only [mul_zero]
  rw [hder]
  ring

/-- 一般補題：v 方向の微分は引き戻しで a 倍される。 -/
theorem scale_dv {a : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : DifferentiableAt ℝ (fun v => G 0 v) 0) :
    Dv (fun u v => G (u / a) (a * v)) 0 0 = a * Dv G 0 0 := by
  have h1 : HasDerivAt (fun v : ℝ => a * v) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  have h2 : HasDerivAt (fun y : ℝ => G 0 y) (Dv G 0 0) (a * 0) := by
    rw [mul_zero]; exact hG.hasDerivAt
  have hcomp := h2.comp 0 h1
  have hder : deriv (fun v' : ℝ => G 0 (a * v')) 0 = Dv G 0 0 * a := hcomp.deriv
  show deriv (fun v' : ℝ => G (0 / a) (a * v')) 0 = a * Dv G 0 0
  simp only [zero_div]
  rw [hder]
  ring

/-- W の u 方向の角の傾きは 1/a 倍される。 -/
theorem scaleFields_du_W {a : ℝ} {F : WedgeFields}
    (hW : DifferentiableAt ℝ (fun u => F.W u 0) 0) :
    Du (scaleFields a F).W 0 0 = (1 / a) * Du F.W 0 0 :=
  scale_du hW

/-- W の v 方向の角の傾きは a 倍される。 -/
theorem scaleFields_dv_W {a : ℝ} {F : WedgeFields}
    (hW : DifferentiableAt ℝ (fun v => F.W 0 v) 0) :
    Dv (scaleFields a F).W 0 0 = a * Dv F.W 0 0 :=
  scale_dv hW

/-- r の u 方向の角の傾きは 1/a 倍される。 -/
theorem scaleFields_du_r {a : ℝ} {F : WedgeFields}
    (hR : DifferentiableAt ℝ (fun u => F.r u 0) 0) :
    Du (scaleFields a F).r 0 0 = (1 / a) * Du F.r 0 0 :=
  scale_du hR

/-- r の v 方向の角の傾きは a 倍される。 -/
theorem scaleFields_dv_r {a : ℝ} {F : WedgeFields}
    (hR : DifferentiableAt ℝ (fun v => F.r 0 v) 0) :
    Dv (scaleFields a F).r 0 0 = a * Dv F.r 0 0 :=
  scale_dv hR

/-- 角の値は相対スケールで不変。 -/
theorem scaleFields_corner_values {a : ℝ} {F : WedgeFields} :
    (scaleFields a F).r 0 0 = F.r 0 0 ∧ (scaleFields a F).Om 0 0 = F.Om 0 0
      ∧ (scaleFields a F).W 0 0 = F.W 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [scaleFields]

/-- Ω の角の値は相対スケールで不変：Ω(0,0) = 1 はスケールを固定しない。 -/
theorem scaleFields_Om_corner {a : ℝ} {F : WedgeFields}
    (hOm : F.Om 0 0 = 1) : (scaleFields a F).Om 0 0 = 1 := by
  rw [(scaleFields_corner_values (a := a)).2.1, hOm]

/-- r の角の傾きは 0 のまま：r の傾きもスケールを固定しない。 -/
theorem scaleFields_corner_r_slopes {a : ℝ} {F : WedgeFields}
    (hR : DifferentiableAt ℝ (fun u => F.r u 0) 0)
    (hRv : DifferentiableAt ℝ (fun v => F.r 0 v) 0)
    (hu : Du F.r 0 0 = 0) (hv : Dv F.r 0 0 = 0) :
    Du (scaleFields a F).r 0 0 = 0 ∧ Dv (scaleFields a F).r 0 0 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [scaleFields_du_r hR, hu, mul_zero]
  · rw [scaleFields_dv_r hRv, hv, mul_zero]

/-- 主結果：角条件 W_u = 1/√2 は相対スケールを a = 1 に固定する。 -/
theorem corner_slope_fixes_scale {a : ℝ} {F : WedgeFields}
    (hW : DifferentiableAt ℝ (fun u => F.W u 0) 0)
    (hF : Du F.W 0 0 = 1 / Real.sqrt 2)
    (hG : Du (scaleFields a F).W 0 0 = 1 / Real.sqrt 2) :
    a = 1 := by
  rw [scaleFields_du_W hW, hF] at hG
  have hsqrt : (1 : ℝ) / Real.sqrt 2 ≠ 0 := by
    rw [one_div]
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hG' : (1 / a) * (1 / Real.sqrt 2) = 1 * (1 / Real.sqrt 2) := by
    rw [one_mul]; exact hG
  have h1 : 1 / a = 1 := mul_right_cancel₀ hsqrt hG'
  rw [one_div] at h1
  exact inv_eq_one.mp h1

/-- まとめ：特性データを持つ場では、角条件を満たす相対スケールは a = 1 のみ。
    角条件 W_u = 1/√2 は特性データから従う（`CFT.WedgeCorner.data_W_u`）ので、
    これは 12-8 (a) の角条件による部分である。 -/
theorem corner_data_fixes_relative_scale {a : ℝ} {F : WedgeFields}
    (hdata : HasWedgeData F)
    (hW : DifferentiableAt ℝ (fun u => F.W u 0) 0)
    (hG : Du (scaleFields a F).W 0 0 = 1 / Real.sqrt 2) :
    a = 1 :=
  corner_slope_fixes_scale hW (CFT.WedgeCorner.data_W_u hdata) hG

/-- 一般補題（2階）：u 方向の2階微分は引き戻しで (1/a)² 倍される。 -/
theorem scale_duu {a : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ∀ u, DifferentiableAt ℝ (fun x => G x 0) u)
    (hG2 : HasDerivAt (fun u => deriv (fun x => G x 0) u) (Duu G 0 0) 0) :
    Duu (fun u v => G (u / a) (a * v)) 0 0 = (1 / a) ^ 2 * Duu G 0 0 := by
  have hinner : ∀ u : ℝ, deriv (fun u'' : ℝ => G (u'' / a) 0) u
      = (1 / a) * deriv (fun x : ℝ => G x 0) (u / a) := by
    intro u
    have h1 : HasDerivAt (fun u'' : ℝ => u'' / a) (1 / a) u := by
      simpa using (hasDerivAt_id u).div_const a
    have h2 : HasDerivAt (fun x : ℝ => G x 0) (deriv (fun x : ℝ => G x 0) (u / a)) (u / a) :=
      (hG (u / a)).hasDerivAt
    have hcomp := h2.comp u h1
    have hder : deriv (fun u'' : ℝ => G (u'' / a) 0) u
        = deriv (fun x : ℝ => G x 0) (u / a) * (1 / a) := hcomp.deriv
    rw [hder]; ring
  have hfun : (fun u : ℝ => deriv (fun u'' : ℝ => G (u'' / a) 0) u)
      = fun u => (1 / a) * deriv (fun x : ℝ => G x 0) (u / a) := funext hinner
  have hG2' : HasDerivAt (fun u => deriv (fun x : ℝ => G x 0) u) (Duu G 0 0) (0 / a) := by
    rw [zero_div]; exact hG2
  have h1 : HasDerivAt (fun u : ℝ => u / a) (1 / a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const a
  have houter : HasDerivAt ((fun u => deriv (fun x : ℝ => G x 0) u) ∘ (fun u : ℝ => u / a))
      (Duu G 0 0 * (1 / a)) 0 := hG2'.comp 0 h1
  have hder2 : deriv (fun u : ℝ => deriv (fun x : ℝ => G x 0) (u / a)) 0
      = Duu G 0 0 * (1 / a) := houter.deriv
  show deriv (fun u : ℝ => deriv (fun u'' : ℝ => G (u'' / a) (a * 0)) u) 0
      = (1 / a) ^ 2 * Duu G 0 0
  simp only [mul_zero]
  have hdiff : DifferentiableAt ℝ (fun u : ℝ => deriv (fun x : ℝ => G x 0) (u / a)) 0 :=
    houter.differentiableAt
  have hstep : deriv (fun u : ℝ => (1 / a) * deriv (fun x : ℝ => G x 0) (u / a)) 0
      = (1 / a) * deriv (fun u : ℝ => deriv (fun x : ℝ => G x 0) (u / a)) 0 :=
    deriv_const_mul _ hdiff
  rw [hfun, hstep, hder2]
  ring

/-- r の2階の角条件 r_uu = −1 は引き戻しで (1/a)² 倍される。 -/
theorem scaleFields_duu_r {a : ℝ} {F : WedgeFields}
    (hR : ∀ u, DifferentiableAt ℝ (fun x => F.r x 0) u)
    (hR2 : HasDerivAt (fun u => deriv (fun x => F.r x 0) u) (Duu F.r 0 0) 0) :
    Duu (scaleFields a F).r 0 0 = (1 / a) ^ 2 * Duu F.r 0 0 :=
  scale_duu hR hR2

/-- 角条件 r_uu = −1 も相対スケールを固定する（a > 0 の範囲で）。 -/
theorem corner_ruu_fixes_scale {a : ℝ} (ha : a > 0) {F : WedgeFields}
    (hR : ∀ u, DifferentiableAt ℝ (fun x => F.r x 0) u)
    (hR2 : HasDerivAt (fun u => deriv (fun x => F.r x 0) u) (Duu F.r 0 0) 0)
    (hF : Duu F.r 0 0 = -1)
    (hG : Duu (scaleFields a F).r 0 0 = -1) :
    a = 1 := by
  rw [scaleFields_duu_r hR hR2, hF] at hG
  -- hG : (1/a)^2 * (-1) = -1
  have h1 : (1 / a) ^ 2 = 1 := by
    have hne : (-1 : ℝ) ≠ 0 := by norm_num
    have := mul_right_cancel₀ hne (show (1 / a) ^ 2 * (-1) = 1 * (-1) by rw [one_mul]; exact hG)
    exact this
  have h2 : 1 / a = 1 ∨ 1 / a = -1 := sq_eq_one_iff.mp h1
  rcases h2 with h | h
  · rw [one_div] at h; exact inv_eq_one.mp h
  · exfalso
    have hpos : (0:ℝ) < 1 / a := by positivity
    rw [h] at hpos; norm_num at hpos


end CFT.WedgeCornerScale
