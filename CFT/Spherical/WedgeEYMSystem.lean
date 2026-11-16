import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 4-1（問題の定式化そのもの）：
  くさび領域の球対称アインシュタイン–ヤン＝ミルズ系を Lean のデータとして書き下す。
  計量は二重ヌル座標で ds² = −2Ω du dv + r² dΩ²（Ω = e^{2σ}）、長さは ℓ 単位（ℓ = 1）。
  発展方程式と拘束は数値計算 `numerics/WedgeEvolution.py` の F と C_u、C_v そのもの：
    r_uv = Ω((1−W²)²/r² − 1)/(2r) − r_u r_v/r
    Ω_uv = Ω_u Ω_v/Ω − 2Ω r_uv/r − Ω²(1−W²)²/r⁴
    W_uv = Ω W(1−W²)/(2r²)   （`CFT.AlphaIV.FW` の Ω = e^{2σ} 版と一致）
    C_u: r_uu − (Ω_u/Ω) r_u + 2 W_u²/r = 0、C_v: 同じく v 方向
  データは帽子（v = 0）と首（u = 0）の2つのヌル面に乗り、角 (0,0) で両立する
  （値の一致と、セクター条件の角での値 W_u = 1/√2 を証明する）。
  ここでは定式化までで、解の存在・一意性には触れない（4-3、4-9、4-16 の領分）。
-/

namespace CFT.Wedge

open Real

/-- u 方向の偏微分（v を固定したスライスの微分）。 -/
noncomputable def Du (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := deriv (fun u' => F u' v) u

/-- v 方向の偏微分。 -/
noncomputable def Dv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := deriv (fun v' => F u v') v

/-- 混合微分 ∂_u∂_v。 -/
noncomputable def Duv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun u' => deriv (fun v' => F u' v') v) u

/-- u 方向の2階微分。 -/
noncomputable def Duu (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun u' => deriv (fun u'' => F u'' v) u') u

/-- v 方向の2階微分。 -/
noncomputable def Dvv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun v' => deriv (fun v'' => F u v'') v') v

/-- r_uv の右辺（`WedgeEvolution.py` の F の第1成分）。 -/
noncomputable def rhsR (Om W ru rv r : ℝ) : ℝ :=
  (1 / 2) * Om * ((1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r

/-- Ω_uv の右辺（F の第2成分。r_uv の値を使う）。 -/
noncomputable def rhsOm (Om Ou Ov ruv r W : ℝ) : ℝ :=
  Ou * Ov / Om - 2 * Om * ruv / r - Om ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4

/-- W_uv の右辺（F の第3成分）。 -/
noncomputable def rhsW (Om W r : ℝ) : ℝ :=
  (1 / 2) * Om * W * (1 - W ^ 2) / r ^ 2

/-- くさびの未知関数（動径 r、計量関数 Ω、ゲージ場 W）。 -/
structure WedgeFields where
  r : ℝ → ℝ → ℝ
  Om : ℝ → ℝ → ℝ
  W : ℝ → ℝ → ℝ

/-- 発展方程式（3本の波動方程式）。 -/
def WedgeEvolutionEqs (F : WedgeFields) : Prop :=
  ∀ u v, Duv F.r u v = rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v)
    ∧ Duv F.Om u v
        = rhsOm (F.Om u v) (Du F.Om u v) (Dv F.Om u v) (Duv F.r u v) (F.r u v) (F.W u v)
    ∧ Duv F.W u v = rhsW (F.Om u v) (F.W u v) (F.r u v)

/-- 拘束（C_u と C_v）。 -/
def WedgeConstraints (F : WedgeFields) : Prop :=
  ∀ u v, Duu F.r u v - (Du F.Om u v / F.Om u v) * Du F.r u v
        + 2 * (Du F.W u v) ^ 2 / F.r u v = 0
    ∧ Dvv F.r u v - (Dv F.Om u v / F.Om u v) * Dv F.r u v
        + 2 * (Dv F.W u v) ^ 2 / F.r u v = 0

/-- 帽子（v = 0 面）のデータ：r = cos²(u/√2)。 -/
noncomputable def capR (u : ℝ) : ℝ := (cos (u / sqrt 2)) ^ 2

/-- 帽子のデータ：Ω = cos²(u/√2)。 -/
noncomputable def capOm (u : ℝ) : ℝ := (cos (u / sqrt 2)) ^ 2

/-- 帽子のデータ：W = sin(u/√2)。 -/
noncomputable def capW (u : ℝ) : ℝ := sin (u / sqrt 2)

/-- 首（u = 0 面）のデータ：Ω = sech²(v/√2)。 -/
noncomputable def neckOm (v : ℝ) : ℝ := ((cosh (v / sqrt 2)) ^ 2)⁻¹

/-- 特性初期データ：v = 0 で帽子、u = 0 で首（r = 1、W = 0）。 -/
def HasWedgeData (F : WedgeFields) : Prop :=
  (∀ u, F.r u 0 = capR u ∧ F.Om u 0 = capOm u ∧ F.W u 0 = capW u)
    ∧ (∀ v, F.r 0 v = 1 ∧ F.Om 0 v = neckOm v ∧ F.W 0 v = 0)

/-- 角 (0,0) での両立：両面のデータの値が一致する。 -/
theorem corner_values :
    capR 0 = 1 ∧ capOm 0 = 1 ∧ capW 0 = 0 ∧ neckOm 0 = 1 := by
  simp [capR, capOm, capW, neckOm]

/-- 角でのセクター条件の値：帽子データの W の傾きは 1/√2
    （数値計算が u = 0 面上で監視する W_u = 1/√2 の角での値）。 -/
theorem corner_capW_slope : deriv capW 0 = 1 / sqrt 2 := by
  have hlin : HasDerivAt (fun u => u / sqrt 2) (1 / sqrt 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const (sqrt 2)
  have h := (hasDerivAt_sin (0 / sqrt 2)).comp 0 hlin
  have hderiv := h.deriv
  simp only [capW, zero_div, cos_zero, one_mul] at hderiv
  exact hderiv

/-- 角での帽子データの r の傾きは 0（時間対称な角の C¹ 条件）。 -/
theorem corner_capR_slope : deriv capR 0 = 0 := by
  have hlin : HasDerivAt (fun u => u / sqrt 2) (1 / sqrt 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const (sqrt 2)
  have hcos : HasDerivAt (fun u => cos (u / sqrt 2)) (-sin (0 / sqrt 2) * (1 / sqrt 2)) 0 := by
    have h := (hasDerivAt_cos (0 / sqrt 2)).comp 0 hlin
    simpa [Function.comp] using h
  have h := hcos.pow 2
  have hderiv := h.deriv
  simp only [capR, zero_div, sin_zero, cos_zero] at hderiv
  simpa using hderiv

end CFT.Wedge
