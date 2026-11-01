/-
  α-V.7 (Z31):量子場の応力と重力の反作用(帽子 = 閉じた輻射 FRW)

  外部の入力(確立した結果、Birrell–Davies 第 6〜7 章、Brown–Cassidy 1977、Ford 1976):
  * 共形平坦な時空の共形真空で、質量ゼロの共形場の繰り込まれた応力は
      ⟨T_μν⟩_ren = (Casimir 項) + α ⁽¹⁾H_μν + β ⁽³⁾H_μν。
    閉じた FRW(半径 a)では、エネルギー密度は ρ_q = ħ(κ₁/a⁴ + κ₂ X²)、X = H² + 1/a²
    (⁽¹⁾H は R = 0 で消え、その係数は R² の対抗項で選べる)。
  * 静的な Einstein 宇宙 ℝ × S³ では Weyl = 0、Euler 密度 = 0、□R = 0 なのでアノマリーは消え、
    ⟨T⟩ は跡ゼロ。ベクトル場 1 本の Casimir エネルギーは 11ħ/(120a)(SU(2) の 1 ループでは 3 本)。
  ここで Lean で示すこと:
  * 伝播と反作用の区別:固定した ℝ × S³ の上の ⟨T⟩ は跡ゼロ。古典の応力と合わせても跡ゼロなので、
    静的な S³ は宇宙定数なしでは自己無撞着でない(`esu_backreaction`、α-VI.3 を使う)。
  * 保存則:p = ρ/3 の ρ = K/a⁴ は連続の式 ρ̇ + 4(ȧ/a)ρ = 0 をみたす(`continuity_radiation`)。
  * 主要な反作用:Casimir 項 κ₁/a⁴ は古典の輻射と同じ a⁻⁴ なので、帽子 a = √(L² − t²) の
    L² = ℓ² + (8πG/3)ħκ₁ を繰り込むだけ(`cap_friedmann`)。
  * 次の項 κ₂X² を入れた Friedmann 方程式 X = L²/a⁴ + γX²(γ = (8πG/3)ħκ₂)は、x = a²X について
    γx² − a²x + L² = 0。実数解があるのは a⁴ ≥ 4γL² のときだけ(`quad_solvable`、γ > 0 のとき
    a_* = (4γL²)^{1/4} ~ (ħG ℓ²)^{1/4} で半古典近似が破れる)。小さい γ の枝は
    x = 2L²/(a² + √(a⁴ − 4γL²))(`small_branch`)で、γ → 0 で古典の L²/a² に戻る。
  解の正則性:a > a_* では枝は実でなめらか。a_* より手前で古典の崩壊 a → 0 に至る前に破綻する。
-/
import CFT.AlphaVI_Static
import Mathlib

namespace CFT.Backreaction

open Real

/-- 二次方程式 γx² − Ax + L = 0 の実数解の存在 ⇔ 判別式 ≥ 0 -/
theorem quad_solvable (γ A L : ℝ) (hγ : γ ≠ 0) :
    (∃ x : ℝ, γ * x ^ 2 - A * x + L = 0) ↔ 4 * γ * L ≤ A ^ 2 := by
  constructor
  · rintro ⟨x, hx⟩
    have : (2 * γ * x - A) ^ 2 = A ^ 2 - 4 * γ * L := by linear_combination 4 * γ * hx
    nlinarith [sq_nonneg (2 * γ * x - A)]
  · intro h
    set s := Real.sqrt (A ^ 2 - 4 * γ * L) with hs
    have hs2 : s ^ 2 = A ^ 2 - 4 * γ * L := Real.sq_sqrt (by linarith)
    refine ⟨(A - s) / (2 * γ), ?_⟩
    have e : γ * ((A - s) / (2 * γ)) ^ 2 - A * ((A - s) / (2 * γ)) + L
        = (s ^ 2 - (A ^ 2 - 4 * γ * L)) / (4 * γ) := by
      field_simp; ring
    rw [e, hs2, sub_self, zero_div]

/-- 小さい γ の枝:x = (a² − s)/(2γ) = 2L/(a² + s)(s = √(a⁴ − 4γL)) -/
theorem small_branch (γ a2 L : ℝ) (hγ : γ ≠ 0) (hD : 4 * γ * L ≤ a2 ^ 2) (ha : 0 < a2) :
    (a2 - Real.sqrt (a2 ^ 2 - 4 * γ * L)) / (2 * γ)
      = 2 * L / (a2 + Real.sqrt (a2 ^ 2 - 4 * γ * L)) := by
  set s := Real.sqrt (a2 ^ 2 - 4 * γ * L) with hs
  have hs2 : s ^ 2 = a2 ^ 2 - 4 * γ * L := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hden : a2 + s ≠ 0 := ne_of_gt (by linarith)
  rw [div_eq_div_iff (mul_ne_zero two_ne_zero hγ) hden]
  linear_combination -hs2

/-- 帽子 a = √(L − t²)(L = ℓ² + 繰り込みの項)は閉じた輻射 FRW の Friedmann 方程式
ȧ² + 1 = L/a² をみたす -/
theorem cap_friedmann (L t : ℝ) (ht : t ^ 2 < L) :
    HasDerivAt (fun τ => Real.sqrt (L - τ ^ 2)) (-t / Real.sqrt (L - t ^ 2)) t ∧
    (-t / Real.sqrt (L - t ^ 2)) ^ 2 + 1 = L / (Real.sqrt (L - t ^ 2)) ^ 2 := by
  have hpos : 0 < L - t ^ 2 := by linarith
  have hsq : (Real.sqrt (L - t ^ 2)) ^ 2 = L - t ^ 2 := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (L - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  constructor
  · have h := ((hasDerivAt_pow 2 t).const_sub L).sqrt hpos.ne'
    refine h.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  · have hne' : L - t ^ 2 ≠ 0 := hpos.ne'
    rw [div_pow, hsq]
    field_simp
    ring

/-- 保存則:ρ = K/a⁴(p = ρ/3)は ρ̇ = −4(ȧ/a)ρ をみたす -/
theorem continuity_radiation (K : ℝ) (a : ℝ → ℝ) (a' t : ℝ) (ha : HasDerivAt a a' t)
    (ha0 : a t ≠ 0) :
    HasDerivAt (fun τ => K / a τ ^ 4) (-4 * (a' / a t) * (K / a t ^ 4)) t := by
  have h4 : a t ^ 4 ≠ 0 := pow_ne_zero 4 ha0
  have h := ((ha.pow 4).inv h4).const_mul K
  show HasDerivAt (fun τ => K * (a τ ^ 4)⁻¹) _ t
  refine h.congr_deriv ?_
  rw [show (4 : ℕ) - 1 = 3 from rfl]
  field_simp
  ring

/-- 【α-V.7】伝播と反作用の区別:固定した ℝ × S³ 上で ⟨T⟩_ren が跡ゼロ(アノマリーが消える)なら、
古典の跡ゼロの応力 T_cl と合わせても、静的な S³ は Einstein 方程式をみたさない(宇宙定数が必要)。 -/
theorem esu_backreaction {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)
    (l σ κ s c κG : S) (H : CFT.S4.SphD d 1 l (l * σ) s c) (hl : ∀ i, d i l = 0)
    (hσ0 : d 0 σ = 0) (hσ1 : d 1 σ = κ) (hκ1 : d 1 κ = -σ) (pyth : σ ^ 2 + κ ^ 2 = 1)
    (Tcl Tq : Fin 4 → Fin 4 → S)
    (E : ∀ a, CFT.S4.Ein d (CFT.S4.gD 1 l (l * σ) s) (CFT.S4.giD 1 l (l * σ) s)
      (CFT.S4.GD d 1 l (l * σ) s c) a a = κG * (Tcl a a + Tq a a))
    (tcl : CFT.S4.giD 1 l (l * σ) s 0 0 * Tcl 0 0 + CFT.S4.giD 1 l (l * σ) s 1 1 * Tcl 1 1
      + CFT.S4.giD 1 l (l * σ) s 2 2 * Tcl 2 2 + CFT.S4.giD 1 l (l * σ) s 3 3 * Tcl 3 3 = 0)
    (tq : CFT.S4.giD 1 l (l * σ) s 0 0 * Tq 0 0 + CFT.S4.giD 1 l (l * σ) s 1 1 * Tq 1 1
      + CFT.S4.giD 1 l (l * σ) s 2 2 * Tq 2 2 + CFT.S4.giD 1 l (l * σ) s 3 3 * Tq 3 3 = 0) :
    False :=
  CFT.VIStatic.static_S3_impossible d l σ κ s c κG H hl hσ0 hσ1 hκ1 pyth
    (fun a b => Tcl a b + Tq a b) E (by linear_combination tcl + tq)

end CFT.Backreaction
