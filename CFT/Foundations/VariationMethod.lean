import Mathlib
import CFT.Quantum.MinisuperspaceVariation

/-!
  命題集 `LEAN_GAP_TREES.md` 1-1（2026-11-16）：変分の方法の固定。

  以後の葉はすべてこの流儀で書く：一般の変分計算は作らず、1 パラメータ族
  `F : ℝ → ℝ`（`ε` が変分パラメータ）に対する `ε = 0` での微分
  `HasDerivAt F δ 0` をもって「変分」とする。1-2 の `L_a`・`L_b` は
  既にこの形で証明されており、本モジュールはその方法を定義・代数・
  停留条件（フェルマー）・方向微分の形で固定し、1-2 への適用
  （`a`・`b` 方向の変分が偏微分に一致すること）まで示す。
-/

namespace CFT.Variation

open CFT.Mini

/-- 1 パラメータ族 `F` の `ε = 0` での変分が `δ` であること。 -/
def HasVariation (F : ℝ → ℝ) (δ : ℝ) : Prop :=
  HasDerivAt F δ 0

/-- 1 パラメータ族 `F` の `ε = 0` での変分（微分係数）。 -/
noncomputable def varDeriv (F : ℝ → ℝ) : ℝ :=
  deriv F 0

theorem hasVariation_iff {F : ℝ → ℝ} {δ : ℝ} :
    HasVariation F δ ↔ HasDerivAt F δ 0 :=
  Iff.rfl

theorem varDeriv_eq {F : ℝ → ℝ} : varDeriv F = deriv F 0 :=
  rfl

/-- 微分可能な族は自分の `varDeriv` を変分として持つ。 -/
theorem hasVariation_varDeriv {F : ℝ → ℝ} (hd : DifferentiableAt ℝ F 0) :
    HasVariation F (varDeriv F) :=
  hd.hasDerivAt

/-- 定数族の変分は 0。 -/
theorem hasVariation_const (c : ℝ) : HasVariation (fun _ => c) 0 :=
  hasDerivAt_const 0 c

/-- 変分の和。 -/
theorem hasVariation_add {F G : ℝ → ℝ} {δ η : ℝ}
    (hF : HasVariation F δ) (hG : HasVariation G η) :
    HasVariation (fun ε => F ε + G ε) (δ + η) :=
  hF.add hG

/-- 変分の差。 -/
theorem hasVariation_sub {F G : ℝ → ℝ} {δ η : ℝ}
    (hF : HasVariation F δ) (hG : HasVariation G η) :
    HasVariation (fun ε => F ε - G ε) (δ - η) :=
  hF.sub hG

/-- 変分の符号反転。 -/
theorem hasVariation_neg {F : ℝ → ℝ} {δ : ℝ} (hF : HasVariation F δ) :
    HasVariation (fun ε => -F ε) (-δ) :=
  hF.neg

/-- 変分の定数倍。 -/
theorem hasVariation_const_mul {F : ℝ → ℝ} {δ : ℝ} (c : ℝ)
    (hF : HasVariation F δ) :
    HasVariation (fun ε => c * F ε) (c * δ) :=
  hF.const_mul c

/-- 変分の積（ライプニッツ則）。 -/
theorem hasVariation_mul {F G : ℝ → ℝ} {δ η : ℝ}
    (hF : HasVariation F δ) (hG : HasVariation G η) :
    HasVariation (fun ε => F ε * G ε) (δ * G 0 + F 0 * η) :=
  hF.mul hG

/-- 方向微分：`f` が `q₀` で微分可能なら、アフィン族 `ε ↦ f (q₀ + h * ε)` の
    変分は `f' * h`。1-2 の偏微分計算がこの形である。 -/
theorem hasVariation_comp_affine {f : ℝ → ℝ} {f' q₀ h : ℝ}
    (hf : HasDerivAt f f' q₀) :
    HasVariation (fun ε => f (q₀ + h * ε)) (f' * h) := by
  have hinner : HasDerivAt (fun ε : ℝ => q₀ + h * ε) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul h).const_add q₀
  have hf' : HasDerivAt f f' ((fun ε : ℝ => q₀ + h * ε) 0) := by
    simpa using hf
  exact hf'.comp 0 hinner

/-- 停留条件（フェルマー）：`ε = 0` が局所極値なら変分は 0。
    オイラー–ラグランジュ方程式の出発点。 -/
theorem variation_eq_zero_of_isLocalExtr {F : ℝ → ℝ} {δ : ℝ}
    (h : IsLocalExtr F 0) (hv : HasVariation F δ) : δ = 0 :=
  h.hasDerivAt_eq_zero hv

/-- 停留条件の `varDeriv` 版。 -/
theorem varDeriv_eq_zero_of_isLocalExtr {F : ℝ → ℝ}
    (h : IsLocalExtr F 0) (hd : DifferentiableAt ℝ F 0) : varDeriv F = 0 :=
  h.hasDerivAt_eq_zero hd.hasDerivAt

/-- 1-2 への適用：`Lfun` の `a` 方向の変分は偏微分 `L_a` の値に一致する。 -/
theorem variation_Lfun_a (a b ad bd N c l : ℝ) :
    HasVariation (fun ε => Lfun (a + ε) b ad bd N c l)
      (-(c * bd ^ 2) / N + c * N * (1 - l ^ 2 / b ^ 2)) := by
  have h := hasVariation_comp_affine (f := fun x => Lfun x b ad bd N c l)
    (f' := -(c * bd ^ 2) / N + c * N * (1 - l ^ 2 / b ^ 2)) (q₀ := a) (h := 1)
    (L_a a b ad bd N c l)
  simpa using h

/-- 1-2 への適用：`Lfun` の `b` 方向の変分は偏微分 `L_b` の値に一致する。 -/
theorem variation_Lfun_b (a b ad bd N c l : ℝ) (hb : b ≠ 0) :
    HasVariation (fun ε => Lfun a (b + ε) ad bd N c l)
      (-2 * c * ad * bd / N + 2 * c * N * a * l ^ 2 / b ^ 3) := by
  have h := hasVariation_comp_affine (f := fun y => Lfun a y ad bd N c l)
    (f' := -2 * c * ad * bd / N + 2 * c * N * a * l ^ 2 / b ^ 3) (q₀ := b) (h := 1)
    (L_b a b ad bd N c l hb)
  simpa using h

end CFT.Variation
