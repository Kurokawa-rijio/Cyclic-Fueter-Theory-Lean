import Mathlib

/-!
  命題集 `LEAN_GAP_TREES.md` 11-11（既知の数値解との照合）のうち、
  シューティングの原点データの形式的検証（部分解決）。

  対象は `numerics/StaticEYMProperDistance.py` の静的 EYM 系（固有距離ゲージ、
  ℓ = 1 規格化、Λ = L）と、`numerics/BartnikMcKinnonShooting.py`・
  `numerics/BartnikMcKinnonBrackets.py` の射撃で使う正則原点の級数データ
  （`init`）：r = s + r3 s³、r′ = 1 + 3 r3 s²、W = 1 − b s²、W′ = −2 b s、
  ν′ = c s。ここで r3 = −(12b² + L)/18、c = 4b² − L/3。

  証明する内容：
  * 級数関数とその導関数の対応（`HasDerivAt` 5 件）。`init` のタプルは
    ちょうど (r, r′, W, W′, ν′) を s0 で評価したものである。
  * 4 本の方程式・拘束への代入残差が、分母を払った多項式の形で
    W 方程式は s⁴、r 方程式は s⁸、ν 方程式は s⁶、拘束は s⁶ のオーダーで
    あること（`W_residual`・`r_residual`・`nu_residual`・`constraint_residual`）。
    すなわち `init` の級数は方程式系の形式的解として正しい次数まで一致する。
    残差の明示多項式は sympy による展開計算（`/tmp/check1111c.py`・
    `/tmp/check1111d.py`）でも照合済み。
  * ESU テスト（`StaticEYMProperDistance.py` の `__main__`、b = 1/4、L = 3/4）
    のパラメータ：r3 = −1/12、c = 0（`r3_esu`・`cc_esu` と級数の特殊化）。

  残り（Lean の外）：b_n = 0.4537、0.6517、0.6970、0.7048、0.7062（n = 1..5）
  という文献値との数値比較そのものは浮動小数点の射撃の出力であり、Lean 化には
  区間演算による射撃の認証が必要。喉での節間隔の漸近則（ln r あたり π/√3、
  質量欠損 ∝ e^{−πn/√3}）の証明も残り。解の存在・一意性には触れない。
-/

namespace CFT.BMOrigin

/-- 正則原点の級数の r³ 係数（`init` の `r3`）。 -/
noncomputable def r3 (b L : ℝ) : ℝ := -(12 * b ^ 2 + L) / 18

/-- 正則原点の級数の ν′ の係数（`init` の `c`）。 -/
noncomputable def cc (b L : ℝ) : ℝ := 4 * b ^ 2 - L / 3

/-- 動径の級数 r(s) = s + r3 s³。 -/
noncomputable def rFun (b L s : ℝ) : ℝ := s + r3 b L * s ^ 3

/-- 動径の導関数 r′(s) = 1 + 3 r3 s²。 -/
noncomputable def rpFun (b L s : ℝ) : ℝ := 1 + 3 * r3 b L * s ^ 2

/-- 動径の 2 階導関数 r″(s) = 6 r3 s。 -/
noncomputable def rppFun (b L s : ℝ) : ℝ := 6 * r3 b L * s

/-- ゲージ場の級数 W(s) = 1 − b s²。 -/
def wFun (b s : ℝ) : ℝ := 1 - b * s ^ 2

/-- ゲージ場の導関数 W′(s) = −2 b s。 -/
def wpFun (b s : ℝ) : ℝ := -2 * b * s

/-- ゲージ場の 2 階導関数 W″(s) = −2 b。 -/
def wppFun (b : ℝ) : ℝ := -2 * b

/-- ν′(s) = c s。 -/
noncomputable def nupFun (b L s : ℝ) : ℝ := cc b L * s

/-- ν″(s) = c。 -/
noncomputable def nuppFun (b L : ℝ) : ℝ := cc b L

/-! ### 級数関数とその導関数 -/

theorem rFun_hasDerivAt (b L s : ℝ) :
    HasDerivAt (rFun b L) (rpFun b L s) s := by
  have hp3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * s ^ 2) s := by
    simpa using hasDerivAt_pow 3 s
  have h := (hasDerivAt_id s).add (hp3.const_mul (r3 b L))
  unfold rFun rpFun
  convert h using 1
  ring

theorem rpFun_hasDerivAt (b L s : ℝ) :
    HasDerivAt (rpFun b L) (rppFun b L s) s := by
  have hp2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have h := (hasDerivAt_const s (1 : ℝ)).add (hp2.const_mul (3 * r3 b L))
  unfold rpFun rppFun
  convert h using 1
  ring

theorem wFun_hasDerivAt (b s : ℝ) :
    HasDerivAt (wFun b) (wpFun b s) s := by
  have hp2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have h := (hp2.const_mul b).const_sub (1 : ℝ)
  unfold wFun wpFun
  convert h using 1
  ring

theorem wpFun_hasDerivAt (b s : ℝ) :
    HasDerivAt (wpFun b) (wppFun b) s := by
  have h := (hasDerivAt_id s).const_mul (-2 * b)
  unfold wpFun wppFun
  convert h using 1
  ring

theorem nupFun_hasDerivAt (b L s : ℝ) :
    HasDerivAt (nupFun b L) (nuppFun b L) s := by
  have h := (hasDerivAt_id s).const_mul (cc b L)
  unfold nupFun nuppFun
  convert h using 1
  ring

/-! ### 方程式・拘束への代入残差（分母を払った多項式形） -/

/-- W 方程式 W″ = −ν′W′ − W(1−W²)/r² に r² を掛けた形の残差。s⁴ のオーダー。 -/
theorem W_residual (b L s : ℝ) :
    (rFun b L s) ^ 2 * wppFun b
      + (rFun b L s) ^ 2 * nupFun b L s * wpFun b s
      + wFun b s * (1 - (wFun b s) ^ 2)
      = s ^ 4 * ((8 * L * b / 9 - 16 * b ^ 3 / 3 - 3 * b ^ 2)
        + (-13 * L ^ 2 * b / 162 - 4 * L * b ^ 3 / 27 + 88 * b ^ 5 / 9 + b ^ 3) * s ^ 2
        + (L ^ 3 * b / 486 + 2 * L ^ 2 * b ^ 3 / 81 - 8 * L * b ^ 5 / 27
          - 32 * b ^ 7 / 9) * s ^ 4) := by
  unfold rFun wppFun nupFun wpFun wFun r3 cc
  ring

/-- r 方程式 r″ = (1 − r′² − r²(ρ + L))/(2r) に 2r⁵ を掛けた形の残差。
    ここで ρ = k + m、r⁶k = 2r⁴W′²、r⁶m = r²(1−W²)² を使った。s⁸ のオーダー。 -/
theorem r_residual (b L s : ℝ) :
    2 * (rFun b L s) ^ 5 * rppFun b L s
      - (rFun b L s) ^ 4 * (1 - (rpFun b L s) ^ 2)
      + (rFun b L s) ^ 6 * L
      + 2 * (rFun b L s) ^ 4 * (wpFun b s) ^ 2
      + (rFun b L s) ^ 2 * (1 - (wFun b s) ^ 2) ^ 2
      = s ^ 8 * ((-5 * L ^ 2 / 108 + 2 * L * b ^ 2 / 3 + 44 * b ^ 4 / 3 - 4 * b ^ 3)
        + (13 * L ^ 3 / 972 + 7 * L ^ 2 * b ^ 2 / 81 - 100 * L * b ^ 4 / 27
          + 4 * L * b ^ 3 / 9 - 304 * b ^ 6 / 9 + 16 * b ^ 5 / 3 + b ^ 4) * s ^ 2
        + (-L ^ 4 / 648 - 28 * L ^ 3 * b ^ 2 / 729 - 4 * L ^ 2 * b ^ 4 / 81
          - L ^ 2 * b ^ 3 / 81 + 128 * L * b ^ 6 / 27 - 8 * L * b ^ 5 / 27
          - L * b ^ 4 / 9 + 800 * b ^ 8 / 27 - 16 * b ^ 7 / 9 - 4 * b ^ 6 / 3) * s ^ 4
        + (7 * L ^ 5 / 78732 + 97 * L ^ 4 * b ^ 2 / 26244 + 4 * L ^ 3 * b ^ 4 / 81
          + 88 * L ^ 2 * b ^ 6 / 729 + L ^ 2 * b ^ 4 / 324 - 512 * L * b ^ 8 / 243
          + 2 * L * b ^ 6 / 27 - 320 * b ^ 10 / 27 + 4 * b ^ 8 / 9) * s ^ 6
        + (-29 * L ^ 6 / 11337408 - 23 * L ^ 5 * b ^ 2 / 157464
          - 85 * L ^ 4 * b ^ 4 / 26244 - 220 * L ^ 3 * b ^ 6 / 6561
          - 100 * L ^ 2 * b ^ 8 / 729 + 32 * L * b ^ 10 / 243 + 448 * b ^ 12 / 243) * s ^ 8
        + (L ^ 7 / 34012224 + L ^ 6 * b ^ 2 / 472392 + 5 * L ^ 5 * b ^ 4 / 78732
          + 20 * L ^ 4 * b ^ 6 / 19683 + 20 * L ^ 3 * b ^ 8 / 2187
          + 32 * L ^ 2 * b ^ 10 / 729 + 64 * L * b ^ 12 / 729) * s ^ 10) := by
  unfold rFun rppFun rpFun wpFun wFun r3
  ring

/-- ν 方程式 ν″ = m − L − r″/r − ν′² − ν′r′/r に r⁴ を掛けた形の残差。
    r⁴m = (1−W²)² を使った。s⁶ のオーダー。 -/
theorem nu_residual (b L s : ℝ) :
    (rFun b L s) ^ 4 * nuppFun b L
      - (1 - (wFun b s) ^ 2) ^ 2
      + L * (rFun b L s) ^ 4
      + (rFun b L s) ^ 3 * rppFun b L s
      + (rFun b L s) ^ 4 * (nupFun b L s) ^ 2
      + (rFun b L s) ^ 3 * nupFun b L s * rpFun b L s
      = s ^ 6 * ((7 * L ^ 2 / 54 - 4 * L * b ^ 2 - 8 * b ^ 4 / 3 + 4 * b ^ 3)
        + (-L ^ 3 / 36 + 11 * L ^ 2 * b ^ 2 / 27 + 68 * L * b ^ 4 / 9
          - 16 * b ^ 6 - b ^ 4) * s ^ 2
        + (13 * L ^ 4 / 5832 - 2 * L ^ 3 * b ^ 2 / 729 - 68 * L ^ 2 * b ^ 4 / 81
          - 32 * L * b ^ 6 / 9 + 736 * b ^ 8 / 27) * s ^ 4
        + (-25 * L ^ 5 / 314928 - 2 * L ^ 4 * b ^ 2 / 2187 + 58 * L ^ 3 * b ^ 4 / 2187
          + 272 * L ^ 2 * b ^ 6 / 729 - 16 * L * b ^ 8 / 27 - 1280 * b ^ 10 / 81) * s ^ 6
        + (L ^ 6 / 944784 + L ^ 5 * b ^ 2 / 39366 - L ^ 4 * b ^ 4 / 6561
          - 16 * L ^ 3 * b ^ 6 / 2187 - 16 * L ^ 2 * b ^ 8 / 729
          + 128 * L * b ^ 10 / 243 + 256 * b ^ 12 / 81) * s ^ 8) := by
  unfold rFun nuppFun wFun rppFun nupFun rpFun r3 cc
  ring

/-- 拘束 2r′ν′/r − (1−r′²)/r² + L − (k − m) = 0 に r⁴ を掛けた形の残差。
    r⁴k = 2r²W′²、r⁴m = (1−W²)² を使った。s⁶ のオーダー。 -/
theorem constraint_residual (b L s : ℝ) :
    2 * (rFun b L s) ^ 3 * rpFun b L s * nupFun b L s
      - (rFun b L s) ^ 2 * (1 - (rpFun b L s) ^ 2)
      + L * (rFun b L s) ^ 4
      - 2 * (rFun b L s) ^ 2 * (wpFun b s) ^ 2
      + (1 - (wFun b s) ^ 2) ^ 2
      = s ^ 6 * ((7 * L ^ 2 / 108 - 2 * L * b ^ 2 / 9 - 12 * b ^ 4 - 4 * b ^ 3)
        + (-5 * L ^ 3 / 486 - 2 * L ^ 2 * b ^ 2 / 81 + 104 * L * b ^ 4 / 27
          + 32 * b ^ 6 + b ^ 4) * s ^ 2
        + (19 * L ^ 4 / 34992 + 5 * L ^ 3 * b ^ 2 / 729 - 2 * L ^ 2 * b ^ 4 / 9
          - 368 * L * b ^ 6 / 81 - 592 * b ^ 8 / 27) * s ^ 4
        + (-L ^ 5 / 104976 - L ^ 4 * b ^ 2 / 4374 + 2 * L ^ 3 * b ^ 4 / 729
          + 32 * L ^ 2 * b ^ 6 / 243 + 112 * L * b ^ 8 / 81 + 128 * b ^ 10 / 27) * s ^ 6) := by
  unfold rFun rpFun nupFun wpFun wFun r3 cc
  ring

/-! ### ESU テストのパラメータ（b = 1/4、L = 3/4） -/

/-- ESU テストでは r3 = −1/12。 -/
theorem r3_esu : r3 (1 / 4) (3 / 4) = -1 / 12 := by
  unfold r3
  norm_num

/-- ESU テストでは c = 0（ν′ ≡ 0）。 -/
theorem cc_esu : cc (1 / 4) (3 / 4) = 0 := by
  unfold cc
  norm_num

/-- ESU テストの動径の級数：r(s) = s − s³/12。 -/
theorem rFun_esu (s : ℝ) : rFun (1 / 4) (3 / 4) s = s - s ^ 3 / 12 := by
  unfold rFun r3
  ring

/-- ESU テストのゲージ場の級数：W(s) = 1 − s²/4。 -/
theorem wFun_esu (s : ℝ) : wFun (1 / 4) s = 1 - s ^ 2 / 4 := by
  unfold wFun
  ring

/-- ESU テストでは ν′(s) ≡ 0。 -/
theorem nupFun_esu (s : ℝ) : nupFun (1 / 4) (3 / 4) s = 0 := by
  unfold nupFun cc
  ring

end CFT.BMOrigin
