/-
  命題集 `LEAN_GAP_TREES.md` 12-8（Ω のゼロの位数と結合 A の発散による
  くさび解の分類）の (b) 対応仮説の証明への一段：

  **残余 R の係数の極端 RN 版の明示公式**。前段
  （`WedgeHorizonDefectSourceDerivClosed`）では ∂_v S の閉形
    ∂_v S = (Ω_v/Ω)·S + R
  が証明され、前々段（`WedgeHorizonDefectRemainder`）では R の四項が
  すべて Dv r か Dv W を因子に持つことから R = 0 の第一の十分条件が
  証明された。ここでは R の四項の係数
    B1（Dv r の項）、C1（(Dv r)² の項）、C2（(Dv W)² の項）、
    C3（Dv W の項）
  を関数として切り出し（`defectRemainderCoeffB1/C1/C2/C3`）、
  g = RN の対数微分 `rnLogDeriv`、g′ = `rnLogDeriv'`、
  g″ = `rnLogDeriv''` の極端版（r₊ = r₋）での明示公式を証明する：
    C1 = 2(3r³ + 3r²r₊ − 7r·r₊² + 3r₊³)/(r−r₊)³、
    C2 = −2(r² + r·r₊ − r₊²)/(r−r₊)²、
    C3 = 2(2r−r₊)/(r−r₊)、
    B1 = (Q·(W⁴ − 2W²) + (−3r⁴ + r²r₊² + Q))/(r−r₊)²、
      ただし Q = 9r² − 10r·r₊ + 3r₊²（W² 係数は W⁴ 係数の −2 倍）。
  B1 は W⁴・W²・W⁰ の三つのピースに分けて証明する
  （`defectRemainderCoeffB1W4/W2/W0` とその極端版）。公式は sympy
  による明示計算（`check_R_coeffs_extremal.py`、C1・C2・C3 と B1 の
  三ピースおよび結合形を照合）でも確認済み。非極端版では
  C1・C2・C3・B1|_{W=0} は (r−r₊)(r−r₋) を分母に持つ巨大な有理式に
  なり、きれいな因数分解はない（前段で確認）。係数の零点の解析
  （C1 = 0、C2 = 0、C3 = 0、B1|_{W=0} = 0 がどこで成り立つか）は
  次の段に残す。
-/
import CFT.Spherical.WedgeHorizonDefectSourceDerivClosed
import CFT.Spherical.WedgeHorizonDefectSourceDeriv

open Real Set Filter Topology
open CFT.Wedge CFT.WedgeDefectTransport CFT.WedgeDefectSource
open CFT.WedgeDefectSourceDeriv CFT.WedgeDefectSourceDerivClosed
open CFT.RNLogDeriv

namespace CFT.WedgeDefectRemainderExtremal

/-- 残余 R の Dv r の項の係数 B1（W の四次までの多項式）。 -/
noncomputable def defectRemainderCoeffB1 (g g' : ℝ → ℝ) (r W : ℝ) : ℝ :=
  2 * W ^ 4 * g r * r - W ^ 4 * g' r * r ^ 2 + 9 * W ^ 4
    - 4 * W ^ 2 * g r * r + 2 * W ^ 2 * g' r * r ^ 2 - 18 * W ^ 2
    - g r * r ^ 3 + 2 * g r * r + g' r * r ^ 4 - g' r * r ^ 2
    - 3 * r ^ 2 + 9

/-- B1 の W⁴ の係数：2·g·r − g′·r² + 9。 -/
noncomputable def defectRemainderCoeffB1W4 (g g' : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * g r * r - g' r * r ^ 2 + 9

/-- B1 の W² の係数：−4·g·r + 2·g′·r² − 18。 -/
noncomputable def defectRemainderCoeffB1W2 (g g' : ℝ → ℝ) (r : ℝ) : ℝ :=
  -4 * g r * r + 2 * g' r * r ^ 2 - 18

/-- B1 の W⁰ の部分：−g·r³ + 2·g·r + g′·r⁴ − g′·r² − 3r² + 9。 -/
noncomputable def defectRemainderCoeffB1W0 (g g' : ℝ → ℝ) (r : ℝ) : ℝ :=
  -g r * r ^ 3 + 2 * g r * r + g' r * r ^ 4 - g' r * r ^ 2 - 3 * r ^ 2 + 9

/-- 残余 R の (Dv r)² の項の係数 C1。 -/
noncomputable def defectRemainderCoeffC1 (g g' g'' : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * g r * r - 2 * g' r * r ^ 2 + g'' r * r ^ 3 + 6

/-- 残余 R の (Dv W)² の項の係数 C2。 -/
noncomputable def defectRemainderCoeffC2 (g g' : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(g r) * r + g' r * r ^ 2 - 2

/-- 残余 R の Dv W の項の係数 C3。 -/
noncomputable def defectRemainderCoeffC3 (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  g r * r + 4

/-- 極端版の B1 の W⁴ 係数に現れる二次式 Q = 9r² − 10r·r₊ + 3r₊²。
    r についての判別式は −8r₊² である（零点の解析は次の段）。
    W² 係数はその −2 倍になる（下記の極端版を参照）。 -/
noncomputable def defectRemainderQuadCoeff (r rp : ℝ) : ℝ :=
  9 * r ^ 2 - 10 * r * rp + 3 * rp ^ 2

/-- 残余 R の四項表示（係数関数による書き換え）。 -/
theorem defectSourceRemainder_eq_coeffs {F : WedgeFields} {g g' g'' : ℝ → ℝ} {u v : ℝ} :
    defectSourceRemainder F g g' g'' u v
      = Dv F.r u v * (F.Om u v / (F.r u v) ^ 5)
          * defectRemainderCoeffB1 g g' (F.r u v) (F.W u v)
        + (Dv F.r u v) ^ 2 * (-(Du F.r u v) / (F.r u v) ^ 3)
          * defectRemainderCoeffC1 g g' g'' (F.r u v)
        + Dv F.W u v * (2 * F.Om u v * F.W u v * (1 - (F.W u v) ^ 2)
          * defectRemainderCoeffC3 g (F.r u v) / (F.r u v) ^ 4)
        + (Dv F.W u v) ^ 2 * (2 * Du F.r u v / (F.r u v) ^ 3)
          * defectRemainderCoeffC2 g g' (F.r u v) := by
  unfold defectSourceRemainder defectRemainderCoeffB1 defectRemainderCoeffC1
    defectRemainderCoeffC2 defectRemainderCoeffC3
  ring

/-- B1 の W による分解：B1 = W⁴·(W⁴ 係数) + W²·(W² 係数) + (W⁰ 部分)。 -/
theorem defectRemainderCoeffB1_eq {g g' : ℝ → ℝ} {r W : ℝ} :
    defectRemainderCoeffB1 g g' r W
      = W ^ 4 * defectRemainderCoeffB1W4 g g' r
        + W ^ 2 * defectRemainderCoeffB1W2 g g' r
        + defectRemainderCoeffB1W0 g g' r := by
  unfold defectRemainderCoeffB1 defectRemainderCoeffB1W4 defectRemainderCoeffB1W2
    defectRemainderCoeffB1W0
  ring

/-- C1 の極端版：2(3r³ + 3r²r₊ − 7r·r₊² + 3r₊³)/(r−r₊)³。 -/
theorem defectRemainderCoeffC1_extremal {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffC1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) r
      = 2 * (3 * r ^ 3 + 3 * r ^ 2 * rp - 7 * r * rp ^ 2 + 3 * rp ^ 3)
        / (r - rp) ^ 3 := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [defectRemainderCoeffC1, rnLogDeriv_extremal, rnLogDeriv',
    rnLogDeriv'']
  field_simp
  ring

/-- C2 の極端版：−2(r² + r·r₊ − r₊²)/(r−r₊)²。 -/
theorem defectRemainderCoeffC2_extremal {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffC2 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r
      = -2 * (r ^ 2 + r * rp - rp ^ 2) / (r - rp) ^ 2 := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [defectRemainderCoeffC2, rnLogDeriv_extremal, rnLogDeriv']
  field_simp
  ring

/-- C3 の極端版：2(2r−r₊)/(r−r₊)。 -/
theorem defectRemainderCoeffC3_extremal {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffC3 (rnLogDeriv rp rp) r
      = 2 * (2 * r - rp) / (r - rp) := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [defectRemainderCoeffC3, rnLogDeriv_extremal]
  field_simp
  ring

/-- B1 の W⁴ 係数の極端版：Q/(r−r₊)²。 -/
theorem defectRemainderCoeffB1W4_extremal {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffB1W4 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r
      = defectRemainderQuadCoeff r rp / (r - rp) ^ 2 := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [defectRemainderCoeffB1W4, defectRemainderQuadCoeff, rnLogDeriv_extremal,
    rnLogDeriv']
  field_simp
  ring

/-- B1 の W² 係数の極端版：W⁴ 係数の −2 倍、すなわち −2Q/(r−r₊)²。 -/
theorem defectRemainderCoeffB1W2_extremal {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffB1W2 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r
      = -2 * defectRemainderQuadCoeff r rp / (r - rp) ^ 2 := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [defectRemainderCoeffB1W2, defectRemainderQuadCoeff,
    rnLogDeriv_extremal, rnLogDeriv']
  field_simp
  ring

/-- B1 の W⁰ 部分の極端版：(−3r⁴ + r²r₊² + Q)/(r−r₊)²。 -/
theorem defectRemainderCoeffB1W0_extremal {rp r : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffB1W0 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r
      = (-3 * r ^ 4 + r ^ 2 * rp ^ 2 + defectRemainderQuadCoeff r rp)
        / (r - rp) ^ 2 := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  simp only [defectRemainderCoeffB1W0, defectRemainderQuadCoeff, rnLogDeriv_extremal,
    rnLogDeriv']
  field_simp
  ring

/-- B1 の極端版（一般の W）：(Q·(W⁴ − 2W²) + (−3r⁴ + r²r₊² + Q))/(r−r₊)²。
    W⁴ 係数と W² 係数は −2 倍の関係にある。三ピースの極端版を組み立てる。 -/
theorem defectRemainderCoeffB1_extremal {rp r W : ℝ} (hr : r ≠ 0) (hrp : r ≠ rp) :
    defectRemainderCoeffB1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r W
      = (defectRemainderQuadCoeff r rp * (W ^ 4 - 2 * W ^ 2)
          + (-3 * r ^ 4 + r ^ 2 * rp ^ 2 + defectRemainderQuadCoeff r rp))
        / (r - rp) ^ 2 := by
  have h1 : r - rp ≠ 0 := sub_ne_zero.mpr hrp
  rw [defectRemainderCoeffB1_eq,
    defectRemainderCoeffB1W4_extremal hr hrp,
    defectRemainderCoeffB1W2_extremal hr hrp,
    defectRemainderCoeffB1W0_extremal hr hrp]
  field_simp
  ring

/-- B1 の極端版（W = 0）：(−3r⁴ + r²r₊² + Q)/(r−r₊)²。分子は
    r についてきれいな因数分解を持たない（sympy で確認）。 -/
theorem defectRemainderCoeffB1_extremal_at_zero {rp r : ℝ} (hr : r ≠ 0)
    (hrp : r ≠ rp) :
    defectRemainderCoeffB1 (rnLogDeriv rp rp) (rnLogDeriv' rp rp) r 0
      = (-3 * r ^ 4 + r ^ 2 * rp ^ 2 + defectRemainderQuadCoeff r rp)
        / (r - rp) ^ 2 := by
  rw [defectRemainderCoeffB1_extremal hr hrp]
  simp

/-- 残余 R の極端 RN 版：四項の係数をすべて閉形で書いたもの。 -/
theorem defectSourceRemainder_extremal {F : WedgeFields} {rp u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) :
    defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u v
      = Dv F.r u v * (F.Om u v / (F.r u v) ^ 5)
          * ((defectRemainderQuadCoeff (F.r u v) rp
              * ((F.W u v) ^ 4 - 2 * (F.W u v) ^ 2)
              + (-3 * (F.r u v) ^ 4 + (F.r u v) ^ 2 * rp ^ 2
                + defectRemainderQuadCoeff (F.r u v) rp))
            / (F.r u v - rp) ^ 2)
        + (Dv F.r u v) ^ 2 * (-(Du F.r u v) / (F.r u v) ^ 3)
          * (2 * (3 * (F.r u v) ^ 3 + 3 * (F.r u v) ^ 2 * rp
              - 7 * (F.r u v) * rp ^ 2 + 3 * rp ^ 3) / (F.r u v - rp) ^ 3)
        + Dv F.W u v * (2 * F.Om u v * F.W u v * (1 - (F.W u v) ^ 2)
          * (2 * (2 * F.r u v - rp) / (F.r u v - rp)) / (F.r u v) ^ 4)
        + (Dv F.W u v) ^ 2 * (2 * Du F.r u v / (F.r u v) ^ 3)
          * (-2 * ((F.r u v) ^ 2 + F.r u v * rp - rp ^ 2)
            / (F.r u v - rp) ^ 2) := by
  rw [defectSourceRemainder_eq_coeffs,
    defectRemainderCoeffB1_extremal hr hrp,
    defectRemainderCoeffC1_extremal hr hrp,
    defectRemainderCoeffC2_extremal hr hrp,
    defectRemainderCoeffC3_extremal hr hrp]

/-- 残余 R の極端 RN 版（W = 0）：Dv W の項が落ち、三項だけが残る。 -/
theorem defectSourceRemainder_extremal_of_W_eq_zero {F : WedgeFields} {rp u v : ℝ}
    (hr : F.r u v ≠ 0) (hrp : F.r u v ≠ rp) (hW : F.W u v = 0) :
    defectSourceRemainder F (rnLogDeriv rp rp) (rnLogDeriv' rp rp)
        (rnLogDeriv'' rp rp) u v
      = Dv F.r u v * (F.Om u v / (F.r u v) ^ 5)
          * ((-3 * (F.r u v) ^ 4 + (F.r u v) ^ 2 * rp ^ 2
              + defectRemainderQuadCoeff (F.r u v) rp)
            / (F.r u v - rp) ^ 2)
        + (Dv F.r u v) ^ 2 * (-(Du F.r u v) / (F.r u v) ^ 3)
          * (2 * (3 * (F.r u v) ^ 3 + 3 * (F.r u v) ^ 2 * rp
              - 7 * (F.r u v) * rp ^ 2 + 3 * rp ^ 3) / (F.r u v - rp) ^ 3)
        + (Dv F.W u v) ^ 2 * (2 * Du F.r u v / (F.r u v) ^ 3)
          * (-2 * ((F.r u v) ^ 2 + F.r u v * rp - rp ^ 2)
            / (F.r u v - rp) ^ 2) := by
  rw [defectSourceRemainder_extremal hr hrp, hW]
  simp

end CFT.WedgeDefectRemainderExtremal
