/-
  α-VII.8(Z28-f):カイラリティと domain wall — 壁を横切る座標がどの空間にあるか

  A. Jackiw–Rebbi(壁を横切る座標 y の一次元の問題、一般論):
    * jr_unique:f′ = −m f の解は f(y) = f(0)·exp(M(0) − M(y))(M′ = m)だけ(ゼロモードは一次元)
    * kink_plus, kink_minus:m(y) = sinh y/cosh y(−1 から +1 への跳び)で、
      二つのカイラリティのゼロモードは f₊ = 1/cosh y(f′ = −m f)と f₋ = cosh y(f′ = +m f)
    * norm_plus:∫_{−R}^{R} f₊² = 2 sinh R/cosh R < 2(R によらず有界:規格化できる)
    * norm_minus:∫_{−R}^{R} f₋² ≥ 2R(発散:規格化できない)
      → 符号の跳び一つにつき、規格化できるカイラルなゼロモードがちょうど一つ。局在したモードは
        y 以外の座標の関数で、y が時空の座標なら一次元低い時空(ダンベルの首 s なら 2+1 次元)の場になる。
  B. 案 1′・2:Q の赤道を壁とする場合(壁を横切る座標は質量殻の上)
    * shell_unit:U(p) = (m − iσ·p)/E の四元数 (m/E, −p/E) は単位(Q-球面 S³ の点)
    * shell_sign:Re U = m/E の符号は m の符号(北半球 m > 0、南半球 m < 0)
    * shell_equator:Re U = 0 ⇔ m = 0(赤道 = 質量ゼロ)
    * shell_celestial:m を固定して |p| → ∞ で Re U → 0(赤道は質量殻 H³ の無限遠の球面、光的な方向)
      → 壁を横切る座標 cos χ = m/E は運動量(質量殻)の座標で、時空の外にある。
    * helicity_chern:赤道 S² の上で、ヘリシティ h = ±1/2 の線束の Chern 数は 2h = ±1(chern_eq_two_q)、
      質量のある状態(両方のヘリシティ)の和は 0
    * chiral_protected:半球(可縮)まで延びる束の Chern 数は 0(外部定理:可縮な空間の上の束は自明)
      ⇒ 一つのカイラリティだけの束は半球に延びない:単独のカイラルなフェルミオンは質量を持てない
    * conjugate_branch:16 の重みの電荷をすべて反転したものは、反対のカイラリティ(マイナスが奇数個)の
      重み 16̄ の電荷と一致(S⁹ の固有値 ±9/2 の二つの枝 = 16 と 16̄、Bär の対応は外部定理)
  結論:案 1(首)は壁の座標が時空の中にあるので 4 次元の物質場にならない。案 1′・2(Q の赤道)は
  壁の座標が質量殻にあり時空の外で、カイラリティは赤道の Chern 数として位相的に守られる。
  ただし S⁹ の最低モードの質量は ±9/2(1/R の単位)で 0 でなく、赤道ではなく半球の内側にある。
  質量ゼロであること自体は、この幾何からは導かれない(Witten の no-go と整合)。
-/
import CFT.Basic
import CFT.AlphaVII_Bundle
import CFT.AlphaVII_SO10
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open Real Filter Topology

namespace CFT.Chirality

/-! ### A. Jackiw–Rebbi -/

/-- ゼロモードの一意性:f′ = −m f、M′ = m なら f(y) = f(0)·exp(M(0) − M(y)) -/
theorem jr_unique (m M f : ℝ → ℝ) (hM : ∀ y, HasDerivAt M (m y) y)
    (hf : ∀ y, HasDerivAt f (-(m y) * f y) y) (y : ℝ) : f y = f 0 * exp (M 0 - M y) := by
  have hg : ∀ x, HasDerivAt (fun x => f x * exp (M x)) 0 x := by
    intro x
    have := (hf x).mul ((hM x).exp)
    convert this using 1; ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) y 0
  simp only at hc
  have he : exp (M y) ≠ 0 := (exp_pos _).ne'
  rw [exp_sub]
  field_simp
  linarith [hc]

/-- m = sinh/cosh で f₊ = 1/cosh は f′ = −m f -/
theorem kink_plus (y : ℝ) :
    HasDerivAt (fun x => 1 / cosh x) (-(sinh y / cosh y) * (1 / cosh y)) y := by
  have hc := (cosh_pos y).ne'
  have := (hasDerivAt_cosh y).inv hc
  convert this using 1
  · funext x; simp
  · field_simp; left; ring

/-- f₋ = cosh は f′ = +m f -/
theorem kink_minus (y : ℝ) : HasDerivAt cosh ((sinh y / cosh y) * cosh y) y := by
  have hc := (cosh_pos y).ne'
  convert hasDerivAt_cosh y using 1; field_simp

theorem tanh_deriv (y : ℝ) : HasDerivAt (fun x => sinh x / cosh x) ((1 / cosh y) ^ 2) y := by
  have hc := (cosh_pos y).ne'
  have := (hasDerivAt_sinh y).div (hasDerivAt_cosh y) hc
  convert this using 1
  field_simp; nlinarith [cosh_sq y]

/-- ∫_{−R}^{R} f₊² = 2 sinh R/cosh R -/
theorem norm_plus (R : ℝ) : ∫ y in (-R)..R, (1 / cosh y) ^ 2 = 2 * (sinh R / cosh R) := by
  have hcont : Continuous fun y => (1 / cosh y) ^ 2 :=
    (continuous_const.div continuous_cosh fun x => (cosh_pos x).ne').pow 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => tanh_deriv y)
    (hcont.intervalIntegrable _ _)]
  rw [sinh_neg, cosh_neg]; ring

/-- 有界:2 sinh R/cosh R < 2 -/
theorem norm_plus_lt (R : ℝ) : ∫ y in (-R)..R, (1 / cosh y) ^ 2 < 2 := by
  rw [norm_plus]
  have hc := cosh_pos R
  have : sinh R < cosh R := by
    rw [sinh_eq, cosh_eq]; linarith [exp_pos (-R)]
  have : sinh R / cosh R < 1 := (div_lt_one hc).mpr this
  linarith

/-- 発散:∫_{−R}^{R} f₋² ≥ 2R -/
theorem norm_minus (R : ℝ) (hR : 0 ≤ R) : 2 * R ≤ ∫ y in (-R)..R, cosh y ^ 2 := by
  have h1 : ∫ _y in (-R)..R, (1 : ℝ) = 2 * R := by simp; ring
  rw [← h1]
  apply intervalIntegral.integral_mono_on (by linarith)
    (continuous_const.intervalIntegrable _ _) ((continuous_cosh.pow 2).intervalIntegrable _ _)
  intro x _
  nlinarith [one_le_cosh x]

/-! ### B. Q の赤道(質量殻の上の壁) -/

/-- U(p) の四元数 (m/E, −p/E) は単位 -/
theorem shell_unit (m p1 p2 p3 E : ℝ) (hE : E ^ 2 = m ^ 2 + p1 ^ 2 + p2 ^ 2 + p3 ^ 2) (h0 : E ≠ 0) :
    (m / E) ^ 2 + (p1 / E) ^ 2 + (p2 / E) ^ 2 + (p3 / E) ^ 2 = 1 := by
  field_simp; linarith

theorem shell_sign (m E : ℝ) (hE : 0 < E) : 0 < m / E ↔ 0 < m := div_pos_iff_of_pos_right hE

theorem shell_equator (m E : ℝ) (hE : E ≠ 0) : m / E = 0 ↔ m = 0 := by
  rw [div_eq_zero_iff]; simp [hE]

/-- |p| → ∞ で Re U = m/√(m²+P²) → 0:赤道は質量殻の無限遠(光的な方向の球面) -/
theorem shell_celestial (m : ℝ) :
    Tendsto (fun P : ℝ => m / sqrt (m ^ 2 + P ^ 2)) atTop (𝓝 0) := by
  have hs : Tendsto (fun P : ℝ => sqrt (m ^ 2 + P ^ 2)) atTop atTop := by
    apply tendsto_atTop_mono (fun P => ?_) tendsto_id
    calc P ≤ |P| := le_abs_self P
      _ = sqrt (P ^ 2) := (sqrt_sq_eq_abs P).symm
      _ ≤ sqrt (m ^ 2 + P ^ 2) := sqrt_le_sqrt (by nlinarith [sq_nonneg m])
  exact hs.const_div_atTop m

/-- 赤道 S² のヘリシティの線束:Chern 数は 2h、質量のある状態の和は 0 -/
theorem helicity_chern :
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (2 * (1 / 2 : ℝ)) / 2 * sin θ) = 1 ∧
    (1 / (2 * π)) * ((2 * π) * ∫ θ in (0 : ℝ)..π, (2 * (-1 / 2 : ℝ)) / 2 * sin θ) = -1 ∧
    (2 * (1 / 2 : ℝ)) + 2 * (-1 / 2 : ℝ) = 0 := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [CFT.Bundle.chern_eq_two_q]; norm_num
  · rw [CFT.Bundle.chern_eq_two_q]; norm_num

/-- 半球に延びる束の Chern 数は 0(外部定理 hext)なら、Chern 数 ±1 の束は延びない -/
theorem chiral_protected (Extends : ℝ → Prop) (c1 : ℝ → ℝ)
    (hext : ∀ h, Extends h → c1 h = 0) (hc : c1 (1 / 2) = 1) : ¬ Extends (1 / 2) := by
  intro h; have := hext _ h; rw [hc] at this; norm_num at this

/-- 反対のカイラリティ(マイナスが奇数個)の重み 16̄ -/
def signsBar : List (List ℤ) :=
  (([1, -1].flatMap fun a => [1, -1].flatMap fun b => [1, -1].flatMap fun c =>
    [1, -1].flatMap fun d => [1, -1].map fun e => [a, b, c, d, e])).filter
    (fun l => (l.count (-1)) % 2 == 1)

def negCharges (x : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (-x.1, -x.2.1, -x.2.2.1, -x.2.2.2)

/-- 16̄ の電荷は 16 の電荷の符号を反転したもの(共役表現) -/
theorem conjugate_branch :
    (signsBar.map CFT.SO10.charges).Perm (CFT.SO10.oneGeneration.map negCharges) := by decide

end CFT.Chirality
