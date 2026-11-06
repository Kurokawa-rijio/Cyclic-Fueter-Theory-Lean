/-
  根幹の見直し 1:接合での「跳び」の診断(2026-11-05)

  問い:量子球面(帽子)と相対双曲面(首)は接合で急に変わるのか。答え:変わる。しかもそれは
  今の作用(純粋に磁気的な EYM、W = r′、時間対称な初期データ)の中では避けられない。

  * 運動学:断面 ds² + r(s)²dΩ²。帽子 r = ℓ sin(s/ℓ)(赤道 s = πℓ/2 で r = ℓ、r′ = 0)、首 r = ℓ。
  * 作用:EYM(W = r′)、ハミルトン拘束 hamC(AlphaII_EYM)。
  * 力学(この節の結果):
    (1) 接合では r と r′ は連続(ℓ と 0)だが、r″ は −1/ℓ(帽子)から 0(首)へ跳ぶ。
        空間のスカラー曲率 ³R = 2(1 − r′² − 2rr″)/r² は 6/ℓ² から 2/ℓ² へ跳ぶ(`curvature_jump`)。
        つまり形は C¹ でつながるが、曲がり方(曲率)は不連続。
    (2) エネルギー密度は 3/(2g²ℓ⁴) から 1/(2g²ℓ⁴) へ 3 分の 1 に跳び、半径方向の圧力は
        +1/(2g²ℓ⁴) から −1/(2g²ℓ⁴) へ符号まで変わる(`stress_jump`)。
    (3) 理由:ハミルトン拘束は r″ について 2 次式 K r″² + 2rr″ + (Ku²/(2r²) − u) = 0(u = 1 − r′²)
        (`hamC_quadratic`)。接合の点 (r, r′) = (ℓ, 0) では解はちょうど二つ、r″ = 0(首)と
        r″ = −1/ℓ(帽子)だけ(`junction_two_values`)。二つの枝は判別式 D = ℓ² > 0 で離れているので、
        帽子の枝から首の枝へ移るには r″ が跳ぶしかない。
    (4) したがって帽子と首の厳密解を接合で貼り合わせる限り、r″ は連続(C²)にならない(`no_C2_junction`)。
        一般の C² 解についての主張には ODE の一意性が要り、ここでは形式化していない。
  * 診断(台帳):部分の 5 項目(III.1、III.2、III.9、IV.2 と、それに依存する X.6)はすべて接合に依存する。
    範囲を絞った項目のうち XI.1、XI.3、IX.14 も接合(または接合の位置)に依存する。
  * 指す先:滑らかさを求めるなら、つなぎ方(または作用)を変える必要がある。
-/
import CFT.AlphaII_EYM
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real

namespace CFT.RootJunction

open Real Filter Topology

/-- 断面 ds² + r²dΩ² の空間のスカラー曲率 ³R = 2(1 − r′² − 2rr″)/r² -/
noncomputable def R3 (r r1 r2 : ℝ) : ℝ := 2 * (1 - r1 ^ 2 - 2 * r * r2) / r ^ 2

/-- 【根幹 1】接合で曲率が跳ぶ:帽子の赤道(r = ℓ、r′ = 0、r″ = −1/ℓ)で ³R = 6/ℓ²、首(r″ = 0)で 2/ℓ² -/
theorem curvature_jump (l : ℝ) (hl : l ≠ 0) :
    R3 l 0 (-1 / l) = 6 / l ^ 2 ∧ R3 l 0 0 = 2 / l ^ 2 := by
  unfold R3
  constructor <;> field_simp <;> ring

/-- 【根幹 1】エネルギー密度と半径方向の圧力の跳び:帽子の赤道 ρ = 3/(2g²ℓ⁴)、p_r = 1/(2g²ℓ⁴)、
首 ρ = 1/(2g²ℓ⁴)、p_r = −1/(2g²ℓ⁴) -/
theorem stress_jump (g l : ℝ) (hg : g ≠ 0) (hl : l ≠ 0) :
    CFT.EYM.rho g (cos (π / 2)) (-(sin (π / 2)) / l) (l * sin (π / 2)) = 3 / (2 * g ^ 2 * l ^ 4) ∧
    CFT.EYM.pr g (cos (π / 2)) (-(sin (π / 2)) / l) (l * sin (π / 2)) = 1 / (2 * g ^ 2 * l ^ 4) ∧
    CFT.EYM.rho g 0 0 l = 1 / (2 * g ^ 2 * l ^ 4) ∧ CFT.EYM.pr g 0 0 l = -(1 / (2 * g ^ 2 * l ^ 4)) := by
  have hs : sin (π / 2) ≠ 0 := by rw [sin_pi_div_two]; exact one_ne_zero
  obtain ⟨c1, c2, -⟩ := CFT.EYM.cap_stress g l (π / 2) hg hl hs
  obtain ⟨n1, n2, -⟩ := CFT.EYM.neck_stress g l hg hl
  exact ⟨c1, c2, n1, n2⟩

/-- 【根幹 1】ハミルトン拘束は r″ の 2 次式:K r″² + 2rr″ + (Ku²/(2r²) − u) = 0(u = 1 − r′²) -/
theorem hamC_quadratic (K r0 r1 r2 : ℝ) (hr : r0 ≠ 0) :
    CFT.EYM.hamC K r0 r1 r2 ↔
      K * r2 ^ 2 + 2 * r0 * r2 + (K * (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 2) - (1 - r1 ^ 2)) = 0 := by
  unfold CFT.EYM.hamC
  have hr2 : r0 ^ 2 ≠ 0 := pow_ne_zero 2 hr
  constructor
  · intro h
    have e : K * r2 ^ 2 + 2 * r0 * r2 + (K * (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 2) - (1 - r1 ^ 2))
        = (r0 ^ 2 / 2) * (2 * K * (r2 ^ 2 / r0 ^ 2 + (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 4))
          - 2 * (1 - r1 ^ 2 - 2 * r0 * r2) / r0 ^ 2) := by
      field_simp <;> ring
    rw [e, h, sub_self, mul_zero]
  · intro h
    have e : 2 * K * (r2 ^ 2 / r0 ^ 2 + (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 4)) - 2 * (1 - r1 ^ 2 - 2 * r0 * r2) / r0 ^ 2
        = (2 / r0 ^ 2) * (K * r2 ^ 2 + 2 * r0 * r2 + (K * (1 - r1 ^ 2) ^ 2 / (2 * r0 ^ 2) - (1 - r1 ^ 2))) := by
      field_simp <;> ring
    rw [h, mul_zero] at e
    linarith

/-- 【根幹 1】接合の点 (ℓ, 0) では拘束をみたす r″ はちょうど二つ:0(首)と −1/ℓ(帽子)(K = 2ℓ²) -/
theorem junction_two_values (l r2 : ℝ) (hl : l ≠ 0) :
    CFT.EYM.hamC (2 * l ^ 2) l 0 r2 ↔ r2 = 0 ∨ r2 = -1 / l := by
  rw [hamC_quadratic _ _ _ _ hl]
  have e : 2 * l ^ 2 * r2 ^ 2 + 2 * l * r2 + (2 * l ^ 2 * (1 - 0 ^ 2) ^ 2 / (2 * l ^ 2) - (1 - 0 ^ 2))
      = 2 * l * r2 * (l * r2 + 1) := by
    field_simp <;> ring
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h1
    · left
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (mul_ne_zero two_ne_zero hl)
      · exact h2
    · right
      rw [eq_div_iff hl]
      linear_combination h1
  · rintro (h | h)
    · rw [h]; ring
    · rw [h, show l * (-1 / l) + 1 = 0 by rw [mul_div_assoc', mul_neg, mul_one, neg_div, div_self hl]; ring,
        mul_zero]

/-- 【根幹 1】C² の接合はない:r″ が s₀ で連続で、左(帽子)では r″ = −r/ℓ²、右(首)では r″ = 0、
r(s₀) = ℓ(r は連続)なら矛盾 -/
theorem no_C2_junction (l s0 : ℝ) (hl : l ≠ 0) (r r2 : ℝ → ℝ) (hr : ContinuousAt r s0) (h0 : r s0 = l)
    (hc : ContinuousAt r2 s0) (hleft : ∀ s < s0, r2 s = -(r s / l ^ 2)) (hright : ∀ s > s0, r2 s = 0) :
    False := by
  have hL : Tendsto r2 (𝓝[<] s0) (𝓝 (-(r s0 / l ^ 2))) := by
    have h1 : Tendsto (fun s => -(r s / l ^ 2)) (𝓝[<] s0) (𝓝 (-(r s0 / l ^ 2))) :=
      ((hr.tendsto.div_const (l ^ 2)).neg).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hleft s hs).symm
  have hR : Tendsto r2 (𝓝[>] s0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hright s hs).symm
  have e1 := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hL
  have e2 := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hR
  rw [e2, h0] at e1
  have : l / l ^ 2 = 0 := by linarith
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · exact hl h
  · exact pow_ne_zero 2 hl h

end CFT.RootJunction
