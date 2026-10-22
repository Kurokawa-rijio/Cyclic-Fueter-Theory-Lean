/-
  α-V.4(Z19)の作り直し(2026-10-21 の評価基準:写像を定義し、計量・質量・地平面との関係を導く)

  旧 AlphaV_Gauss は単位法線の成分を数 (r′, z′) で与えて代数で処理していた。ここでは
  * 埋め込み X(s, n) = (r(s) n, z(s)) ∈ ℝ³ × ℝ(n ∈ S²)と、その接ベクトル ∂_sX = (r′n, z′)、
    球面方向 (r t, 0)(t ⊥ n)を定義し
  * embed_exists:|r′| ≤ 1 で r′ が連続なら z(s) = ∫₀^s √(1 − r′²) が埋め込みを与え、r′² + z′² = 1
  * embed_metric:誘導計量は ds² + r²dΩ²(⟨∂_sX, ∂_sX⟩ = 1、⟨(rt, 0), (rt, 0)⟩ = r²|t|²、交差項 0)
  * normal_unit、normal_orth:N = (−z′n, r′) は単位で、すべての接ベクトルに直交
  * normal_unique:すべての接ベクトルに直交する単位ベクトルは ±N だけ(Gauss 写像 s ↦ N は向きを除いて一意)
  * gauss_cos:極角 χ(N と北極 e₄ のなす角)について cos χ = ⟨N, e₄⟩ = r′
  * gauss_sin_mass:時間対称な切り口の Misner–Sharp 質量 2Gm = r(1 − r′²)(|∇r|² = r′²)で sin²χ = 2Gm/r
  * gauss_equator:χ = π/2(cos χ = 0)⇔ r′ = 0 ⇔ 2Gm = r(周縁的捕捉面)
-/
import CFT.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Algebra.BigOperators.Fin

open Real

namespace CFT.GaussMap

/-- ℝ³ の内積 -/
def ip (v w : Fin 3 → ℝ) : ℝ := ∑ i, v i * w i

/-- ℝ⁴ = ℝ³ × ℝ の内積 -/
def ip4 (p q : (Fin 3 → ℝ) × ℝ) : ℝ := ip p.1 q.1 + p.2 * q.2

/-- 埋め込みの点 X(s, n) = (r n, z) -/
def X (r z : ℝ) (n : Fin 3 → ℝ) : (Fin 3 → ℝ) × ℝ := (fun i => r * n i, z)
/-- 動径方向の接ベクトル ∂_sX = (r′ n, z′) -/
def Ts (r1 z1 : ℝ) (n : Fin 3 → ℝ) : (Fin 3 → ℝ) × ℝ := (fun i => r1 * n i, z1)
/-- 球面方向の接ベクトル (r t, 0)(t ⊥ n) -/
def Ta (r : ℝ) (t : Fin 3 → ℝ) : (Fin 3 → ℝ) × ℝ := (fun i => r * t i, 0)
/-- 単位法線 N = (−z′ n, r′) -/
def Nrm (r1 z1 : ℝ) (n : Fin 3 → ℝ) : (Fin 3 → ℝ) × ℝ := (fun i => -z1 * n i, r1)

theorem ip_smul_left (c : ℝ) (v w : Fin 3 → ℝ) : ip (fun i => c * v i) w = c * ip v w := by
  simp only [ip, Finset.mul_sum]; congr 1; ext i; ring

theorem ip_smul_right (c : ℝ) (v w : Fin 3 → ℝ) : ip v (fun i => c * w i) = c * ip v w := by
  simp only [ip, Finset.mul_sum]; congr 1; ext i; ring

theorem ip_comm (v w : Fin 3 → ℝ) : ip v w = ip w v := by
  simp only [ip]; congr 1; ext i; ring

/-- X は s について微分でき、∂_sX = Ts(各成分) -/
theorem X_deriv (r z : ℝ → ℝ) (r1 z1 : ℝ) (s : ℝ) (hr : HasDerivAt r r1 s) (hz : HasDerivAt z z1 s)
    (n : Fin 3 → ℝ) :
    (∀ i, HasDerivAt (fun s => (X (r s) (z s) n).1 i) ((Ts r1 z1 n).1 i) s) ∧
    HasDerivAt (fun s => (X (r s) (z s) n).2) (Ts r1 z1 n).2 s := by
  refine ⟨fun i => ?_, hz⟩
  simpa [X, Ts] using hr.mul_const (n i)

/-- 高さ関数 z(s)=∫₀ˢ√(1−r′(x)²) の導関数と速度恒等式。
    これ単独では profileMap の大域的な単射性・位相的埋め込み性を主張しない。-/
theorem embed_exists (r1 : ℝ → ℝ) (hc : Continuous r1) (hb : ∀ s, r1 s ^ 2 ≤ 1) (s : ℝ) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..s, √(1 - r1 x ^ 2)) (√(1 - r1 s ^ 2)) s ∧
    r1 s ^ 2 + (√(1 - r1 s ^ 2)) ^ 2 = 1 := by
  have hcont : Continuous fun x => √(1 - r1 x ^ 2) := by fun_prop
  refine ⟨intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt, ?_⟩
  rw [Real.sq_sqrt (by linarith [hb s])]; ring

/-- プロフィール曲線の高さ z(s)=∫₀ˢ√(1−r′²)。-/
noncomputable def zProfile (r1 : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..s, √(1 - r1 x ^ 2)

/-- プロフィール写像 X(s,n)=(r(s)n,z(s))。n は単位球面上に制限して使う。-/
noncomputable def profileMap (r r1 : ℝ → ℝ) (p : ℝ × (Fin 3 → ℝ)) : (Fin 3 → ℝ) × ℝ :=
  X (r p.1) (zProfile r1 p.1) p.2

/-- z が狭義単調かつ r が消えなければ、プロフィール写像は単射。
    「局所的な等長浸入データ」と「大域的な単射性」を分離して明示する。-/
theorem profileMap_injective (r r1 : ℝ → ℝ)
    (hz : StrictMono (zProfile r1)) (hr : ∀ s, r s ≠ 0) : Function.Injective (profileMap r r1) := by
  intro p q hpq
  rcases p with ⟨s, n⟩
  rcases q with ⟨t, m⟩
  have hst : s = t := hz.injective (congrArg Prod.snd hpq)
  subst t
  have hvec : (fun i => r s * n i) = (fun i => r s * m i) := congrArg Prod.fst hpq
  have hnm : n = m := by
    funext i
    exact mul_left_cancel₀ (hr s) (congrFun hvec i)
  subst m
  rfl

/-- 誘導計量は ds² + r² dΩ² -/
theorem embed_metric (r r1 z1 : ℝ) (n t t' : Fin 3 → ℝ) (hn : ip n n = 1) (hnt : ip n t = 0)
    (hu : r1 ^ 2 + z1 ^ 2 = 1) :
    ip4 (Ts r1 z1 n) (Ts r1 z1 n) = 1 ∧ ip4 (Ts r1 z1 n) (Ta r t) = 0 ∧
    ip4 (Ta r t) (Ta r t') = r ^ 2 * ip t t' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ip4, Ts, ip_smul_left, ip_smul_right, hn]; linarith
  · simp only [ip4, Ts, Ta, ip_smul_left, ip_smul_right, hnt]; ring
  · simp only [ip4, Ta, ip_smul_left, ip_smul_right]; ring

/-- 微分・誘導計量を一つにまとめたプロフィール定理。
    高さ z の導関数と X の微分、動径方向の単位長、球面方向の計量を同時に接続する。
    これにより「点ごとの代数公式」だけでなく、実際に定義した profileMap の微分と計量を対応させる。-/
theorem profile_immersion_data (r r1 : ℝ → ℝ) (hc : Continuous r1)
    (hb : ∀ u, r1 u ^ 2 ≤ 1) (s : ℝ) (hr : HasDerivAt r (r1 s) s)
    (n t t' : Fin 3 → ℝ) (hn : ip n n = 1) (hnt : ip n t = 0) :
    (∀ i, HasDerivAt (fun u => (profileMap r r1 (u, n)).1 i) (r1 s * n i) s) ∧
    HasDerivAt (fun u => (profileMap r r1 (u, n)).2) (√(1 - r1 s ^ 2)) s ∧
    ip4 (Ts (r1 s) (√(1 - r1 s ^ 2)) n) (Ts (r1 s) (√(1 - r1 s ^ 2)) n) = 1 ∧
    ip4 (Ts (r1 s) (√(1 - r1 s ^ 2)) n) (Ta (r s) t) = 0 ∧
    ip4 (Ta (r s) t) (Ta (r s) t') = (r s) ^ 2 * ip t t' := by
  have hz : HasDerivAt (zProfile r1) (√(1 - r1 s ^ 2)) s := by
    simpa [zProfile] using (embed_exists r1 hc hb s).1
  have hu := (embed_exists r1 hc hb s).2
  have hd := X_deriv r (zProfile r1) (r1 s) (√(1 - r1 s ^ 2)) s hr hz n
  have hm := embed_metric (r s) (r1 s) (√(1 - r1 s ^ 2)) n t t' hn hnt hu
  refine ⟨?_, ?_, hm.1, hm.2.1, hm.2.2⟩
  · intro i
    simpa [profileMap, X, Ts] using hd.1 i
  · simpa [profileMap, X, Ts] using hd.2


/-- N は単位 -/
theorem normal_unit (r1 z1 : ℝ) (n : Fin 3 → ℝ) (hn : ip n n = 1) (hu : r1 ^ 2 + z1 ^ 2 = 1) :
    ip4 (Nrm r1 z1 n) (Nrm r1 z1 n) = 1 := by
  simp only [ip4, Nrm, ip_smul_left, ip_smul_right, hn]; linarith

/-- N はすべての接ベクトルに直交 -/
theorem normal_orth (r r1 z1 : ℝ) (n t : Fin 3 → ℝ) (hn : ip n n = 1) (hnt : ip n t = 0) :
    ip4 (Nrm r1 z1 n) (Ts r1 z1 n) = 0 ∧ ip4 (Nrm r1 z1 n) (Ta r t) = 0 := by
  constructor
  · simp only [ip4, Nrm, Ts, ip_smul_left, ip_smul_right, hn]; ring
  · simp only [ip4, Nrm, Ta, ip_smul_left, ip_smul_right, hnt]; ring

/-- 法線の一意性:すべての接ベクトルに直交する単位ベクトル Y は ±N(r ≠ 0) -/
theorem normal_unique (r r1 z1 : ℝ) (hr : r ≠ 0) (n : Fin 3 → ℝ) (hn : ip n n = 1)
    (hu : r1 ^ 2 + z1 ^ 2 = 1) (Y : (Fin 3 → ℝ) × ℝ) (hY : ip4 Y Y = 1)
    (hs : ip4 Y (Ts r1 z1 n) = 0) (ha : ∀ t, ip n t = 0 → ip4 Y (Ta r t) = 0) :
    Y = Nrm r1 z1 n ∨ Y = (fun i => -(Nrm r1 z1 n).1 i, -(Nrm r1 z1 n).2) := by
  obtain ⟨y, w⟩ := Y
  simp only [ip4] at hY hs ha
  -- y は n に平行:t = y − ⟨y, n⟩ n は n に直交
  set α := ip y n with hα
  let t : Fin 3 → ℝ := fun i => y i - α * n i
  have hnt : ip n t = 0 := by
    have : ip n t = ip n y - α * ip n n := by
      simp only [ip, t, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]; congr 1; congr 1; ext i; ring
    rw [this, hn, ip_comm n y, ← hα]; ring
  have hyt : ip y t = 0 := by
    have := ha t hnt
    simp only [Ta, ip_smul_right, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hr
  have htt : ip t t = 0 := by
    have : ip t t = ip y t - α * ip n t := by
      simp only [ip, t, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]; congr 1; congr 1; ext i; ring
    rw [this, hyt, hnt]; ring
  have ht0 : ∀ i, t i = 0 := by
    intro i
    have hsum : ∑ j, t j ^ 2 = 0 := by simpa [ip, sq] using htt
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (t j))).mp hsum i (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hy : ∀ i, y i = α * n i := fun i => by have := ht0 i; simp only [t] at this; linarith
  have hyy : ip y y = α ^ 2 := by
    have : y = fun i => α * n i := funext hy
    rw [this, ip_smul_left, ip_smul_right, hn]; ring
  have hyn : ip y n = α := rfl
  rw [show ip y (Ts r1 z1 n).1 = r1 * α by simp only [Ts, ip_smul_right, hyn]] at hs
  simp only [Ts] at hs
  rw [hyy] at hY
  -- (α, w) は (r′, z′) に直交する単位ベクトル ⇒ ±(−z′, r′)
  have hl : (w * r1 - α * z1) ^ 2 = 1 := by nlinarith [hs, hY, hu]
  have hαe : α = -(w * r1 - α * z1) * z1 := by nlinarith [hs, hu]
  have hwe : w = (w * r1 - α * z1) * r1 := by nlinarith [hs, hu]
  have hlam : w * r1 - α * z1 = 1 ∨ w * r1 - α * z1 = -1 := by
    have : (w * r1 - α * z1 - 1) * (w * r1 - α * z1 + 1) = 0 := by nlinarith [hl]
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hlam with h | h
  · left
    rw [h] at hαe hwe
    ext i
    · simp only [Nrm]; rw [hy i, hαe]; ring
    · simp only [Nrm]; rw [hwe]; ring
  · right
    rw [h] at hαe hwe
    ext i
    · simp only [Nrm]; rw [hy i, hαe]; ring
    · simp only [Nrm]; rw [hwe]; ring

/-- 北極 e₄ = (0, 1) との内積:cos χ = r′ -/
theorem gauss_cos (r1 z1 : ℝ) (n : Fin 3 → ℝ) :
    ip4 (Nrm r1 z1 n) ((fun _ => 0), 1) = r1 := by
  simp [ip4, Nrm, ip]

/-- Misner–Sharp 質量(時間対称な切り口、|∇r|² = r′²)2Gm = r(1 − r′²) で sin²χ = 1 − cos²χ = 2Gm/r -/
theorem gauss_sin_mass (r r1 z1 G m : ℝ) (hr : r ≠ 0) (hu : r1 ^ 2 + z1 ^ 2 = 1)
    (hm : 2 * G * m = r * (1 - r1 ^ 2)) : 1 - r1 ^ 2 = 2 * G * m / r ∧ z1 ^ 2 = 2 * G * m / r := by
  constructor
  · rw [hm]; field_simp
  · rw [hm]; field_simp; linarith

/-- 赤道 χ = π/2 ⇔ cos χ = r′ = 0 ⇔ 2Gm = r(周縁的捕捉面) -/
theorem gauss_equator (r r1 G m : ℝ) (hr : r ≠ 0) (hm : 2 * G * m = r * (1 - r1 ^ 2)) :
    (r1 = 0 ↔ 2 * G * m = r) := by
  constructor
  · intro h; rw [hm, h]; ring
  · intro h
    have : r * r1 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left hr)

end CFT.GaussMap
