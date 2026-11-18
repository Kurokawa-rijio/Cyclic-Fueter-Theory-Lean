/-
  命題集 `LEAN_GAP_TREES.md` 4-7(一意性)の組み立て 第 2・3 段:くさびの 2 つの解は一致する(2026-11-18)

  長方形 R = [0,a]×[0,b] の上だけで仮定を置く(R の外での値・方程式は使わない)。
  F、G が R の上でくさびの発展方程式(`WedgeEqsOn`)、2 辺の上で同じ特性データ(`WedgeDataOn`)、
  R の上で C² 級(`C2On`。辺の点でも偏微分が存在する)をみたし、R の上で r > 0、Ω > 0 なら、R の上で F = G。

  方法:右辺の差が「値と 1 階微分の差」で抑えられること(リプシッツ性)を、式の組み立てに沿って示す。
  * `Pt`:右辺に出てくる 7 個の量 (Ω, W, r_u, r_v, r, Ω_u, Ω_v)。`Good B m p`:上の評価。`pdist`:差の絶対値の和。
  * `UL B m e`:e は Good な点の上で有界かつリプシッツ(定数は B と m だけで決まる)。
    `UL_const`、`UL_var`、`UL_invr`、`UL_invOm`(1/r、1/Ω)、`UL_add`、`UL_sub`、`UL_mul`、`UL_congr`。
  * `UL_rhsR`、`UL_rhsOm`、`UL_rhsW`:3 本の右辺はすべて UL(Ω の式の r_uv は r の式で置き換える)。
  * `wedge_uniqueness`:評価つきの一意性。差 (δr, δΩ, δW) を `CharacteristicUniqueness.char_uniqueness` に入れる。
  * `wedge_uniqueness_of_pos`:主定理。B、m は連続性とコンパクト性から出る(`WedgeCompactBounds` の
    `exists_abs_bound_of_continuousOn`・`exists_pos_lower_bound_of_continuousOn`)ので、残る仮定は r > 0、Ω > 0。
  * `wedgeEqsOn_of_global`、`wedgeDataOn_of_global`:全平面の `WedgeEvolutionEqs`、`HasWedgeData` からの橋渡し。
-/
import CFT.Foundations.CharacteristicUniqueness
import CFT.Spherical.WedgeEYMSystem
import CFT.Spherical.WedgeCompactBounds

open Real Set CFT.Wedge

namespace CFT.WedgeUniq

/-! ### 有界でリプシッツな式の組み立て -/

/-- 右辺に出てくる 7 個の量 -/
structure Pt where
  Om : ℝ
  W : ℝ
  ru : ℝ
  rv : ℝ
  r : ℝ
  Ou : ℝ
  Ov : ℝ

/-- 解の値の評価 -/
def Good (B m : ℝ) (p : Pt) : Prop :=
  |p.Om| ≤ B ∧ |p.W| ≤ B ∧ |p.ru| ≤ B ∧ |p.rv| ≤ B ∧ |p.Ou| ≤ B ∧ |p.Ov| ≤ B ∧ m ≤ p.r ∧ m ≤ p.Om

/-- 差の絶対値の和 -/
def pdist (p q : Pt) : ℝ :=
  |p.Om - q.Om| + |p.W - q.W| + |p.ru - q.ru| + |p.rv - q.rv| + |p.r - q.r| + |p.Ou - q.Ou|
    + |p.Ov - q.Ov|

theorem pdist_nonneg (p q : Pt) : 0 ≤ pdist p q := by
  unfold pdist
  positivity

theorem abs_add_le' {x y A C : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ C) : |x + y| ≤ A + C := by
  rw [abs_le] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem abs_sub_le' {x y A C : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ C) : |x - y| ≤ A + C := by
  rw [abs_le] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Good な点の上で有界かつリプシッツ -/
def UL (B m : ℝ) (e : Pt → ℝ) : Prop :=
  ∃ Λ, 0 ≤ Λ ∧ ∀ p q, Good B m p → Good B m q →
    |e p| ≤ Λ ∧ |e q| ≤ Λ ∧ |e p - e q| ≤ Λ * pdist p q

theorem UL_congr {B m : ℝ} {e1 e2 : Pt → ℝ} (h : UL B m e1) (he : ∀ p, e1 p = e2 p) :
    UL B m e2 := by
  have : e1 = e2 := funext he
  rw [← this]
  exact h

theorem UL_const (B m c : ℝ) : UL B m (fun _ => c) :=
  ⟨|c|, abs_nonneg c, fun p q _ _ => ⟨le_rfl, le_rfl, by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg c) (pdist_nonneg p q)⟩⟩

theorem UL_var {B m : ℝ} (proj : Pt → ℝ) (hb : ∀ p, Good B m p → |proj p| ≤ B)
    (hd : ∀ p q, |proj p - proj q| ≤ pdist p q) : UL B m proj :=
  ⟨max B 1, le_trans zero_le_one (le_max_right _ _), fun p q hp hq =>
    ⟨(hb p hp).trans (le_max_left _ _), (hb q hq).trans (le_max_left _ _),
      (hd p q).trans (le_mul_of_one_le_left (pdist_nonneg p q) (le_max_right _ _))⟩⟩

theorem pdist_ge (p q : Pt) :
    |p.Om - q.Om| ≤ pdist p q ∧ |p.W - q.W| ≤ pdist p q ∧ |p.ru - q.ru| ≤ pdist p q ∧
      |p.rv - q.rv| ≤ pdist p q ∧ |p.r - q.r| ≤ pdist p q ∧ |p.Ou - q.Ou| ≤ pdist p q ∧
      |p.Ov - q.Ov| ≤ pdist p q := by
  have h1 := abs_nonneg (p.Om - q.Om)
  have h2 := abs_nonneg (p.W - q.W)
  have h3 := abs_nonneg (p.ru - q.ru)
  have h4 := abs_nonneg (p.rv - q.rv)
  have h5 := abs_nonneg (p.r - q.r)
  have h6 := abs_nonneg (p.Ou - q.Ou)
  have h7 := abs_nonneg (p.Ov - q.Ov)
  unfold pdist
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem UL_Om (B m : ℝ) : UL B m Pt.Om := UL_var _ (fun _ hp => hp.1) (fun p q => (pdist_ge p q).1)
theorem UL_W (B m : ℝ) : UL B m Pt.W := UL_var _ (fun _ hp => hp.2.1) (fun p q => (pdist_ge p q).2.1)
theorem UL_ru (B m : ℝ) : UL B m Pt.ru :=
  UL_var _ (fun _ hp => hp.2.2.1) (fun p q => (pdist_ge p q).2.2.1)
theorem UL_rv (B m : ℝ) : UL B m Pt.rv :=
  UL_var _ (fun _ hp => hp.2.2.2.1) (fun p q => (pdist_ge p q).2.2.2.1)
theorem UL_Ou (B m : ℝ) : UL B m Pt.Ou :=
  UL_var _ (fun _ hp => hp.2.2.2.2.1) (fun p q => (pdist_ge p q).2.2.2.2.2.1)
theorem UL_Ov (B m : ℝ) : UL B m Pt.Ov :=
  UL_var _ (fun _ hp => hp.2.2.2.2.2.1) (fun p q => (pdist_ge p q).2.2.2.2.2.2)

/-- 下から m > 0 で抑えられた量の逆数は UL(一般形) -/
theorem UL_inv_of {B m : ℝ} (hm : 0 < m) (proj : Pt → ℝ) (hlow : ∀ p, Good B m p → m ≤ proj p)
    (hd : ∀ p q, |proj p - proj q| ≤ pdist p q) : UL B m (fun p => (proj p)⁻¹) := by
  have hmi : 0 < m⁻¹ := inv_pos.mpr hm
  refine ⟨m⁻¹ + m⁻¹ * m⁻¹, by positivity, fun p q hp hq => ?_⟩
  have hpr := hlow p hp
  have hqr := hlow q hq
  have hp0 : 0 < proj p := hm.trans_le hpr
  have hq0 : 0 < proj q := hm.trans_le hqr
  have i1 : (proj p)⁻¹ ≤ m⁻¹ := by
    have := one_div_le_one_div_of_le hm hpr
    simpa [one_div] using this
  have i2 : (proj q)⁻¹ ≤ m⁻¹ := by
    have := one_div_le_one_div_of_le hm hqr
    simpa [one_div] using this
  have ip : 0 < (proj p)⁻¹ := inv_pos.mpr hp0
  have iq : 0 < (proj q)⁻¹ := inv_pos.mpr hq0
  have a1 : |(proj p)⁻¹| ≤ m⁻¹ := by rw [abs_of_pos ip]; exact i1
  have a2 : |(proj q)⁻¹| ≤ m⁻¹ := by rw [abs_of_pos iq]; exact i2
  have hmm : 0 ≤ m⁻¹ * m⁻¹ := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  have e : (proj p)⁻¹ - (proj q)⁻¹ = (proj q - proj p) * ((proj p)⁻¹ * (proj q)⁻¹) := by
    field_simp
  rw [e, abs_mul]
  have h1 : |proj q - proj p| ≤ pdist p q := by rw [abs_sub_comm]; exact hd p q
  have h2 : |(proj p)⁻¹ * (proj q)⁻¹| ≤ m⁻¹ * m⁻¹ := by
    rw [abs_of_pos (mul_pos ip iq)]
    exact mul_le_mul i1 i2 iq.le hmi.le
  have hd0 := pdist_nonneg p q
  calc |proj q - proj p| * |(proj p)⁻¹ * (proj q)⁻¹| ≤ pdist p q * (m⁻¹ * m⁻¹) :=
        mul_le_mul h1 h2 (abs_nonneg _) hd0
    _ ≤ (m⁻¹ + m⁻¹ * m⁻¹) * pdist p q := by nlinarith [mul_nonneg hmi.le hd0]

theorem UL_invr {B m : ℝ} (hm : 0 < m) : UL B m (fun p => p.r⁻¹) :=
  UL_inv_of hm Pt.r (fun _ hp => hp.2.2.2.2.2.2.1) (fun p q => (pdist_ge p q).2.2.2.2.1)

theorem UL_invOm {B m : ℝ} (hm : 0 < m) : UL B m (fun p => p.Om⁻¹) :=
  UL_inv_of hm Pt.Om (fun _ hp => hp.2.2.2.2.2.2.2) (fun p q => (pdist_ge p q).1)

theorem UL_add {B m : ℝ} {e1 e2 : Pt → ℝ} (h1 : UL B m e1) (h2 : UL B m e2) :
    UL B m (fun p => e1 p + e2 p) := by
  obtain ⟨Λ1, h1n, h1⟩ := h1
  obtain ⟨Λ2, h2n, h2⟩ := h2
  refine ⟨Λ1 + Λ2, by linarith, fun p q hp hq => ?_⟩
  obtain ⟨a1, b1, c1⟩ := h1 p q hp hq
  obtain ⟨a2, b2, c2⟩ := h2 p q hp hq
  refine ⟨abs_add_le' a1 a2, abs_add_le' b1 b2, ?_⟩
  have e : e1 p + e2 p - (e1 q + e2 q) = (e1 p - e1 q) + (e2 p - e2 q) := by ring
  rw [e]
  calc |(e1 p - e1 q) + (e2 p - e2 q)| ≤ Λ1 * pdist p q + Λ2 * pdist p q := abs_add_le' c1 c2
    _ = (Λ1 + Λ2) * pdist p q := by ring

theorem UL_sub {B m : ℝ} {e1 e2 : Pt → ℝ} (h1 : UL B m e1) (h2 : UL B m e2) :
    UL B m (fun p => e1 p - e2 p) := by
  obtain ⟨Λ1, h1n, h1⟩ := h1
  obtain ⟨Λ2, h2n, h2⟩ := h2
  refine ⟨Λ1 + Λ2, by linarith, fun p q hp hq => ?_⟩
  obtain ⟨a1, b1, c1⟩ := h1 p q hp hq
  obtain ⟨a2, b2, c2⟩ := h2 p q hp hq
  refine ⟨abs_sub_le' a1 a2, abs_sub_le' b1 b2, ?_⟩
  have e : e1 p - e2 p - (e1 q - e2 q) = (e1 p - e1 q) - (e2 p - e2 q) := by ring
  rw [e]
  calc |(e1 p - e1 q) - (e2 p - e2 q)| ≤ Λ1 * pdist p q + Λ2 * pdist p q := abs_sub_le' c1 c2
    _ = (Λ1 + Λ2) * pdist p q := by ring

theorem UL_mul {B m : ℝ} {e1 e2 : Pt → ℝ} (h1 : UL B m e1) (h2 : UL B m e2) :
    UL B m (fun p => e1 p * e2 p) := by
  obtain ⟨Λ1, h1n, h1⟩ := h1
  obtain ⟨Λ2, h2n, h2⟩ := h2
  refine ⟨2 * Λ1 * Λ2, by positivity, fun p q hp hq => ?_⟩
  obtain ⟨a1, b1, c1⟩ := h1 p q hp hq
  obtain ⟨a2, b2, c2⟩ := h2 p q hp hq
  have hΛ : 0 ≤ Λ1 * Λ2 := mul_nonneg h1n h2n
  have m1 : |e1 p * e2 p| ≤ Λ1 * Λ2 := by
    rw [abs_mul]; exact mul_le_mul a1 a2 (abs_nonneg _) h1n
  have m2 : |e1 q * e2 q| ≤ Λ1 * Λ2 := by
    rw [abs_mul]; exact mul_le_mul b1 b2 (abs_nonneg _) h1n
  have t1 : |e1 p * (e2 p - e2 q)| ≤ Λ1 * (Λ2 * pdist p q) := by
    rw [abs_mul]; exact mul_le_mul a1 c2 (abs_nonneg _) h1n
  have t2 : |e2 q * (e1 p - e1 q)| ≤ Λ2 * (Λ1 * pdist p q) := by
    rw [abs_mul]; exact mul_le_mul b2 c1 (abs_nonneg _) h2n
  refine ⟨by linarith, by linarith, ?_⟩
  have e : e1 p * e2 p - e1 q * e2 q = e1 p * (e2 p - e2 q) + e2 q * (e1 p - e1 q) := by ring
  rw [e]
  calc |e1 p * (e2 p - e2 q) + e2 q * (e1 p - e1 q)|
      ≤ Λ1 * (Λ2 * pdist p q) + Λ2 * (Λ1 * pdist p q) := abs_add_le' t1 t2
    _ = 2 * Λ1 * Λ2 * pdist p q := by ring

/-! ### くさびの 3 本の右辺 -/

/-- r の式の右辺を点の関数として -/
noncomputable def eR (p : Pt) : ℝ := rhsR p.Om p.W p.ru p.rv p.r

/-- Ω の式の右辺(r_uv は r の式で置き換える) -/
noncomputable def eOm (p : Pt) : ℝ := rhsOm p.Om p.Ou p.Ov (eR p) p.r p.W

/-- W の式の右辺 -/
noncomputable def eW (p : Pt) : ℝ := rhsW p.Om p.W p.r

theorem UL_oneMinusW2 (B m : ℝ) : UL B m (fun p => 1 - p.W * p.W) :=
  UL_sub (UL_const B m 1) (UL_mul (UL_W B m) (UL_W B m))

theorem UL_rhsR {B m : ℝ} (hm : 0 < m) : UL B m eR := by
  have q := UL_mul (UL_oneMinusW2 B m) (UL_oneMinusW2 B m)
  have ir2 := UL_mul (UL_invr (B := B) hm) (UL_invr (B := B) hm)
  have t := UL_sub (UL_mul q ir2) (UL_const B m 1)
  have A := UL_mul (UL_mul (UL_mul (UL_const B m 2⁻¹) (UL_Om B m)) t) (UL_invr (B := B) hm)
  have Bt := UL_mul (UL_mul (UL_ru B m) (UL_rv B m)) (UL_invr (B := B) hm)
  refine UL_congr (UL_sub A Bt) (fun p => ?_)
  simp only [eR, rhsR]
  ring

theorem UL_rhsOm {B m : ℝ} (hm : 0 < m) : UL B m eOm := by
  have q := UL_mul (UL_oneMinusW2 B m) (UL_oneMinusW2 B m)
  have ir2 := UL_mul (UL_invr (B := B) hm) (UL_invr (B := B) hm)
  have t1 := UL_mul (UL_mul (UL_Ou B m) (UL_Ov B m)) (UL_invOm (B := B) hm)
  have t2 := UL_mul (UL_mul (UL_mul (UL_const B m 2) (UL_Om B m)) (UL_rhsR (B := B) hm))
    (UL_invr (B := B) hm)
  have t3 := UL_mul (UL_mul (UL_mul (UL_Om B m) (UL_Om B m)) q) (UL_mul ir2 ir2)
  refine UL_congr (UL_sub (UL_sub t1 t2) t3) (fun p => ?_)
  simp only [eOm, rhsOm]
  ring

theorem UL_rhsW {B m : ℝ} (hm : 0 < m) : UL B m eW := by
  have ir2 := UL_mul (UL_invr (B := B) hm) (UL_invr (B := B) hm)
  have A := UL_mul (UL_mul (UL_mul (UL_mul (UL_const B m 2⁻¹) (UL_Om B m)) (UL_W B m))
    (UL_oneMinusW2 B m)) ir2
  refine UL_congr A (fun p => ?_)
  simp only [eW, rhsW]
  ring

/-! ### 長方形の上の方程式・データ・正則性 -/

open CFT.CharUniqueness CFT.WedgeCompactBounds

/-- 長方形 [0,a]×[0,b] の上の C² 級(微分は `Du`、`Dv`、`Duv`) -/
abbrev C2On (a b : ℝ) (x : ℝ → ℝ → ℝ) : Prop := C2Data a b x (Du x) (Dv x) (Duv x)

/-- 発展方程式を長方形の上だけで課したもの -/
def WedgeEqsOn (a b : ℝ) (F : WedgeFields) : Prop :=
  ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
    Duv F.r u v = rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v)
    ∧ Duv F.Om u v
        = rhsOm (F.Om u v) (Du F.Om u v) (Dv F.Om u v) (Duv F.r u v) (F.r u v) (F.W u v)
    ∧ Duv F.W u v = rhsW (F.Om u v) (F.W u v) (F.r u v)

/-- 特性データを長方形の 2 辺の上だけで課したもの -/
def WedgeDataOn (a b : ℝ) (F : WedgeFields) : Prop :=
  (∀ u ∈ Icc (0:ℝ) a, F.r u 0 = capR u ∧ F.Om u 0 = capOm u ∧ F.W u 0 = capW u)
    ∧ (∀ v ∈ Icc (0:ℝ) b, F.r 0 v = 1 ∧ F.Om 0 v = neckOm v ∧ F.W 0 v = 0)

/-- 全平面の方程式は長方形の上の方程式を含む -/
theorem wedgeEqsOn_of_global {F : WedgeFields} (h : WedgeEvolutionEqs F) (a b : ℝ) :
    WedgeEqsOn a b F := fun u _ v _ => h u v

/-- 全平面のデータは長方形の辺の上のデータを含む -/
theorem wedgeDataOn_of_global {F : WedgeFields} (h : HasWedgeData F) (a b : ℝ) :
    WedgeDataOn a b F := ⟨fun u _ => h.1 u, fun v _ => h.2 v⟩

/-! ### 主定理 -/

/-- 解の、右辺に出てくる 7 個の量 -/
noncomputable def ptOf (F : WedgeFields) (u v : ℝ) : Pt :=
  ⟨F.Om u v, F.W u v, Du F.r u v, Dv F.r u v, F.r u v, Du F.Om u v, Dv F.Om u v⟩

/-- 2 つの解の差 (δr, δΩ, δW) と、その微分 -/
noncomputable def dd (F G : WedgeFields) : Fin 3 → ℝ → ℝ → ℝ :=
  ![fun s t => F.r s t - G.r s t, fun s t => F.Om s t - G.Om s t, fun s t => F.W s t - G.W s t]

noncomputable def ddu (F G : WedgeFields) : Fin 3 → ℝ → ℝ → ℝ :=
  ![fun s t => Du F.r s t - Du G.r s t, fun s t => Du F.Om s t - Du G.Om s t,
    fun s t => Du F.W s t - Du G.W s t]

noncomputable def ddv (F G : WedgeFields) : Fin 3 → ℝ → ℝ → ℝ :=
  ![fun s t => Dv F.r s t - Dv G.r s t, fun s t => Dv F.Om s t - Dv G.Om s t,
    fun s t => Dv F.W s t - Dv G.W s t]

noncomputable def dduv (F G : WedgeFields) : Fin 3 → ℝ → ℝ → ℝ :=
  ![fun s t => Duv F.r s t - Duv G.r s t, fun s t => Duv F.Om s t - Duv G.Om s t,
    fun s t => Duv F.W s t - Duv G.W s t]

/-- 一意性(評価つき):長方形の上で方程式・データ・C² 級をみたす 2 つの解が、
評価 `Good B m`(m > 0)をみたせば、長方形の上で一致する。 -/
theorem wedge_uniqueness (F G : WedgeFields) {a b B m : ℝ}
    (eF : WedgeEqsOn a b F) (eG : WedgeEqsOn a b G)
    (dF : WedgeDataOn a b F) (dG : WedgeDataOn a b G)
    (rFr : C2On a b F.r) (rFO : C2On a b F.Om) (rFW : C2On a b F.W)
    (rGr : C2On a b G.r) (rGO : C2On a b G.Om) (rGW : C2On a b G.W)
    (hm : 0 < m)
    (hgood : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      Good B m (ptOf F u v) ∧ Good B m (ptOf G u v)) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      F.r u v = G.r u v ∧ F.Om u v = G.Om u v ∧ F.W u v = G.W u v := by
  obtain ⟨ΛR, hRn, hR⟩ := UL_rhsR (B := B) hm
  obtain ⟨ΛO, hOn, hO⟩ := UL_rhsOm (B := B) hm
  obtain ⟨ΛW, hWn, hW⟩ := UL_rhsW (B := B) hm
  have hC : ∀ i, C2Data a b (dd F G i) (ddu F G i) (ddv F G i) (dduv F G i) := by
    intro i
    fin_cases i
    · exact rFr.sub rGr
    · exact rFO.sub rGO
    · exact rFW.sub rGW
  have hpd : ∀ u v, pdist (ptOf F u v) (ptOf G u v)
      ≤ ∑ j, (|dd F G j u v| + |ddu F G j u v| + |ddv F G j u v|) := by
    intro u v
    rw [Fin.sum_univ_three]
    simp only [pdist, ptOf, dd, ddu, ddv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    linarith [abs_nonneg (Du F.W u v - Du G.W u v), abs_nonneg (Dv F.W u v - Dv G.W u v)]
  have key := char_uniqueness (n := 3) (a := a) (b := b)
    (L := ΛR + ΛO + ΛW) (by linarith) (dd F G) (ddu F G) (ddv F G) (dduv F G) hC
    (fun i u hu => by
      fin_cases i
      · show F.r u 0 - G.r u 0 = 0
        rw [(dF.1 u hu).1, (dG.1 u hu).1, sub_self]
      · show F.Om u 0 - G.Om u 0 = 0
        rw [(dF.1 u hu).2.1, (dG.1 u hu).2.1, sub_self]
      · show F.W u 0 - G.W u 0 = 0
        rw [(dF.1 u hu).2.2, (dG.1 u hu).2.2, sub_self])
    (fun i v hv => by
      fin_cases i
      · show F.r 0 v - G.r 0 v = 0
        rw [(dF.2 v hv).1, (dG.2 v hv).1, sub_self]
      · show F.Om 0 v - G.Om 0 v = 0
        rw [(dF.2 v hv).2.1, (dG.2 v hv).2.1, sub_self]
      · show F.W 0 v - G.W 0 v = 0
        rw [(dF.2 v hv).2.2, (dG.2 v hv).2.2, sub_self])
    (fun i u hu v hv => by
      obtain ⟨gF, gG⟩ := hgood u hu v hv
      have hp := hpd u v
      have lift : ∀ Λ : ℝ, 0 ≤ Λ → Λ ≤ ΛR + ΛO + ΛW →
          Λ * pdist (ptOf F u v) (ptOf G u v)
            ≤ (ΛR + ΛO + ΛW) * ∑ j, (|dd F G j u v| + |ddu F G j u v| + |ddv F G j u v|) :=
        fun Λ h0 h1 => mul_le_mul h1 hp (pdist_nonneg _ _) (by linarith)
      fin_cases i
      · show |Duv F.r u v - Duv G.r u v| ≤ _
        rw [(eF u hu v hv).1, (eG u hu v hv).1]
        exact (hR _ _ gF gG).2.2.trans (lift ΛR hRn (by linarith))
      · show |Duv F.Om u v - Duv G.Om u v| ≤ _
        rw [(eF u hu v hv).2.1, (eG u hu v hv).2.1, (eF u hu v hv).1, (eG u hu v hv).1]
        exact (hO _ _ gF gG).2.2.trans (lift ΛO hOn (by linarith))
      · show |Duv F.W u v - Duv G.W u v| ≤ _
        rw [(eF u hu v hv).2.2, (eG u hu v hv).2.2]
        exact (hW _ _ gF gG).2.2.trans (lift ΛW hWn (by linarith)))
  intro u hu v hv
  have k0 : F.r u v - G.r u v = 0 := key 0 u hu v hv
  have k1 : F.Om u v - G.Om u v = 0 := key 1 u hu v hv
  have k2 : F.W u v - G.W u v = 0 := key 2 u hu v hv
  exact ⟨sub_eq_zero.mp k0, sub_eq_zero.mp k1, sub_eq_zero.mp k2⟩

/-! ### 第 3 段:定数 B、m は連続性とコンパクト性から出る(`CFT.WedgeCompactBounds` を使う) -/

/-- 主定理:長方形 [0,a]×[0,b] の上で、発展方程式・特性データ・C² 級をみたす 2 つの解が、
そこで r > 0、Ω > 0 なら、長方形の上で一致する(長方形の外については何も仮定しない)。 -/
theorem wedge_uniqueness_of_pos (F G : WedgeFields) {a b : ℝ}
    (eF : WedgeEqsOn a b F) (eG : WedgeEqsOn a b G)
    (dF : WedgeDataOn a b F) (dG : WedgeDataOn a b G)
    (rFr : C2On a b F.r) (rFO : C2On a b F.Om) (rFW : C2On a b F.W)
    (rGr : C2On a b G.r) (rGO : C2On a b G.Om) (rGW : C2On a b G.W)
    (hpos : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      0 < F.r u v ∧ 0 < F.Om u v ∧ 0 < G.r u v ∧ 0 < G.Om u v) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      F.r u v = G.r u v ∧ F.Om u v = G.Om u v ∧ F.W u v = G.W u v := by
  by_cases hne : (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b).Nonempty
  swap
  · intro u hu v hv
    exact absurd ⟨(u, v), Set.mk_mem_prod hu hv⟩ hne
  have hK : IsCompact (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := isCompact_Icc.prod isCompact_Icc
  let S : ℝ × ℝ → ℝ := fun p =>
    |Function.uncurry F.Om p| + |Function.uncurry F.W p| + |Function.uncurry (Du F.r) p|
      + |Function.uncurry (Dv F.r) p| + |Function.uncurry (Du F.Om) p|
      + |Function.uncurry (Dv F.Om) p|
      + (|Function.uncurry G.Om p| + |Function.uncurry G.W p| + |Function.uncurry (Du G.r) p|
      + |Function.uncurry (Dv G.r) p| + |Function.uncurry (Du G.Om) p|
      + |Function.uncurry (Dv G.Om) p|)
  have hS : ContinuousOn S (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) :=
    ((((((rFO.cont.abs.add rFW.cont.abs).add rFr.cont_u.abs).add rFr.cont_v.abs).add
      rFO.cont_u.abs).add rFO.cont_v.abs).add
      (((((rGO.cont.abs.add rGW.cont.abs).add rGr.cont_u.abs).add rGr.cont_v.abs).add
      rGO.cont_u.abs).add rGO.cont_v.abs))
  obtain ⟨B, hB⟩ := exists_abs_bound_of_continuousOn hK hne (f := fun u v => S (u, v))
    (hS.congr (fun p _ => rfl))
  have hpos' : ∀ u v, (u, v) ∈ Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b →
      0 < F.r u v ∧ 0 < F.Om u v ∧ 0 < G.r u v ∧ 0 < G.Om u v := fun u v huv =>
    hpos u (Set.mem_prod.mp huv).1 v (Set.mem_prod.mp huv).2
  obtain ⟨m1, hm1, h1⟩ := exists_pos_lower_bound_of_continuousOn hK hne rFr.cont
    (fun u v huv => (hpos' u v huv).1)
  obtain ⟨m2, hm2, h2⟩ := exists_pos_lower_bound_of_continuousOn hK hne rFO.cont
    (fun u v huv => (hpos' u v huv).2.1)
  obtain ⟨m3, hm3, h3⟩ := exists_pos_lower_bound_of_continuousOn hK hne rGr.cont
    (fun u v huv => (hpos' u v huv).2.2.1)
  obtain ⟨m4, hm4, h4⟩ := exists_pos_lower_bound_of_continuousOn hK hne rGO.cont
    (fun u v huv => (hpos' u v huv).2.2.2)
  have hm : 0 < min (min m1 m2) (min m3 m4) := lt_min (lt_min hm1 hm2) (lt_min hm3 hm4)
  refine wedge_uniqueness F G eF eG dF dG rFr rFO rFW rGr rGO rGW (B := B) hm ?_
  intro u hu v hv
  have huv : (u, v) ∈ Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b := Set.mk_mem_prod hu hv
  have hb := hB u v huv
  have l1 : min (min m1 m2) (min m3 m4) ≤ F.r u v :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (h1 u v huv))
  have l2 : min (min m1 m2) (min m3 m4) ≤ F.Om u v :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (h2 u v huv))
  have l3 : min (min m1 m2) (min m3 m4) ≤ G.r u v :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (h3 u v huv))
  have l4 : min (min m1 m2) (min m3 m4) ≤ G.Om u v :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (h4 u v huv))
  simp only [S, Function.uncurry_apply_pair] at hb
  rw [abs_of_nonneg (by positivity)] at hb
  have := abs_nonneg (F.Om u v)
  have := abs_nonneg (F.W u v)
  have := abs_nonneg (Du F.r u v)
  have := abs_nonneg (Dv F.r u v)
  have := abs_nonneg (Du F.Om u v)
  have := abs_nonneg (Dv F.Om u v)
  have := abs_nonneg (G.Om u v)
  have := abs_nonneg (G.W u v)
  have := abs_nonneg (Du G.r u v)
  have := abs_nonneg (Dv G.r u v)
  have := abs_nonneg (Du G.Om u v)
  have := abs_nonneg (Dv G.Om u v)
  simp only [Good, ptOf]
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, l1, l2⟩,
    ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, l3, l4⟩⟩

end CFT.WedgeUniq
