/-
  命題集 `LEAN_GAP_TREES.md` 4-7(一意性)の組み立て 第 2 段:くさびの 2 つの解は一致する(2026-11-18)

  F、G をくさびの発展方程式(`CFT.Wedge.WedgeEvolutionEqs`)の解で、同じ特性データ(`HasWedgeData`)を持つとする。
  長方形 [0,a]×[0,b] の上で、両方の解が
    |Ω|, |W|, |r_u|, |r_v|, |Ω_u|, |Ω_v| ≤ B、 r ≥ m > 0、 Ω ≥ m > 0
  をみたし、C² 級(`C2`)なら、長方形の上で F = G。

  方法:右辺の差が「値と 1 階微分の差」で抑えられること(リプシッツ性)を、式の組み立てに沿って示す。
  * `Pt`:右辺に出てくる 7 個の量 (Ω, W, r_u, r_v, r, Ω_u, Ω_v)。`Good B m p`:上の評価。`pdist`:差の絶対値の和。
  * `UL B m e`:e は Good な点の上で有界かつリプシッツ(定数は B と m だけで決まる)。
    `UL_const`、`UL_var`、`UL_invr`、`UL_invOm`(1/r、1/Ω)、`UL_add`、`UL_sub`、`UL_mul`、`UL_congr`。
  * `UL_rhsR`、`UL_rhsOm`、`UL_rhsW`:3 本の右辺はすべて UL(Ω の式の r_uv は r の式で置き換える)。
  * `C2`:正則性(連続性と、混合偏微分の交換を含む HasDerivAt)。`C2.sub`、`Du_sub`、`Dv_sub`、`Duv_sub`:差も C2 で、微分は差の微分。
  * `wedge_uniqueness`:主定理。差 (δr, δΩ, δW) が `CharacteristicUniqueness.char_uniqueness` の条件をみたす。
  定数 B、m の存在(連続性とコンパクト性から出る部分)は第 3 段で扱う。
-/
import CFT.Foundations.CharacteristicUniqueness

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

/-! ### 正則性と差 -/

/-- C² 級(連続性と、混合偏微分の交換を含む偏微分の存在) -/
structure C2 (x : ℝ → ℝ → ℝ) : Prop where
  cont : Continuous (Function.uncurry x)
  cont_u : Continuous (Function.uncurry (Du x))
  cont_v : Continuous (Function.uncurry (Dv x))
  cont_uv : Continuous (Function.uncurry (Duv x))
  du : ∀ u v, HasDerivAt (fun t => x t v) (Du x u v) u
  dv : ∀ u v, HasDerivAt (fun s => x u s) (Dv x u v) v
  duv_u : ∀ u v, HasDerivAt (fun t => Dv x t v) (Duv x u v) u
  duv_v : ∀ u v, HasDerivAt (fun s => Du x u s) (Duv x u v) v

variable {x y : ℝ → ℝ → ℝ}

theorem Du_sub (hx : C2 x) (hy : C2 y) (u v : ℝ) :
    Du (fun a b => x a b - y a b) u v = Du x u v - Du y u v :=
  ((hx.du u v).sub (hy.du u v)).deriv

theorem Dv_sub (hx : C2 x) (hy : C2 y) (u v : ℝ) :
    Dv (fun a b => x a b - y a b) u v = Dv x u v - Dv y u v :=
  ((hx.dv u v).sub (hy.dv u v)).deriv

theorem Duv_sub (hx : C2 x) (hy : C2 y) (u v : ℝ) :
    Duv (fun a b => x a b - y a b) u v = Duv x u v - Duv y u v := by
  have h : (fun t => deriv (fun s => x t s - y t s) v) = fun t => Dv x t v - Dv y t v := by
    funext t
    exact Dv_sub hx hy t v
  show deriv (fun t => deriv (fun s => x t s - y t s) v) u = _
  rw [h]
  exact ((hx.duv_u u v).sub (hy.duv_u u v)).deriv

theorem C2.sub (hx : C2 x) (hy : C2 y) : C2 (fun a b => x a b - y a b) where
  cont := hx.cont.sub hy.cont
  cont_u := by
    have : Function.uncurry (Du (fun a b => x a b - y a b))
        = fun p => Function.uncurry (Du x) p - Function.uncurry (Du y) p := by
      funext p
      exact Du_sub hx hy p.1 p.2
    rw [this]
    exact hx.cont_u.sub hy.cont_u
  cont_v := by
    have : Function.uncurry (Dv (fun a b => x a b - y a b))
        = fun p => Function.uncurry (Dv x) p - Function.uncurry (Dv y) p := by
      funext p
      exact Dv_sub hx hy p.1 p.2
    rw [this]
    exact hx.cont_v.sub hy.cont_v
  cont_uv := by
    have : Function.uncurry (Duv (fun a b => x a b - y a b))
        = fun p => Function.uncurry (Duv x) p - Function.uncurry (Duv y) p := by
      funext p
      exact Duv_sub hx hy p.1 p.2
    rw [this]
    exact hx.cont_uv.sub hy.cont_uv
  du := fun u v => by
    rw [Du_sub hx hy]
    exact (hx.du u v).sub (hy.du u v)
  dv := fun u v => by
    rw [Dv_sub hx hy]
    exact (hx.dv u v).sub (hy.dv u v)
  duv_u := fun u v => by
    rw [Duv_sub hx hy]
    have : (fun t => Dv (fun a b => x a b - y a b) t v) = fun t => Dv x t v - Dv y t v := by
      funext t
      exact Dv_sub hx hy t v
    rw [this]
    exact (hx.duv_u u v).sub (hy.duv_u u v)
  duv_v := fun u v => by
    rw [Duv_sub hx hy]
    have : (fun s => Du (fun a b => x a b - y a b) u s) = fun s => Du x u s - Du y u s := by
      funext s
      exact Du_sub hx hy u s
    rw [this]
    exact (hx.duv_v u v).sub (hy.duv_v u v)

/-! ### 主定理 -/

/-- 解の、右辺に出てくる 7 個の量 -/
noncomputable def ptOf (F : WedgeFields) (u v : ℝ) : Pt :=
  ⟨F.Om u v, F.W u v, Du F.r u v, Dv F.r u v, F.r u v, Du F.Om u v, Dv F.Om u v⟩

/-- 2 つの解の差 (δr, δΩ, δW) -/
noncomputable def dd (F G : WedgeFields) : Fin 3 → ℝ → ℝ → ℝ :=
  ![fun a b => F.r a b - G.r a b, fun a b => F.Om a b - G.Om a b, fun a b => F.W a b - G.W a b]

theorem wedge_uniqueness (F G : WedgeFields) (eF : WedgeEvolutionEqs F) (eG : WedgeEvolutionEqs G)
    (dF : HasWedgeData F) (dG : HasWedgeData G)
    (rFr : C2 F.r) (rFO : C2 F.Om) (rFW : C2 F.W)
    (rGr : C2 G.r) (rGO : C2 G.Om) (rGW : C2 G.W)
    {a b B m : ℝ} (hm : 0 < m)
    (hgood : ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      Good B m (ptOf F u v) ∧ Good B m (ptOf G u v)) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      F.r u v = G.r u v ∧ F.Om u v = G.Om u v ∧ F.W u v = G.W u v := by
  obtain ⟨ΛR, hRn, hR⟩ := UL_rhsR (B := B) hm
  obtain ⟨ΛO, hOn, hO⟩ := UL_rhsOm (B := B) hm
  obtain ⟨ΛW, hWn, hW⟩ := UL_rhsW (B := B) hm
  have cr := rFr.sub rGr
  have cO := rFO.sub rGO
  have cW := rFW.sub rGW
  have hC : ∀ i, C2 (dd F G i) := by
    intro i
    fin_cases i
    · exact cr
    · exact cO
    · exact cW
  -- 差の和
  have hS : ∀ u v, ∑ j, (|dd F G j u v| + |Du (dd F G j) u v| + |Dv (dd F G j) u v|)
      = (|F.r u v - G.r u v| + |Du F.r u v - Du G.r u v| + |Dv F.r u v - Dv G.r u v|)
        + (|F.Om u v - G.Om u v| + |Du F.Om u v - Du G.Om u v| + |Dv F.Om u v - Dv G.Om u v|)
        + (|F.W u v - G.W u v| + |Du F.W u v - Du G.W u v| + |Dv F.W u v - Dv G.W u v|) := by
    intro u v
    rw [Fin.sum_univ_three]
    simp only [dd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [Du_sub rFr rGr, Dv_sub rFr rGr, Du_sub rFO rGO, Dv_sub rFO rGO, Du_sub rFW rGW,
      Dv_sub rFW rGW]
  have hpd : ∀ u v, pdist (ptOf F u v) (ptOf G u v)
      ≤ ∑ j, (|dd F G j u v| + |Du (dd F G j) u v| + |Dv (dd F G j) u v|) := by
    intro u v
    rw [hS]
    simp only [pdist, ptOf]
    have := abs_nonneg (Du F.W u v - Du G.W u v)
    have := abs_nonneg (Dv F.W u v - Dv G.W u v)
    linarith
  have hSn : ∀ u v, 0 ≤ ∑ j, (|dd F G j u v| + |Du (dd F G j) u v| + |Dv (dd F G j) u v|) :=
    fun u v => Finset.sum_nonneg (fun j _ => by positivity)
  have key := CFT.CharUniqueness.char_uniqueness (n := 3) (a := a) (b := b)
    (L := ΛR + ΛO + ΛW) (by linarith) (dd F G)
    (fun i u => by
      fin_cases i <;> simp only [dd, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk]
      · rw [(dF.1 u).1, (dG.1 u).1, sub_self]
      · rw [(dF.1 u).2.1, (dG.1 u).2.1, sub_self]
      · rw [(dF.1 u).2.2, (dG.1 u).2.2, sub_self])
    (fun i v => by
      fin_cases i <;> simp only [dd, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk]
      · rw [(dF.2 v).1, (dG.2 v).1, sub_self]
      · rw [(dF.2 v).2.1, (dG.2 v).2.1, sub_self]
      · rw [(dF.2 v).2.2, (dG.2 v).2.2, sub_self])
    (fun i => (hC i).cont) (fun i => (hC i).cont_u) (fun i => (hC i).cont_v)
    (fun i => (hC i).cont_uv)
    (fun i u _ v _ => (hC i).dv u v) (fun i u _ v _ => (hC i).duv_u u v)
    (fun i u _ v _ => (hC i).duv_v u v)
    (fun i u hu v hv => by
      obtain ⟨gF, gG⟩ := hgood u hu v hv
      have hp := hpd u v
      have hs := hSn u v
      have lift : ∀ Λ : ℝ, 0 ≤ Λ → Λ ≤ ΛR + ΛO + ΛW →
          Λ * pdist (ptOf F u v) (ptOf G u v)
            ≤ (ΛR + ΛO + ΛW) * ∑ j, (|dd F G j u v| + |Du (dd F G j) u v| + |Dv (dd F G j) u v|) :=
        fun Λ h0 h1 => mul_le_mul h1 hp (pdist_nonneg _ _) (by linarith)
      fin_cases i
      · show |Duv (fun a b => F.r a b - G.r a b) u v| ≤ _
        rw [Duv_sub rFr rGr, (eF u v).1, (eG u v).1]
        exact (hR _ _ gF gG).2.2.trans (lift ΛR hRn (by linarith))
      · show |Duv (fun a b => F.Om a b - G.Om a b) u v| ≤ _
        rw [Duv_sub rFO rGO, (eF u v).2.1, (eG u v).2.1, (eF u v).1, (eG u v).1]
        exact (hO _ _ gF gG).2.2.trans (lift ΛO hOn (by linarith))
      · show |Duv (fun a b => F.W a b - G.W a b) u v| ≤ _
        rw [Duv_sub rFW rGW, (eF u v).2.2, (eG u v).2.2]
        exact (hW _ _ gF gG).2.2.trans (lift ΛW hWn (by linarith)))
  intro u hu v hv
  have k0 := key 0 u hu v hv
  have k1 := key 1 u hu v hv
  have k2 := key 2 u hu v hv
  simp only [dd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at k0 k1 k2
  exact ⟨sub_eq_zero.mp k0, sub_eq_zero.mp k1, sub_eq_zero.mp k2⟩

end CFT.WedgeUniq
