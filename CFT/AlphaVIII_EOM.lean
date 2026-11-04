/-
  α-VIII.2(Z39, Z40):標準埋め込みで α′ の項が消えることを、作用ではなく運動方程式のレベルで示す

  監査の指摘:作用密度の α′ 項が A = ι(Ω) の上で 0 になっても、A を独立に変分して得るゲージ場の方程式の
  源が消えるとは言えない。ここでは各場の方程式の O(α′) の項を一つずつ扱う。

  ヘテロティック弦の O(α′) の有効作用(Bergshoeff–de Roo 1989。弦の枠、e^{−2φ} は省略)
    S = ∫ √g e^{−2φ}[R + 4(∂φ)² − H²/12 − (α′/8)(Tr F² − tr R(Ω₊)²)]、dH = (α′/4)(tr R₊∧R₊ − Tr F∧F)。
  (外部の事実 BdR):Ω₊ による作用の変分は、O(α′⁰) の運動方程式に比例する(Bergshoeff–de Roo の補題)。
    したがって O(α′) までは Ω₊ を独立な場のように扱ってよく、tr R(Ω₊)² の項の計量方程式への寄与は
    Tr F² の項と同じ形の応力 T(R₊) になる。

  Lean で示すこと(R は関数の可換環、∂_μ は導分、接続は行列値)
  * ゲージ場の方程式:D_μ(w^{μνρσ} F_ρσ) を `ymOp` と書く(w = √g g^{μρ}g^{νσ}、微分は w にもかかる)。
    A = ι(Ω) なら ymOp(A) = ι(ymOp(Ω))(`ym_embed`)、したがって
      ymOp(A) = 0 ⇔ ymOp(Ω) = 0(`ym_embed_iff`)。
    つまりゲージ場の方程式は独立な条件ではなく、Ω₊ の方程式そのもの。BdR の補題により Ω₊ の方程式は
    O(α′) で O(α′⁰) の方程式から従うので、ゲージ場の方程式もこの次数で成り立つ。
  * 計量の方程式の O(α′) の項:T_μν(F) − T_μν(R₊)(T_μν = g^{ρσ} tr(F_μρ F_νσ) − ¼ g_μν tr F²)は
    A = ι(Ω₊) で恒等的に 0(`stress_embed`、`metric_alpha_cancel`)。
  * ディラトンの方程式の O(α′) の項:Tr F² − tr R₊² = 0(AlphaVIII_Embedding `z40_alpha_term_vanishes`)。
  * H の方程式:Bianchi の右辺 tr R₊∧R₊ − Tr F∧F = 0(`gs_rhs_vanishes`)。d(e^{−2φ}⋆H) = 0 には O(α′) の
    項がない。
  結論:標準埋め込みでは、4 つの場の方程式すべてで O(α′) の項が消え、方程式は O(α′⁰) の形に戻る。
  とくに計量の方程式に Yang–Mills の源が残らない。U21′(I) の YM の源(Z40)は、この切り詰めと
  この埋め込みからは運動方程式のレベルでも得られない(障害)。非標準の埋め込みは別の経路。
  適用範囲:O(α′) の打ち切りの範囲。高次の α′ 補正の制御は α-VIII.5 の α′R > 1 の問題として別に残る。
-/
import CFT.AlphaVIII_Embedding

open Matrix

namespace CFT.EmbeddingEOM

open CFT.Embedding

variable {R : Type*} [CommRing R] [Algebra ℚ R] (d : Fin 4 → Derivation ℚ R R)
set_option linter.unusedSectionVars false

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

theorem iota_smul (r : R) (X : Matrix k k R) : iota (m := m) (r • X) = r • iota X := by
  ext (i | i) (j | j) <;> simp [iota]

theorem iota_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix k k R) :
    iota (m := m) (∑ i ∈ s, f i) = ∑ i ∈ s, iota (f i) := by
  ext (i | i) (j | j) <;> simp [iota, Matrix.sum_apply]

theorem iota_zero : iota (m := m) (0 : Matrix k k R) = 0 := by
  ext (i | i) (j | j) <;> simp [iota]

theorem iota_inj (X Y : Matrix k k R) (h : iota (m := m) X = iota Y) : X = Y := by
  ext i j
  have := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) h
  simpa [iota] using this

/-- 共変微分 D_μ X = ∂_μ X + [A_μ, X] -/
def covD {p : Type*} [Fintype p] (A : Fin 4 → Matrix p p R) (μ : Fin 4) (X : Matrix p p R) :
    Matrix p p R :=
  dM d μ X + (A μ * X - X * A μ)

theorem covD_embed (Ω : Fin 4 → Matrix k k R) (μ : Fin 4) (X : Matrix k k R) :
    covD d (fun a => iota (m := m) (Ω a)) μ (iota X) = iota (covD d Ω μ X) := by
  simp only [covD, dM_iota, iota_mul, iota_sub, iota_add]

/-- ゲージ場の方程式の左辺 D_μ(w^{μνρσ} F_ρσ) -/
def ymOp {p : Type*} [Fintype p] (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R)
    (A : Fin 4 → Matrix p p R) (ν : Fin 4) : Matrix p p R :=
  ∑ μ, covD d A μ (∑ ρ, ∑ σ, w μ ν ρ σ • curv d A ρ σ)

/-- 【α-VIII.2】ゲージ場の方程式は埋め込みと可換:ymOp(ιΩ) = ι(ymOp Ω) -/
theorem ym_embed (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) (Ω : Fin 4 → Matrix k k R) (ν : Fin 4) :
    ymOp d w (fun a => iota (m := m) (Ω a)) ν = iota (ymOp d w Ω ν) := by
  simp only [ymOp, curvature_embed, ← iota_smul, ← iota_sum, covD_embed]

/-- 【α-VIII.2】A = ι(Ω) のゲージ場の方程式 ⇔ Ω の方程式(独立な条件ではない) -/
theorem ym_embed_iff (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) (Ω : Fin 4 → Matrix k k R) (ν : Fin 4) :
    ymOp d w (fun a => iota (m := m) (Ω a)) ν = 0 ↔ ymOp d w Ω ν = 0 := by
  rw [ym_embed]
  constructor
  · intro h; exact iota_inj _ _ (h.trans iota_zero.symm)
  · intro h; rw [h, iota_zero]

/-- 応力 T_μν = g^{ρσ} tr(F_μρ F_νσ) − ¼ g_μν g^{αγ}g^{βδ} tr(F_αβ F_γδ) -/
def stress {p : Type*} [Fintype p] (g gi : Fin 4 → Fin 4 → R) (A : Fin 4 → Matrix p p R) (μ ν : Fin 4) : R :=
  ∑ ρ, ∑ σ, gi ρ σ * (curv d A μ ρ * curv d A ν σ).trace - (1 / 4 : ℚ) • (g μ ν * sqDensity d gi A)

theorem sq_embed (gi : Fin 4 → Fin 4 → R) (Ω : Fin 4 → Matrix k k R) :
    sqDensity d gi (fun a => iota (m := m) (Ω a)) = sqDensity d gi Ω := by
  unfold sqDensity
  simp only [pontryagin_match]

/-- 【α-VIII.2】応力は埋め込みで変わらない:T(F(ιΩ)) = T(R(Ω)) -/
theorem stress_embed (g gi : Fin 4 → Fin 4 → R) (Ω : Fin 4 → Matrix k k R) (μ ν : Fin 4) :
    stress d g gi (fun a => iota (m := m) (Ω a)) μ ν = stress d g gi Ω μ ν := by
  unfold stress
  simp only [pontryagin_match, sq_embed]

/-- 【α-VIII.2】計量の方程式の O(α′) の項 c_α(T(F) − T(R₊)) は標準埋め込みで 0 -/
theorem metric_alpha_cancel (g gi : Fin 4 → Fin 4 → R) (cα : R) (Ω : Fin 4 → Matrix k k R) (μ ν : Fin 4) :
    cα * (stress d g gi (fun a => iota (m := m) (Ω a)) μ ν - stress d g gi Ω μ ν) = 0 := by
  rw [stress_embed, sub_self, mul_zero]

/-- 【α-VIII.2】4 つの方程式の O(α′) の項がそろって消える(計量・ディラトン・H の Bianchi・ゲージ場) -/
theorem all_alpha_terms_vanish (g gi : Fin 4 → Fin 4 → R) (w : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R)
    (cα : R) (Ω : Fin 4 → Matrix k k R) :
    (∀ μ ν, cα * (stress d g gi (fun a => iota (m := m) (Ω a)) μ ν - stress d g gi Ω μ ν) = 0) ∧
    cα * (sqDensity d gi (fun a => iota (m := m) (Ω a)) - sqDensity d gi Ω) = 0 ∧
    (∀ μ ν ρ σ, (curv d (fun a => iota (m := m) (Ω a)) μ ν * curv d (fun a => iota (m := m) (Ω a)) ρ σ).trace
      - (curv d Ω μ ν * curv d Ω ρ σ).trace = 0) ∧
    (∀ ν, ymOp d w (fun a => iota (m := m) (Ω a)) ν = 0 ↔ ymOp d w Ω ν = 0) :=
  ⟨fun μ ν => metric_alpha_cancel d g gi cα Ω μ ν, z40_alpha_term_vanishes d gi cα Ω,
    fun μ ν ρ σ => gs_rhs_vanishes d Ω μ ν ρ σ, fun ν => ym_embed_iff d w Ω ν⟩

end CFT.EmbeddingEOM
