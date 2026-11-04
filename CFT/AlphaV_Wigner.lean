/-
  α-V.1 (Z14, Z15):量子半球と質量殻の共形対応、Wigner 回転をスピン接続のホロノミーとして構成する

  Z14(共形対応)
  * g^Q = ½(dχ² + sin²χ dΩ²)、g^R = (2/cos²χ) g^Q、tan χ = sinh ρ(χ = gd ρ)。
    引き戻すと g^R = dρ² + sinh²ρ dΩ²(H³ の計量)(`metric_pullback`)。
  * 境界の対応:gd は [0, ∞) から [0, π/2) への狭義単調な全単射(`gd_strictMono`、`gd_lt`、`gd_surj`)、
    ρ → ∞ で χ → π/2(`boundary_limit`)。H³ の無限遠は半球の赤道 χ = π/2 に移る。
    共形因子は 2/cos²χ = 2cosh²ρ(`conformal_factor`)で、境界で発散する。
  * 測地線:動径方向の測地線(原点を通る)は子午線(大円の弧)に移る(点集合として。助変数は gd で
    単調に付け替わる)。それ以外の測地線は一般に保存されない(共形かつ測地線を保つ写像は相似写像に限る。
    曲率の符号が逆の H³ と S³ の間に相似写像はない。外部の古典的事実)。
  * 固有値問題:保存されるのは共形共変な作用素の絡み合い関係で、スペクトルそのものではない。
    共形 Laplacian(Yamabe 作用素)L_g = −Δ_g + R_g/8 は L_{Ω²g}(Ω^{−1/2}u) = Ω^{−5/2} L_g u、
    Dirac 作用素は D_{Ω²g}(Ω^{−1}ψ) = Ω^{−2} D_g ψ をみたす(n = 3。Hitchin 1974、外部定理。
    条件:Ω が正でなめらか。ここでは Ω² = 2cosh²ρ で ρ ∈ [0, ∞) の上で成り立つ)。
    したがって核(零固有値の解)と、共形重みをつけた解の対応は保存される。H³ の連続スペクトルと、
    半球の(境界条件つきの)離散スペクトルは一致しない。

  Z15(Wigner 回転)
  * 標準ブースト L(p) = (q + σ·p)/s、q = E + m、s² = 2m(E+m)、E² = m² + |p|²。
    L⁻¹ = (q − σ·p)/s(`boost_inv`)、L² = 2(E+m)s⁻²(E + σ·p) = (E + σ·p)/m(`boost_sq`)、det L = 1(`boost_det`)、
    p が実数なら L はエルミート(`boost_herm`)。
  * Wigner 回転 W(Λ, p) = L(Λp)⁻¹ Λ L(p) はユニタリ(`wigner_unitary`)で det W = 1(`wigner_det`)。
    条件 Λ L(p)² Λ† = L(Λp)² は、SL(2,ℂ) が P = (E + σ·p)/m に X ↦ ΛXΛ† で作用すること
    (二重被覆 SL(2,ℂ) → SO⁺(1,3)、標準的事実)の言い換え。
  * 合成則(コサイクル):W(Λ₂Λ₁, p) = W(Λ₂, Λ₁p) W(Λ₁, p)(`wigner_cocycle`)。
    閉じた経路(Λp = p)では W = L(p)⁻¹ΛL(p)、つまり Λ = L W L⁻¹ は小群 SU(2) の元に共役(`loop_conjugate`)。
  * 局所的な接続:L⁻¹ dL(方向 v = ṗ)を Hermite 部分と反 Hermite 部分に分けると、反 Hermite 部分は
    A_W(v) = −iσ·(p×v)/(2m(E+m))(`wigner_connection`、`wigner_AW`)。これは AlphaI_AW の
    a = −1/(2m(E+m))、b = 0(`wigner_coeffs`)と同じ接続(`Av_ev`)。
  * 輸送方程式:静止系での純粋なブーストを積み重ねた運動 g′ = L Z L⁻¹ g(Z エルミート)について
    W(t) = L(p(t))⁻¹ g(t) L(p₀) は W′W† = −A_W(ṗ) をみたす(`transport`)。
    微分は行列の成分ごとの微分として Lean で扱う(`MD`)。
    この線形 ODE の解は一意(Picard–Lindelöf、外部定理)なので、W(t) は A_W の平行移動そのもの。
    経路が閉じると W(1) は大域的なホロノミー = 一周したときの Wigner 回転。
    小さな閉曲線のホロノミーは曲率 F_W(AlphaI_AW の curv_formula、α = −1/(2mE) など)で決まる
    (Ambrose–Singer、外部定理)。
  * 論文 G の点検(Berry、Fueter の接続との関係)
    - A_B = ½(1 − m/E) iσ·(n×dn)(p = |p|n)(`cross_radial`、`berry_half_angle`)。
      A_W = −½(E/m − 1) iσ·(n×dn)(`wigner_half_angle`)。
    - V = ((E+m) − iσ·p)/√(2E(E+m)) は V² = U = (m − iσ·p)/E(`half_rotation_sq`)。
      V は Foldy–Wouthuysen の変換(AlphaV_FW の Û と同じ規格化)の 2 成分の形。
    - 新しく確かめた関係:A_B = V A_F V⁻¹ + V d(V⁻¹)(`berry_fueter_gauge`、`gauge_form`)。
      つまり Fueter 接続 A_F = ½U⁻¹dU と Berry 接続はゲージ同値で、ゲージ変換は FW の半回転 V。
      これは trG_F = trG_B(AlphaI_AW)と整合する。一方 A_W は trG が違うのでどちらともゲージ同値でない
      (`berry_not_gauge_wigner`)。
-/
import CFT.AlphaV
import CFT.AlphaI_AW
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace CFT.Wigner

open Real Filter Topology Matrix CFT.AlphaI_AW
open CFT.AlphaIV (gd)

noncomputable section

/-! ### Z14:共形対応 -/

/-- 引き戻し:g^R = (2/cos²χ)·½(dχ² + sin²χ dΩ²) は χ = gd ρ で dρ² + sinh²ρ dΩ²。
dχ/dρ = 1/cosh ρ、動径の係数 1、角度の係数 sinh²ρ -/
theorem metric_pullback (ρ : ℝ) :
    HasDerivAt gd (1 / cosh ρ) ρ ∧
    (2 / cos (gd ρ) ^ 2) * (1 / 2) * (1 / cosh ρ) ^ 2 = 1 ∧
    (2 / cos (gd ρ) ^ 2) * (1 / 2) * sin (gd ρ) ^ 2 = sinh ρ ^ 2 := by
  have hc : cosh ρ ≠ 0 := (cosh_pos ρ).ne'
  refine ⟨CFT.AlphaIV.gd_deriv ρ, ?_, ?_⟩
  · rw [CFT.AlphaV.cos_gd]; field_simp <;> ring
  · rw [CFT.AlphaV.cos_gd, CFT.AlphaV.sin_gd]; field_simp <;> ring

/-- 共形因子 2/cos²χ = 2cosh²ρ -/
theorem conformal_factor (ρ : ℝ) : 2 / cos (gd ρ) ^ 2 = 2 * cosh ρ ^ 2 := by
  have hc : cosh ρ ≠ 0 := (cosh_pos ρ).ne'
  rw [CFT.AlphaV.cos_gd]; field_simp <;> ring

theorem gd_strictMono : StrictMono gd := arctan_strictMono.comp sinh_strictMono

theorem gd_lt (ρ : ℝ) : gd ρ < π / 2 := arctan_lt_pi_div_two _

theorem gd_nonneg {ρ : ℝ} (h : 0 ≤ ρ) : 0 ≤ gd ρ := by
  have := gd_strictMono.monotone h
  rwa [CFT.AlphaIV.gd_zero] at this

/-- [0, π/2) の各点は [0, ∞) の点の像 -/
theorem gd_surj (χ : ℝ) (h0 : 0 ≤ χ) (h1 : χ < π / 2) : ∃ ρ, 0 ≤ ρ ∧ gd ρ = χ := by
  refine ⟨arsinh (tan χ), arsinh_nonneg_iff.mpr (tan_nonneg_of_nonneg_of_le_pi_div_two h0 h1.le), ?_⟩
  have hpi : 0 < π / 2 := by linarith [Real.pi_pos]
  rw [gd, sinh_arsinh, arctan_tan (by linarith) h1]

/-- 【Z14 境界】ρ → ∞ で χ = gd ρ → π/2(H³ の無限遠 ↦ 半球の赤道) -/
theorem boundary_limit : Tendsto gd atTop (𝓝 (π / 2)) := by
  have hs : Tendsto sinh atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun x hx => self_le_sinh_iff.mpr hx)
      tendsto_id
  exact (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hs

/-! ### Pauli 行列の代数(ℂ 係数) -/

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- 内積 a·b(複素の成分、共役なし) -/
def dotc (a b : Fin 3 → ℂ) : ℂ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- (σ·a)(σ·b) = (a·b) + iσ·(a×b) -/
theorem sd_mul_sd (a b : Fin 3 → ℂ) :
    sd a * sd b = dotc a b • (1 : M2) + Complex.I • sd (crossv a b) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sd, σ, σ1, σ2, σ3, dotc, crossv, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
    | ring1
    | linear_combination (-(a 1 * b 1)) * hI
    | linear_combination (a 1 * b 1) * hI
    | linear_combination (a 2 * b 0 - a 0 * b 2) * hI
    | linear_combination (a 0 * b 2 - a 2 * b 0) * hI

theorem cross_self (p : Fin 3 → ℂ) : crossv p p = 0 := by
  funext k; fin_cases k <;> simp [crossv] <;> ring

theorem sd_zero : sd (0 : Fin 3 → ℂ) = 0 := by simp [sd]

theorem dot_p_cross (p v : Fin 3 → ℂ) : dotc p (crossv p v) = 0 := by
  simp [dotc, crossv] <;> ring

theorem dot_cross_p (p v : Fin 3 → ℂ) : dotc (crossv p v) p = 0 := by
  simp [dotc, crossv] <;> ring

/-- sd は線形 -/
theorem sd_lin (a b : ℂ) (x y : Fin 3 → ℂ) : sd (a • x - b • y) = a • sd x - b • sd y := by
  simp only [sd, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, mul_smul]
  module

theorem sd_cross_cross1 (p v : Fin 3 → ℂ) :
    sd (crossv p (crossv p v)) = dotc p v • sd p - dotc p p • sd v := by
  rw [← sd_lin]; congr 1
  funext k; fin_cases k <;> simp [crossv, dotc] <;> ring

theorem sd_cross_cross2 (p v : Fin 3 → ℂ) :
    sd (crossv (crossv p v) p) = dotc p p • sd v - dotc p v • sd p := by
  rw [← sd_lin]; congr 1
  funext k; fin_cases k <;> simp [crossv, dotc] <;> ring

/-- 方向 v への接続 A(v) = a iσ·(p×v) + b iσ·v -/
def Av (p v : Fin 3 → ℂ) (a b : ℂ) : M2 :=
  (a * Complex.I) • sd (crossv p v) + (b * Complex.I) • sd v

theorem sd_ev (i : Fin 3) : sd (ev i) = σ i := by
  fin_cases i <;> simp [sd, ev, Fin.sum_univ_three, Pi.single_apply]

/-- v = eᵢ のとき AlphaI_AW の Aᵢ と一致 -/
theorem Av_ev (p : Fin 3 → ℂ) (a b : ℂ) (i : Fin 3) : Av p (ev i) a b = A p a b i := by
  simp only [Av, A, sd_ev]

/-! ### Z15:標準ブースト -/

/-- L(p) = s⁻¹((E+m) + σ·p)(si = s⁻¹) -/
def boost (m E si : ℂ) (p : Fin 3 → ℂ) : M2 := si • ((E + m) • (1 : M2) + sd p)

/-- L(p)⁻¹ = s⁻¹((E+m) − σ·p) -/
def boostInv (m E si : ℂ) (p : Fin 3 → ℂ) : M2 := si • ((E + m) • (1 : M2) - sd p)

/-- 方向 v への微分 dL(連鎖律:d(s⁻¹) = −s⁻² ds) -/
def boostD (m E si dE ds : ℂ) (p v : Fin 3 → ℂ) : M2 :=
  si • (dE • (1 : M2) + sd v) - (ds * si ^ 2) • ((E + m) • (1 : M2) + sd p)

section Boost

variable (m E s si : ℂ) (p : Fin 3 → ℂ)
  (hE : E ^ 2 = m ^ 2 + dotc p p) (hs : s ^ 2 = 2 * m * (E + m)) (hsi : s * si = 1)

include hs hsi in
theorem si_sq : si ^ 2 * (2 * m * (E + m)) = 1 := by
  linear_combination (-(si ^ 2)) * hs + (s * si + 1) * hsi

include hE hs hsi in
theorem boost_inv : boostInv m E si p * boost m E si p = 1 ∧ boost m E si p * boostInv m E si p = 1 := by
  have h2 := si_sq m E s si hs hsi
  constructor
  · simp only [boost, boostInv, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, sd_mul_sd, cross_self, sd_zero, smul_zero, add_zero]
    linear_combination (norm := module) (si ^ 2 * hE + h2) • (1 : M2)
  · simp only [boost, boostInv, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, sd_mul_sd, cross_self, sd_zero, smul_zero, add_zero]
    linear_combination (norm := module) (si ^ 2 * hE + h2) • (1 : M2)

include hE in
/-- L² = 2(E+m)s⁻²(E + σ·p)(= (E + σ·p)/m) -/
theorem boost_sq : boost m E si p * boost m E si p = (2 * (E + m) * si ^ 2) • (E • (1 : M2) + sd p) := by
  simp only [boost, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, sd_mul_sd, cross_self, sd_zero, smul_zero, add_zero]
  linear_combination (norm := module) (-(si ^ 2) * hE) • (1 : M2)

include hE hs hsi in
theorem boost_det : (boost m E si p).det = 1 := by
  have h2 := si_sq m E s si hs hsi
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [Matrix.det_fin_two]
  simp only [dotc] at hE
  simp [boost, sd, σ, σ1, σ2, σ3, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination si ^ 2 * hE + h2 + si ^ 2 * p 1 ^ 2 * hI

end Boost

/-! ### 実の運動量でのエルミート性 -/

def ofR (q : Fin 3 → ℝ) : Fin 3 → ℂ := fun k => (q k : ℂ)

def crossr (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

theorem sd_herm (q : Fin 3 → ℝ) : (sd (ofR q))ᴴ = sd (ofR q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ofR, Matrix.conjTranspose_apply, sd, σ, σ1, σ2, σ3, Fin.sum_univ_three, Matrix.add_apply,
      Matrix.smul_apply, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.star_def, Complex.conj_ofReal] <;> ring

theorem cross_ofR (q w : Fin 3 → ℝ) : crossv (ofR q) (ofR w) = ofR (crossr q w) := by
  funext k; fin_cases k <;> simp [crossv, crossr, ofR]

theorem dotc_ofR (q w : Fin 3 → ℝ) :
    dotc (ofR q) (ofR w) = ((q 0 * w 0 + q 1 * w 1 + q 2 * w 2 : ℝ) : ℂ) := by
  simp [dotc, ofR]

theorem boost_herm (m E si : ℝ) (q : Fin 3 → ℝ) :
    (boost m E si (ofR q))ᴴ = boost m E si (ofR q) := by
  simp only [boost, conjTranspose_smul, conjTranspose_add, sd_herm, conjTranspose_one]
  simp [Complex.star_def, Complex.conj_ofReal]

theorem boostInv_herm (m E si : ℝ) (q : Fin 3 → ℝ) :
    (boostInv m E si (ofR q))ᴴ = boostInv m E si (ofR q) := by
  simp only [boostInv, conjTranspose_smul, conjTranspose_sub, sd_herm, conjTranspose_one]
  simp [Complex.star_def, Complex.conj_ofReal]

/-! ### Wigner 回転:ユニタリ性、det、合成則 -/

/-- 【Z15】W = L₂⁻¹ Λ L₁ はユニタリ。条件:L₁、L₂⁻¹ はエルミート、Λ L₁² Λ† = L₂²(p₂ = Λp₁) -/
theorem wigner_unitary (Λ L1 L2 L2i : M2) (h1 : L1ᴴ = L1) (h2 : L2iᴴ = L2i) (hi : L2i * L2 = 1)
    (hi' : L2 * L2i = 1) (hΛ : Λ * (L1 * L1) * Λᴴ = L2 * L2) :
    (L2i * Λ * L1) * (L2i * Λ * L1)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1, h2]
  calc L2i * Λ * L1 * (L1 * (Λᴴ * L2i)) = L2i * (Λ * (L1 * L1) * Λᴴ) * L2i := by noncomm_ring
    _ = L2i * (L2 * L2) * L2i := by rw [hΛ]
    _ = (L2i * L2) * (L2 * L2i) := by noncomm_ring
    _ = 1 := by rw [hi, hi', one_mul]

theorem wigner_det (Λ L1 L2i : M2) (h1 : L1.det = 1) (h2 : L2i.det = 1) (hΛ : Λ.det = 1) :
    (L2i * Λ * L1).det = 1 := by
  simp [Matrix.det_mul, h1, h2, hΛ]

/-- 【Z15 合成則】W(Λ₂Λ₁, p₁) = W(Λ₂, p₂) W(Λ₁, p₁)(p₂ = Λ₁p₁、L₂L₂⁻¹ = 1) -/
theorem wigner_cocycle (L1 L2 L2i L3i Λ1 Λ2 : M2) (h : L2 * L2i = 1) :
    L3i * (Λ2 * Λ1) * L1 = (L3i * Λ2 * L2) * (L2i * Λ1 * L1) := by
  calc L3i * (Λ2 * Λ1) * L1 = L3i * Λ2 * (L2 * L2i) * Λ1 * L1 := by rw [h]; noncomm_ring
    _ = (L3i * Λ2 * L2) * (L2i * Λ1 * L1) := by noncomm_ring

/-- 【Z15 閉じた経路】Λp = p なら Λ = L W L⁻¹(小群 SU(2) の元に共役) -/
theorem loop_conjugate (L Li Λ : M2) (h : L * Li = 1) : L * (Li * Λ * L) * Li = Λ := by
  calc L * (Li * Λ * L) * Li = (L * Li) * Λ * (L * Li) := by noncomm_ring
    _ = Λ := by rw [h, one_mul, mul_one]

/-! ### 局所的な接続:L⁻¹dL の反エルミート部分 -/

/-- 反エルミート部分 ½(Y − Y†) -/
def antiH (Y : M2) : M2 := (1 / 2 : ℂ) • (Y - Yᴴ)

theorem antiH_eq (Hm K : M2) (hH : Hmᴴ = Hm) (hK : Kᴴ = -K) : antiH (Hm + K) = K := by
  simp only [antiH, conjTranspose_add, hH, hK]
  module

/-- 【Z15】L⁻¹ dL = s⁻²(E+m) σ·v − s⁻² dE σ·p + A(v)、A(v) = −s⁻² iσ·(p×v)。
仮定 E dE = p·v、s ds = m dE は E² = m² + |p|²、s² = 2m(E+m) を微分したもの(`E_deriv`、`s_deriv`) -/
theorem wigner_connection (m E s si dE ds : ℂ) (p v : Fin 3 → ℂ)
    (hE : E ^ 2 = m ^ 2 + dotc p p) (hs : s ^ 2 = 2 * m * (E + m)) (hsi : s * si = 1)
    (hdE : E * dE = dotc p v) (hds : s * ds = m * dE) :
    boostInv m E si p * boostD m E si dE ds p v
      = (si ^ 2 * (E + m)) • sd v - (si ^ 2 * dE) • sd p + Av p v (-(si ^ 2)) 0 := by
  have hds' : ds = m * dE * si := by linear_combination si * hds - ds * hsi
  have h2 := si_sq m E s si hs hsi
  simp only [boostInv, boostD, Av, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, sd_mul_sd, cross_self, sd_zero, smul_zero, add_zero]
  linear_combination (norm := module)
    (si ^ 2 * hdE - ds * si ^ 3 * hE - ds * si * h2 - si * hds') • (1 : M2)

/-- 【Z15】実の運動量では反エルミート部分が A_W(v) = −iσ·(p×v)/(2m(E+m)) -/
theorem wigner_AW (m E s si dE ds : ℝ) (q w : Fin 3 → ℝ)
    (hE : E ^ 2 = m ^ 2 + (q 0 * q 0 + q 1 * q 1 + q 2 * q 2)) (hs : s ^ 2 = 2 * m * (E + m))
    (hsi : s * si = 1) (hdE : E * dE = q 0 * w 0 + q 1 * w 1 + q 2 * w 2) (hds : s * ds = m * dE) :
    antiH (boostInv m E si (ofR q) * boostD m E si dE ds (ofR q) (ofR w))
      = Av (ofR q) (ofR w) (-(si ^ 2 : ℂ)) 0 := by
  have hE' : (E : ℂ) ^ 2 = (m : ℂ) ^ 2 + dotc (ofR q) (ofR q) := by
    rw [dotc_ofR]; exact_mod_cast hE
  have hs' : (s : ℂ) ^ 2 = 2 * m * (E + m) := by exact_mod_cast hs
  have hsi' : (s : ℂ) * si = 1 := by exact_mod_cast hsi
  have hdE' : (E : ℂ) * dE = dotc (ofR q) (ofR w) := by rw [dotc_ofR]; exact_mod_cast hdE
  have hds' : (s : ℂ) * ds = m * dE := by exact_mod_cast hds
  rw [wigner_connection m E s si dE ds (ofR q) (ofR w) hE' hs' hsi' hdE' hds']
  apply antiH_eq
  · simp only [conjTranspose_sub, conjTranspose_smul, sd_herm]
    simp [Complex.star_def, Complex.conj_ofReal]
  · simp only [Av, conjTranspose_add, conjTranspose_smul, cross_ofR, sd_herm]
    simp only [zero_mul, star_zero, star_mul', star_neg, star_pow, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I, map_zero, zero_smul, add_zero, neg_zero]
    module

/-- s⁻² = 1/(2m(E+m)):A_W の係数は AlphaI_AW の a = −1/(2m(E+m)) -/
theorem wigner_coeff (m E s si : ℂ) (hs : s ^ 2 = 2 * m * (E + m)) (hsi : s * si = 1)
    (hm : m ≠ 0) (hEm : E + m ≠ 0) : -(si ^ 2) = -1 / (2 * m * (E + m)) := by
  have h2 := si_sq m E s si hs hsi
  have hne : 2 * m * (E + m) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero hm) hEm
  rw [eq_div_iff hne]
  linear_combination -h2

/-! ### 成分ごとの微分と輸送方程式 -/

/-- 行列値の関数の成分ごとの微分 -/
def MD (A : ℝ → M2) (Ad : M2) (t : ℝ) : Prop := ∀ a b, HasDerivAt (fun s => A s a b) (Ad a b) t

theorem MD.mul {A B : ℝ → M2} {Ad Bd : M2} {t : ℝ} (hA : MD A Ad t) (hB : MD B Bd t) :
    MD (fun s => A s * B s) (Ad * B t + A t * Bd) t := by
  intro a b
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]
  have h := ((hA a 0).mul (hB 0 b)).add ((hA a 1).mul (hB 1 b))
  convert h using 1
  ring

theorem MD.const (C : M2) (t : ℝ) : MD (fun _ => C) 0 t := by
  intro a b
  simpa using hasDerivAt_const t (C a b)

theorem MD.unique {A : ℝ → M2} {Ad Ad' : M2} {t : ℝ} (h1 : MD A Ad t) (h2 : MD A Ad' t) : Ad = Ad' := by
  ext a b
  exact (h1 a b).unique (h2 a b)

theorem MD.conjT {A : ℝ → M2} {Ad : M2} {t : ℝ} (h : MD A Ad t) : MD (fun s => (A s)ᴴ) Adᴴ t := by
  intro a b
  simp only [Matrix.conjTranspose_apply]
  exact (h b a).star

/-- ユニタリ性 W W† = 1 を微分すると W′W† + W W′† = 0 -/
theorem unitary_deriv {W : ℝ → M2} {Wd : M2} {t : ℝ} (hU : ∀ s, W s * (W s)ᴴ = 1) (hW : MD W Wd t) :
    Wd * (W t)ᴴ + W t * Wdᴴ = 0 := by
  have h1 := hW.mul hW.conjT
  have h2 : MD (fun s => W s * (W s)ᴴ) 0 t := by
    have e : (fun s => W s * (W s)ᴴ) = fun _ => (1 : M2) := funext hU
    rw [e]; exact MD.const 1 t
  exact MD.unique h1 h2

/-- 逆行列の微分:L⁻¹′ = −L⁻¹ L′ L⁻¹ -/
theorem inv_deriv {L Li : ℝ → M2} {Ld Lid : M2} {t : ℝ} (hinv : ∀ s, Li s * L s = 1)
    (hinv' : L t * Li t = 1) (hL : MD L Ld t) (hLi : MD Li Lid t) : Lid = -(Li t * Ld * Li t) := by
  have h1 := hLi.mul hL
  have h2 : MD (fun s => Li s * L s) 0 t := by
    have e : (fun s => Li s * L s) = fun _ => (1 : M2) := funext hinv
    rw [e]; exact MD.const 1 t
  have h := MD.unique h1 h2
  calc Lid = Lid * (L t * Li t) := by rw [hinv', mul_one]
    _ = (Lid * L t + Li t * Ld) * Li t - Li t * Ld * Li t := by noncomm_ring
    _ = -(Li t * Ld * Li t) := by rw [h]; noncomm_ring

/-- 【Z15 輸送方程式】静止系の純粋なブースト Z(エルミート)を積み重ねた運動 g′ = L Z L⁻¹ g について、
W(s) = L(s)⁻¹ g(s) L₀ は W′ W† = −antiH(L⁻¹ L′)。各 s で W がユニタリであることは `wigner_unitary`
(g(s) L₀² g(s)† = L(s)²、つまり p(s) = g(s) p₀)から従う -/
theorem transport {L Li g : ℝ → M2} {Ld Lid Z L0 : M2} {t : ℝ}
    (hinv : ∀ s, Li s * L s = 1) (hinv' : ∀ s, L s * Li s = 1)
    (hLh : ∀ s, (Li s)ᴴ = Li s) (hL0 : L0ᴴ = L0)
    (hshell : ∀ s, g s * (L0 * L0) * (g s)ᴴ = L s * L s)
    (hL : MD L Ld t) (hLi : MD Li Lid t) (hg : MD g (L t * Z * Li t * g t) t) (hZ : Zᴴ = Z) :
    ∃ Wd, MD (fun s => Li s * g s * L0) Wd t ∧
      Wd * (Li t * g t * L0)ᴴ = -antiH (Li t * Ld) := by
  set W : ℝ → M2 := fun s => Li s * g s * L0 with hWdef
  have hU : ∀ s, W s * (W s)ᴴ = 1 := fun s =>
    wigner_unitary (g s) L0 (L s) (Li s) hL0 (hLh s) (hinv s) (hinv' s) (hshell s)
  have hD := (hLi.mul hg).mul (MD.const L0 t)
  refine ⟨_, hD, ?_⟩
  have hLid := inv_deriv hinv (hinv' t) hL hLi
  have hWd : (Lid * g t + Li t * (L t * Z * Li t * g t)) * L0 + Li t * g t * 0
      = -(Li t * Ld) * W t + Z * W t := by
    calc (Lid * g t + Li t * (L t * Z * Li t * g t)) * L0 + Li t * g t * 0
        = -(Li t * Ld * Li t) * g t * L0 + Li t * (L t * Z * Li t * g t) * L0 := by
          rw [hLid]; noncomm_ring
      _ = -(Li t * Ld) * (Li t * g t * L0) + (Li t * L t) * Z * (Li t * g t * L0) := by noncomm_ring
      _ = -(Li t * Ld) * W t + Z * W t := by rw [hinv t, one_mul]
  have hanti := unitary_deriv hU hD
  rw [hWd] at hanti ⊢
  set Y := Li t * Ld
  show (-Y * W t + Z * W t) * (W t)ᴴ = -antiH Y
  set X := (-Y * W t + Z * W t) * (W t)ᴴ with hXdef
  have hX : X = -Y + Z := by
    calc X = (-Y + Z) * (W t * (W t)ᴴ) := by rw [hXdef]; noncomm_ring
      _ = -Y + Z := by rw [hU t, mul_one]
  have hXa : Xᴴ = -X := by
    have e : Xᴴ = W t * (-Y * W t + Z * W t)ᴴ := by
      rw [hXdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [e]
    exact (eq_neg_of_add_eq_zero_right hanti)
  have e1 : Xᴴ = -Yᴴ + Z := by
    rw [hX, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, hZ]
  rw [hXa] at e1
  have h2 : X + X = -(Y - Yᴴ) := by
    calc X + X = X - (-X) := by abel
      _ = (-Y + Z) - (-Yᴴ + Z) := by rw [← hX, e1]
      _ = -(Y - Yᴴ) := by abel
  calc X = (1 / 2 : ℂ) • (X + X) := by rw [← two_smul ℂ X, smul_smul]; norm_num
    _ = -antiH Y := by rw [h2, antiH, smul_neg]

/-! ### スカラーの微分(E Ė = p·ṗ、s ṡ = m Ė、ṅ = −n³ Ė(2E+m)) -/

/-- E = √(m² + r) なら E Ė = ṙ/2(r = |p|²、ṙ = 2p·ṗ) -/
theorem E_deriv (m : ℝ) (r : ℝ → ℝ) (rd t : ℝ) (hr : HasDerivAt r rd t) (hpos : 0 < m ^ 2 + r t) :
    HasDerivAt (fun s => √(m ^ 2 + r s)) (rd / (2 * √(m ^ 2 + r t))) t ∧
      √(m ^ 2 + r t) * (rd / (2 * √(m ^ 2 + r t))) = rd / 2 := by
  have hS : √(m ^ 2 + r t) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine ⟨(hr.const_add (m ^ 2)).sqrt hpos.ne', ?_⟩
  field_simp <;> ring

/-- s = √(2m(E+m)) なら s ṡ = m Ė -/
theorem s_deriv (m : ℝ) (E : ℝ → ℝ) (Ed t : ℝ) (hE : HasDerivAt E Ed t) (hpos : 0 < 2 * m * (E t + m)) :
    HasDerivAt (fun s => √(2 * m * (E s + m))) (2 * m * Ed / (2 * √(2 * m * (E t + m)))) t ∧
      √(2 * m * (E t + m)) * (2 * m * Ed / (2 * √(2 * m * (E t + m)))) = m * Ed := by
  have hS : √(2 * m * (E t + m)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine ⟨?_, by field_simp <;> ring⟩
  exact ((hE.add_const m).const_mul (2 * m)).sqrt hpos.ne'

/-- n = (2E(E+m))^{−1/2} なら ṅ = −n³ Ė (2E+m) -/
theorem n_deriv (m : ℝ) (E : ℝ → ℝ) (Ed t : ℝ) (hE : HasDerivAt E Ed t)
    (hpos : 0 < 2 * E t * (E t + m)) :
    HasDerivAt (fun s => (√(2 * E s * (E s + m)))⁻¹)
      (-((√(2 * E t * (E t + m)))⁻¹) ^ 3 * Ed * (2 * E t + m)) t := by
  have hS : √(2 * E t * (E t + m)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have h := (((hE.const_mul 2).mul (hE.add_const m)).sqrt hpos.ne').inv hS
  convert h using 1
  field_simp <;> ring

/-! ### 論文 G の点検:半角の形と、Fueter 接続と Berry 接続のゲージ同値 -/

/-- p = ρn、ṗ = ρ̇n + ρṅ なら p × ṗ = ρ²(n × ṅ) -/
theorem cross_radial (ρ ρd : ℂ) (n nd : Fin 3 → ℂ) :
    crossv (ρ • n) (ρd • n + ρ • nd) = ρ ^ 2 • crossv n nd := by
  funext k; fin_cases k <;> simp [crossv] <;> ring

/-- A_B の係数:|p|²/(2E(E+m)) = ½(1 − m/E)(E² = m² + |p|²) -/
theorem berry_half_angle (m E ρ : ℝ) (hE : E ^ 2 = m ^ 2 + ρ ^ 2) (hE0 : E ≠ 0) (hEm : E + m ≠ 0) :
    ρ ^ 2 / (2 * E * (E + m)) = (1 - m / E) / 2 := by
  rw [show ρ ^ 2 = E ^ 2 - m ^ 2 by linarith]
  field_simp <;> ring

/-- A_W の係数:−|p|²/(2m(E+m)) = −½(E/m − 1) -/
theorem wigner_half_angle (m E ρ : ℝ) (hE : E ^ 2 = m ^ 2 + ρ ^ 2) (hm : m ≠ 0) (hEm : E + m ≠ 0) :
    -ρ ^ 2 / (2 * m * (E + m)) = -(E / m - 1) / 2 := by
  rw [show ρ ^ 2 = E ^ 2 - m ^ 2 by linarith]
  field_simp <;> ring

/-- 半回転 V = n((E+m) − iσ·p)、n² = 1/(2E(E+m)) は V² = U = (m − iσ·p)/E -/
theorem half_rotation_sq (m E n : ℂ) (p : Fin 3 → ℂ) (hE : E ^ 2 = m ^ 2 + dotc p p)
    (hE0 : E ≠ 0) (hEm : E + m ≠ 0) (hn2 : n ^ 2 = 1 / (2 * E * (E + m))) :
    (n • ((E + m) • (1 : M2) - Complex.I • sd p)) * (n • ((E + m) • (1 : M2) - Complex.I • sd p))
      = (1 / E) • (m • (1 : M2) - Complex.I • sd p) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have cU1 : n ^ 2 * (2 * m * (E + m)) - m * (1 / E) = 0 := by rw [hn2]; field_simp <;> ring
  have cU2 : 1 / E - 2 * (E + m) * n ^ 2 = 0 := by rw [hn2]; field_simp <;> ring
  simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    sd_mul_sd, cross_self, sd_zero, smul_zero, add_zero]
  linear_combination (norm := module)
    (cU1 + n ^ 2 * hE + n ^ 2 * dotc p p * hI) • (1 : M2) + (Complex.I * cU2) • sd p

/-- 【論文 G、新しい関係】V A_F − dV = A_B V(方向 v)。V = n((E+m) − iσ·p)、
A_F = ½U⁻¹dU(a = 1/(2E²)、b = −m/(2E²))、A_B(a = 1/(2E(E+m))、b = 0)。
仮定 E dE = p·v と dn = −n³ dE(2E+m) は微分の関係(`E_deriv`、`n_deriv`) -/
theorem berry_fueter_gauge (m E n dn dE : ℂ) (p v : Fin 3 → ℂ)
    (hE0 : E ≠ 0) (hEm : E + m ≠ 0) (hE : E ^ 2 = m ^ 2 + dotc p p) (hdE : E * dE = dotc p v)
    (hn2 : n ^ 2 = 1 / (2 * E * (E + m))) (hdn : dn = -n ^ 3 * dE * (2 * E + m)) :
    (n • ((E + m) • (1 : M2) - Complex.I • sd p)) * Av p v (1 / (2 * E ^ 2)) (-m / (2 * E ^ 2))
      - (n • (dE • (1 : M2) - Complex.I • sd v) + dn • ((E + m) • (1 : M2) - Complex.I • sd p))
      = Av p v (1 / (2 * E * (E + m))) 0 * (n • ((E + m) • (1 : M2) - Complex.I • sd p)) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hr : dotc p p = E ^ 2 - m ^ 2 := by linear_combination -hE
  have hpv : dotc p v = E * dE := by linear_combination -hdE
  have cX : (E + m) * (1 / (2 * E ^ 2) - 1 / (2 * E * (E + m))) + -m / (2 * E ^ 2) = 0 := by
    field_simp <;> ring
  have cV : (E + m) * (-m / (2 * E ^ 2)) + 1
      - dotc p p * (1 / (2 * E * (E + m)) + 1 / (2 * E ^ 2)) = 0 := by
    rw [hr]; field_simp <;> ring
  have cP : dn + n * dotc p v * (1 / (2 * E * (E + m)) + 1 / (2 * E ^ 2)) = 0 := by
    rw [hpv, hdn, show n ^ 3 = n * n ^ 2 by ring, hn2]; field_simp <;> ring
  have c1 : -(E + m) * dn + -m / (2 * E ^ 2) * n * dotc p v - dE * n = 0 := by
    rw [hpv, hdn, show n ^ 3 = n * n ^ 2 by ring, hn2]; field_simp <;> ring
  simp only [Av, mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    sd_mul_sd, cross_self, sd_zero, smul_zero, add_zero, dot_p_cross, dot_cross_p, zero_smul,
    zero_add, sd_cross_cross1, sd_cross_cross2]
  linear_combination (norm := module)
    ((Complex.I * n) * cX - (Complex.I * n * (-m / (2 * E ^ 2))) * hI) • sd (crossv p v)
    + ((Complex.I * n) * cV
        + (Complex.I * n * dotc p p * (1 / (2 * E * (E + m)) + 1 / (2 * E ^ 2))) * hI) • sd v
    + (Complex.I * cP
        - (Complex.I * n * dotc p v * (1 / (2 * E * (E + m)) + 1 / (2 * E ^ 2))) * hI) • sd p
    + (c1 - (-m / (2 * E ^ 2) * n * dotc p v) * hI) • (1 : M2)

/-- ゲージ変換の形:V A_F − dV = A_B V、V V⁻¹ = 1、d(V⁻¹) = −V⁻¹ dV V⁻¹ なら
A_B = V A_F V⁻¹ + V d(V⁻¹) -/
theorem gauge_form (V Vi dV dVi AF AB : M2) (h : V * AF - dV = AB * V) (hVi : V * Vi = 1)
    (hdVi : dVi = -(Vi * dV * Vi)) : V * AF * Vi + V * dVi = AB := by
  rw [hdVi]
  calc V * AF * Vi + V * -(Vi * dV * Vi) = (V * AF - (V * Vi) * dV) * Vi := by noncomm_ring
    _ = (V * AF - dV) * Vi := by rw [hVi, one_mul]
    _ = AB * (V * Vi) := by rw [h]; noncomm_ring
    _ = AB := by rw [hVi, mul_one]

end

end CFT.Wigner
