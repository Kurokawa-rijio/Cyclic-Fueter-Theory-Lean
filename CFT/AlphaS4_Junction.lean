/-
  段階 4:接合(α-III.1、α-III.2、α-III.9)を、Levi-Civita の曲率(AlphaS4_Curv)と
  YM の応力から閉じる(2026-10-21 の外部監査の論証を Lean に移し、足りない段を補う)

  単位:8πG T = (8πG/g²) T̂ = 2ℓ² T̂(ℓ² = 4πG/g²)。Einstein 方程式は G_μν = 2ℓ² T̂_μν。

  A. 曲率と応力から読む量(微分体 S の上、AlphaS4_Curv の公式から)
    * tube_K:時間的な管 x = x₀ の外曲率 K_ab = −A Γ^x_ab:K_tt = −N N_x/A、K_θθ = R R_x/A、非対角 0
    * gauss_tube:G_nn = G_xx/A² は管の内部の量(N, R と t 微分)と K(N_x/A、R_x/A)だけで書ける(Gnn)。
      x の 2 階微分を含まない(Gauss–Codazzi の nn 成分を計量から直接)
    * tube_tt_form、tube_ang_form:x の 2 階微分は G_tt に −(2N²/(A²R)) R_xx、
      G_θθ + (R²/(2N²)) G_tt に (R²/(A²N)) N_xx としてだけ現れる(球対称の Israel 条件の出所)
    * tnn_tube、rho_tube、flux_tube:YM の T_nn、ρ、T_tn(正規直交成分)
    * ym_flux_tube:YM 方程式 ∂_μ(√−g F^{aμν}) の x 方向の流束 √−g F^{1xθ} = N s W_x/A
    * slice_hamiltonian:時間対称(R_t = A_t = 0)な切り口で G_tt/N² = (1 − (DR)² − 2R·DDR)/R² = ½ ³R
      (D = A⁻¹∂_x)。α-III.9 の Gauss の式(AlphaIII_Junction の scalR)が計量から出る
    * uu_form:G_uu = −(2/r)(r_uu − (Ω_u/Ω) r_u)(Ω = e^{2σ} で r_uu − 2σ_u r_u)
    * mixed_eq:uv 成分の Einstein 方程式 ⇔ r r_uv + r_u r_v = (Ω/2)(ℓ²(1 − W²)²/r² − 1)
    * ym_flux_null:√−g F^{1uθ} = −s W_v(ヌルな面 u = 一定 を横切る YM の流束は接線微分 W_v だけ)
    * null_tangential_stress:T̂_vv = 2W_v²/r²、T̂_uv = Ω(1 − W²)²/(2r⁴)、T̂_vθ = T̂_vφ = 0
  B. 分布としての跳び(1 次元の横断線、試験関数で)
    * delta_coeff:∂g の弱い形の δ の係数は [g](null_shell_from_weak の一般形)
  C. α-III.1(Z6):時間的な殻なし接合の不可能性
    * tube_israel:δ の係数から、殻なし(S_tt = 0、S_θθ + (R²/(2N²))S_tt = 0)⇔ [R_x] = [N_x] = 0
    * tube_K_jump:N, A, R が連続なら [K_ab] = 0 ⇔ [N_x] = [R_x] = 0
    * timelike_no_go:殻なし([K] = 0)と両側の nn 方程式から、時間対称な瞬間に [W_x²/A²] = 0
    * boosted_jump:管がどの速さ β で動いても、[T(n,n)] = γ²(1 + β²)[w²]/R²(w = W_x/A)
    * color_current:YM の表面流 = N s [w](delta_coeff と ym_flux_tube)。なしなら [w] = 0
    * cap_slope、dumbbell_timelike:帽子 W = cos(s/ℓ) の赤道で w = −1/ℓ、首で w = 0。
    * dumbbell_no_shellfree_timelike、dumbbell_color_current:合成した不可能性定理。
      したがってダンベルの接合球を通る時間的な面は、重力の殻(S_ab ≠ 0)と YM の表面流の両方を要する。
      時間的な薄殻一般は否定しない(台帳の閉鎖条件どおり)
  D. α-III.2(Z7):ヌルな波面の殻なし
    * jump_mixed、jump_transport:混合成分の式の差 r[r_uv] + r_v[r_u] = 0 から (r q)′ = 0(q = [r_u])、
      q(v₀) = 0、r > 0 なら波面全体で q = 0
    * initial_jump:時間対称(r_t = 0)と C¹ の空間接合([r_s] = 0)から、角での q(v₀) = 0
    * null_front_no_shell、null_front_from_mixed:面密度 μ = −[r_u]/(4πG r)(AlphaIII_Null)は波面全体で 0
    * 角度成分・uv・vv の δ は横断微分 ∂_u が連続な量(r_v、Ω_v)にかかるだけなので 0、
      YM の表面流も W_v の跳び(= 0)だけ(delta_coeff と ym_flux_null)。k^μ[T_μν] = 0 は
      null_tangential_stress から(T_vν は W, W_v, r, Ω だけで決まる)
    * dumbbell_front:ダンベルの接合から出る波面では [W_u] = −α[w] ≠ 0 で、[T̂_uu] ≠ 0。
      角(r_u = 0)では [r_uu] = −(2ℓ²/r)[W_u²]。波面は殻ではなく弱い不連続を運ぶ。
      波面の上の一般の点の [r_uu] は [Ω_u/Ω] r_u の項を含む(監査の注意どおり)
  外部に残るもの:折れ目のある初期データからの EYM の解が各側で波面まで C²(特性線に沿う弱い不連続の
  標準的な理論)であること。
-/
import CFT.AlphaS4_Curv
import CFT.AlphaIII_Null
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open Real Set

namespace CFT.S4J

open CFT.S4

/-! ### A. 曲率と応力から読む量 -/

section Alg
variable {S : Type*} [Field S] [CharZero S] (d : Fin 4 → Derivation ℤ S S)

/-- 管 x = x₀(単位法線 n = A dx)の外曲率 K_ab = ∇_a n_b = −A Γ^x_ab -/
theorem tube_K (N A R s c : S) (H : SphD d N A R s c) :
    -(A * Gam d (gD N A R s) (giD N A R s) 1 0 0) = -(N * (d 1 N * A⁻¹)) ∧
    -(A * Gam d (gD N A R s) (giD N A R s) 1 2 2) = R * (d 1 R * A⁻¹) ∧
    -(A * Gam d (gD N A R s) (giD N A R s) 1 3 3) = R * s ^ 2 * (d 1 R * A⁻¹) ∧
    -(A * Gam d (gD N A R s) (giD N A R s) 1 0 2) = 0 ∧
    -(A * Gam d (gD N A R s) (giD N A R s) 1 0 3) = 0 ∧
    -(A * Gam d (gD N A R s) (giD N A R s) 1 2 3) = 0 := by
  have hA := H.hA
  rw [gamD d N A R s c H]
  simp only [GD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, mul_zero, neg_zero]
  refine ⟨?_, ?_, ?_, trivial, trivial, trivial⟩ <;> field_simp <;> ring

/-- 管の G_nn(内部の量と外曲率だけ) -/
def Gnn {K : Type*} [Field K] (N R Nt Rt Rtt k1 k2 : K) : K :=
  -R⁻¹ ^ 2 - 2 * Rtt * N⁻¹ ^ 2 * R⁻¹ - Rt ^ 2 * N⁻¹ ^ 2 * R⁻¹ ^ 2 + 2 * Nt * Rt * N⁻¹ ^ 3 * R⁻¹
    + k2 ^ 2 * R⁻¹ ^ 2 + 2 * k1 * k2 * N⁻¹ * R⁻¹

/-- Gauss の式(nn 成分):G_xx/A² = Gnn(N, R, N_t, R_t, R_tt, N_x/A, R_x/A) -/
theorem gauss_tube (N A R s c : S) (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 1 1 * A⁻¹ ^ 2
      = Gnn N R (d 0 N) (d 0 R) (d 0 (d 0 R)) (d 1 N * A⁻¹) (d 1 R * A⁻¹) := by
  have hA := H.hA
  have hN := H.hN
  have hR := H.hR
  rw [einD_11 d N A R s c H]
  simp only [Gnn]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((2 : S) * A * (d 0 N) * (d 0 R) * iA * iN ^ 3 * iR + (-1 : S) * A * (d 0 R) ^ 2 * iA * iN ^ 2 * iR ^ 2 + (-2 : S) * A * (d 0 (d 0 R)) * iA * iN ^ 2 * iR + (-1 : S) * A * iA * iR ^ 2 + (2 : S) * (d 0 N) * (d 0 R) * iN ^ 3 * iR + (-1 : S) * (d 0 R) ^ 2 * iN ^ 2 * iR ^ 2 + (-2 : S) * (d 0 (d 0 R)) * iN ^ 2 * iR + (-1 : S) * iR ^ 2) * hiA

/-- G_tt の x の 2 階微分は R_xx だけ -/
theorem tube_tt_form (N A R s c : S) (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0
      = -(2 * N ^ 2 * A⁻¹ ^ 2 * R⁻¹) * d 1 (d 1 R)
        + (2 * d 0 A * d 0 R * A⁻¹ * R⁻¹ + 2 * d 1 A * N ^ 2 * d 1 R * A⁻¹ ^ 3 * R⁻¹
          - N ^ 2 * (d 1 R) ^ 2 * A⁻¹ ^ 2 * R⁻¹ ^ 2 + N ^ 2 * R⁻¹ ^ 2 + (d 0 R) ^ 2 * R⁻¹ ^ 2) := by
  rw [einD_00 d N A R s c H]; ring

/-- G_θθ + (R²/(2N²)) G_tt の x の 2 階微分は N_xx だけ -/
theorem tube_ang_form (N A R s c : S) (H : SphD d N A R s c) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 2 2
      + R ^ 2 * N⁻¹ ^ 2 / 2 * Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0
      = R ^ 2 * A⁻¹ ^ 2 * N⁻¹ * d 1 (d 1 N)
        + (-(d 0 (d 0 A)) * R ^ 2 * A⁻¹ * N⁻¹ ^ 2 - R * d 0 (d 0 R) * N⁻¹ ^ 2
          + d 0 A * d 0 N * R ^ 2 * A⁻¹ * N⁻¹ ^ 3 + d 0 N * R * d 0 R * N⁻¹ ^ 3
          - d 1 A * d 1 N * R ^ 2 * A⁻¹ ^ 3 * N⁻¹ + d 1 N * R * d 1 R * A⁻¹ ^ 2 * N⁻¹
          - (d 1 R) ^ 2 * A⁻¹ ^ 2 / 2 + 1 / 2 + (d 0 R) ^ 2 * N⁻¹ ^ 2 / 2) := by
  have hA := H.hA
  have hN := H.hN
  have hR := H.hR
  rw [einD_22 d N A R s c H, einD_00 d N A R s c H]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((1 : S) * (d 1 A) * N * R ^ 2 * (d 1 R) * iA ^ 3 * iN * iR + (1 : S) * (d 1 A) * R ^ 2 * (d 1 R) * iA ^ 3 * iR + (-1/2 : S) * N * R ^ 2 * (d 1 R) ^ 2 * iA ^ 2 * iN * iR ^ 2 + (-1 : S) * N * R ^ 2 * (d 1 (d 1 R)) * iA ^ 2 * iN * iR + (1/2 : S) * N * R ^ 2 * iN * iR ^ 2 + (-1/2 : S) * R ^ 2 * (d 1 R) ^ 2 * iA ^ 2 * iR ^ 2 + (-1 : S) * R ^ 2 * (d 1 (d 1 R)) * iA ^ 2 * iR + (1/2 : S) * R ^ 2 * iR ^ 2) * hiN + ((1 : S) * (d 0 A) * R * (d 0 R) * iA * iN ^ 2 + (1 : S) * (d 1 A) * R * (d 1 R) * iA ^ 3 + (1/2 : S) * R * (d 0 R) ^ 2 * iN ^ 2 * iR + (-1/2 : S) * R * (d 1 R) ^ 2 * iA ^ 2 * iR + (-1 : S) * R * (d 1 (d 1 R)) * iA ^ 2 + (1/2 : S) * R * iR + (1/2 : S) * (d 0 R) ^ 2 * iN ^ 2 + (-1/2 : S) * (d 1 R) ^ 2 * iA ^ 2 + (1/2 : S)) * hiR

/-- 時間対称な切り口のハミルトン拘束の幾何:G_tt/N² = (1 − (DR)² − 2R·DDR)/R² = ½ ³R(D = A⁻¹∂_x) -/
theorem slice_hamiltonian (N A R s c : S) (H : SphD d N A R s c) (hRt : d 0 R = 0) (hAt : d 0 A = 0) :
    Ein d (gD N A R s) (giD N A R s) (GD d N A R s c) 0 0 * N⁻¹ ^ 2
      = (1 - (d 1 R * A⁻¹) ^ 2 - 2 * R * (d 1 (d 1 R) * A⁻¹ ^ 2 - d 1 A * d 1 R * A⁻¹ ^ 3)) * R⁻¹ ^ 2 := by
  have hA := H.hA
  have hN := H.hN
  have hR := H.hR
  rw [einD_00 d N A R s c H, hRt, hAt]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((2 : S) * (d 1 A) * N * (d 1 R) * iA ^ 3 * iN * iR + (2 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR + (-1 : S) * N * (d 1 R) ^ 2 * iA ^ 2 * iN * iR ^ 2 + (-2 : S) * N * (d 1 (d 1 R)) * iA ^ 2 * iN * iR + (1 : S) * N * iN * iR ^ 2 + (-1 : S) * (d 1 R) ^ 2 * iA ^ 2 * iR ^ 2 + (-2 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR + (1 : S) * iR ^ 2) * hiN + ((-2 : S) * (d 1 A) * (d 1 R) * iA ^ 3 * iR + (2 : S) * (d 1 (d 1 R)) * iA ^ 2 * iR) * hiR

/-- 管の法線方向の応力 T̂_nn(正規直交成分) -/
def Tnn {K : Type*} [Field K] (R W wt wx : K) : K :=
  wx ^ 2 * R⁻¹ ^ 2 + wt ^ 2 * R⁻¹ ^ 2 - (1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 / 2

/-- エネルギー密度 ρ̂(正規直交成分) -/
def Rho {K : Type*} [Field K] (R W wt wx : K) : K :=
  wx ^ 2 * R⁻¹ ^ 2 + wt ^ 2 * R⁻¹ ^ 2 + (1 - W ^ 2) ^ 2 * R⁻¹ ^ 4 / 2

theorem tnn_tube (W s N A R : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 1 1 * A⁻¹ ^ 2 = Tnn R W (d 0 W * N⁻¹) (d 1 W * A⁻¹) := by
  rw [tymD_11 d W s hN hA hR hs]; simp only [Tnn]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((-1/2 : S) * A * W ^ 4 * iA * iR ^ 4 + (1 : S) * A * W ^ 2 * iA * iR ^ 4 + (1 : S) * A * (d 0 W) ^ 2 * iA * iN ^ 2 * iR ^ 2 + (-1/2 : S) * A * iA * iR ^ 4 + (-1/2 : S) * W ^ 4 * iR ^ 4 + (1 : S) * W ^ 2 * iR ^ 4 + (1 : S) * (d 0 W) ^ 2 * iN ^ 2 * iR ^ 2 + (-1/2 : S) * iR ^ 4) * hiA

theorem rho_tube (W s N A R : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 0 * N⁻¹ ^ 2 = Rho R W (d 0 W * N⁻¹) (d 1 W * A⁻¹) := by
  rw [tymD_00 d W s hN hA hR hs]; simp only [Rho]
  have hiN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize N⁻¹ = iN at hiN ⊢
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((1/2 : S) * N * W ^ 4 * iN * iR ^ 4 + (-1 : S) * N * W ^ 2 * iN * iR ^ 4 + (1 : S) * N * (d 1 W) ^ 2 * iA ^ 2 * iN * iR ^ 2 + (1/2 : S) * N * iN * iR ^ 4 + (1/2 : S) * W ^ 4 * iR ^ 4 + (-1 : S) * W ^ 2 * iR ^ 4 + (1 : S) * (d 1 W) ^ 2 * iA ^ 2 * iR ^ 2 + (1/2 : S) * iR ^ 4) * hiN

theorem flux_tube (W s N A R : S) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hs : s ≠ 0) :
    Tym (gD N A R s) (giD N A R s) (FT d W s) 0 1 * (N⁻¹ * A⁻¹)
      = 2 * (d 0 W * N⁻¹) * (d 1 W * A⁻¹) * R⁻¹ ^ 2 := by
  rw [tymD_01 d W s hN hA hR hs]; ring

/-- YM 方程式の x 方向の流束:√−g g^{xx} g^{θθ} F^1_{xθ} = N s W_x/A(√−g = N A R² s) -/
theorem ym_flux_tube (W s N A R : S) (hA : A ≠ 0) (hR : R ≠ 0) :
    (N * A * R ^ 2 * s) * giD N A R s 1 1 * giD N A R s 2 2 * FT d W s 0 1 2 = N * s * (d 1 W * A⁻¹) := by
  simp only [giD, FT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  have hiA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hiR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR
  generalize A⁻¹ = iA at hiA ⊢
  generalize R⁻¹ = iR at hiR ⊢
  linear_combination ((1 : S) * N * R ^ 2 * (d 1 W) * iA * iR ^ 2 * s) * hiA + ((1 : S) * N * R * (d 1 W) * iA * iR * s + (1 : S) * N * (d 1 W) * iA * s) * hiR

/-- ヌルな面の uu 成分:G_uu = −(2/r)(r_uu − (Ω_u/Ω) r_u) -/
theorem uu_form (Om r s c : S) (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 0
      = -(2 * r⁻¹) * (d 0 (d 0 r) - d 0 Om * Om⁻¹ * d 0 r) := by
  rw [einN_00 d Om r s c H]; ring

/-- uv 成分の Einstein 方程式 ⇔ r r_uv + r_u r_v = (Ω/2)(ℓ²(1 − W²)²/r² − 1) -/
theorem mixed_eq (W Om r s c l : S) (H : SphN d Om r s c) :
    Ein d (gN Om r s) (giN Om r s) (GN d Om r s c) 0 1 = 2 * l ^ 2 * Tym (gN Om r s) (giN Om r s) (FT d W s) 0 1
      ↔ r * d 0 (d 1 r) + d 0 r * d 1 r = Om / 2 * (l ^ 2 * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 2 - 1) := by
  have hO := H.hO
  have hr := H.hr
  rw [einN_01 d Om r s c H, tymN_01 d W s hO hr H.hs]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  constructor
  · intro h
    linear_combination (r ^ 2 / 2) * h + ((1/2 : S) * Om * W ^ 4 * ir ^ 3 * l ^ 2 * r + (1/2 : S) * Om * W ^ 4 * ir ^ 2 * l ^ 2 + (-1 : S) * Om * W ^ 2 * ir ^ 3 * l ^ 2 * r + (-1 : S) * Om * W ^ 2 * ir ^ 2 * l ^ 2 + (1/2 : S) * Om * ir ^ 3 * l ^ 2 * r + (1/2 : S) * Om * ir ^ 2 * l ^ 2 + (-1/2 : S) * Om * ir * r + (-1/2 : S) * Om + (-1 : S) * ir * r * (d 0 r) * (d 1 r) + (-1 : S) * r * (d 0 (d 1 r)) + (-1 : S) * (d 0 r) * (d 1 r)) * hir
  · intro h
    linear_combination (2 * ir ^ 2) * h + ((-2 : S) * ir * (d 0 (d 1 r))) * hir

/-- ヌルな面 u = 一定 を横切る YM の流束:√−g g^{uv} g^{θθ} F^1_{vθ} = −s W_v(√−g = Ω r² s) -/
theorem ym_flux_null (W s Om r : S) (hO : Om ≠ 0) (hr : r ≠ 0) :
    (Om * r ^ 2 * s) * giN Om r s 0 1 * giN Om r s 2 2 * FT d W s 0 1 2 = -(s * d 1 W) := by
  simp only [giN, FT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]
  have hiOm : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hO
  have hir : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  generalize Om⁻¹ = iOm at hiOm ⊢
  generalize r⁻¹ = ir at hir ⊢
  linear_combination ((-1 : S) * (d 1 W) * ir ^ 2 * r ^ 2 * s) * hiOm + ((-1 : S) * (d 1 W) * ir * r * s + (-1 : S) * (d 1 W) * s) * hir

/-- 生成子 k = ∂_v の方向の応力:T̂_vv、T̂_uv、T̂_vθ、T̂_vφ は W, W_v, r, Ω だけで決まる -/
theorem null_tangential_stress (W s Om r : S) (hO : Om ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    Tym (gN Om r s) (giN Om r s) (FT d W s) 1 1 = 2 * (d 1 W) ^ 2 * r⁻¹ ^ 2 ∧
    Tym (gN Om r s) (giN Om r s) (FT d W s) 0 1 = Om * (1 - W ^ 2) ^ 2 * r⁻¹ ^ 4 / 2 ∧
    Tym (gN Om r s) (giN Om r s) (FT d W s) 1 2 = 0 ∧
    Tym (gN Om r s) (giN Om r s) (FT d W s) 1 3 = 0 := by
  refine ⟨(tymN_11 d W s hO hr hs).trans (by ring), (tymN_01 d W s hO hr hs).trans (by ring),
    tymN_12 d W s hO hr hs, tymN_13 d W s hO hr hs⟩

end Alg

/-! ### B. 分布としての跳び -/

/-- 横断線の上の弱い形:−∫ g φ′ = ∫ S φ + m φ(u₀) がすべての試験関数で成り立てば、δ の係数 m = [g] -/
theorem delta_coeff {a u₀ b m : ℝ} (hau : a < u₀) (hub : u₀ < b)
    {pm pp qm qp Sm Sp : ℝ → ℝ}
    (hpm : ∀ x ∈ Icc a u₀, HasDerivWithinAt pm (qm x) (Icc a u₀) x)
    (hpp : ∀ x ∈ Icc u₀ b, HasDerivWithinAt pp (qp x) (Icc u₀ b) x)
    (hqm : IntervalIntegrable qm MeasureTheory.volume a u₀)
    (hqp : IntervalIntegrable qp MeasureTheory.volume u₀ b)
    (sideM : ∀ x ∈ Icc a u₀, qm x = Sm x) (sideP : ∀ x ∈ Icc u₀ b, qp x = Sp x)
    (weak : ∀ φ φ' : ℝ → ℝ,
      (∀ x ∈ Icc a u₀, HasDerivWithinAt φ (φ' x) (Icc a u₀) x) →
      (∀ x ∈ Icc u₀ b, HasDerivWithinAt φ (φ' x) (Icc u₀ b) x) →
      Continuous φ' → φ a = 0 → φ b = 0 →
      -((∫ x in a..u₀, pm x * φ' x) + ∫ x in u₀..b, pp x * φ' x)
        = (∫ x in a..u₀, Sm x * φ x) + (∫ x in u₀..b, Sp x * φ x) + m * φ u₀) :
    m = pp u₀ - pm u₀ := by
  set φ : ℝ → ℝ := fun u => (u - a) * (b - u) with hφ
  set φ' : ℝ → ℝ := fun u => (b - u) - (u - a) with hφ'
  have dφm : ∀ x ∈ Icc a u₀, HasDerivWithinAt φ (φ' x) (Icc a u₀) x :=
    fun x _ => CFT.Null.tent_deriv a b x _
  have dφp : ∀ x ∈ Icc u₀ b, HasDerivWithinAt φ (φ' x) (Icc u₀ b) x :=
    fun x _ => CFT.Null.tent_deriv a b x _
  have cφ' : Continuous φ' := by simp only [hφ']; fun_prop
  have hw := weak φ φ' dφm dφp cφ' (by simp [hφ]) (by simp [hφ])
  have hparts := CFT.Junction.weak_second_derivative hau.le hub.le hpm hpp dφm dφp hqm hqp
    (cφ'.intervalIntegrable _ _) (cφ'.intervalIntegrable _ _) (by simp [hφ]) (by simp [hφ])
  have e1 : ∫ x in a..u₀, qm x * φ x = ∫ x in a..u₀, Sm x * φ x := by
    apply intervalIntegral.integral_congr; intro x hx; rw [uIcc_of_le hau.le] at hx; simp only
    rw [sideM x hx]
  have e2 : ∫ x in u₀..b, qp x * φ x = ∫ x in u₀..b, Sp x * φ x := by
    apply intervalIntegral.integral_congr; intro x hx; rw [uIcc_of_le hub.le] at hx; simp only
    rw [sideP x hx]
  rw [hparts, e1, e2] at hw
  have hpos : φ u₀ ≠ 0 := by
    simp only [hφ]; exact mul_ne_zero (by linarith) (by linarith)
  have key : ((pp u₀ - pm u₀) - m) * φ u₀ = 0 := by linarith
  have k2 := (mul_eq_zero.mp key).resolve_right hpos
  linarith

/-! ### C. α-III.1:時間的な殻なし接合の不可能性 -/

/-- 球対称な管の Israel 条件:tt 成分と角度の組み合わせの δ の係数(tube_tt_form、tube_ang_form と
  delta_coeff)が 8πG S なら、殻なし ⇔ [R_x] = [N_x] = 0 -/
theorem tube_israel (G N A R jR jN Stt Sang : ℝ) (hG : G ≠ 0) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0)
    (htt : -(2 * N ^ 2 * A⁻¹ ^ 2 * R⁻¹) * jR = 8 * π * G * Stt)
    (hang : R ^ 2 * A⁻¹ ^ 2 * N⁻¹ * jN = 8 * π * G * Sang) :
    (Stt = 0 ∧ Sang = 0) ↔ (jR = 0 ∧ jN = 0) := by
  have hπ : π ≠ 0 := pi_ne_zero
  have c1 : -(2 * N ^ 2 * A⁻¹ ^ 2 * R⁻¹) ≠ 0 := by
    have : (2 : ℝ) * N ^ 2 * A⁻¹ ^ 2 * R⁻¹ ≠ 0 := by positivity
    exact neg_ne_zero.mpr this
  have c2 : R ^ 2 * A⁻¹ ^ 2 * N⁻¹ ≠ 0 := by positivity
  have c3 : (8 : ℝ) * π * G ≠ 0 := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, mul_zero] at htt; rw [h2, mul_zero] at hang
    exact ⟨(mul_eq_zero.mp htt).resolve_left c1, (mul_eq_zero.mp hang).resolve_left c2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, mul_zero] at htt; rw [h2, mul_zero] at hang
    exact ⟨(mul_eq_zero.mp htt.symm).resolve_left c3, (mul_eq_zero.mp hang.symm).resolve_left c3⟩

/-- N, A, R が連続なら、外曲率の跳び [K_tt] = −N[N_x]/A、[K_θθ] = R[R_x]/A は
  [N_x] = [R_x] = 0 と同値 -/
theorem tube_K_jump (N A R Nxp Nxm Rxp Rxm : ℝ) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) :
    (-(N * (Nxp * A⁻¹)) - -(N * (Nxm * A⁻¹)) = 0 ∧ R * (Rxp * A⁻¹) - R * (Rxm * A⁻¹) = 0)
      ↔ (Nxp - Nxm = 0 ∧ Rxp - Rxm = 0) := by
  have e1 : -(N * (Nxp * A⁻¹)) - -(N * (Nxm * A⁻¹)) = -(N * A⁻¹) * (Nxp - Nxm) := by ring
  have e2 : R * (Rxp * A⁻¹) - R * (Rxm * A⁻¹) = R * A⁻¹ * (Rxp - Rxm) := by ring
  have c1 : -(N * A⁻¹) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have c2 : R * A⁻¹ ≠ 0 := by positivity
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_eq_zero.mp h1).resolve_left c1, (mul_eq_zero.mp h2).resolve_left c2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]; simp

/-- 殻なしの時間的な接合([K] = 0、内部の量は連続)と両側の nn 方程式 G_nn = 2ℓ² T̂_nn から、
  時間対称な瞬間(W_t = 0)に [w²] = 0(w = W_x/A) -/
theorem timelike_no_go (l N R Nt Rt Rtt k1 k2 W wp wm : ℝ) (hl : l ≠ 0) (hR : R ≠ 0)
    (eP : Gnn N R Nt Rt Rtt k1 k2 = 2 * l ^ 2 * Tnn R W 0 wp)
    (eM : Gnn N R Nt Rt Rtt k1 k2 = 2 * l ^ 2 * Tnn R W 0 wm) :
    wp ^ 2 = wm ^ 2 := by
  have h : 2 * l ^ 2 * Tnn R W 0 wp = 2 * l ^ 2 * Tnn R W 0 wm := by rw [← eP, ← eM]
  have hl2 : (2 : ℝ) * l ^ 2 ≠ 0 := by positivity
  have h2 := mul_left_cancel₀ hl2 h
  simp only [Tnn] at h2
  have hR2 : R⁻¹ ^ 2 ≠ 0 := by positivity
  have h3 : (wp ^ 2 - wm ^ 2) * R⁻¹ ^ 2 = 0 := by linear_combination h2
  linarith [(mul_eq_zero.mp h3).resolve_right hR2]

/-- 管が速さ β(|β| < 1、γ² = 1/(1 − β²))で動いていても、W_t = 0 の瞬間の法線応力の跳びは
  [T(n,n)] = γ²(1 + β²)[w²]/R²(n = γ(e_x + β e_t)) -/
theorem boosted_jump (R W wp wm β γ2 : ℝ) :
    γ2 * ((Tnn R W 0 wp - Tnn R W 0 wm) + 2 * β * (2 * 0 * wp * R⁻¹ ^ 2 - 2 * 0 * wm * R⁻¹ ^ 2)
        + β ^ 2 * (Rho R W 0 wp - Rho R W 0 wm))
      = γ2 * (1 + β ^ 2) * (wp ^ 2 - wm ^ 2) * R⁻¹ ^ 2 := by
  simp only [Tnn, Rho]; ring

/-- YM の表面流:流束 √−g F^{1xθ} = N s w の δ の係数(delta_coeff)は N s [w]。なしなら [w] = 0 -/
theorem color_current (N s wp wm j : ℝ) (hN : N ≠ 0) (hs : s ≠ 0) (hj : j = N * s * wp - N * s * wm) :
    j = 0 ↔ wp = wm := by
  rw [hj]
  constructor
  · intro h
    have : N * s * (wp - wm) = 0 := by linear_combination h
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero hN hs)
    linarith
  · intro h; rw [h]; ring

/-- 帽子 W = cos(s/ℓ)(W = r′)の赤道 s = πℓ/2 での傾き −1/ℓ -/
theorem cap_slope (l : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun x => cos (x / l)) (-1 / l) (π * l / 2) := by
  have h := ((hasDerivAt_id (π * l / 2)).div_const l).cos
  simp only [id] at h
  convert h using 1
  rw [show π * l / 2 / l = π / 2 by field_simp; ring, sin_pi_div_two]
  ring

/-- ダンベルの接合球:帽子側 w = −1/ℓ、首側 w = 0(A = 1、W_t = 0)。
  殻なしの時間的な接合は [w²] = 0 を要し(timelike_no_go)、YM の表面流なしは [w] = 0 を要する
  (color_current)。どちらも成り立たない:どの速さで動く時間的な面にも、重力の殻と YM の表面流の
  両方が必要(boosted_jump で [T(n,n)] = γ²(1 + β²)(−1/ℓ²)/ℓ² ≠ 0) -/
theorem dumbbell_timelike (l : ℝ) (hl : l ≠ 0) :
    (0 : ℝ) ^ 2 ≠ (-1 / l) ^ 2 ∧ (0 : ℝ) ≠ -1 / l := by
  have : (-1 / l) ≠ 0 := by
    have : (1 : ℝ) / l ≠ 0 := one_div_ne_zero hl
    rw [neg_div]; exact neg_ne_zero.mpr this
  refine ⟨?_, fun h => this h.symm⟩
  intro h
  have h2 : (-1 / l) ^ 2 = 0 := by rw [← h]; ring
  exact this (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)

/-- α-III.1 の合成:ダンベルの接合球(帽子側 w = −1/ℓ、首側 w = 0、W_t = 0)を通る時間的な面は殻なしに
  なれない。Israel の δ の係数(tube_israel)、K の跳び([R_x] = A[k₂]、[N_x] = A[k₁]、A 連続)、
  両側の nn 方程式 G_nn = 2ℓ² T̂_nn(gauss_tube、tnn_tube)を合わせる -/
theorem dumbbell_no_shellfree_timelike (G l N A R Nt Rt Rtt k1p k1m k2p k2m W jR jN Stt Sang : ℝ)
    (hG : G ≠ 0) (hl : l ≠ 0) (hN : N ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0)
    (htt : -(2 * N ^ 2 * A⁻¹ ^ 2 * R⁻¹) * jR = 8 * π * G * Stt)
    (hang : R ^ 2 * A⁻¹ ^ 2 * N⁻¹ * jN = 8 * π * G * Sang)
    (hjR : jR = (k2p - k2m) * A) (hjN : jN = (k1p - k1m) * A)
    (eP : Gnn N R Nt Rt Rtt k1p k2p = 2 * l ^ 2 * Tnn R W 0 (-1 / l))
    (eM : Gnn N R Nt Rt Rtt k1m k2m = 2 * l ^ 2 * Tnn R W 0 0) :
    ¬ (Stt = 0 ∧ Sang = 0) := by
  intro hS
  obtain ⟨h1, h2⟩ := (tube_israel G N A R jR jN Stt Sang hG hN hA hR htt hang).mp hS
  rw [hjR] at h1; rw [hjN] at h2
  have e2 : k2p = k2m := by
    have := (mul_eq_zero.mp h1).resolve_right hA; linarith
  have e1 : k1p = k1m := by
    have := (mul_eq_zero.mp h2).resolve_right hA; linarith
  rw [e1, e2] at eP
  have := timelike_no_go l N R Nt Rt Rtt k1m k2m W (-1 / l) 0 hl hR eP eM
  exact (dumbbell_timelike l hl).1 this.symm

/-- YM の側の合成:同じ接合球で、表面の色の流れなしの時間的な面はない(j = N s [w] = N s/ℓ ≠ 0) -/
theorem dumbbell_color_current (N s l : ℝ) (hN : N ≠ 0) (hs : s ≠ 0) (hl : l ≠ 0) :
    N * s * 0 - N * s * (-1 / l) ≠ 0 := by
  intro h
  have := (color_current N s 0 (-1 / l) _ hN hs rfl).mp h
  exact (dumbbell_timelike l hl).2 this

/-! ### D. α-III.2:ヌルな波面の殻なし -/

/-- 混合成分の式の差:両側で r r_uv + r_u r_v = F(r, Ω, W の値が共通)なら r[r_uv] + r_v[r_u] = 0 -/
theorem jump_mixed (r rv rup rum ruvp ruvm F : ℝ) (hp : r * ruvp + rup * rv = F)
    (hm : r * ruvm + rum * rv = F) : r * (ruvp - ruvm) + rv * (rup - rum) = 0 := by
  linear_combination hp - hm

/-- 跳びの輸送:r q′ + r_v q = 0、q(v₀) = 0、r ≠ 0 なら区間の上で q = 0((r q)′ = 0) -/
theorem jump_transport {v0 v1 : ℝ} {r rv q q' : ℝ → ℝ}
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hq : ∀ v ∈ Icc v0 v1, HasDerivWithinAt q (q' v) (Icc v0 v1) v)
    (heq : ∀ v ∈ Icc v0 v1, r v * q' v + rv v * q v = 0) (h0 : q v0 = 0)
    (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0) :
    ∀ v ∈ Icc v0 v1, q v = 0 := by
  have hd : ∀ v ∈ Icc v0 v1, HasDerivWithinAt (fun v => r v * q v) 0 (Icc v0 v1) v := by
    intro v hv
    have := (hr v hv).mul (hq v hv)
    convert this using 1
    linear_combination -(heq v hv)
  have hc : ContinuousOn (fun v => r v * q v) (Icc v0 v1) := fun v hv => (hd v hv).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hc (fun v hv =>
    (hd v (Ico_subset_Icc_self hv)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv))
  intro v hv
  have e := hconst v hv
  simp only [h0, mul_zero] at e
  exact (mul_eq_zero.mp e).resolve_left (hpos v hv)

/-- 角での初期値:∂_u = α(e_t − e_x) の向き(α は両側で共通)で、時間対称(r_t = 0)と
  C¹ の空間接合([r_x] = 0)なら [r_u] = 0 -/
theorem initial_jump (α rtp rtm rxp rxm : ℝ) (htp : rtp = 0) (htm : rtm = 0) (hx : rxp = rxm) :
    α * (rtp - rxp) - α * (rtm - rxm) = 0 := by
  rw [htp, htm, hx]; ring

/-- 波面全体で殻なし:面密度 μ(v) = −[r_u](v)/(4πG r(v))(AlphaIII_Null の null_shell_from_weak を
  各 v で)と、跳びの輸送から μ = 0 -/
theorem null_front_no_shell {v0 v1 G : ℝ} {r rv q q' μ : ℝ → ℝ}
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hq : ∀ v ∈ Icc v0 v1, HasDerivWithinAt q (q' v) (Icc v0 v1) v)
    (heq : ∀ v ∈ Icc v0 v1, r v * q' v + rv v * q v = 0) (h0 : q v0 = 0)
    (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0)
    (hμ : ∀ v ∈ Icc v0 v1, μ v = -q v / (4 * π * G * r v)) :
    ∀ v ∈ Icc v0 v1, μ v = 0 := by
  intro v hv
  rw [hμ v hv, jump_transport hr hq heq h0 hpos v hv]
  simp

/-- α-III.2 の合成:両側の混合成分の式 r r_uv± + r_u± r_v = F(mixed_eq、F は r, Ω, W の共通の値)、
  角での [r_u] = 0(initial_jump)、r > 0 から、波面全体で面密度 μ = −[r_u]/(4πG r) = 0 -/
theorem null_front_from_mixed {v0 v1 G : ℝ} {r rv rup rum ruvp ruvm F μ : ℝ → ℝ}
    (hr : ∀ v ∈ Icc v0 v1, HasDerivWithinAt r (rv v) (Icc v0 v1) v)
    (hup : ∀ v ∈ Icc v0 v1, HasDerivWithinAt rup (ruvp v) (Icc v0 v1) v)
    (hum : ∀ v ∈ Icc v0 v1, HasDerivWithinAt rum (ruvm v) (Icc v0 v1) v)
    (sideP : ∀ v ∈ Icc v0 v1, r v * ruvp v + rup v * rv v = F v)
    (sideM : ∀ v ∈ Icc v0 v1, r v * ruvm v + rum v * rv v = F v)
    (h0 : rup v0 = rum v0) (hpos : ∀ v ∈ Icc v0 v1, r v ≠ 0)
    (hμ : ∀ v ∈ Icc v0 v1, μ v = -(rup v - rum v) / (4 * π * G * r v)) :
    ∀ v ∈ Icc v0 v1, μ v = 0 := by
  refine null_front_no_shell (q := fun v => rup v - rum v) (q' := fun v => ruvp v - ruvm v) hr
    (fun v hv => (hup v hv).sub (hum v hv)) (fun v hv => ?_) (by simp [h0]) hpos hμ
  have := jump_mixed (r v) (rv v) (rup v) (rum v) (ruvp v) (ruvm v) (F v) (sideP v hv) (sideM v hv)
  linear_combination this

/-- ダンベルの接合から出る波面:W_u = α(W_t − w)、W_t = 0 で [W_u] = −α[w] = −α/ℓ ≠ 0、
  [T̂_uu] = 2[W_u²]/r² ≠ 0。角(両側で r_u = 0)では uu 方程式 r_uu = (Ω_u/Ω) r_u − 2ℓ² W_u²/r から
  [r_uu] = −(2ℓ²/r)[W_u²]:波面は殻ではなく弱い不連続を運ぶ -/
theorem dumbbell_front (α l r : ℝ) (hα : α ≠ 0) (hl : l ≠ 0) (hr : r ≠ 0)
    (rup rum OuOp OuOm ruup ruum : ℝ) (hup : rup = 0) (hum : rum = 0)
    (hp : ruup = OuOp * rup - 2 * l ^ 2 * (α * (0 - 0)) ^ 2 / r)
    (hm : ruum = OuOm * rum - 2 * l ^ 2 * (α * (0 - -1 / l)) ^ 2 / r) :
    α * (0 - 0) - α * (0 - -1 / l) ≠ 0 ∧
    ruup - ruum = -(2 * l ^ 2 / r) * ((α * (0 - 0)) ^ 2 - (α * (0 - -1 / l)) ^ 2) ∧
    ruup - ruum ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have : α * (0 - 0) - α * (0 - -1 / l) = -(α / l) := by ring
    rw [this]; exact neg_ne_zero.mpr (div_ne_zero hα hl)
  · rw [hp, hm, hup, hum]; ring
  · have key : ruup - ruum = 2 * α ^ 2 / r := by rw [hp, hm, hup, hum]; field_simp; ring
    rw [key]; exact div_ne_zero (by positivity) hr

end CFT.S4J
