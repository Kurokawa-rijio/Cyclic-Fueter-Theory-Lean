/-
  橋 B:首の曲率と温度(2026-11-05、否定的な結果 IX.32 が指した先)

  IX.32 でエルゴード性を外した後に残った 1/ℓ(Euclid の測地線の発散率)は、カオスの指数そのものではなく、
  **温度が生じるかどうかを分ける臨界の加速度**だった。仮説「2πT = 1/ℓ」は規格化によるので、そのままでは
  成り立たない(否定)。規格化によらない形は次の恒等式。

  * 運動学:首 −dt² + cos²(t/ℓ)dz²(曲率 −1/ℓ²)。
  * 作用:JT(IX.12)。dilaton の一般解 φ = A sin(t/ℓ) + cos(t/ℓ)(B cosh(z/ℓ) + C sinh(z/ℓ))(IX.14)。
  * 力学:
    (1) 不変量 I = φ²/ℓ² − (∇φ)² = (A² + B² − C²)/ℓ² はどこでも一定(`dilaton_invariant`)。
    (2) ξ^μ = ε^{μν}∂_νφ のノルムは ξ·ξ = −(∇φ)² = I − φ²/ℓ²(`xi_norm`)。地平線は φ² = Iℓ²。
    (3) ξ の軌道の固有加速度 a² = φ²/(ℓ²(φ² − Iℓ²))、表面重力 κ² = φ²/ℓ⁴(地平線で I/ℓ²)、
        **a² − 1/ℓ² = κ_h²/(−ξ·ξ) = I/(φ² − Iℓ²)**(`accel_identity`、`deser_levin`)。
        T = κ/2π(Gibbons–Hawking、外部)を入れると (2πT_loc)² = a² − 1/ℓ²:AdS の Unruh 温度
        (Deser–Levin)がダンベルの首で、JT の dilaton が選ぶ Killing ベクトルとして実現する。
    (4) I の符号で三つの類(`three_classes`):I > 0 は JT の永遠のブラックホール(IX.14 の対称な解 I = B²/ℓ²)、
        I = 0 は極限の喉(T = 0、a = 1/ℓ)、I < 0 は温度が強制されない(IX.25 の静的な首)。
    (5) 規格化した Rindler の lapse N = sinh(ρ/ℓ) は Jacobi の式 N″ = N/ℓ² をみたし N′(0) = 1/ℓ(`rindler_lapse`)。
        2πT_loc = 1/ℓ となるのは N = 1 の観測者 ρ* = ℓ log(1 + √2)、a = √2/ℓ だけ(`unit_observer`)。
    (6) 接合での値:sin u_c = 1/cosh(L/ℓ) なら tan u_c = 1/sinh(L/ℓ)(`junction_tan`)、2πT_j = tan(u_c)/ℓ。
  * 外部:T = κ/2π、Euclid の正則性 ⇔ 熱的、MSS の上限と JT の λ_L = 2πT。測地線の発散 1/ℓ を OTOC の
    指数と同一視することはしない。
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CFT.BridgeThermal

open Real

/-- 【橋 B】dilaton の不変量:φ² − ℓ²(∇φ)² = A² + B² − C²(ℓ²(∇φ)² = −(ℓφ_t)² + (ℓφ_z/cos)²) -/
theorem dilaton_invariant (l A B C t z : ℝ) :
    (A * sin (t / l) + cos (t / l) * (B * cosh (z / l) + C * sinh (z / l))) ^ 2
      - (-(A * cos (t / l) - sin (t / l) * (B * cosh (z / l) + C * sinh (z / l))) ^ 2
        + (B * sinh (z / l) + C * cosh (z / l)) ^ 2) = A ^ 2 + B ^ 2 - C ^ 2 := by
  have h1 : sin (t / l) ^ 2 + cos (t / l) ^ 2 = 1 := sin_sq_add_cos_sq _
  have h2 : cosh (z / l) ^ 2 - sinh (z / l) ^ 2 = 1 := cosh_sq_sub_sinh_sq _
  linear_combination (A ^ 2 + (B * cosh (z / l) + C * sinh (z / l)) ^ 2) * h1 + (B ^ 2 - C ^ 2) * h2

/-- ℓφ_t と ℓφ_z/cos(IX.14 の `jt_dt`、`jt_dz` を ℓ 倍) -/
theorem dilaton_grad (l A B C t z : ℝ) (hl : l ≠ 0) (hc : cos (t / l) ≠ 0) :
    l * (A / l * cos (t / l) - sin (t / l) / l * (B * cosh (z / l) + C * sinh (z / l)))
      = A * cos (t / l) - sin (t / l) * (B * cosh (z / l) + C * sinh (z / l)) ∧
    l * (cos (t / l) * ((B * sinh (z / l) + C * cosh (z / l)) / l)) / cos (t / l)
      = B * sinh (z / l) + C * cosh (z / l) := by
  constructor <;> field_simp <;> ring

/-- 【橋 B】ξ^t = φ_z/cos、ξ^z = −φ_t/cos のノルム −(ξ^t)² + cos²(ξ^z)² = −(−φ_t² + φ_z²/cos²) -/
theorem xi_norm (φt φz c : ℝ) (hc : c ≠ 0) :
    -(φz / c) ^ 2 + c ^ 2 * (-φt / c) ^ 2 = -(-φt ^ 2 + φz ^ 2 / c ^ 2) := by
  field_simp <;> ring

/-- 【橋 B】固有加速度:N² = φ²/ℓ² − I、|∇N|² = (φ/(ℓ²N))²(∇φ)²、(∇φ)² = N² なら
a² = |∇N|²/N² = φ²/(ℓ²(φ² − Iℓ²)) -/
theorem accel_formula (φ l I N : ℝ) (hl : l ≠ 0) (hN : N ≠ 0) (hN2 : N ^ 2 = φ ^ 2 / l ^ 2 - I)
    (hφ : φ ^ 2 - I * l ^ 2 ≠ 0) :
    (φ / (l ^ 2 * N)) ^ 2 * N ^ 2 / N ^ 2 = φ ^ 2 / (l ^ 2 * (φ ^ 2 - I * l ^ 2)) := by
  have e : l ^ 2 * N ^ 2 = φ ^ 2 - I * l ^ 2 := by rw [hN2]; field_simp <;> ring
  have hN2' : N ^ 2 ≠ 0 := pow_ne_zero 2 hN
  rw [← e]
  field_simp <;> ring

/-- 【橋 B】a² − 1/ℓ² = I/(φ² − Iℓ²) -/
theorem accel_identity (φ l I : ℝ) (hl : l ≠ 0) (hφ : φ ^ 2 - I * l ^ 2 ≠ 0) :
    φ ^ 2 / (l ^ 2 * (φ ^ 2 - I * l ^ 2)) - 1 / l ^ 2 = I / (φ ^ 2 - I * l ^ 2) := by
  field_simp <;> ring

/-- 【橋 B】表面重力:κ² = φ²/ℓ⁴(∇_μξ_ν = ε_μν φ/ℓ²、−½ε·ε = 1)、地平線 φ² = Iℓ² で κ² = I/ℓ²。
局所温度の 2 乗 κ_h²/(−ξ·ξ) = (I/ℓ²)/(φ²/ℓ² − I) は a² − 1/ℓ² に等しい(Deser–Levin の形) -/
theorem deser_levin (φ l I : ℝ) (hl : l ≠ 0) (hφ : φ ^ 2 - I * l ^ 2 ≠ 0) (hh : φ ^ 2 / l ^ 2 - I ≠ 0) :
    (I / l ^ 2) / (φ ^ 2 / l ^ 2 - I) = φ ^ 2 / (l ^ 2 * (φ ^ 2 - I * l ^ 2)) - 1 / l ^ 2 ∧
    ∀ φh, φh ^ 2 = I * l ^ 2 → φh ^ 2 / l ^ 4 = I / l ^ 2 := by
  refine ⟨?_, fun φh h => ?_⟩
  · rw [accel_identity φ l I hl hφ, div_eq_div_iff hh hφ]
    field_simp
    ring
  · rw [h]; field_simp <;> ring

/-- 【橋 B】三つの類:IX.14 の対称な解(A = C = 0)は I = B²/ℓ² > 0(熱的)、A = 0、B = C は I = 0(極限)、
A = B = 0 は I < 0(C ≠ 0) -/
theorem three_classes (l B C : ℝ) (hl : l ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    0 < (0 ^ 2 + B ^ 2 - 0 ^ 2) / l ^ 2 ∧ (0 ^ 2 + B ^ 2 - B ^ 2) / l ^ 2 = 0 ∧
    (0 ^ 2 + 0 ^ 2 - C ^ 2) / l ^ 2 < 0 := by
  have hB2 : 0 < B ^ 2 := lt_of_le_of_ne (sq_nonneg B) (Ne.symm (pow_ne_zero 2 hB))
  have hC2 : 0 < C ^ 2 := lt_of_le_of_ne (sq_nonneg C) (Ne.symm (pow_ne_zero 2 hC))
  have hl2 : 0 < l ^ 2 := lt_of_le_of_ne (sq_nonneg l) (Ne.symm (pow_ne_zero 2 hl))
  have e1 : (0 ^ 2 + B ^ 2 - 0 ^ 2) / l ^ 2 = B ^ 2 / l ^ 2 := by ring
  refine ⟨by rw [e1]; exact div_pos hB2 hl2, by ring, ?_⟩
  have : 0 < C ^ 2 / l ^ 2 := div_pos hC2 hl2
  have e : (0 ^ 2 + 0 ^ 2 - C ^ 2) / l ^ 2 = -(C ^ 2 / l ^ 2) := by ring
  rw [e]; linarith

/-- 【橋 B】規格化した Rindler の lapse N = sinh(ρ/ℓ):N′ = cosh(ρ/ℓ)/ℓ、N″ = N/ℓ²(Jacobi の式)、N′(0) = 1/ℓ -/
theorem rindler_lapse (l ρ : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun x => sinh (x / l)) (cosh (ρ / l) / l) ρ ∧
    HasDerivAt (fun x => cosh (x / l) / l) (sinh (ρ / l) / l ^ 2) ρ ∧ cosh (0 / l) / l = 1 / l := by
  have hu : HasDerivAt (fun x : ℝ => x / l) (1 / l) ρ := (hasDerivAt_id' ρ).div_const l
  refine ⟨?_, ?_, by simp⟩
  · have h := (Real.hasDerivAt_sinh (ρ / l)).comp ρ hu
    convert h using 1; ring
  · have h := ((Real.hasDerivAt_cosh (ρ / l)).comp ρ hu).div_const l
    convert h using 1; ring

/-- 【橋 B】N = 1 の観測者:sinh(log(1 + √2)) = 1、cosh = √2(加速度 a = cosh/(ℓ sinh) = √2/ℓ) -/
theorem unit_observer : sinh (Real.log (1 + √2)) = 1 ∧ cosh (Real.log (1 + √2)) = √2 := by
  have hs : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 1 + √2 := by positivity
  have hinv : (1 + √2)⁻¹ = √2 - 1 := by
    have hne : (1 + √2) ≠ 0 := hpos.ne'
    field_simp
    nlinarith [hs]
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg, Real.exp_log hpos, hinv]
  constructor <;> ring

/-- 【橋 B】接合:sin u = 1/cosh(L/ℓ)(0 < u < π/2、L > 0)なら tan u = 1/sinh(L/ℓ) -/
theorem junction_tan (L l u : ℝ) (hl : 0 < l) (hL : 0 < L) (hu1 : 0 < u) (hu2 : u < π / 2)
    (hs : sin u = 1 / cosh (L / l)) : tan u = 1 / sinh (L / l) := by
  have hch : 0 < cosh (L / l) := cosh_pos _
  have hsh : 0 < sinh (L / l) := Real.sinh_pos_iff.2 (div_pos hL hl)
  have hc : 0 < cos u := cos_pos_of_mem_Ioo ⟨by linarith, hu2⟩
  have hcos : cos u = sinh (L / l) / cosh (L / l) := by
    have h1 := sin_sq_add_cos_sq u
    have h2 := cosh_sq_sub_sinh_sq (L / l)
    have hsq : cos u ^ 2 = (sinh (L / l) / cosh (L / l)) ^ 2 := by
      rw [hs] at h1
      field_simp at h1 ⊢
      nlinarith [h1, h2]
    have hpos : 0 < sinh (L / l) / cosh (L / l) := div_pos hsh hch
    nlinarith [sq_nonneg (cos u - sinh (L / l) / cosh (L / l)), sq_nonneg (cos u + sinh (L / l) / cosh (L / l))]
  have hsh' := hsh.ne'
  have hch' := hch.ne'
  rw [tan_eq_sin_div_cos, hs, hcos]
  field_simp

end CFT.BridgeThermal
