/-
  命題集 `LEAN_GAP_TREES.md` 5-4（時間の導入）。

  内部時計としてスケール因子 a を選ぶ（t = a）。厳密解 Ψ₊, Ψ₋ は a 方向の
  平面波なので、拘束（WDW 方程式、a について 2 階）の解でありながら、
  1 階のシュレディンガー方程式 i∂_t Ψ = ĤΨ を満たす。ハミルトニアンは
  掛け算作用素 Ĥ₊ = −σ(b)·κ（正の枝）、Ĥ₋ = +σ(b)·κ（負の枝）で、b にのみ依存し
  t = a には依らない。すなわち時計 t = a の下では、厳密解の時間発展は
  位相回転 e^{∓iσ κ t} そのものである。

  枝の結合 (Ψ_DW, Ψ_HH) = (sin(aσκ)/σ, cos(aσκ)/σ) は、単独では
  シュレディンガー方程式を満たさないが、2 準位の閉じた系を満たす：
  ∂_a Ψ_DW = σκ·Ψ_HH、∂_a Ψ_HH = −σκ·Ψ_DW（結合行列 σκ·σ_y に対応）。

  注意：時計の選択は規約である。枝と古典的「外向き」の対応付けは
  5-8 の残りとして別問題のまま残る。
-/
import CFT.Quantum.WDWBoundaryConditions

namespace CFT.WDWClock

open Complex CFT.WKB CFT.WDWBoundary

variable (c l κ : ℝ)

/-- シュレディンガー方程式 i∂_t ψ = H ψ（HasDerivAt 形：∂_t ψ = −i H ψ）。
H は t に依ってもよい（ここでは a に依らない掛け算作用素として使う）。 -/
def SchrodingerEq (ψ : ℝ → ℂ) (H : ℝ → ℂ) : Prop :=
  ∀ t, HasDerivAt ψ (-I * (H t * ψ t)) t

/-- 内部時計 t = a における正の枝 Ψ₊ のハミルトニアン：−σ(b)·κ（掛け算作用素）。 -/
noncomputable def clockHamiltonianPlus (C b : ℝ) : ℂ :=
  -((Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ))

/-- 内部時計 t = a における負の枝 Ψ₋ のハミルトニアン：+σ(b)·κ（掛け算作用素）。 -/
noncomputable def clockHamiltonianMinus (C b : ℝ) : ℂ :=
  ((Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ))

/-- 正の枝は内部時計 t = a についてシュレディンガー方程式を満たす。 -/
theorem psiPlus_schrodinger (C b : ℝ) :
    SchrodingerEq (fun t => PsiPlus c l κ C t b)
      (fun _ => clockHamiltonianPlus c l κ C b) := by
  intro t
  have h := hasDerivAt_Psi_a κ (fun y => 1 / Real.sqrt (Q c l C y))
    (fun y => Real.sqrt (Q c l C y)) t b
  convert h using 1
  simp only [PsiPlus, Psia, clockHamiltonianPlus]
  ring

/-- 負の枝は内部時計 t = a についてシュレディンガー方程式を満たす（符号は逆）。 -/
theorem psiMinus_schrodinger (C b : ℝ) :
    SchrodingerEq (fun t => PsiMinus c l κ C t b)
      (fun _ => clockHamiltonianMinus c l κ C b) := by
  intro t
  have h := hasDerivAt_Psi_a κ (fun y => (-Real.sqrt (Q c l C y))⁻¹)
    (fun y => -Real.sqrt (Q c l C y)) t b
  convert h using 1
  simp only [PsiMinus, Psia, clockHamiltonianMinus]
  push_cast
  ring

/-- i∂_t Ψ₊ = Ĥ₊ Ψ₊（deriv 形）。 -/
theorem psiPlus_schrodinger_form (C a b : ℝ) :
    I * deriv (fun t => PsiPlus c l κ C t b) a
      = clockHamiltonianPlus c l κ C b * PsiPlus c l κ C a b := by
  have h := psiPlus_schrodinger c l κ C b a
  have hI : (I : ℂ) * -I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [h.deriv]
  show I * (-I * (clockHamiltonianPlus c l κ C b * PsiPlus c l κ C a b))
      = clockHamiltonianPlus c l κ C b * PsiPlus c l κ C a b
  rw [← mul_assoc, hI, one_mul]

/-- i∂_t Ψ₋ = Ĥ₋ Ψ₋（deriv 形）。 -/
theorem psiMinus_schrodinger_form (C a b : ℝ) :
    I * deriv (fun t => PsiMinus c l κ C t b) a
      = clockHamiltonianMinus c l κ C b * PsiMinus c l κ C a b := by
  have h := psiMinus_schrodinger c l κ C b a
  have hI : (I : ℂ) * -I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [h.deriv]
  show I * (-I * (clockHamiltonianMinus c l κ C b * PsiMinus c l κ C a b))
      = clockHamiltonianMinus c l κ C b * PsiMinus c l κ C a b
  rw [← mul_assoc, hI, one_mul]

/-- 厳密解は拘束（WDW 方程式）とシュレディンガー方程式の両方を満たす。
拘束は a について 2 階、シュレディンガー方程式は時計 t = a について 1 階：
平面波の形の解の上で、拘束は 1 階の方程式に帰着する。 -/
theorem psiPlus_wdw_and_schrodinger (hb : ℝ) (hhb : hb * κ = 1) (hc : c ≠ 0)
    (C a b : ℝ) (hQ : 0 < Q c l C b) (Daa Dab : ℂ)
    (hDaa : HasDerivAt (fun x => Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
      (fun y => Real.sqrt (Q c l C y)) x b) Daa a)
    (hDab : HasDerivAt (fun y => Psia κ (fun y => 1 / Real.sqrt (Q c l C y))
      (fun y => Real.sqrt (Q c l C y)) a y) Dab b) :
    wdwOp c l hb a b (PsiPlus c l κ C a b) Daa Dab = 0 ∧
      SchrodingerEq (fun t => PsiPlus c l κ C t b)
        (fun _ => clockHamiltonianPlus c l κ C b) :=
  ⟨wdw_exact_sqrt c l κ hb hhb hc C a b hQ Daa Dab hDaa hDab,
    psiPlus_schrodinger c l κ C b⟩

/-- DeWitt 型結合の a 微分は Hartle–Hawking 型結合に比例する。 -/
theorem psiDW_hasDerivAt (C a b : ℝ) :
    HasDerivAt (fun t => PsiDW c l κ C t b)
      (((Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ)) * PsiHH c l κ C a b) a := by
  have h1 := hasDerivAt_Psi_a κ (fun y => 1 / Real.sqrt (Q c l C y))
    (fun y => Real.sqrt (Q c l C y)) a b
  have h2 := hasDerivAt_Psi_a κ (fun y => (-Real.sqrt (Q c l C y))⁻¹)
    (fun y => -Real.sqrt (Q c l C y)) a b
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have h := (h1.add h2).div_const (2 * I)
  convert h using 1
  simp only [PsiDW, PsiHH, PsiPlus, PsiMinus, Psia]
  field_simp
  ring

/-- Hartle–Hawking 型結合の a 微分は DeWitt 型結合に比例する（符号は逆）。 -/
theorem psiHH_hasDerivAt (C a b : ℝ) :
    HasDerivAt (fun t => PsiHH c l κ C t b)
      (-(((Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ)) * PsiDW c l κ C a b)) a := by
  have h1 := hasDerivAt_Psi_a κ (fun y => 1 / Real.sqrt (Q c l C y))
    (fun y => Real.sqrt (Q c l C y)) a b
  have h2 := hasDerivAt_Psi_a κ (fun y => (-Real.sqrt (Q c l C y))⁻¹)
    (fun y => -Real.sqrt (Q c l C y)) a b
  have h := (h1.sub h2).div_const (2 : ℂ)
  convert h using 1
  simp only [PsiDW, PsiHH, PsiPlus, PsiMinus, Psia]
  field_simp
  simp only [one_div]
  linear_combination (-2 * (Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ) *
    (Psi κ (fun y => (Real.sqrt (Q c l C y))⁻¹) (fun y => Real.sqrt (Q c l C y)) a b +
      Psi κ (fun y => (-Real.sqrt (Q c l C y))⁻¹) (fun y => -Real.sqrt (Q c l C y)) a b)) *
    Complex.I_mul_I

/-- 2 準位系：(Ψ_DW, Ψ_HH) は時計 t = a について閉じた 2 準位の
シュレディンガー系を満たす（結合定数 σκ、行列 σκ·σ_y に対応）。 -/
theorem psiDW_psiHH_system (C a b : ℝ) :
    HasDerivAt (fun t => PsiDW c l κ C t b)
        (((Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ)) * PsiHH c l κ C a b) a ∧
      HasDerivAt (fun t => PsiHH c l κ C t b)
        (-(((Real.sqrt (Q c l C b) : ℂ) * (κ : ℂ)) * PsiDW c l κ C a b)) a :=
  ⟨psiDW_hasDerivAt c l κ C a b, psiHH_hasDerivAt c l κ C a b⟩

end CFT.WDWClock
