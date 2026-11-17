import CFT.Quantum.MinisuperspaceEulerLagrange

/-!
  命題集 `LEAN_GAP_TREES.md` 1-7（正準形式への移行、2026-11-16）：
  ミニスーパースペース系のラグランジュ形式と正準形式の等価性を内部で固定する。
  運動量 `momA`/`momB`、EL 方程式と Hamilton 方程式の等価、Legendre 逆写像は
  `MinisuperspaceEulerLagrange.lean`（1-2）で既に証明済み。本モジュールで追加する残りは：
  (a) 正準 Hamiltonian `Hcan = N * Hfun` と Hamilton 拘束 `Hfun = 0` の定義、
  (b) N の運動方程式（∂L/∂N = 0）が拘束 `Hfun = 0` と等価なこと（`L_N` から）、
  (c) 正準方程式系 `CanonicalEqs`（ȧ = N ∂H/∂p_a、ḃ = N ∂H/∂p_b、
      ṗ_a = −N ∂H/∂a、ṗ_b = −N ∂H/∂b、偏微分は `H_pa`/`H_pb`/`H_a`/`H_b` の値）と
      Euler–Lagrange 方程式系の等価性、(d) その組み立てとしての
      「ラグランジュ形式 ⟺ 正準形式＋拘束」。
  これで第5章の量子化の前提（正準変数 (a, b, p_a, p_b) と Hamiltonian）が内部に揃う。
  ゲージは Ṅ = 0（N は定数）の範囲。
-/

open CFT.AlphaCompleteA

namespace CFT.Mini

/-- 正準 Hamiltonian：H = p_a ȧ + p_b ḃ − L = N · Hfun（`legendre` の右辺）。 -/
noncomputable def Hcan (a b pa pb N c l : ℝ) : ℝ :=
  N * Hfun a b pa pb c l

/-- Hamilton 拘束：Hfun = 0。N の運動方程式（∂L/∂N = 0）と等価（下の定理）。 -/
def HamiltonConstraint (a b pa pb c l : ℝ) : Prop :=
  Hfun a b pa pb c l = 0

/-- 軌道に沿った Legendre 恒等式：p_a ȧ + p_b ḃ − L = Hcan。 -/
theorem hamiltonian_legendre (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hb0 : b t ≠ 0) (hc : c ≠ 0) :
    momA a b N c t * deriv a t + momB a b N c t * deriv b t
      - Lfun (a t) (b t) (deriv a t) (deriv b t) N c l
      = Hcan (a t) (b t) (momA a b N c t) (momB a b N c t) N c l := by
  rw [Hcan]
  simp only [momA, momB]
  exact legendre (a t) (b t) (deriv a t) (deriv b t) N c l hN hb0 hc

/-- N の運動方程式 ∂L/∂N = 0 は Hamilton 拘束 Hfun = 0 と等価（`L_N` の値 −Hfun から）。 -/
theorem constraint_iff_N_equation (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hb0 : b t ≠ 0) (hc : c ≠ 0) :
    deriv (fun n => Lfun (a t) (b t) (deriv a t) (deriv b t) n c l) N = 0 ↔
      Hfun (a t) (b t) (momA a b N c t) (momB a b N c t) c l = 0 := by
  have h := (L_N (a t) (b t) (deriv a t) (deriv b t) N c l hN hb0 hc).deriv
  simp only [momA, momB] at h ⊢
  rw [h]
  exact neg_eq_zero

/-- 正準 Hamiltonian が拘束面上で消えるのは、拘束そのものと等価（N ≠ 0）。 -/
theorem hcan_eq_zero_iff (a b pa pb N c l : ℝ) (hN : N ≠ 0) :
    Hcan a b pa pb N c l = 0 ↔ Hfun a b pa pb c l = 0 := by
  simp only [Hcan, mul_eq_zero, hN, false_or]

/-- ∂H/∂p_a の軌道に沿った値（`H_pa` の値）。 -/
theorem dH_dpa (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hb0 : b t ≠ 0) (hc : c ≠ 0) :
    deriv (fun x => Hfun (a t) (b t) x (momB a b N c t) c l) (momA a b N c t)
      = (a t * momA a b N c t - b t * momB a b N c t) / (2 * (b t) ^ 2 * c) :=
  (H_pa (a t) (b t) (momA a b N c t) (momB a b N c t) c l hb0 hc).deriv

/-- ∂H/∂p_b の軌道に沿った値（`H_pb` の値）。 -/
theorem dH_dpb (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hb0 : b t ≠ 0) (hc : c ≠ 0) :
    deriv (fun x => Hfun (a t) (b t) (momA a b N c t) x c l) (momB a b N c t)
      = -(momA a b N c t) / (2 * b t * c) :=
  (H_pb (a t) (b t) (momA a b N c t) (momB a b N c t) c l hb0 hc).deriv

/-- ∂H/∂a の軌道に沿った値（`H_a` の値）。 -/
theorem dH_da (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hb0 : b t ≠ 0) (hc : c ≠ 0) :
    deriv (fun x => Hfun x (b t) (momA a b N c t) (momB a b N c t) c l) (a t)
      = -c + c * l ^ 2 / (b t) ^ 2 + (momA a b N c t) ^ 2 / (4 * (b t) ^ 2 * c) :=
  (H_a (a t) (b t) (momA a b N c t) (momB a b N c t) c l hb0 hc).deriv

/-- ∂H/∂b の軌道に沿った値（`H_b` の値）。 -/
theorem dH_db (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hb0 : b t ≠ 0) (hc : c ≠ 0) :
    deriv (fun x => Hfun (a t) x (momA a b N c t) (momB a b N c t) c l) (b t)
      = (-4 * a t * c ^ 2 * l ^ 2
          + (momA a b N c t) * (-(a t) * momA a b N c t + b t * momB a b N c t))
        / (2 * (b t) ^ 3 * c) :=
  (H_b (a t) (b t) (momA a b N c t) (momB a b N c t) c l hb0 hc).deriv

/-- 正準方程式系：ȧ = N ∂H/∂p_a、ḃ = N ∂H/∂p_b、ṗ_a = −N ∂H/∂a、ṗ_b = −N ∂H/∂b。 -/
def CanonicalEqs (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ) : Prop :=
  deriv a t = N * deriv (fun x => Hfun (a t) (b t) x (momB a b N c t) c l) (momA a b N c t) ∧
  deriv b t = N * deriv (fun x => Hfun (a t) (b t) (momA a b N c t) x c l) (momB a b N c t) ∧
  deriv (momA a b N c) t
    = -N * deriv (fun x => Hfun x (b t) (momA a b N c t) (momB a b N c t) c l) (a t) ∧
  deriv (momB a b N c) t
    = -N * deriv (fun x => Hfun (a t) x (momA a b N c t) (momB a b N c t) c l) (b t)

/-- Euler–Lagrange 方程式系 ⟺ 正準方程式系。 -/
theorem euler_iff_canonical (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    (deriv (momA a b N c) t - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)) = 0 ∧
     deriv (momB a b N c) t
        - (-2 * c * deriv a t * deriv b t / N
          + 2 * c * N * a t * l ^ 2 / (b t) ^ 3) = 0)
      ↔ CanonicalEqs a b N c l t := by
  unfold CanonicalEqs
  rw [dH_dpa a b N c l t hb0 hc, dH_dpb a b N c l t hb0 hc,
    dH_da a b N c l t hb0 hc, dH_db a b N c l t hb0 hc]
  have hA := euler_iff_hamilton_a a b N c l t hN hc hb0
  have hB := euler_iff_hamilton_b a b N c l t hN hc hb0
  have hva := legendre_vel_a a b N c t hN hc hb0
  have hvb := legendre_vel_b a b N c t hN hc hb0
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hva.symm, hvb.symm, hA.mp h1, hB.mp h2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hA.mpr h3, hB.mpr h4⟩

/-- 組み立て：ラグランジュ形式 ⟺ 正準形式＋Hamilton 拘束。 -/
theorem lagrangian_iff_canonical (a b : ℝ → ℝ) (N c l : ℝ) (t : ℝ)
    (hN : N ≠ 0) (hc : c ≠ 0) (hb0 : b t ≠ 0) :
    (deriv (momA a b N c) t - (-(c * deriv b t ^ 2) / N + c * N * (1 - l ^ 2 / (b t) ^ 2)) = 0 ∧
     deriv (momB a b N c) t
        - (-2 * c * deriv a t * deriv b t / N
          + 2 * c * N * a t * l ^ 2 / (b t) ^ 3) = 0 ∧
     HamiltonConstraint (a t) (b t) (momA a b N c t) (momB a b N c t) c l)
      ↔ (CanonicalEqs a b N c l t ∧
        HamiltonConstraint (a t) (b t) (momA a b N c t) (momB a b N c t) c l) := by
  have hec := euler_iff_canonical a b N c l t hN hc hb0
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hec.mp ⟨h1, h2⟩, h3⟩
  · rintro ⟨hcan, h3⟩
    obtain ⟨h1, h2⟩ := hec.mpr hcan
    exact ⟨h1, h2, h3⟩

end CFT.Mini
