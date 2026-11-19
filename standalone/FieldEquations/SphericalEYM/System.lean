import Mathlib

/-
# Spherically symmetric Einstein–Yang–Mills equations in double-null form

Metric ds² = −2Ω du dv + r² dΩ² and the SU(2) magnetic ansatz with one function W(u,v),
in units where the gauge coupling scale is 1. The evolution equations are
  r_{uv} = Ω((1−W²)²/r² − 1)/(2r) − r_u r_v / r,
  Ω_{uv} = Ω_u Ω_v / Ω − 2Ω r_{uv}/r − Ω²(1−W²)²/r⁴,
  W_{uv} = Ω W (1−W²)/(2r²),
and the constraint equations are
  r_{uu} − (Ω_u/Ω) r_u + 2 W_u²/r = 0,  r_{vv} − (Ω_v/Ω) r_v + 2 W_v²/r = 0.
`Du`, `Dv`, `Duv`, `Duu`, `Dvv` are partial derivatives defined through `deriv` of slices.
-/

namespace FieldEquations.SphericalEYM

open Real

noncomputable def Du (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := deriv (fun u' => F u' v) u

noncomputable def Dv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := deriv (fun v' => F u v') v

noncomputable def Duv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun u' => deriv (fun v' => F u' v') v) u

noncomputable def Duu (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun u' => deriv (fun u'' => F u'' v) u') u

noncomputable def Dvv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun v' => deriv (fun v'' => F u v'') v') v

/-- Right-hand side of the r_{uv} equation. -/
noncomputable def rhsR (Om W ru rv r : ℝ) : ℝ :=
  (1 / 2) * Om * ((1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r

/-- Right-hand side of the Ω_{uv} equation (it uses the value of r_{uv}). -/
noncomputable def rhsOm (Om Ou Ov ruv r W : ℝ) : ℝ :=
  Ou * Ov / Om - 2 * Om * ruv / r - Om ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4

/-- Right-hand side of the W_{uv} equation. -/
noncomputable def rhsW (Om W r : ℝ) : ℝ :=
  (1 / 2) * Om * W * (1 - W ^ 2) / r ^ 2

/-- The unknowns (r, Ω, W). -/
structure EYMFields where
  r : ℝ → ℝ → ℝ
  Om : ℝ → ℝ → ℝ
  W : ℝ → ℝ → ℝ

/-- The three evolution equations on all of ℝ². -/
def EYMEvolutionEqs (F : EYMFields) : Prop :=
  ∀ u v, Duv F.r u v = rhsR (F.Om u v) (F.W u v) (Du F.r u v) (Dv F.r u v) (F.r u v)
    ∧ Duv F.Om u v
        = rhsOm (F.Om u v) (Du F.Om u v) (Dv F.Om u v) (Duv F.r u v) (F.r u v) (F.W u v)
    ∧ Duv F.W u v = rhsW (F.Om u v) (F.W u v) (F.r u v)

/-- The two constraint equations on all of ℝ². -/
def EYMConstraints (F : EYMFields) : Prop :=
  ∀ u v, Duu F.r u v - (Du F.Om u v / F.Om u v) * Du F.r u v
        + 2 * (Du F.W u v) ^ 2 / F.r u v = 0
    ∧ Dvv F.r u v - (Dv F.Om u v / F.Om u v) * Dv F.r u v
        + 2 * (Dv F.W u v) ^ 2 / F.r u v = 0

end FieldEquations.SphericalEYM
