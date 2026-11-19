import FieldEquations.SphericalEYM.System
import Mathlib.Tactic

/-
# Bounds from continuity on compact rectangles

A continuous function on a compact set is bounded, and a positive one is bounded below by a
positive constant. These give the a priori bounds needed for the uniqueness theorem.
-/

open FieldEquations.SphericalEYM

namespace FieldEquations.CompactBounds

theorem exists_abs_bound_of_continuousOn {K : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ContinuousOn (Function.uncurry f) K) :
    ∃ B, ∀ u v, (u, v) ∈ K → |f u v| ≤ B := by
  obtain ⟨x₀, hx₀, hmax⟩ :=
    hK.exists_isMaxOn hne (continuous_abs.comp_continuousOn hf)
  exact ⟨|f x₀.1 x₀.2|, fun u v huv => hmax huv⟩

theorem exists_pos_lower_bound_of_continuousOn {K : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ContinuousOn (Function.uncurry f) K)
    (hpos : ∀ u v, (u, v) ∈ K → 0 < f u v) :
    ∃ m, 0 < m ∧ ∀ u v, (u, v) ∈ K → m ≤ f u v := by
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
  exact ⟨f x₀.1 x₀.2, hpos x₀.1 x₀.2 hx₀, fun u v huv => hmin huv⟩

theorem exists_abs_bound_on_rect {a b : ℝ × ℝ} {f : ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn (Function.uncurry f) (Set.Icc a b)) :
    ∃ B, ∀ u v, (u, v) ∈ Set.Icc a b → |f u v| ≤ B :=
  exists_abs_bound_of_continuousOn isCompact_Icc (Set.nonempty_Icc.mpr hab) hf

theorem exists_pos_lower_bound_on_rect {a b : ℝ × ℝ} {f : ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn (Function.uncurry f) (Set.Icc a b))
    (hpos : ∀ u v, (u, v) ∈ Set.Icc a b → 0 < f u v) :
    ∃ m, 0 < m ∧ ∀ u v, (u, v) ∈ Set.Icc a b → m ≤ f u v :=
  exists_pos_lower_bound_of_continuousOn isCompact_Icc (Set.nonempty_Icc.mpr hab) hf hpos

theorem eym_fields_bounds {K : Set (ℝ × ℝ)}
    {r r' Om Om' W W' : ℝ → ℝ → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hr : ContinuousOn (Function.uncurry r) K)
    (hr' : ContinuousOn (Function.uncurry r') K)
    (hOm : ContinuousOn (Function.uncurry Om) K)
    (hOm' : ContinuousOn (Function.uncurry Om') K)
    (hW : ContinuousOn (Function.uncurry W) K)
    (hW' : ContinuousOn (Function.uncurry W') K)
    (hDur : ContinuousOn (Function.uncurry (Du r)) K)
    (hDvr : ContinuousOn (Function.uncurry (Dv r)) K)
    (hDur' : ContinuousOn (Function.uncurry (Du r')) K)
    (hDvr' : ContinuousOn (Function.uncurry (Dv r')) K)
    (hDuvr : ContinuousOn (Function.uncurry (Duv r)) K)
    (hDuvr' : ContinuousOn (Function.uncurry (Duv r')) K)
    (hDuOm : ContinuousOn (Function.uncurry (Du Om)) K)
    (hDvOm : ContinuousOn (Function.uncurry (Dv Om)) K)
    (hDuOm' : ContinuousOn (Function.uncurry (Du Om')) K)
    (hDvOm' : ContinuousOn (Function.uncurry (Dv Om')) K)
    (hrpos : ∀ u v, (u, v) ∈ K → 0 < r u v)
    (hr'pos : ∀ u v, (u, v) ∈ K → 0 < r' u v)
    (hOmpos : ∀ u v, (u, v) ∈ K → 0 < Om u v)
    (hOm'pos : ∀ u v, (u, v) ∈ K → 0 < Om' u v) :
    ∃ BW BW' BOm BOm' Br Br' BDuR BDvR BDuR' BDvR' BDuvR BDuvR'
      BDuOm BDvOm BDuOm' BDvOm' mr mr' mOm mOm',
      (0 < mr ∧ 0 < mr' ∧ 0 < mOm ∧ 0 < mOm')
        ∧ (∀ u v, (u, v) ∈ K → |W u v| ≤ BW)
        ∧ (∀ u v, (u, v) ∈ K → |W' u v| ≤ BW')
        ∧ (∀ u v, (u, v) ∈ K → |Om u v| ≤ BOm)
        ∧ (∀ u v, (u, v) ∈ K → |Om' u v| ≤ BOm')
        ∧ (∀ u v, (u, v) ∈ K → |r u v| ≤ Br)
        ∧ (∀ u v, (u, v) ∈ K → |r' u v| ≤ Br')
        ∧ (∀ u v, (u, v) ∈ K → |Du r u v| ≤ BDuR)
        ∧ (∀ u v, (u, v) ∈ K → |Dv r u v| ≤ BDvR)
        ∧ (∀ u v, (u, v) ∈ K → |Du r' u v| ≤ BDuR')
        ∧ (∀ u v, (u, v) ∈ K → |Dv r' u v| ≤ BDvR')
        ∧ (∀ u v, (u, v) ∈ K → |Duv r u v| ≤ BDuvR)
        ∧ (∀ u v, (u, v) ∈ K → |Duv r' u v| ≤ BDuvR')
        ∧ (∀ u v, (u, v) ∈ K → |Du Om u v| ≤ BDuOm)
        ∧ (∀ u v, (u, v) ∈ K → |Dv Om u v| ≤ BDvOm)
        ∧ (∀ u v, (u, v) ∈ K → |Du Om' u v| ≤ BDuOm')
        ∧ (∀ u v, (u, v) ∈ K → |Dv Om' u v| ≤ BDvOm')
        ∧ (∀ u v, (u, v) ∈ K → mr ≤ r u v)
        ∧ (∀ u v, (u, v) ∈ K → mr' ≤ r' u v)
        ∧ (∀ u v, (u, v) ∈ K → mOm ≤ Om u v)
        ∧ (∀ u v, (u, v) ∈ K → mOm' ≤ Om' u v) := by
  obtain ⟨BW, hBW⟩ := exists_abs_bound_of_continuousOn hK hne hW
  obtain ⟨BW', hBW'⟩ := exists_abs_bound_of_continuousOn hK hne hW'
  obtain ⟨BOm, hBOm⟩ := exists_abs_bound_of_continuousOn hK hne hOm
  obtain ⟨BOm', hBOm'⟩ := exists_abs_bound_of_continuousOn hK hne hOm'
  obtain ⟨Br, hBr⟩ := exists_abs_bound_of_continuousOn hK hne hr
  obtain ⟨Br', hBr'⟩ := exists_abs_bound_of_continuousOn hK hne hr'
  obtain ⟨BDuR, hBDuR⟩ := exists_abs_bound_of_continuousOn hK hne hDur
  obtain ⟨BDvR, hBDvR⟩ := exists_abs_bound_of_continuousOn hK hne hDvr
  obtain ⟨BDuR', hBDuR'⟩ := exists_abs_bound_of_continuousOn hK hne hDur'
  obtain ⟨BDvR', hBDvR'⟩ := exists_abs_bound_of_continuousOn hK hne hDvr'
  obtain ⟨BDuvR, hBDuvR⟩ := exists_abs_bound_of_continuousOn hK hne hDuvr
  obtain ⟨BDuvR', hBDuvR'⟩ := exists_abs_bound_of_continuousOn hK hne hDuvr'
  obtain ⟨BDuOm, hBDuOm⟩ := exists_abs_bound_of_continuousOn hK hne hDuOm
  obtain ⟨BDvOm, hBDvOm⟩ := exists_abs_bound_of_continuousOn hK hne hDvOm
  obtain ⟨BDuOm', hBDuOm'⟩ := exists_abs_bound_of_continuousOn hK hne hDuOm'
  obtain ⟨BDvOm', hBDvOm'⟩ := exists_abs_bound_of_continuousOn hK hne hDvOm'
  obtain ⟨mr, hmrpos, hmrlow⟩ :=
    exists_pos_lower_bound_of_continuousOn hK hne hr hrpos
  obtain ⟨mr', hmr'pos, hmr'low⟩ :=
    exists_pos_lower_bound_of_continuousOn hK hne hr' hr'pos
  obtain ⟨mOm, hmOmpos, hmOmlow⟩ :=
    exists_pos_lower_bound_of_continuousOn hK hne hOm hOmpos
  obtain ⟨mOm', hmOm'pos, hmOm'low⟩ :=
    exists_pos_lower_bound_of_continuousOn hK hne hOm' hOm'pos
  exact ⟨BW, BW', BOm, BOm', Br, Br', BDuR, BDvR, BDuR', BDvR', BDuvR, BDuvR',
    BDuOm, BDvOm, BDuOm', BDvOm', mr, mr', mOm, mOm',
    ⟨hmrpos, hmr'pos, hmOmpos, hmOm'pos⟩,
    hBW, hBW', hBOm, hBOm', hBr, hBr', hBDuR, hBDvR, hBDuR', hBDvR',
    hBDuvR, hBDuvR', hBDuOm, hBDvOm, hBDuOm', hBDvOm',
    hmrlow, hmr'low, hmOmlow, hmOm'low⟩

end FieldEquations.CompactBounds
