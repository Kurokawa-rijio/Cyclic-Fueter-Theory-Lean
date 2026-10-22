import CFT.AlphaS4_Final
import CFT.AlphaS5_Curvature
import CFT.AlphaV_GaussMap
import CFT.AlphaS5_Final
import CFT.AlphaS3_Mass
import CFT.AlphaS3_Closure
import CFT.AlphaS2_4DMatch
open Lean Elab Command

/-- 定理 n の証明本体が(推移的に)参照する定数の集合に k が含まれるか。
    型に現れるだけの定数は数えず、証明依存と型依存を分離する。-/
partial def usesConstInProof (env : Environment) (n k : Name) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c == k then return true
    match env.find? c with
    | some ci =>
      let deps := (ci.value?.map Expr.getUsedConstants).getD #[]
      for d in deps do
        if !seen.contains d && (d.getRoot == `CFT) then todo := todo.push d
    | none => pure ()
  return false

/-- 定理 n の型宣言が(推移的に)参照する定数。証明本体の依存とは別に報告する。-/
partial def usesConstInType (env : Environment) (n k : Name) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c == k then return true
    match env.find? c with
    | some ci =>
      let deps := ci.type.getUsedConstants
      for d in deps do
        if !seen.contains d && (d.getRoot == `CFT) then todo := todo.push d
    | none => pure ()
  return false

elab "#uses " n:ident " [" ks:ident,* "]" : command => do
  let env ← getEnv
  let n := n.getId
  for k in ks.getElems do
    let kn := k.getId
    let b := usesConstInProof env n kn
    logInfo m!"{n} uses {kn}: {b}"

elab "#type_uses " n:ident " [" ks:ident,* "]" : command => do
  let env ← getEnv
  let n := n.getId
  for k in ks.getElems do
    let kn := k.getId
    let b := usesConstInType env n kn
    logInfo m!"{n} has type-dependency on {kn}: {b}"

#uses CFT.S4F.timelike_final [CFT.S4D.delta_coeff_weighted, CFT.S4D.nn_eq_eval, CFT.S4J.tube_israel, CFT.S4J.timelike_no_go, CFT.S4J.gauss_tube, CFT.S4J.tnn_tube, CFT.S4J.tube_tt_form, CFT.S4J.tube_ang_form, CFT.S4.einD_00, CFT.S4.ricD_00, CFT.S4.tymD_11]
#uses CFT.S4F.color_final [CFT.S4D.delta_coeff_weighted, CFT.S4D.ymD_split, CFT.S4D.ymD_02, CFT.S4.fym_eq]
#uses CFT.S4F.slice_final [CFT.S4D.delta_coeff_weighted, CFT.S4J.tube_tt_form, CFT.S4.einD_00]
#uses CFT.S4F.null_final [CFT.S4D.delta_coeff_weighted, CFT.S4J.uu_form, CFT.S4J.mixed_eq, CFT.S4D.trace_deriv_eq, CFT.S4J.null_front_from_mixed, CFT.S4J.jump_transport, CFT.S4.einN_00, CFT.S4.tymN_01]
#uses CFT.S4D.timelike_dumbbell [CFT.S4D.delta_coeff_weighted, CFT.S4D.nn_eq_eval]
#uses CFT.S4D.null_front_weak [CFT.S4D.delta_coeff_weighted]
#uses CFT.S5.goursat_W [CFT.S5.ymN_02]
#uses CFT.S5.constraint_prop_u [CFT.S5.goursat_r]
#uses CFT.S5K.kret_cap [CFT.S5K.kretD, CFT.S5.capSph]
#uses CFT.S5.cap_00 [CFT.S4.einD_00, CFT.S4.tymD_00]
#uses CFT.GaussMap.normal_unique [CFT.GaussMap.ip_smul_left]
#uses CFT.S4F.timelike_final [CFT.S4.fym_eq, CFT.S4F.shell_coeff]
#uses CFT.S4F.color_final [CFT.S4.fym_eq]
#uses CFT.S4F.null_final [CFT.S4.fym_eq, CFT.S4J.mixed_eq]
#uses CFT.S5F.wave_jump_final [CFT.S5.goursat_W, CFT.S5.ymN_02, CFT.S4.fym_eq]
#uses CFT.S5F.cap_crunch_final [CFT.S5.cap_00, CFT.S5.cap_22, CFT.S5K.kret_cap, CFT.S5K.kretD, CFT.S5K.kret_blowup, CFT.S4.fym_eq, CFT.S4.einD_22]
#uses CFT.S5K.constraint_prop_from_eqs [CFT.S5.goursat_r, CFT.S5.goursat_Om, CFT.S5.goursat_W, CFT.S5.constraint_prop_u, CFT.S5.constraint_prop_v]
#uses CFT.S3M.min_mass_from_constraints [CFT.Shape.penrose_from_constraints, CFT.AlphaIII.min_mass]
#uses CFT.S3.c2_window [CFT.Cartan.C2.kappa_nonpos, CFT.S3.strict_window, CFT.AlphaII.kappa_closed]

-- 2026-10-21j:新しい定理の証明本体依存を確認する。
#uses CFT.S4F.null_final [CFT.S4D.delta_coeff_weighted, CFT.S4D.trace_deriv_eq, CFT.S4J.null_front_from_mixed]
#uses CFT.S3M.min_mass_from_constraints [CFT.EYM.ell_neck, CFT.Shape.penrose_from_constraints, CFT.AlphaIII.min_mass]
#uses CFT.GaussMap.profile_immersion_data [CFT.GaussMap.embed_exists, CFT.GaussMap.X_deriv, CFT.GaussMap.embed_metric]
#uses CFT.GaussMap.profileMap_injective [CFT.GaussMap.zProfile]
#type_uses CFT.S4F.null_final [CFT.S4D.delta_coeff_weighted, CFT.S4D.trace_deriv_eq]
-- 2026-10-21 第 10 弾:段階 2 の 4 次元照合(Palais を使わない)
#uses CFT.S2M.full_4d_iff_alpha [CFT.S2M.sync_00, CFT.S2M.sync_01, CFT.S2M.sync_11, CFT.S2M.sync_22, CFT.S2M.sync_33, CFT.S2M.ym_sync_02, CFT.S2M.ym_sync_13, CFT.S2M.ymA_00, CFT.S2M.ymA_23, CFT.S4.fym_eq]
#uses CFT.S2M.sync_00 [CFT.S2M.einA_00, CFT.S2M.tymA_00]
#uses CFT.S2M.ym_sync_02 [CFT.S4D.ymD_split]
#uses CFT.S2M.palais_free [CFT.S2M.full_4d_iff_alpha, CFT.S2.el_iff_alpha]
