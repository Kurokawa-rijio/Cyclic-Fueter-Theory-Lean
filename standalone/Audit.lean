import FieldEquations.Characteristic.Dependence
import FieldEquations.Characteristic.Goursat
import FieldEquations.Characteristic.Gronwall
import FieldEquations.Characteristic.LinearStability
import FieldEquations.Characteristic.Uniqueness
import FieldEquations.Gravity.BianchiSecond
import FieldEquations.Gravity.CartanPalatini
import FieldEquations.Gravity.ContractedBianchi
import FieldEquations.Gravity.CurvatureJet
import FieldEquations.Gravity.FrameCoordinate
import FieldEquations.Gravity.Geodesic
import FieldEquations.Gravity.Linearized
import FieldEquations.Gravity.TorsionLorentz
import FieldEquations.Quaternionic.AdS2Killing
import FieldEquations.Quaternionic.CayleyForm
import FieldEquations.Quaternionic.ContinuumLaws
import FieldEquations.Quaternionic.FueterForms
import FieldEquations.Quaternionic.Mechanics
import FieldEquations.Quaternionic.MonopoleLangevin
import FieldEquations.Quaternionic.NullField
import FieldEquations.Quaternionic.Octonion
import FieldEquations.Quaternionic.Operators
import FieldEquations.Quaternionic.SelfDual
import FieldEquations.SphericalEYM.CompactBounds
import FieldEquations.SphericalEYM.Dependence
import FieldEquations.SphericalEYM.LocalExistence
import FieldEquations.SphericalEYM.System
import FieldEquations.SphericalEYM.Truncation
import FieldEquations.SphericalEYM.Uniqueness

#print axioms FieldEquations.CharacteristicDependence.char_gronwall_inhom
#print axioms FieldEquations.CharacteristicDependence.abs_le_add_integral_abs
#print axioms FieldEquations.CharacteristicDependence.char_dependence
#print axioms FieldEquations.Goursat.slice_v
#print axioms FieldEquations.Goursat.slice_u
#print axioms FieldEquations.Goursat.primV_cont
#print axioms FieldEquations.Goursat.primU_cont
#print axioms FieldEquations.Goursat.primUV_cont
#print axioms FieldEquations.Goursat.primV_deriv
#print axioms FieldEquations.Goursat.primU_deriv
#print axioms FieldEquations.Goursat.primUV_deriv_u
#print axioms FieldEquations.Goursat.primUV_deriv_v
#print axioms FieldEquations.Goursat.primUV_zero_right
#print axioms FieldEquations.Goursat.primUV_zero_left
#print axioms FieldEquations.Goursat.primV_sub
#print axioms FieldEquations.Goursat.primU_sub
#print axioms FieldEquations.Goursat.primUV_sub
#print axioms FieldEquations.Goursat.exp_cont_aux
#print axioms FieldEquations.Goursat.primV_bound
#print axioms FieldEquations.Goursat.primU_bound
#print axioms FieldEquations.Goursat.primUV_bound
#print axioms FieldEquations.Goursat.GlobalC2.toC2Data
#print axioms FieldEquations.Goursat.Uof_C2
#print axioms FieldEquations.Goursat.cont_of_lip
#print axioms FieldEquations.Goursat.extR_cont
#print axioms FieldEquations.Goursat.wz_cont
#print axioms FieldEquations.Goursat.goursat_exists
#print axioms FieldEquations.CharacteristicGronwall.exp_int_le
#print axioms FieldEquations.CharacteristicGronwall.char_gronwall_on
#print axioms FieldEquations.CharacteristicGronwall.char_gronwall
#print axioms FieldEquations.CharacteristicGronwall.char_gronwall_triple
#print axioms FieldEquations.LinearStability.linear_rhs_bound
#print axioms FieldEquations.LinearStability.linear_stability
#print axioms FieldEquations.CharacteristicUniqueness.C2Data.sub
#print axioms FieldEquations.CharacteristicUniqueness.abs_le_integral_abs
#print axioms FieldEquations.CharacteristicUniqueness.sliceOn1
#print axioms FieldEquations.CharacteristicUniqueness.sliceOn2
#print axioms FieldEquations.CharacteristicUniqueness.edge_deriv_zero
#print axioms FieldEquations.CharacteristicUniqueness.char_uniqueness
#print axioms FieldEquations.Curvature.gauge_bianchi
#print axioms curv_apply
#print axioms nablaR_explicit
#print axioms bianchi_second
#print axioms FieldEquations.CartanPalatini.eps_0123
#print axioms FieldEquations.CartanPalatini.eps_swap12
#print axioms FieldEquations.CartanPalatini.eps_swap23
#print axioms FieldEquations.CartanPalatini.eps_swap34
#print axioms FieldEquations.CartanPalatini.cartan_einstein
#print axioms FieldEquations.CartanPalatini.quad_expansion
#print axioms FieldEquations.CartanPalatini.first_variation_hasDerivAt
#print axioms FieldEquations.CartanPalatini.Lb_k_delta
#print axioms FieldEquations.CartanPalatini.Lb_delta_k
#print axioms FieldEquations.CartanPalatini.first_variation
#print axioms FieldEquations.CartanPalatini.pick
#print axioms FieldEquations.CartanPalatini.einstein_iff_stationary
#print axioms FieldEquations.CartanPalatini.einstein_with_matter
#print axioms FieldEquations.ContractedBianchi.relabel_pairs
#print axioms FieldEquations.ContractedBianchi.relabel_within
#print axioms FieldEquations.ContractedBianchi.relabel_reverse
#print axioms FieldEquations.ContractedBianchi.S4_congr
#print axioms FieldEquations.ContractedBianchi.contracted_bianchi_normal
#print axioms FieldEquations.Curvature.riemann_antisymm
#print axioms FieldEquations.Curvature.bianchi_first
#print axioms MetricJet.chr1_symm
#print axioms MetricJet.metric_compat
#print axioms MetricJet.dchr1_symm
#print axioms MetricJet.chr2_symm
#print axioms MetricJet.dchr2_symm
#print axioms MetricJet.bianchi_first_metric
#print axioms MetricJet.riem_antisymm
#print axioms FieldEquations.FrameCoordinate.sum3
#print axioms FieldEquations.FrameCoordinate.sum4
#print axioms FieldEquations.FrameCoordinate.sum5
#print axioms FieldEquations.FrameCoordinate.sum_mul_sum'
#print axioms FieldEquations.FrameCoordinate.complete_of_heE
#print axioms FieldEquations.FrameCoordinate.metric_inverse
#print axioms FieldEquations.FrameCoordinate.ricci_frame
#print axioms FieldEquations.FrameCoordinate.scalar_frame
#print axioms FieldEquations.FrameCoordinate.metric_frame
#print axioms FieldEquations.FrameCoordinate.einstein_frame
#print axioms FieldEquations.FrameCoordinate.coord_of_frame
#print axioms FieldEquations.FrameCoordinate.einstein_frame_iff
#print axioms FieldEquations.FrameCoordinate.RF_antisymm1
#print axioms FieldEquations.FrameCoordinate.RF_antisymm2
#print axioms FieldEquations.FrameCoordinate.GF_etaL
#print axioms FieldEquations.FrameCoordinate.einstein_lorentz_coord
#print axioms FieldEquations.Geodesic.geodesic_EL
#print axioms FieldEquations.LinearizedGravity.d_half
#print axioms FieldEquations.LinearizedGravity.ric_gauge
#print axioms FieldEquations.LinearizedGravity.lin_bianchi
#print axioms FieldEquations.LinearizedGravity.matter_conservation
#print axioms FieldEquations.LinearizedGravity.G_harmonic
#print axioms FieldEquations.LinearizedGravity.G_lorenz_gauge
#print axioms FieldEquations.LinearizedGravity.gw_vacuum
#print axioms FieldEquations.LinearizedGravity.newton_G00
#print axioms FieldEquations.LinearizedGravity.newton_poisson
#print axioms FieldEquations.LinearizedGravity.newton_christoffel
#print axioms FieldEquations.CartanPalatini.torsion_contraction
#print axioms FieldEquations.CartanPalatini.torsion_free_of_stationary
#print axioms FieldEquations.CartanPalatini.levi_civita_unique
#print axioms FieldEquations.CartanPalatini.etaL_sq
#print axioms FieldEquations.CartanPalatini.eps_raise
#print axioms FieldEquations.CartanPalatini.Gt_Rt
#print axioms FieldEquations.CartanPalatini.cartan_einstein_lorentz
#print axioms FieldEquations.CartanPalatini.einstein_lorentz_iff
#print axioms FieldEquations.Curvature.curv_gauge_covariant
#print axioms FieldEquations.AdS2Killing.hasDerivAt_f
#print axioms FieldEquations.AdS2Killing.xi1_a_eta
#print axioms FieldEquations.AdS2Killing.xi1_a_chi
#print axioms FieldEquations.AdS2Killing.xi1_b_eta
#print axioms FieldEquations.AdS2Killing.xi1_b_chi
#print axioms FieldEquations.AdS2Killing.xi2_a_eta
#print axioms FieldEquations.AdS2Killing.xi2_a_chi
#print axioms FieldEquations.AdS2Killing.xi2_b_eta
#print axioms FieldEquations.AdS2Killing.xi2_b_chi
#print axioms FieldEquations.AdS2Killing.killing_xi0
#print axioms FieldEquations.AdS2Killing.killing_xi1
#print axioms FieldEquations.AdS2Killing.killing_xi2
#print axioms FieldEquations.AdS2Killing.comm_01_a
#print axioms FieldEquations.AdS2Killing.comm_01_b
#print axioms FieldEquations.AdS2Killing.comm_02_a
#print axioms FieldEquations.AdS2Killing.comm_02_b
#print axioms FieldEquations.AdS2Killing.comm_12_a
#print axioms FieldEquations.AdS2Killing.comm_12_b
#print axioms FieldEquations.Octonion.TwoForm.T_quadratic
#print axioms FieldEquations.Octonion.TwoForm.T_rightForm
#print axioms FieldEquations.Octonion.TwoForm.rightForm_spec
#print axioms FieldEquations.Octonion.TwoForm.T_decomp
#print axioms FieldEquations.Octonion.TwoForm.T_eigen_neg_one
#print axioms FieldEquations.Octonion.TwoForm.proj7_rightForm
#print axioms FieldEquations.Octonion.TwoForm.proj7_T
#print axioms FieldEquations.Octonion.TwoForm.cayley_link
#print axioms FieldEquations.Continuum.d_half'
#print axioms FieldEquations.Continuum.navier_stokes
#print axioms FieldEquations.Continuum.bernoulli
#print axioms FieldEquations.Continuum.navier_cauchy
#print axioms FieldEquations.Continuum.sound_wave
#print axioms FieldEquations.Continuum.coulomb_harmonic
#print axioms FieldEquations.Continuum.coulomb_field
#print axioms FieldEquations.FueterForms.vec_vector
#print axioms FieldEquations.FueterForms.fueter_regular_iff
#print axioms FieldEquations.FueterForms.vec_vec
#print axioms FieldEquations.FueterForms.maxwell_biquaternion
#print axioms FieldEquations.FueterForms.maxwell_single_equation
#print axioms FieldEquations.FueterForms.em_square
#print axioms FieldEquations.FueterForms.em_square_invariant
#print axioms FieldEquations.FueterForms.mass_shell_biquaternion
#print axioms bernoulli_fueter
#print axioms ns_viscous_fueter
#print axioms coulomb_fueter
#print axioms box_bridge
#print axioms lorenz_gauge_fueter
#print axioms quaternion_gauge_bianchi
#print axioms FieldEquations.QuaternionMechanics.ks_pure
#print axioms FieldEquations.QuaternionMechanics.ks_norm
#print axioms FieldEquations.QuaternionMechanics.ks_velocity
#print axioms FieldEquations.QuaternionMechanics.ks_speed
#print axioms FieldEquations.QuaternionMechanics.euler_commutator
#print axioms ks_oscillator
#print axioms dq_mul
#print axioms dq_star
#print axioms dq_add
#print axioms frame_geodesic_speed
#print axioms attitude_unit
#print axioms FieldEquations.MonopoleLangevin.sinh_ne
#print axioms FieldEquations.MonopoleLangevin.W_eq_inv_Z
#print axioms FieldEquations.MonopoleLangevin.Z_integral
#print axioms FieldEquations.MonopoleLangevin.hasDerivAt_Z
#print axioms FieldEquations.MonopoleLangevin.hasDerivAt_logZ
#print axioms FieldEquations.MonopoleLangevin.bogomolny_W
#print axioms FieldEquations.MonopoleLangevin.bogomolny_h
#print axioms FieldEquations.NullField.M_det
#print axioms FieldEquations.NullField.M_sq
#print axioms FieldEquations.NullField.M_sq_zero_iff
#print axioms FieldEquations.NullField.M_det_zero_iff
#print axioms FieldEquations.NullField.pauli_param
#print axioms FieldEquations.NullField.fsq_re
#print axioms FieldEquations.NullField.fsq_im
#print axioms FieldEquations.NullField.null_iff
#print axioms FieldEquations.NullField.null_iff_nilpotent
#print axioms FieldEquations.Octonion.normSq_mul
#print axioms FieldEquations.Octonion.left_alt
#print axioms FieldEquations.Octonion.right_alt
#print axioms FieldEquations.Octonion.flexible
#print axioms FieldEquations.Octonion.moufang_left
#print axioms FieldEquations.Octonion.moufang_right
#print axioms FieldEquations.Octonion.moufang_middle
#print axioms FieldEquations.Octonion.conj_mul
#print axioms FieldEquations.Octonion.mul_conj
#print axioms FieldEquations.Octonion.conj_mul_self
#print axioms FieldEquations.Octonion.inner_mul_left
#print axioms FieldEquations.Octonion.inner_mul_right
#print axioms FieldEquations.Octonion.not_assoc
#print axioms FieldEquations.Octonion.null_example
#print axioms FieldEquations.QuaternionOperators.conj_product
#print axioms FieldEquations.QuaternionOperators.product_conj
#print axioms FieldEquations.QuaternionOperators.square
#print axioms FieldEquations.QuaternionOperators.square_sum
#print axioms FieldEquations.QuaternionOperators.biquaternion_box
#print axioms FieldEquations.SelfDual.star_star
#print axioms FieldEquations.SelfDual.star_leftForm
#print axioms FieldEquations.SelfDual.star_rightForm
#print axioms FieldEquations.SelfDual.leftForm_spec
#print axioms FieldEquations.SelfDual.rightForm_spec
#print axioms FieldEquations.SelfDual.decomp
#print axioms FieldEquations.SelfDual.selfDual_of_right_zero
#print axioms FieldEquations.SelfDual.antiSelfDual_of_left_zero
#print axioms FieldEquations.CompactBounds.exists_abs_bound_of_continuousOn
#print axioms FieldEquations.CompactBounds.exists_pos_lower_bound_of_continuousOn
#print axioms FieldEquations.CompactBounds.exists_abs_bound_on_rect
#print axioms FieldEquations.CompactBounds.exists_pos_lower_bound_on_rect
#print axioms FieldEquations.CompactBounds.eym_fields_bounds
#print axioms FieldEquations.EYMDependence.eym_dependence
#print axioms FieldEquations.EYMLocalExistence.sameDataOn_of_charData
#print axioms FieldEquations.EYMLocalExistence.abs_le_of_near
#print axioms FieldEquations.EYMLocalExistence.eym_local_existence
#print axioms FieldEquations.EYMLocalExistence.eym_local_wellposed
#print axioms FieldEquations.EYMTruncation.clampIcc_lip
#print axioms FieldEquations.EYMTruncation.clampIcc_ge
#print axioms FieldEquations.EYMTruncation.clampIcc_le
#print axioms FieldEquations.EYMTruncation.clampIcc_of
#print axioms FieldEquations.EYMTruncation.trunc_good
#print axioms FieldEquations.EYMTruncation.trunc_pdist
#print axioms FieldEquations.EYMTruncation.trunc_of
#print axioms FieldEquations.EYMTruncation.lip_trunc
#print axioms FieldEquations.EYMTruncation.toPt_pdist
#print axioms FieldEquations.EYMTruncation.Fw_lip
#print axioms FieldEquations.EYMUniqueness.pdist_nonneg
#print axioms FieldEquations.EYMUniqueness.abs_add_le'
#print axioms FieldEquations.EYMUniqueness.abs_sub_le'
#print axioms FieldEquations.EYMUniqueness.UL_congr
#print axioms FieldEquations.EYMUniqueness.UL_const
#print axioms FieldEquations.EYMUniqueness.UL_var
#print axioms FieldEquations.EYMUniqueness.pdist_ge
#print axioms FieldEquations.EYMUniqueness.UL_Om
#print axioms FieldEquations.EYMUniqueness.UL_W
#print axioms FieldEquations.EYMUniqueness.UL_ru
#print axioms FieldEquations.EYMUniqueness.UL_rv
#print axioms FieldEquations.EYMUniqueness.UL_Ou
#print axioms FieldEquations.EYMUniqueness.UL_Ov
#print axioms FieldEquations.EYMUniqueness.UL_inv_of
#print axioms FieldEquations.EYMUniqueness.UL_invr
#print axioms FieldEquations.EYMUniqueness.UL_invOm
#print axioms FieldEquations.EYMUniqueness.UL_add
#print axioms FieldEquations.EYMUniqueness.UL_sub
#print axioms FieldEquations.EYMUniqueness.UL_mul
#print axioms FieldEquations.EYMUniqueness.UL_oneMinusW2
#print axioms FieldEquations.EYMUniqueness.UL_rhsR
#print axioms FieldEquations.EYMUniqueness.UL_rhsOm
#print axioms FieldEquations.EYMUniqueness.UL_rhsW
#print axioms FieldEquations.EYMUniqueness.eymEqsOn_of_global
#print axioms FieldEquations.EYMUniqueness.eym_uniqueness
#print axioms FieldEquations.EYMUniqueness.eym_uniqueness_of_pos
