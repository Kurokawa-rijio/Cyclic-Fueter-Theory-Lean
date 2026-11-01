import CFT.AlphaVI_Static
import CFT.AlphaVII_Commutant
import CFT.AlphaVI_Sech
import CFT.AlphaIV_Minisuperspace
import CFT.AlphaIV_WKB
import CFT.AlphaVI_Physical
import CFT.AlphaV_S3Dirac
import CFT.AlphaVII_Maxwell
import CFT.AlphaV_Backreaction
import CFT.AlphaIV_Reduction
import CFT.AlphaIV_WKB2
import CFT.AlphaVI_Physical2
import CFT.AlphaV_FRW
import CFT.AlphaVII_Tangent

#print axioms CFT.VIStatic.trace_einD
#print axioms CFT.VIStatic.rsc_static_S3
#print axioms CFT.VIStatic.static_S3_impossible
#print axioms CFT.VIStatic.tym_traceless
#print axioms CFT.VIStatic.static_S3_YM_impossible
#print axioms CFT.VIIComm.Rm_mem
#print axioms CFT.VIIComm.commutant_so4
#print axioms CFT.VIIComm.no_hypercharge_left
#print axioms CFT.VIIComm.weinberg_left_only
#print axioms CFT.VISech.cosh_ne
#print axioms CFT.VISech.sinh_sq
#print axioms CFT.VISech.hasDerivAt_th
#print axioms CFT.VISech.th_sq
#print axioms CFT.VISech.hasDerivAt_F
#print axioms CFT.VISech.th_eq
#print axioms CFT.VISech.th_top
#print axioms CFT.VISech.th_neg
#print axioms CFT.VISech.th_bot
#print axioms CFT.VISech.F_top
#print axioms CFT.VISech.F_bot
#print axioms CFT.VISech.sech4_cont
#print axioms CFT.VISech.integrable_sech4
#print axioms CFT.VISech.integral_sech4
#print axioms CFT.VISech.integral_two_sech4
#print axioms CFT.VISech.instanton_action_integral
#print axioms CFT.Mini.density_aux
#print axioms CFT.Mini.fsq_aux
#print axioms CFT.Mini.fsq_W0
#print axioms CFT.Mini.reduced_density
#print axioms CFT.Mini.L_ad
#print axioms CFT.Mini.L_bd
#print axioms CFT.Mini.legendre
#print axioms CFT.Mini.L_N
#print axioms CFT.WKB.hasDerivAt_Psi_a
#print axioms CFT.WKB.hasDerivAt_Psia_a
#print axioms CFT.WKB.hasDerivAt_Psi_b
#print axioms CFT.WKB.hasDerivAt_Psia_b
#print axioms CFT.WKB.wkb_identity
#print axioms CFT.WKB.hasDerivAt_Q
#print axioms CFT.WKB.wdw_exact_sqrt
#print axioms CFT.WKB.norm_Psi
#print axioms CFT.Phys.bracket_TH
#print axioms CFT.Phys.bracket_TH_weak
#print axioms CFT.Phys.K_eigen
#print axioms CFT.Phys.domain_nonempty_iff
#print axioms CFT.Phys.dS_dC
#print axioms CFT.Phys.phys_inner_nonneg
#print axioms CFT.Phys.phys_inner_eq_zero
#print axioms CFT.S3Dirac.lie_bracket
#print axioms CFT.S3Dirac.koszul
#print axioms CFT.S3Dirac.spin_term
#print axioms CFT.S3Dirac.reduced_dirac
#print axioms CFT.S3Dirac.level_singlet
#print axioms CFT.S3Dirac.level_triplet'
#print axioms CFT.S3Dirac.frame_tangent
#print axioms CFT.S3Dirac.frame_orthonormal
#print axioms CFT.S3Dirac.frame_deriv
#print axioms CFT.S3Dirac.frame_bracket
#print axioms CFT.S3Dirac.SS_dndn
#print axioms CFT.S3Dirac.SS_tsym
#print axioms CFT.S3Dirac.level_of
#print axioms CFT.S3Dirac.decomp
#print axioms CFT.S3Dirac.reduced_dirac_spectrum
#print axioms CFT.Maxwell.bianchi
#print axioms CFT.Maxwell.first_variation
#print axioms CFT.Maxwell.div_div_F
#print axioms CFT.Maxwell.current_conserved
#print axioms CFT.Backreaction.quad_solvable
#print axioms CFT.Backreaction.small_branch
#print axioms CFT.Backreaction.cap_friedmann
#print axioms CFT.Backreaction.continuity_radiation
#print axioms CFT.Backreaction.esu_backreaction
#print axioms CFT.Reduction.kext_divergence
#print axioms CFT.Reduction.ghy_boundary
#print axioms CFT.Reduction.action_with_ghy
#print axioms CFT.Reduction.angular_integral
#print axioms CFT.Reduction.reduced_coefficient
#print axioms CFT.Reduction.legendre_hessian
#print axioms CFT.Reduction.legendre_hessian_ne
#print axioms CFT.Reduction.legendre_inverse
#print axioms CFT.Reduction.legendre_onto
#print axioms CFT.Reduction.supermetric_kinetic
#print axioms CFT.Reduction.supermetric_inverse
#print axioms CFT.Reduction.hamiltonian_supermetric
#print axioms CFT.Reduction.lb_coeff_a
#print axioms CFT.Reduction.lb_coeff_b
#print axioms CFT.Reduction.lb_operator
#print axioms CFT.WKB2.wdw_exact_of
#print axioms CFT.WKB2.wdw_exact_neg
#print axioms CFT.WKB2.wdwOp_linear
#print axioms CFT.WKB2.wdw_exact_LB
#print axioms CFT.Phys2.physical_branch
#print axioms CFT.Phys2.K_minus_min
#print axioms CFT.Phys2.K_gt_min
#print axioms CFT.Phys2.affine_bracket
#print axioms CFT.Phys2.translation_norm
#print axioms CFT.Phys2.dilation_isometry
#print axioms CFT.Phys2.hasDerivAt_Q_C
#print axioms CFT.Phys2.d2S_dC2
#print axioms CFT.Phys2.stationary_nondegenerate
#print axioms CFT.Phys2.domain_Ioi
#print axioms CFT.Phys2.T_strictAnti
#print axioms CFT.Phys2.stationary_unique
#print axioms CFT.FRW.frw_subs
#print axioms CFT.FRW.frw_r0
#print axioms CFT.FRW.frw_r1
#print axioms CFT.FRW.frw_r2
#print axioms CFT.FRW.frw_r3
#print axioms CFT.FRW.frw_ric01
#print axioms CFT.FRW.frw_rsc
#print axioms CFT.FRW.frw_G00
#print axioms CFT.FRW.h3_frw
#print axioms CFT.FRW.ricci_sq_identity
#print axioms CFT.FRW.esu_trace_zero
#print axioms CFT.FRW.h3_conserved
#print axioms CFT.FRW.friedmann_quadratic
#print axioms CFT.FRW.cap_semiclassical
#print axioms CFT.Tangent.chart_derivative
#print axioms CFT.Tangent.transition_on_equator
#print axioms CFT.Tangent.transition_winding
#print axioms CFT.Tangent.tangent_single_valued
#print axioms CFT.Tangent.tangent_chern
#print axioms CFT.Tangent.euler_char_two
#print axioms CFT.Tangent.chern_eq_euler
