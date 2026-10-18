/- α-II.5:2 段目の捩れの式が C2 枠で成り立つこと(row3) -/
import CFT.Cartan.SSFirst
import CFT.Cartan.SSJet
import CFT.Cartan.SSCoefR3

namespace CFT.Cartan

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- 大きな多項式の elaborate を速くするための局所インスタンス(標準のものと定義上同じ) -/
local instance (priority := high) hmR_SSRows1a : HMul R R R := instHMul
local instance (priority := high) haR_SSRows1a : HAdd R R R := instHAdd
local instance (priority := high) hsR_SSRows1a : HSub R R R := instHSub
local instance (priority := high) hpR_SSRows1a : HPow R ℕ R := instHPow
local instance (priority := high) ngR_SSRows1a : Neg R := inferInstance

namespace C2

variable {F : Frame R} {lam : Fin 3 → R} (H : C2 F lam)
include H

theorem row3 : n3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam))) = 0 := by
  have t := F.torsion 0 1 (beta F lam)
  simp only [Fin.sum_univ_three] at t
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at t
  have d01be := congrArg (F.e 0) H.fs1be
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, Nat.cast_ofNat, pow_one, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at d01be
  have d10be := congrArg (F.e 1) H.fs0be
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, Nat.cast_ofNat, pow_one, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at d10be
  have key : (((-2 * (lam 0) * ((lam 2)^(3:ℕ))) + (-2 * (lam 2) * ((lam 0)^(3:ℕ))) + (-2 * ((lam 0)^(2:ℕ)) * ((lam 1)^(2:ℕ))) + (-2 * ((lam 1)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (2 * (lam 1) * ((lam 0)^(3:ℕ))) + (2 * (lam 1) * ((lam 2)^(3:ℕ))) + (4 * ((lam 0)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (-2 * (lam 0) * (lam 1) * ((lam 2)^(2:ℕ))) + (-2 * (lam 1) * (lam 2) * ((lam 0)^(2:ℕ))) + (4 * (lam 0) * (lam 2) * ((lam 1)^(2:ℕ))))) * n3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam))) = 0 := by
    have g0 : (cfr3_0 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr3_1 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr3_2 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr3_3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr3_4 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (F.e 2 (gamma F lam))) + (cfr3_5 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (F.e 2 (eta F lam))) + 1 * (n3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam)))) + (cfr3_6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_0, cfr3_1, cfr3_2, cfr3_3, cfr3_4, cfr3_5, cfr3_6, n3]
      ring
    have g1 : (cfr3_8 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (beta F lam)) + (cfr3_9 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfr3_10 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + 1 * (F.e 0 (F.e 1 (beta F lam))) + (-1) * (F.e 1 (F.e 0 (beta F lam))) = 0 := by
      simp only [cfr3_8, cfr3_9, cfr3_10]
      linear_combination t
    have g2 : (cfr3_12 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (alpha F lam)) + (cfr3_13 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (beta F lam)) + (cfr3_14 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (gamma F lam)) + (cfr3_15 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (eta F lam)) + (cfr3_16 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfr3_17 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr3_18 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (F.e 2 (gamma F lam))) + (cfr3_19 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (F.e 1 (beta F lam))) + (cfr3_20 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_12, cfr3_13, cfr3_14, cfr3_15, cfr3_16, cfr3_17, cfr3_18, cfr3_19, cfr3_20]
      linear_combination d01be
    have g3 : (cfr3_22 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfr3_23 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr3_24 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_22, cfr3_23, cfr3_24]
      linear_combination H.fs1be
    have g4 : (cfr3_26 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (alpha F lam)) + (cfr3_27 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr3_28 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_26, cfr3_27, cfr3_28]
      linear_combination H.fs0al
    have g5 : (cfr3_30 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (beta F lam)) + (cfr3_31 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr3_32 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_30, cfr3_31, cfr3_32]
      linear_combination H.fs0be
    have g6 : (cfr3_34 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (gamma F lam)) + (cfr3_35 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr3_36 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_34, cfr3_35, cfr3_36]
      linear_combination H.fs0ga
    have g7 : (cfr3_38 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (eta F lam)) + (cfr3_39 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr3_40 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_38, cfr3_39, cfr3_40]
      linear_combination H.fs0et
    have g8 : (cfr3_42 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (beta F lam)) + (cfr3_43 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (alpha F lam)) + (cfr3_44 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfr3_45 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (gamma F lam)) + (cfr3_46 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (eta F lam)) + (cfr3_47 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr3_48 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (F.e 2 (eta F lam))) + (cfr3_49 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (F.e 0 (beta F lam))) + (cfr3_50 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_42, cfr3_43, cfr3_44, cfr3_45, cfr3_46, cfr3_47, cfr3_48, cfr3_49, cfr3_50]
      linear_combination d10be
    have g9 : (cfr3_52 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (alpha F lam)) + (cfr3_53 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr3_54 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_52, cfr3_53, cfr3_54]
      linear_combination H.fs1al
    have g10 : (cfr3_56 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (gamma F lam)) + (cfr3_57 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr3_58 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_56, cfr3_57, cfr3_58]
      linear_combination H.fs1ga
    have g11 : (cfr3_60 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (eta F lam)) + (cfr3_61 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr3_62 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr3_60, cfr3_61, cfr3_62]
      linear_combination H.fs1et
    have k0 := cfr3_k0 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k1 := cfr3_k1 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k2 := cfr3_k2 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k3 := cfr3_k3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k4 := cfr3_k4 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k5 := cfr3_k5 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k6 := cfr3_k6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k7 := cfr3_k7 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k8 := cfr3_k8 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k9 := cfr3_k9 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k10 := cfr3_k10 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k11 := cfr3_k11 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k12 := cfr3_k12 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k13 := cfr3_k13 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k14 := cfr3_k14 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k15 := cfr3_k15 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k16 := cfr3_k16 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k17 := cfr3_k17 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    linear_combination ((cfr3_7 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g0 + ((cfr3_11 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g1 + ((cfr3_21 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g2 + ((cfr3_25 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g3 + ((cfr3_29 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g4 + ((cfr3_33 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g5 + ((cfr3_37 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g6 + ((cfr3_41 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g7 + ((cfr3_51 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g8 + ((cfr3_55 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g9 + ((cfr3_59 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g10 + ((cfr3_63 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g11 + 1 * k0 + (n3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam)))) * k1 + (F.e 1 (F.e 0 (beta F lam))) * k2 + (F.e 0 (F.e 1 (beta F lam))) * k3 + (F.e 1 (F.e 2 (eta F lam))) * k4 + (F.e 0 (F.e 2 (gamma F lam))) * k5 + (F.e 2 (eta F lam)) * k6 + (F.e 2 (gamma F lam)) * k7 + (F.e 2 (beta F lam)) * k8 + (F.e 2 (alpha F lam)) * k9 + (F.e 1 (eta F lam)) * k10 + (F.e 1 (gamma F lam)) * k11 + (F.e 1 (beta F lam)) * k12 + (F.e 1 (alpha F lam)) * k13 + (F.e 0 (eta F lam)) * k14 + (F.e 0 (gamma F lam)) * k15 + (F.e 0 (beta F lam)) * k16 + (F.e 0 (alpha F lam)) * k17
  have hU : IsUnit (((-2 * (lam 0) * ((lam 2)^(3:ℕ))) + (-2 * (lam 2) * ((lam 0)^(3:ℕ))) + (-2 * ((lam 0)^(2:ℕ)) * ((lam 1)^(2:ℕ))) + (-2 * ((lam 1)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (2 * (lam 1) * ((lam 0)^(3:ℕ))) + (2 * (lam 1) * ((lam 2)^(3:ℕ))) + (4 * ((lam 0)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (-2 * (lam 0) * (lam 1) * ((lam 2)^(2:ℕ))) + (-2 * (lam 1) * (lam 2) * ((lam 0)^(2:ℕ))) + (4 * (lam 0) * (lam 2) * ((lam 1)^(2:ℕ))))) := by
    have e : ((-2 * (lam 0) * ((lam 2)^(3:ℕ))) + (-2 * (lam 2) * ((lam 0)^(3:ℕ))) + (-2 * ((lam 0)^(2:ℕ)) * ((lam 1)^(2:ℕ))) + (-2 * ((lam 1)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (2 * (lam 1) * ((lam 0)^(3:ℕ))) + (2 * (lam 1) * ((lam 2)^(3:ℕ))) + (4 * ((lam 0)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (-2 * (lam 0) * (lam 1) * ((lam 2)^(2:ℕ))) + (-2 * (lam 1) * (lam 2) * ((lam 0)^(2:ℕ))) + (4 * (lam 0) * (lam 2) * ((lam 1)^(2:ℕ)))) = ((2 : R) ^ 1 * (lam 0 - lam 1) ^ 1 * (lam 0 - lam 2) ^ 2 * (lam 1 - lam 2) ^ 1) := by ring
    rw [e]; exact H.unit_prod 1 1 2 1
  exact hU.mul_right_eq_zero.mp key

end C2

end CFT.Cartan
