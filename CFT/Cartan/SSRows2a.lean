/- α-II.5:2 段目の捩れの式が C2 枠で成り立つこと(row6) -/
import CFT.Cartan.SSFirst
import CFT.Cartan.SSJet
import CFT.Cartan.SSCoefR6

namespace CFT.Cartan

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- 大きな多項式の elaborate を速くするための局所インスタンス(標準のものと定義上同じ) -/
local instance (priority := high) hmR_SSRows2a : HMul R R R := instHMul
local instance (priority := high) haR_SSRows2a : HAdd R R R := instHAdd
local instance (priority := high) hsR_SSRows2a : HSub R R R := instHSub
local instance (priority := high) hpR_SSRows2a : HPow R ℕ R := instHPow
local instance (priority := high) ngR_SSRows2a : Neg R := inferInstance

namespace C2

variable {F : Frame R} {lam : Fin 3 → R} (H : C2 F lam)
include H

theorem row6 : n6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam))) = 0 := by
  have t := F.torsion 0 1 (gamma F lam)
  simp only [Fin.sum_univ_three] at t
  try simp only [F.metric 1 0, F.metric 2 0, F.metric 2 1, F.Γ_diag, H.pG010, H.pG020, H.pG120, H.pG011, H.pG021, H.pG121, H.pG012, H.pG022, H.pG122] at t
  have d01ga := congrArg (F.e 0) H.fs1ga
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, Nat.cast_ofNat, pow_one, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at d01ga
  have d10ga := congrArg (F.e 1) H.fs0ga
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, Nat.cast_ofNat, pow_one, smul_eq_mul, Derivation.map_one_eq_zero, H.e_ofNat, H.pD00, H.pD01, H.pD02, H.pD10, H.pD11, H.pD12, H.pD20, H.pD21, H.pD22] at d10ga
  have key : (((((lam 0)^(3:ℕ)) * ((lam 1)^(4:ℕ))) + (((lam 0)^(5:ℕ)) * ((lam 1)^(2:ℕ))) + (((lam 0)^(5:ℕ)) * ((lam 2)^(2:ℕ))) + (-1 * ((lam 0)^(2:ℕ)) * ((lam 2)^(5:ℕ))) + (-1 * ((lam 1)^(2:ℕ)) * ((lam 2)^(5:ℕ))) + (-1 * ((lam 1)^(4:ℕ)) * ((lam 2)^(3:ℕ))) + (-3 * ((lam 0)^(4:ℕ)) * ((lam 2)^(3:ℕ))) + (-2 * ((lam 0)^(4:ℕ)) * ((lam 1)^(3:ℕ))) + (2 * ((lam 1)^(3:ℕ)) * ((lam 2)^(4:ℕ))) + (3 * ((lam 0)^(3:ℕ)) * ((lam 2)^(4:ℕ))) + ((lam 2) * ((lam 0)^(4:ℕ)) * ((lam 1)^(2:ℕ))) + (-1 * (lam 0) * ((lam 1)^(2:ℕ)) * ((lam 2)^(4:ℕ))) + (-8 * ((lam 0)^(3:ℕ)) * ((lam 1)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (-4 * (lam 0) * ((lam 1)^(3:ℕ)) * ((lam 2)^(3:ℕ))) + (-4 * (lam 1) * ((lam 0)^(2:ℕ)) * ((lam 2)^(4:ℕ))) + (-3 * (lam 2) * ((lam 0)^(2:ℕ)) * ((lam 1)^(4:ℕ))) + (-2 * (lam 1) * (lam 2) * ((lam 0)^(5:ℕ))) + (2 * (lam 0) * (lam 1) * ((lam 2)^(5:ℕ))) + (3 * (lam 0) * ((lam 1)^(4:ℕ)) * ((lam 2)^(2:ℕ))) + (4 * (lam 1) * ((lam 0)^(4:ℕ)) * ((lam 2)^(2:ℕ))) + (4 * (lam 2) * ((lam 0)^(3:ℕ)) * ((lam 1)^(3:ℕ))) + (8 * ((lam 0)^(2:ℕ)) * ((lam 1)^(2:ℕ)) * ((lam 2)^(3:ℕ))))) * n6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam))) = 0 := by
    have g0 : (cfr6_0 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr6_1 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr6_2 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr6_3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr6_4 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (F.e 2 (beta F lam))) + (cfr6_5 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (F.e 2 (alpha F lam))) + 1 * (n6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam)))) + (cfr6_6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_0, cfr6_1, cfr6_2, cfr6_3, cfr6_4, cfr6_5, cfr6_6, n6]
      ring
    have g1 : (cfr6_8 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (gamma F lam)) + (cfr6_9 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (gamma F lam)) + (cfr6_10 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + 1 * (F.e 0 (F.e 1 (gamma F lam))) + (-1) * (F.e 1 (F.e 0 (gamma F lam))) = 0 := by
      simp only [cfr6_8, cfr6_9, cfr6_10]
      linear_combination t
    have g2 : (cfr6_12 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (alpha F lam)) + (cfr6_13 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (beta F lam)) + (cfr6_14 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (gamma F lam)) + (cfr6_15 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (eta F lam)) + (cfr6_16 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (gamma F lam)) + (cfr6_17 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr6_18 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (F.e 2 (beta F lam))) + (cfr6_19 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (F.e 1 (gamma F lam))) + (cfr6_20 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_12, cfr6_13, cfr6_14, cfr6_15, cfr6_16, cfr6_17, cfr6_18, cfr6_19, cfr6_20]
      linear_combination d01ga
    have g3 : (cfr6_22 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (gamma F lam)) + (cfr6_23 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr6_24 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_22, cfr6_23, cfr6_24]
      linear_combination H.fs1ga
    have g4 : (cfr6_26 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (alpha F lam)) + (cfr6_27 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr6_28 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_26, cfr6_27, cfr6_28]
      linear_combination H.fs0al
    have g5 : (cfr6_30 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (beta F lam)) + (cfr6_31 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr6_32 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_30, cfr6_31, cfr6_32]
      linear_combination H.fs0be
    have g6 : (cfr6_34 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (gamma F lam)) + (cfr6_35 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr6_36 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_34, cfr6_35, cfr6_36]
      linear_combination H.fs0ga
    have g7 : (cfr6_38 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (eta F lam)) + (cfr6_39 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (beta F lam)) + (cfr6_40 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_38, cfr6_39, cfr6_40]
      linear_combination H.fs0et
    have g8 : (cfr6_42 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 0 (gamma F lam)) + (cfr6_43 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (alpha F lam)) + (cfr6_44 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfr6_45 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (gamma F lam)) + (cfr6_46 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (eta F lam)) + (cfr6_47 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr6_48 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (F.e 2 (alpha F lam))) + (cfr6_49 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (F.e 0 (gamma F lam))) + (cfr6_50 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_42, cfr6_43, cfr6_44, cfr6_45, cfr6_46, cfr6_47, cfr6_48, cfr6_49, cfr6_50]
      linear_combination d10ga
    have g9 : (cfr6_52 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (alpha F lam)) + (cfr6_53 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (eta F lam)) + (cfr6_54 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_52, cfr6_53, cfr6_54]
      linear_combination H.fs1al
    have g10 : (cfr6_56 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (beta F lam)) + (cfr6_57 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (gamma F lam)) + (cfr6_58 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_56, cfr6_57, cfr6_58]
      linear_combination H.fs1be
    have g11 : (cfr6_60 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 1 (eta F lam)) + (cfr6_61 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * (F.e 2 (alpha F lam)) + (cfr6_62 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1 = 0 := by
      simp only [cfr6_60, cfr6_61, cfr6_62]
      linear_combination H.fs1et
    have k0 := cfr6_k0 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k1 := cfr6_k1 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k2 := cfr6_k2 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k3 := cfr6_k3 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k4 := cfr6_k4 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k5 := cfr6_k5 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k6 := cfr6_k6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k7 := cfr6_k7 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k8 := cfr6_k8 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k9 := cfr6_k9 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k10 := cfr6_k10 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k11 := cfr6_k11 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k12 := cfr6_k12 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k13 := cfr6_k13 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k14 := cfr6_k14 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k15 := cfr6_k15 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k16 := cfr6_k16 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    have k17 := cfr6_k17 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)
    linear_combination ((cfr6_7 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g0 + ((cfr6_11 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g1 + ((cfr6_21 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g2 + ((cfr6_25 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g3 + ((cfr6_29 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g4 + ((cfr6_33 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g5 + ((cfr6_37 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g6 + ((cfr6_41 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g7 + ((cfr6_51 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g8 + ((cfr6_55 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g9 + ((cfr6_59 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g10 + ((cfr6_63 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam)) * 1) * g11 + 1 * k0 + (n6 (lam 0) (lam 1) (lam 2) (alpha F lam) (beta F lam) (gamma F lam) (eta F lam) (F.e 2 (alpha F lam)) (F.e 2 (beta F lam)) (F.e 2 (gamma F lam)) (F.e 2 (eta F lam)) (F.e 0 (F.e 2 (alpha F lam))) (F.e 0 (F.e 2 (beta F lam))) (F.e 0 (F.e 2 (gamma F lam))) (F.e 0 (F.e 2 (eta F lam))) (F.e 1 (F.e 2 (alpha F lam))) (F.e 1 (F.e 2 (beta F lam))) (F.e 1 (F.e 2 (gamma F lam))) (F.e 1 (F.e 2 (eta F lam))) (F.e 2 (F.e 2 (alpha F lam))) (F.e 2 (F.e 2 (beta F lam))) (F.e 2 (F.e 2 (gamma F lam))) (F.e 2 (F.e 2 (eta F lam)))) * k1 + (F.e 1 (F.e 0 (gamma F lam))) * k2 + (F.e 0 (F.e 1 (gamma F lam))) * k3 + (F.e 1 (F.e 2 (alpha F lam))) * k4 + (F.e 0 (F.e 2 (beta F lam))) * k5 + (F.e 2 (eta F lam)) * k6 + (F.e 2 (gamma F lam)) * k7 + (F.e 2 (beta F lam)) * k8 + (F.e 2 (alpha F lam)) * k9 + (F.e 1 (eta F lam)) * k10 + (F.e 1 (gamma F lam)) * k11 + (F.e 1 (beta F lam)) * k12 + (F.e 1 (alpha F lam)) * k13 + (F.e 0 (eta F lam)) * k14 + (F.e 0 (gamma F lam)) * k15 + (F.e 0 (beta F lam)) * k16 + (F.e 0 (alpha F lam)) * k17
  have hU : IsUnit (((((lam 0)^(3:ℕ)) * ((lam 1)^(4:ℕ))) + (((lam 0)^(5:ℕ)) * ((lam 1)^(2:ℕ))) + (((lam 0)^(5:ℕ)) * ((lam 2)^(2:ℕ))) + (-1 * ((lam 0)^(2:ℕ)) * ((lam 2)^(5:ℕ))) + (-1 * ((lam 1)^(2:ℕ)) * ((lam 2)^(5:ℕ))) + (-1 * ((lam 1)^(4:ℕ)) * ((lam 2)^(3:ℕ))) + (-3 * ((lam 0)^(4:ℕ)) * ((lam 2)^(3:ℕ))) + (-2 * ((lam 0)^(4:ℕ)) * ((lam 1)^(3:ℕ))) + (2 * ((lam 1)^(3:ℕ)) * ((lam 2)^(4:ℕ))) + (3 * ((lam 0)^(3:ℕ)) * ((lam 2)^(4:ℕ))) + ((lam 2) * ((lam 0)^(4:ℕ)) * ((lam 1)^(2:ℕ))) + (-1 * (lam 0) * ((lam 1)^(2:ℕ)) * ((lam 2)^(4:ℕ))) + (-8 * ((lam 0)^(3:ℕ)) * ((lam 1)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (-4 * (lam 0) * ((lam 1)^(3:ℕ)) * ((lam 2)^(3:ℕ))) + (-4 * (lam 1) * ((lam 0)^(2:ℕ)) * ((lam 2)^(4:ℕ))) + (-3 * (lam 2) * ((lam 0)^(2:ℕ)) * ((lam 1)^(4:ℕ))) + (-2 * (lam 1) * (lam 2) * ((lam 0)^(5:ℕ))) + (2 * (lam 0) * (lam 1) * ((lam 2)^(5:ℕ))) + (3 * (lam 0) * ((lam 1)^(4:ℕ)) * ((lam 2)^(2:ℕ))) + (4 * (lam 1) * ((lam 0)^(4:ℕ)) * ((lam 2)^(2:ℕ))) + (4 * (lam 2) * ((lam 0)^(3:ℕ)) * ((lam 1)^(3:ℕ))) + (8 * ((lam 0)^(2:ℕ)) * ((lam 1)^(2:ℕ)) * ((lam 2)^(3:ℕ))))) := by
    have e : ((((lam 0)^(3:ℕ)) * ((lam 1)^(4:ℕ))) + (((lam 0)^(5:ℕ)) * ((lam 1)^(2:ℕ))) + (((lam 0)^(5:ℕ)) * ((lam 2)^(2:ℕ))) + (-1 * ((lam 0)^(2:ℕ)) * ((lam 2)^(5:ℕ))) + (-1 * ((lam 1)^(2:ℕ)) * ((lam 2)^(5:ℕ))) + (-1 * ((lam 1)^(4:ℕ)) * ((lam 2)^(3:ℕ))) + (-3 * ((lam 0)^(4:ℕ)) * ((lam 2)^(3:ℕ))) + (-2 * ((lam 0)^(4:ℕ)) * ((lam 1)^(3:ℕ))) + (2 * ((lam 1)^(3:ℕ)) * ((lam 2)^(4:ℕ))) + (3 * ((lam 0)^(3:ℕ)) * ((lam 2)^(4:ℕ))) + ((lam 2) * ((lam 0)^(4:ℕ)) * ((lam 1)^(2:ℕ))) + (-1 * (lam 0) * ((lam 1)^(2:ℕ)) * ((lam 2)^(4:ℕ))) + (-8 * ((lam 0)^(3:ℕ)) * ((lam 1)^(2:ℕ)) * ((lam 2)^(2:ℕ))) + (-4 * (lam 0) * ((lam 1)^(3:ℕ)) * ((lam 2)^(3:ℕ))) + (-4 * (lam 1) * ((lam 0)^(2:ℕ)) * ((lam 2)^(4:ℕ))) + (-3 * (lam 2) * ((lam 0)^(2:ℕ)) * ((lam 1)^(4:ℕ))) + (-2 * (lam 1) * (lam 2) * ((lam 0)^(5:ℕ))) + (2 * (lam 0) * (lam 1) * ((lam 2)^(5:ℕ))) + (3 * (lam 0) * ((lam 1)^(4:ℕ)) * ((lam 2)^(2:ℕ))) + (4 * (lam 1) * ((lam 0)^(4:ℕ)) * ((lam 2)^(2:ℕ))) + (4 * (lam 2) * ((lam 0)^(3:ℕ)) * ((lam 1)^(3:ℕ))) + (8 * ((lam 0)^(2:ℕ)) * ((lam 1)^(2:ℕ)) * ((lam 2)^(3:ℕ)))) = ((2 : R) ^ 0 * (lam 0 - lam 1) ^ 2 * (lam 0 - lam 2) ^ 3 * (lam 1 - lam 2) ^ 2) := by ring
    rw [e]; exact H.unit_prod 0 2 3 2
  exact hU.mul_right_eq_zero.mp key

end C2

end CFT.Cartan
