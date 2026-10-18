/- α-II.5:捩れの行だけの左核 4 本(K0〜K3)の恒等式 -/
import CFT.Cartan.SSJet
import CFT.Cartan.SSCoefK0
import CFT.Cartan.SSCoefK1
import CFT.Cartan.SSCoefK2
import CFT.Cartan.SSCoefK3

namespace CFT.Cartan

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- 大きな多項式の elaborate を速くするための局所インスタンス(標準のものと定義上同じ) -/
local instance (priority := high) hmR_SSK : HMul R R R := instHMul
local instance (priority := high) haR_SSK : HAdd R R R := instHAdd
local instance (priority := high) hsR_SSK : HSub R R R := instHSub
local instance (priority := high) hpR_SSK : HPow R ℕ R := instHPow
local instance (priority := high) ngR_SSK : Neg R := inferInstance

section Jet
variable (l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23 : R)

set_option maxHeartbeats 0 in
/-- 捩れの行だけの左核 K0 -/
theorem K0 : (((-1 * (l2^(6:ℕ))) + (-1 * (l0^(4:ℕ)) * (l1^(2:ℕ))) + (-1 * (l0^(4:ℕ)) * (l2^(2:ℕ))) + (-1 * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (-6 * (l0^(2:ℕ)) * (l2^(4:ℕ))) + (2 * l1 * (l2^(5:ℕ))) + (4 * l0 * (l2^(5:ℕ))) + (4 * (l0^(3:ℕ)) * (l2^(3:ℕ))) + (-8 * l0 * l1 * (l2^(4:ℕ))) + (-8 * l1 * (l0^(3:ℕ)) * (l2^(2:ℕ))) + (-6 * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (2 * l1 * l2 * (l0^(4:ℕ))) + (4 * l0 * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (4 * l2 * (l0^(3:ℕ)) * (l1^(2:ℕ))) + (12 * l1 * (l0^(2:ℕ)) * (l2^(3:ℕ))))) * (n2 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + (((l2^(4:ℕ)) + (l1 * (l0^(3:ℕ))) + (-1 * l1 * (l2^(3:ℕ))) + (-1 * l2 * (l0^(3:ℕ))) + (-3 * l0 * (l2^(3:ℕ))) + (3 * (l0^(2:ℕ)) * (l2^(2:ℕ))) + (-3 * l1 * l2 * (l0^(2:ℕ))) + (3 * l0 * l1 * (l2^(2:ℕ))))) * (n4 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + (((l0^(5:ℕ)) + ((l0^(3:ℕ)) * (l2^(2:ℕ))) + (-1 * (l0^(2:ℕ)) * (l1^(3:ℕ))) + (-1 * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (-3 * l1 * (l0^(4:ℕ))) + (-2 * l2 * (l0^(4:ℕ))) + (3 * (l0^(3:ℕ)) * (l1^(2:ℕ))) + (-6 * l2 * (l0^(2:ℕ)) * (l1^(2:ℕ))) + (-3 * l1 * (l0^(2:ℕ)) * (l2^(2:ℕ))) + (2 * l0 * l2 * (l1^(3:ℕ))) + (3 * l0 * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (6 * l1 * l2 * (l0^(3:ℕ))))) * (n6 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
  have g0 : (cfk0_0 l0 l1 l2 al be ga et) * ((et) * ((al)^(2:ℕ))) + (cfk0_1 l0 l1 l2 al be ga et) * ((al) * (be) * (ga)) + (cfk0_2 l0 l1 l2 al be ga et) * ((f1) * (al)) + (cfk0_3 l0 l1 l2 al be ga et) * ((et) * ((be)^(2:ℕ))) + (cfk0_4 l0 l1 l2 al be ga et) * ((f0) * (be)) + (cfk0_5 l0 l1 l2 al be ga et) * ((et) * ((ga)^(2:ℕ))) + (cfk0_6 l0 l1 l2 al be ga et) * ((f3) * (ga)) + (cfk0_7 l0 l1 l2 al be ga et) * ((et)^(3:ℕ)) + (cfk0_8 l0 l1 l2 al be ga et) * ((f2) * (et)) + (cfk0_9 l0 l1 l2 al be ga et) * (et) + (cfk0_10 l0 l1 l2 al be ga et) * (E10) + (cfk0_11 l0 l1 l2 al be ga et) * (E23) + 1 * (n2 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk0_0, cfk0_1, cfk0_2, cfk0_3, cfk0_4, cfk0_5, cfk0_6, cfk0_7, cfk0_8, cfk0_9, cfk0_10, cfk0_11, n2]
    ring
  have g1 : (cfk0_13 l0 l1 l2 al be ga et) * ((et) * ((al)^(2:ℕ))) + (cfk0_14 l0 l1 l2 al be ga et) * ((al) * (be) * (ga)) + (cfk0_15 l0 l1 l2 al be ga et) * ((f1) * (al)) + (cfk0_16 l0 l1 l2 al be ga et) * ((et) * ((be)^(2:ℕ))) + (cfk0_17 l0 l1 l2 al be ga et) * ((f0) * (be)) + (cfk0_18 l0 l1 l2 al be ga et) * ((et) * ((ga)^(2:ℕ))) + (cfk0_19 l0 l1 l2 al be ga et) * ((f3) * (ga)) + (cfk0_20 l0 l1 l2 al be ga et) * ((et)^(3:ℕ)) + (cfk0_21 l0 l1 l2 al be ga et) * ((f2) * (et)) + (cfk0_22 l0 l1 l2 al be ga et) * (et) + (cfk0_23 l0 l1 l2 al be ga et) * (E01) + (cfk0_24 l0 l1 l2 al be ga et) * (E23) + 1 * (n4 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk0_13, cfk0_14, cfk0_15, cfk0_16, cfk0_17, cfk0_18, cfk0_19, cfk0_20, cfk0_21, cfk0_22, cfk0_23, cfk0_24, n4]
    ring
  have g2 : (cfk0_26 l0 l1 l2 al be ga et) * ((et) * ((al)^(2:ℕ))) + (cfk0_27 l0 l1 l2 al be ga et) * ((al) * (be) * (ga)) + (cfk0_28 l0 l1 l2 al be ga et) * ((f1) * (al)) + (cfk0_29 l0 l1 l2 al be ga et) * ((et) * ((be)^(2:ℕ))) + (cfk0_30 l0 l1 l2 al be ga et) * ((f0) * (be)) + (cfk0_31 l0 l1 l2 al be ga et) * ((et) * ((ga)^(2:ℕ))) + (cfk0_32 l0 l1 l2 al be ga et) * ((f3) * (ga)) + (cfk0_33 l0 l1 l2 al be ga et) * ((et)^(3:ℕ)) + (cfk0_34 l0 l1 l2 al be ga et) * ((f2) * (et)) + (cfk0_35 l0 l1 l2 al be ga et) * (et) + (cfk0_36 l0 l1 l2 al be ga et) * (E01) + (cfk0_37 l0 l1 l2 al be ga et) * (E10) + 1 * (n6 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk0_26, cfk0_27, cfk0_28, cfk0_29, cfk0_30, cfk0_31, cfk0_32, cfk0_33, cfk0_34, cfk0_35, cfk0_36, cfk0_37, n6]
    ring
  have k0 := cfk0_k0 l0 l1 l2 al be ga et
  have k1 := cfk0_k1 l0 l1 l2 al be ga et
  have k2 := cfk0_k2 l0 l1 l2 al be ga et
  have k3 := cfk0_k3 l0 l1 l2 al be ga et
  have k4 := cfk0_k4 l0 l1 l2 al be ga et
  have k5 := cfk0_k5 l0 l1 l2 al be ga et
  have k6 := cfk0_k6 l0 l1 l2 al be ga et
  have k7 := cfk0_k7 l0 l1 l2 al be ga et
  have k8 := cfk0_k8 l0 l1 l2 al be ga et
  have k9 := cfk0_k9 l0 l1 l2 al be ga et
  have k10 := cfk0_k10 l0 l1 l2 al be ga et
  have k11 := cfk0_k11 l0 l1 l2 al be ga et
  have k12 := cfk0_k12 l0 l1 l2 al be ga et
  have k13 := cfk0_k13 l0 l1 l2 al be ga et
  have k14 := cfk0_k14 l0 l1 l2 al be ga et
  have k15 := cfk0_k15 l0 l1 l2 al be ga et
  linear_combination ((cfk0_12 l0 l1 l2 al be ga et) * 1) * g0 + ((cfk0_25 l0 l1 l2 al be ga et) * 1) * g1 + ((cfk0_38 l0 l1 l2 al be ga et) * 1) * g2 + (n6 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k0 + (n4 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k1 + (n2 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k2 + (E23) * k3 + (E10) * k4 + (E01) * k5 + (et) * k6 + ((f2) * (et)) * k7 + ((et)^(3:ℕ)) * k8 + ((f3) * (ga)) * k9 + ((et) * ((ga)^(2:ℕ))) * k10 + ((f0) * (be)) * k11 + ((et) * ((be)^(2:ℕ))) * k12 + ((f1) * (al)) * k13 + ((al) * (be) * (ga)) * k14 + ((et) * ((al)^(2:ℕ))) * k15

set_option maxHeartbeats 0 in
/-- 捩れの行だけの左核 K1 -/
theorem K1 : (((l2^(6:ℕ)) + (l1 * (l0^(5:ℕ))) + (-1 * l1 * (l2^(5:ℕ))) + (-1 * l2 * (l0^(5:ℕ))) + (-10 * (l0^(3:ℕ)) * (l2^(3:ℕ))) + (-5 * l0 * (l2^(5:ℕ))) + (5 * (l0^(4:ℕ)) * (l2^(2:ℕ))) + (10 * (l0^(2:ℕ)) * (l2^(4:ℕ))) + (-10 * l1 * (l0^(2:ℕ)) * (l2^(3:ℕ))) + (-5 * l1 * l2 * (l0^(4:ℕ))) + (5 * l0 * l1 * (l2^(4:ℕ))) + (10 * l1 * (l0^(3:ℕ)) * (l2^(2:ℕ))))) * (n1 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + (((l2^(4:ℕ)) + (l1 * (l0^(3:ℕ))) + (-1 * l1 * (l2^(3:ℕ))) + (-1 * l2 * (l0^(3:ℕ))) + (-3 * l0 * (l2^(3:ℕ))) + (3 * (l0^(2:ℕ)) * (l2^(2:ℕ))) + (-3 * l1 * l2 * (l0^(2:ℕ))) + (3 * l0 * l1 * (l2^(2:ℕ))))) * (n5 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + (((2 * (l0^(5:ℕ))) + (-6 * l1 * (l0^(4:ℕ))) + (-4 * l2 * (l0^(4:ℕ))) + (-2 * (l0^(2:ℕ)) * (l1^(3:ℕ))) + (-2 * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (2 * (l0^(3:ℕ)) * (l2^(2:ℕ))) + (6 * (l0^(3:ℕ)) * (l1^(2:ℕ))) + (-12 * l2 * (l0^(2:ℕ)) * (l1^(2:ℕ))) + (-6 * l1 * (l0^(2:ℕ)) * (l2^(2:ℕ))) + (4 * l0 * l2 * (l1^(3:ℕ))) + (6 * l0 * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (12 * l1 * l2 * (l0^(3:ℕ))))) * (n9 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = (((-20 * ga * (l0^(6:ℕ)) * (l1^(3:ℕ))) + (-10 * ga * (l0^(4:ℕ)) * (l1^(5:ℕ))) + (-6 * ga * (l0^(7:ℕ)) * (l2^(2:ℕ))) + (-2 * ga * l1 * (l0^(8:ℕ))) + (-2 * ga * (l0^(5:ℕ)) * (l2^(4:ℕ))) + (-2 * ga * (l1^(6:ℕ)) * (l2^(3:ℕ))) + (2 * ga * l2 * (l0^(8:ℕ))) + (2 * ga * (l0^(3:ℕ)) * (l1^(6:ℕ))) + (2 * ga * (l1^(5:ℕ)) * (l2^(4:ℕ))) + (6 * ga * (l0^(6:ℕ)) * (l2^(3:ℕ))) + (10 * ga * (l0^(7:ℕ)) * (l1^(2:ℕ))) + (20 * ga * (l0^(5:ℕ)) * (l1^(4:ℕ))) + (-50 * ga * l2 * (l0^(4:ℕ)) * (l1^(4:ℕ))) + (-40 * ga * (l0^(3:ℕ)) * (l1^(3:ℕ)) * (l2^(3:ℕ))) + (-30 * ga * (l0^(5:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (-28 * ga * l1 * (l0^(5:ℕ)) * (l2^(3:ℕ))) + (-24 * ga * (l0^(2:ℕ)) * (l1^(5:ℕ)) * (l2^(2:ℕ))) + (-20 * ga * (l0^(3:ℕ)) * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (-10 * ga * l0 * (l1^(4:ℕ)) * (l2^(4:ℕ))) + (-10 * ga * l2 * (l0^(6:ℕ)) * (l1^(2:ℕ))) + (-6 * ga * l2 * (l0^(2:ℕ)) * (l1^(6:ℕ))) + (-4 * ga * l1 * l2 * (l0^(7:ℕ))) + (4 * ga * l0 * (l1^(5:ℕ)) * (l2^(3:ℕ))) + (6 * ga * l0 * (l1^(6:ℕ)) * (l2^(2:ℕ))) + (10 * ga * l1 * (l0^(4:ℕ)) * (l2^(4:ℕ))) + (10 * ga * (l0^(2:ℕ)) * (l1^(4:ℕ)) * (l2^(3:ℕ))) + (20 * ga * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(4:ℕ))) + (24 * ga * l1 * (l0^(6:ℕ)) * (l2^(2:ℕ))) + (28 * ga * l2 * (l0^(3:ℕ)) * (l1^(5:ℕ))) + (30 * ga * (l0^(3:ℕ)) * (l1^(4:ℕ)) * (l2^(2:ℕ))) + (40 * ga * l2 * (l0^(5:ℕ)) * (l1^(3:ℕ))) + (50 * ga * (l0^(4:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))))) * Bj l0 l1 l2 al be ga et := by
  have g0 : (cfk1_0 l0 l1 l2 al be ga et) * ((ga) * ((al)^(2:ℕ))) + (cfk1_1 l0 l1 l2 al be ga et) * ((al) * (be) * (et)) + (cfk1_2 l0 l1 l2 al be ga et) * ((f0) * (al)) + (cfk1_3 l0 l1 l2 al be ga et) * ((ga) * ((be)^(2:ℕ))) + (cfk1_4 l0 l1 l2 al be ga et) * ((f1) * (be)) + (cfk1_5 l0 l1 l2 al be ga et) * ((ga)^(3:ℕ)) + (cfk1_6 l0 l1 l2 al be ga et) * ((ga) * ((et)^(2:ℕ))) + (cfk1_7 l0 l1 l2 al be ga et) * ((f2) * (ga)) + (cfk1_8 l0 l1 l2 al be ga et) * (ga) + (cfk1_9 l0 l1 l2 al be ga et) * ((f3) * (et)) + (cfk1_10 l0 l1 l2 al be ga et) * (E00) + (cfk1_11 l0 l1 l2 al be ga et) * (E22) + 1 * (n1 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk1_0, cfk1_1, cfk1_2, cfk1_3, cfk1_4, cfk1_5, cfk1_6, cfk1_7, cfk1_8, cfk1_9, cfk1_10, cfk1_11, n1]
    ring
  have g1 : (cfk1_13 l0 l1 l2 al be ga et) * ((ga) * ((al)^(2:ℕ))) + (cfk1_14 l0 l1 l2 al be ga et) * ((al) * (be) * (et)) + (cfk1_15 l0 l1 l2 al be ga et) * ((f0) * (al)) + (cfk1_16 l0 l1 l2 al be ga et) * ((ga) * ((be)^(2:ℕ))) + (cfk1_17 l0 l1 l2 al be ga et) * ((f1) * (be)) + (cfk1_18 l0 l1 l2 al be ga et) * ((ga)^(3:ℕ)) + (cfk1_19 l0 l1 l2 al be ga et) * ((ga) * ((et)^(2:ℕ))) + (cfk1_20 l0 l1 l2 al be ga et) * ((f2) * (ga)) + (cfk1_21 l0 l1 l2 al be ga et) * (ga) + (cfk1_22 l0 l1 l2 al be ga et) * ((f3) * (et)) + (cfk1_23 l0 l1 l2 al be ga et) * (E11) + (cfk1_24 l0 l1 l2 al be ga et) * (E22) + 1 * (n5 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk1_13, cfk1_14, cfk1_15, cfk1_16, cfk1_17, cfk1_18, cfk1_19, cfk1_20, cfk1_21, cfk1_22, cfk1_23, cfk1_24, n5]
    ring
  have g2 : (cfk1_26 l0 l1 l2 al be ga et) * ((ga) * ((al)^(2:ℕ))) + (cfk1_27 l0 l1 l2 al be ga et) * ((al) * (be) * (et)) + (cfk1_28 l0 l1 l2 al be ga et) * ((f0) * (al)) + (cfk1_29 l0 l1 l2 al be ga et) * ((ga) * ((be)^(2:ℕ))) + (cfk1_30 l0 l1 l2 al be ga et) * ((f1) * (be)) + (cfk1_31 l0 l1 l2 al be ga et) * ((ga)^(3:ℕ)) + (cfk1_32 l0 l1 l2 al be ga et) * ((ga) * ((et)^(2:ℕ))) + (cfk1_33 l0 l1 l2 al be ga et) * ((f2) * (ga)) + (cfk1_34 l0 l1 l2 al be ga et) * (ga) + (cfk1_35 l0 l1 l2 al be ga et) * ((f3) * (et)) + (cfk1_36 l0 l1 l2 al be ga et) * (E00) + (cfk1_37 l0 l1 l2 al be ga et) * (E11) + 1 * (n9 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk1_26, cfk1_27, cfk1_28, cfk1_29, cfk1_30, cfk1_31, cfk1_32, cfk1_33, cfk1_34, cfk1_35, cfk1_36, cfk1_37, n9]
    ring
  have g3 : (cfk1_39 l0 l1 l2 al be ga et) * ((al)^(2:ℕ)) + (cfk1_40 l0 l1 l2 al be ga et) * ((be)^(2:ℕ)) + (cfk1_41 l0 l1 l2 al be ga et) * ((ga)^(2:ℕ)) + (cfk1_42 l0 l1 l2 al be ga et) * ((et)^(2:ℕ)) + 1 * (Bj l0 l1 l2 al be ga et) + (cfk1_43 l0 l1 l2 al be ga et) * 1 = 0 := by
    simp only [cfk1_39, cfk1_40, cfk1_41, cfk1_42, cfk1_43, Bj]
    ring
  have k0 := cfk1_k0 l0 l1 l2 al be ga et
  have k1 := cfk1_k1 l0 l1 l2 al be ga et
  have k2 := cfk1_k2 l0 l1 l2 al be ga et
  have k3 := cfk1_k3 l0 l1 l2 al be ga et
  have k4 := cfk1_k4 l0 l1 l2 al be ga et
  have k5 := cfk1_k5 l0 l1 l2 al be ga et
  have k6 := cfk1_k6 l0 l1 l2 al be ga et
  have k7 := cfk1_k7 l0 l1 l2 al be ga et
  have k8 := cfk1_k8 l0 l1 l2 al be ga et
  have k9 := cfk1_k9 l0 l1 l2 al be ga et
  have k10 := cfk1_k10 l0 l1 l2 al be ga et
  have k11 := cfk1_k11 l0 l1 l2 al be ga et
  have k12 := cfk1_k12 l0 l1 l2 al be ga et
  have k13 := cfk1_k13 l0 l1 l2 al be ga et
  have k14 := cfk1_k14 l0 l1 l2 al be ga et
  have k15 := cfk1_k15 l0 l1 l2 al be ga et
  have k16 := cfk1_k16 l0 l1 l2 al be ga et
  linear_combination ((cfk1_12 l0 l1 l2 al be ga et) * 1) * g0 + ((cfk1_25 l0 l1 l2 al be ga et) * 1) * g1 + ((cfk1_38 l0 l1 l2 al be ga et) * 1) * g2 + ((cfk1_44 l0 l1 l2 al be ga et) * (ga)) * g3 + (n9 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k0 + (n5 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k1 + (n1 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k2 + (E22) * k3 + (E11) * k4 + (E00) * k5 + ((f3) * (et)) * k6 + (ga) * k7 + ((Bj l0 l1 l2 al be ga et) * (ga)) * k8 + ((f2) * (ga)) * k9 + ((ga) * ((et)^(2:ℕ))) * k10 + ((ga)^(3:ℕ)) * k11 + ((f1) * (be)) * k12 + ((ga) * ((be)^(2:ℕ))) * k13 + ((f0) * (al)) * k14 + ((al) * (be) * (et)) * k15 + ((ga) * ((al)^(2:ℕ))) * k16

set_option maxHeartbeats 0 in
/-- 捩れの行だけの左核 K2 -/
theorem K2 : (((l2^(3:ℕ)) + (-1 * (l0^(3:ℕ))) + (-3 * l0 * (l2^(2:ℕ))) + (3 * l2 * (l0^(2:ℕ))))) * (n0 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + ((((l0^(6:ℕ)) * (l1^(2:ℕ))) + ((l0^(6:ℕ)) * (l2^(2:ℕ))) + ((l1^(3:ℕ)) * (l2^(5:ℕ))) + ((l1^(5:ℕ)) * (l2^(3:ℕ))) + (-1 * (l0^(3:ℕ)) * (l1^(5:ℕ))) + (-1 * (l0^(3:ℕ)) * (l2^(5:ℕ))) + (-3 * (l0^(5:ℕ)) * (l1^(3:ℕ))) + (-3 * (l0^(5:ℕ)) * (l2^(3:ℕ))) + (-2 * (l1^(4:ℕ)) * (l2^(4:ℕ))) + (3 * (l0^(4:ℕ)) * (l1^(4:ℕ))) + (3 * (l0^(4:ℕ)) * (l2^(4:ℕ))) + (-12 * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(3:ℕ))) + (-12 * (l0^(4:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (-7 * l1 * (l0^(3:ℕ)) * (l2^(4:ℕ))) + (-7 * l2 * (l0^(3:ℕ)) * (l1^(4:ℕ))) + (-3 * l0 * (l1^(2:ℕ)) * (l2^(5:ℕ))) + (-3 * l0 * (l1^(5:ℕ)) * (l2^(2:ℕ))) + (-2 * l1 * l2 * (l0^(6:ℕ))) + (3 * l0 * (l1^(3:ℕ)) * (l2^(4:ℕ))) + (3 * l0 * (l1^(4:ℕ)) * (l2^(3:ℕ))) + (3 * l1 * (l0^(2:ℕ)) * (l2^(5:ℕ))) + (3 * l1 * (l0^(4:ℕ)) * (l2^(3:ℕ))) + (3 * l1 * (l0^(5:ℕ)) * (l2^(2:ℕ))) + (3 * l2 * (l0^(2:ℕ)) * (l1^(5:ℕ))) + (3 * l2 * (l0^(4:ℕ)) * (l1^(3:ℕ))) + (3 * l2 * (l0^(5:ℕ)) * (l1^(2:ℕ))) + (3 * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (3 * (l0^(2:ℕ)) * (l1^(4:ℕ)) * (l2^(2:ℕ))) + (8 * (l0^(3:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (8 * (l0^(3:ℕ)) * (l1^(3:ℕ)) * (l2^(2:ℕ))))) * (n8 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + (((l0^(6:ℕ)) + ((l0^(2:ℕ)) * (l1^(4:ℕ))) + ((l0^(4:ℕ)) * (l2^(2:ℕ))) + ((l1^(4:ℕ)) * (l2^(2:ℕ))) + (-4 * l1 * (l0^(5:ℕ))) + (-4 * (l0^(3:ℕ)) * (l1^(3:ℕ))) + (-2 * l2 * (l0^(5:ℕ))) + (6 * (l0^(4:ℕ)) * (l1^(2:ℕ))) + (-12 * l2 * (l0^(3:ℕ)) * (l1^(2:ℕ))) + (-4 * l0 * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (-4 * l1 * (l0^(3:ℕ)) * (l2^(2:ℕ))) + (-2 * l0 * l2 * (l1^(4:ℕ))) + (6 * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (8 * l1 * l2 * (l0^(4:ℕ))) + (8 * l2 * (l0^(2:ℕ)) * (l1^(3:ℕ))))) * (n10 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = (((be * (l0^(7:ℕ))) + (be * (l0^(3:ℕ)) * (l2^(4:ℕ))) + (-1 * be * (l0^(4:ℕ)) * (l1^(3:ℕ))) + (-1 * be * (l1^(3:ℕ)) * (l2^(4:ℕ))) + (-4 * be * l2 * (l0^(6:ℕ))) + (-4 * be * (l0^(4:ℕ)) * (l2^(3:ℕ))) + (-3 * be * l1 * (l0^(6:ℕ))) + (3 * be * (l0^(5:ℕ)) * (l1^(2:ℕ))) + (6 * be * (l0^(5:ℕ)) * (l2^(2:ℕ))) + (-18 * be * l1 * (l0^(4:ℕ)) * (l2^(2:ℕ))) + (-12 * be * l2 * (l0^(4:ℕ)) * (l1^(2:ℕ))) + (-12 * be * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (-6 * be * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (-3 * be * l1 * (l0^(2:ℕ)) * (l2^(4:ℕ))) + (3 * be * l0 * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (4 * be * l0 * (l1^(3:ℕ)) * (l2^(3:ℕ))) + (4 * be * l2 * (l0^(3:ℕ)) * (l1^(3:ℕ))) + (12 * be * l1 * l2 * (l0^(5:ℕ))) + (12 * be * l1 * (l0^(3:ℕ)) * (l2^(3:ℕ))) + (18 * be * (l0^(3:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))))) * Bj l0 l1 l2 al be ga et := by
  have g0 : (cfk2_0 l0 l1 l2 al be ga et) * ((be) * ((al)^(2:ℕ))) + (cfk2_1 l0 l1 l2 al be ga et) * ((al) * (et) * (ga)) + (cfk2_2 l0 l1 l2 al be ga et) * ((f3) * (al)) + (cfk2_3 l0 l1 l2 al be ga et) * ((be)^(3:ℕ)) + (cfk2_4 l0 l1 l2 al be ga et) * ((be) * ((ga)^(2:ℕ))) + (cfk2_5 l0 l1 l2 al be ga et) * ((be) * ((et)^(2:ℕ))) + (cfk2_6 l0 l1 l2 al be ga et) * ((f2) * (be)) + (cfk2_7 l0 l1 l2 al be ga et) * (be) + (cfk2_8 l0 l1 l2 al be ga et) * ((f1) * (ga)) + (cfk2_9 l0 l1 l2 al be ga et) * ((f0) * (et)) + (cfk2_10 l0 l1 l2 al be ga et) * (E03) + (cfk2_11 l0 l1 l2 al be ga et) * (E12) + 1 * (n0 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk2_0, cfk2_1, cfk2_2, cfk2_3, cfk2_4, cfk2_5, cfk2_6, cfk2_7, cfk2_8, cfk2_9, cfk2_10, cfk2_11, n0]
    ring
  have g1 : (cfk2_13 l0 l1 l2 al be ga et) * ((al) * (et) * (ga)) + (cfk2_14 l0 l1 l2 al be ga et) * ((f3) * (al)) + (cfk2_15 l0 l1 l2 al be ga et) * ((be) * ((ga)^(2:ℕ))) + (cfk2_16 l0 l1 l2 al be ga et) * ((be) * ((et)^(2:ℕ))) + (cfk2_17 l0 l1 l2 al be ga et) * ((f2) * (be)) + (cfk2_18 l0 l1 l2 al be ga et) * ((f1) * (ga)) + (cfk2_19 l0 l1 l2 al be ga et) * ((f0) * (et)) + (cfk2_20 l0 l1 l2 al be ga et) * (E12) + (cfk2_21 l0 l1 l2 al be ga et) * (E21) + 1 * (n8 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk2_13, cfk2_14, cfk2_15, cfk2_16, cfk2_17, cfk2_18, cfk2_19, cfk2_20, cfk2_21, n8]
    ring
  have g2 : (cfk2_23 l0 l1 l2 al be ga et) * ((al) * (et) * (ga)) + (cfk2_24 l0 l1 l2 al be ga et) * ((f3) * (al)) + (cfk2_25 l0 l1 l2 al be ga et) * ((be) * ((ga)^(2:ℕ))) + (cfk2_26 l0 l1 l2 al be ga et) * ((be) * ((et)^(2:ℕ))) + (cfk2_27 l0 l1 l2 al be ga et) * ((f2) * (be)) + (cfk2_28 l0 l1 l2 al be ga et) * ((f1) * (ga)) + (cfk2_29 l0 l1 l2 al be ga et) * ((f0) * (et)) + (cfk2_30 l0 l1 l2 al be ga et) * (E03) + (cfk2_31 l0 l1 l2 al be ga et) * (E21) + 1 * (n10 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk2_23, cfk2_24, cfk2_25, cfk2_26, cfk2_27, cfk2_28, cfk2_29, cfk2_30, cfk2_31, n10]
    ring
  have g3 : (cfk2_33 l0 l1 l2 al be ga et) * ((al)^(2:ℕ)) + (cfk2_34 l0 l1 l2 al be ga et) * ((be)^(2:ℕ)) + (cfk2_35 l0 l1 l2 al be ga et) * ((ga)^(2:ℕ)) + (cfk2_36 l0 l1 l2 al be ga et) * ((et)^(2:ℕ)) + 1 * (Bj l0 l1 l2 al be ga et) + (cfk2_37 l0 l1 l2 al be ga et) * 1 = 0 := by
    simp only [cfk2_33, cfk2_34, cfk2_35, cfk2_36, cfk2_37, Bj]
    ring
  have k0 := cfk2_k0 l0 l1 l2 al be ga et
  have k1 := cfk2_k1 l0 l1 l2 al be ga et
  have k2 := cfk2_k2 l0 l1 l2 al be ga et
  have k3 := cfk2_k3 l0 l1 l2 al be ga et
  have k4 := cfk2_k4 l0 l1 l2 al be ga et
  have k5 := cfk2_k5 l0 l1 l2 al be ga et
  have k6 := cfk2_k6 l0 l1 l2 al be ga et
  have k7 := cfk2_k7 l0 l1 l2 al be ga et
  have k8 := cfk2_k8 l0 l1 l2 al be ga et
  have k9 := cfk2_k9 l0 l1 l2 al be ga et
  have k10 := cfk2_k10 l0 l1 l2 al be ga et
  have k11 := cfk2_k11 l0 l1 l2 al be ga et
  have k12 := cfk2_k12 l0 l1 l2 al be ga et
  have k13 := cfk2_k13 l0 l1 l2 al be ga et
  have k14 := cfk2_k14 l0 l1 l2 al be ga et
  have k15 := cfk2_k15 l0 l1 l2 al be ga et
  have k16 := cfk2_k16 l0 l1 l2 al be ga et
  linear_combination ((cfk2_12 l0 l1 l2 al be ga et) * 1) * g0 + ((cfk2_22 l0 l1 l2 al be ga et) * 1) * g1 + ((cfk2_32 l0 l1 l2 al be ga et) * 1) * g2 + ((cfk2_38 l0 l1 l2 al be ga et) * (be)) * g3 + (n10 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k0 + (n8 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k1 + (n0 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k2 + (E21) * k3 + (E12) * k4 + (E03) * k5 + ((f0) * (et)) * k6 + ((f1) * (ga)) * k7 + (be) * k8 + ((Bj l0 l1 l2 al be ga et) * (be)) * k9 + ((f2) * (be)) * k10 + ((be) * ((et)^(2:ℕ))) * k11 + ((be) * ((ga)^(2:ℕ))) * k12 + ((be)^(3:ℕ)) * k13 + ((f3) * (al)) * k14 + ((al) * (et) * (ga)) * k15 + ((be) * ((al)^(2:ℕ))) * k16

set_option maxHeartbeats 0 in
/-- 捩れの行だけの左核 K3 -/
theorem K3 : (((l0^(3:ℕ)) + (-1 * (l2^(3:ℕ))) + (-3 * l2 * (l0^(2:ℕ))) + (3 * l0 * (l2^(2:ℕ))))) * (n3 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + ((((l0^(3:ℕ)) * (l2^(7:ℕ))) + ((l0^(5:ℕ)) * (l1^(5:ℕ))) + (-1 * (l0^(8:ℕ)) * (l1^(2:ℕ))) + (-1 * (l0^(8:ℕ)) * (l2^(2:ℕ))) + (-1 * (l1^(3:ℕ)) * (l2^(7:ℕ))) + (-1 * (l1^(5:ℕ)) * (l2^(5:ℕ))) + (-10 * (l0^(6:ℕ)) * (l2^(4:ℕ))) + (-5 * (l0^(4:ℕ)) * (l2^(6:ℕ))) + (-3 * (l0^(6:ℕ)) * (l1^(4:ℕ))) + (2 * (l1^(4:ℕ)) * (l2^(6:ℕ))) + (3 * (l0^(7:ℕ)) * (l1^(3:ℕ))) + (5 * (l0^(7:ℕ)) * (l2^(3:ℕ))) + (10 * (l0^(5:ℕ)) * (l2^(5:ℕ))) + ((l0^(3:ℕ)) * (l1^(2:ℕ)) * (l2^(5:ℕ))) + ((l0^(5:ℕ)) * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (-1 * l0 * (l1^(3:ℕ)) * (l2^(6:ℕ))) + (-1 * l2 * (l0^(7:ℕ)) * (l1^(2:ℕ))) + (-35 * (l0^(3:ℕ)) * (l1^(3:ℕ)) * (l2^(4:ℕ))) + (-35 * (l0^(5:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (-20 * l1 * (l0^(4:ℕ)) * (l2^(5:ℕ))) + (-20 * (l0^(4:ℕ)) * (l1^(4:ℕ)) * (l2^(2:ℕ))) + (-10 * (l0^(2:ℕ)) * (l1^(5:ℕ)) * (l2^(3:ℕ))) + (-9 * l2 * (l0^(6:ℕ)) * (l1^(3:ℕ))) + (-9 * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(6:ℕ))) + (-7 * l0 * (l1^(4:ℕ)) * (l2^(5:ℕ))) + (-7 * l1 * (l0^(7:ℕ)) * (l2^(2:ℕ))) + (-5 * l2 * (l0^(4:ℕ)) * (l1^(5:ℕ))) + (-3 * l1 * (l0^(2:ℕ)) * (l2^(7:ℕ))) + (2 * l1 * l2 * (l0^(8:ℕ))) + (3 * l0 * (l1^(2:ℕ)) * (l2^(7:ℕ))) + (5 * l0 * (l1^(5:ℕ)) * (l2^(4:ℕ))) + (5 * l1 * (l0^(6:ℕ)) * (l2^(3:ℕ))) + (5 * (l0^(2:ℕ)) * (l1^(4:ℕ)) * (l2^(4:ℕ))) + (10 * l1 * (l0^(5:ℕ)) * (l2^(4:ℕ))) + (10 * (l0^(3:ℕ)) * (l1^(4:ℕ)) * (l2^(3:ℕ))) + (10 * (l0^(3:ℕ)) * (l1^(5:ℕ)) * (l2^(2:ℕ))) + (13 * l1 * (l0^(3:ℕ)) * (l2^(6:ℕ))) + (13 * l2 * (l0^(5:ℕ)) * (l1^(4:ℕ))) + (17 * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(5:ℕ))) + (17 * (l0^(6:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (25 * (l0^(4:ℕ)) * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (25 * (l0^(4:ℕ)) * (l1^(3:ℕ)) * (l2^(3:ℕ))))) * (n7 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) + (((l1 * (l0^(7:ℕ))) + ((l0^(3:ℕ)) * (l1^(5:ℕ))) + ((l0^(4:ℕ)) * (l2^(4:ℕ))) + ((l1^(4:ℕ)) * (l2^(4:ℕ))) + (-1 * l2 * (l0^(7:ℕ))) + (-1 * (l1^(5:ℕ)) * (l2^(3:ℕ))) + (-4 * (l0^(4:ℕ)) * (l1^(4:ℕ))) + (-4 * (l0^(6:ℕ)) * (l1^(2:ℕ))) + (-3 * (l0^(5:ℕ)) * (l2^(3:ℕ))) + (3 * (l0^(6:ℕ)) * (l2^(2:ℕ))) + (6 * (l0^(5:ℕ)) * (l1^(3:ℕ))) + (l0 * (l1^(4:ℕ)) * (l2^(3:ℕ))) + (l1 * l2 * (l0^(6:ℕ))) + (-14 * l2 * (l0^(4:ℕ)) * (l1^(3:ℕ))) + (-14 * (l0^(3:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (-9 * l1 * (l0^(5:ℕ)) * (l2^(2:ℕ))) + (-9 * (l0^(2:ℕ)) * (l1^(4:ℕ)) * (l2^(2:ℕ))) + (-4 * l0 * (l1^(3:ℕ)) * (l2^(4:ℕ))) + (-4 * l1 * (l0^(3:ℕ)) * (l2^(4:ℕ))) + (-3 * l2 * (l0^(2:ℕ)) * (l1^(5:ℕ))) + (3 * l0 * (l1^(5:ℕ)) * (l2^(2:ℕ))) + (6 * l2 * (l0^(5:ℕ)) * (l1^(2:ℕ))) + (6 * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (6 * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(3:ℕ))) + (6 * (l0^(3:ℕ)) * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (6 * (l0^(4:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))) + (11 * l1 * (l0^(4:ℕ)) * (l2^(3:ℕ))) + (11 * l2 * (l0^(3:ℕ)) * (l1^(4:ℕ))))) * (n11 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = (((l2 * (l0^(6:ℕ))) + ((l0^(3:ℕ)) * (l1^(4:ℕ))) + ((l1^(3:ℕ)) * (l2^(4:ℕ))) + (-1 * l1 * (l0^(6:ℕ))) + (-1 * (l0^(3:ℕ)) * (l2^(4:ℕ))) + (-1 * (l1^(4:ℕ)) * (l2^(3:ℕ))) + (-3 * (l0^(4:ℕ)) * (l1^(3:ℕ))) + (-3 * (l0^(5:ℕ)) * (l2^(2:ℕ))) + (3 * (l0^(4:ℕ)) * (l2^(3:ℕ))) + (3 * (l0^(5:ℕ)) * (l1^(2:ℕ))) + (-8 * l1 * (l0^(3:ℕ)) * (l2^(3:ℕ))) + (-6 * l2 * (l0^(4:ℕ)) * (l1^(2:ℕ))) + (-6 * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (-3 * l0 * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (-3 * l2 * (l0^(2:ℕ)) * (l1^(4:ℕ))) + (3 * l0 * (l1^(4:ℕ)) * (l2^(2:ℕ))) + (3 * l1 * (l0^(2:ℕ)) * (l2^(4:ℕ))) + (6 * l1 * (l0^(4:ℕ)) * (l2^(2:ℕ))) + (6 * (l0^(2:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (8 * l2 * (l0^(3:ℕ)) * (l1^(3:ℕ))))) * L0j l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23 + (((4 * al * (l0^(9:ℕ))) + (al * (l1^(3:ℕ)) * (l2^(6:ℕ))) + (al * (l1^(6:ℕ)) * (l2^(3:ℕ))) + (-1 * al * (l0^(3:ℕ)) * (l1^(6:ℕ))) + (-1 * al * (l0^(3:ℕ)) * (l2^(6:ℕ))) + (-21 * al * (l0^(6:ℕ)) * (l1^(3:ℕ))) + (-21 * al * (l0^(6:ℕ)) * (l2^(3:ℕ))) + (-18 * al * l1 * (l0^(8:ℕ))) + (-18 * al * l2 * (l0^(8:ℕ))) + (-3 * al * (l1^(4:ℕ)) * (l2^(5:ℕ))) + (-3 * al * (l1^(5:ℕ)) * (l2^(4:ℕ))) + (3 * al * (l0^(4:ℕ)) * (l1^(5:ℕ))) + (3 * al * (l0^(4:ℕ)) * (l2^(5:ℕ))) + (3 * al * (l0^(5:ℕ)) * (l1^(4:ℕ))) + (3 * al * (l0^(5:ℕ)) * (l2^(4:ℕ))) + (30 * al * (l0^(7:ℕ)) * (l1^(2:ℕ))) + (30 * al * (l0^(7:ℕ)) * (l2^(2:ℕ))) + (-225 * al * (l0^(4:ℕ)) * (l1^(2:ℕ)) * (l2^(3:ℕ))) + (-225 * al * (l0^(4:ℕ)) * (l1^(3:ℕ)) * (l2^(2:ℕ))) + (-147 * al * l1 * (l0^(6:ℕ)) * (l2^(2:ℕ))) + (-147 * al * l2 * (l0^(6:ℕ)) * (l1^(2:ℕ))) + (-75 * al * (l0^(2:ℕ)) * (l1^(3:ℕ)) * (l2^(4:ℕ))) + (-75 * al * (l0^(2:ℕ)) * (l1^(4:ℕ)) * (l2^(3:ℕ))) + (-30 * al * l1 * (l0^(4:ℕ)) * (l2^(4:ℕ))) + (-30 * al * l2 * (l0^(4:ℕ)) * (l1^(4:ℕ))) + (-6 * al * l1 * (l0^(3:ℕ)) * (l2^(5:ℕ))) + (-6 * al * l2 * (l0^(3:ℕ)) * (l1^(5:ℕ))) + (-3 * al * l0 * (l1^(2:ℕ)) * (l2^(6:ℕ))) + (-3 * al * l0 * (l1^(6:ℕ)) * (l2^(2:ℕ))) + (3 * al * l1 * (l0^(2:ℕ)) * (l2^(6:ℕ))) + (3 * al * l2 * (l0^(2:ℕ)) * (l1^(6:ℕ))) + (6 * al * l0 * (l1^(3:ℕ)) * (l2^(5:ℕ))) + (6 * al * l0 * (l1^(5:ℕ)) * (l2^(3:ℕ))) + (30 * al * l0 * (l1^(4:ℕ)) * (l2^(4:ℕ))) + (75 * al * (l0^(3:ℕ)) * (l1^(2:ℕ)) * (l2^(4:ℕ))) + (75 * al * (l0^(3:ℕ)) * (l1^(4:ℕ)) * (l2^(2:ℕ))) + (84 * al * l1 * l2 * (l0^(7:ℕ))) + (114 * al * l1 * (l0^(5:ℕ)) * (l2^(3:ℕ))) + (114 * al * l2 * (l0^(5:ℕ)) * (l1^(3:ℕ))) + (200 * al * (l0^(3:ℕ)) * (l1^(3:ℕ)) * (l2^(3:ℕ))) + (270 * al * (l0^(5:ℕ)) * (l1^(2:ℕ)) * (l2^(2:ℕ))))) * Bj l0 l1 l2 al be ga et := by
  have g0 : (cfk3_0 l0 l1 l2 al be ga et) * ((al)^(3:ℕ)) + (cfk3_1 l0 l1 l2 al be ga et) * ((al) * ((be)^(2:ℕ))) + (cfk3_2 l0 l1 l2 al be ga et) * ((al) * ((ga)^(2:ℕ))) + (cfk3_3 l0 l1 l2 al be ga et) * ((al) * ((et)^(2:ℕ))) + (cfk3_4 l0 l1 l2 al be ga et) * ((f2) * (al)) + (cfk3_5 l0 l1 l2 al be ga et) * (al) + (cfk3_6 l0 l1 l2 al be ga et) * ((be) * (et) * (ga)) + (cfk3_7 l0 l1 l2 al be ga et) * ((f3) * (be)) + (cfk3_8 l0 l1 l2 al be ga et) * ((f0) * (ga)) + (cfk3_9 l0 l1 l2 al be ga et) * ((f1) * (et)) + (cfk3_10 l0 l1 l2 al be ga et) * (E02) + (cfk3_11 l0 l1 l2 al be ga et) * (E13) + 1 * (n3 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk3_0, cfk3_1, cfk3_2, cfk3_3, cfk3_4, cfk3_5, cfk3_6, cfk3_7, cfk3_8, cfk3_9, cfk3_10, cfk3_11, n3]
    ring
  have g1 : (cfk3_13 l0 l1 l2 al be ga et) * ((al) * ((ga)^(2:ℕ))) + (cfk3_14 l0 l1 l2 al be ga et) * ((al) * ((et)^(2:ℕ))) + (cfk3_15 l0 l1 l2 al be ga et) * ((f2) * (al)) + (cfk3_16 l0 l1 l2 al be ga et) * ((be) * (et) * (ga)) + (cfk3_17 l0 l1 l2 al be ga et) * ((f3) * (be)) + (cfk3_18 l0 l1 l2 al be ga et) * ((f0) * (ga)) + (cfk3_19 l0 l1 l2 al be ga et) * ((f1) * (et)) + (cfk3_20 l0 l1 l2 al be ga et) * (E02) + (cfk3_21 l0 l1 l2 al be ga et) * (E20) + 1 * (n7 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk3_13, cfk3_14, cfk3_15, cfk3_16, cfk3_17, cfk3_18, cfk3_19, cfk3_20, cfk3_21, n7]
    ring
  have g2 : (cfk3_23 l0 l1 l2 al be ga et) * ((al) * ((ga)^(2:ℕ))) + (cfk3_24 l0 l1 l2 al be ga et) * ((al) * ((et)^(2:ℕ))) + (cfk3_25 l0 l1 l2 al be ga et) * ((f2) * (al)) + (cfk3_26 l0 l1 l2 al be ga et) * ((be) * (et) * (ga)) + (cfk3_27 l0 l1 l2 al be ga et) * ((f3) * (be)) + (cfk3_28 l0 l1 l2 al be ga et) * ((f0) * (ga)) + (cfk3_29 l0 l1 l2 al be ga et) * ((f1) * (et)) + (cfk3_30 l0 l1 l2 al be ga et) * (E13) + (cfk3_31 l0 l1 l2 al be ga et) * (E20) + 1 * (n11 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk3_23, cfk3_24, cfk3_25, cfk3_26, cfk3_27, cfk3_28, cfk3_29, cfk3_30, cfk3_31, n11]
    ring
  have g3 : (cfk3_33 l0 l1 l2 al be ga et) * ((al)^(2:ℕ)) + (cfk3_34 l0 l1 l2 al be ga et) * ((be)^(2:ℕ)) + (cfk3_35 l0 l1 l2 al be ga et) * ((ga)^(2:ℕ)) + (cfk3_36 l0 l1 l2 al be ga et) * ((et)^(2:ℕ)) + 1 * (Bj l0 l1 l2 al be ga et) + (cfk3_37 l0 l1 l2 al be ga et) * 1 = 0 := by
    simp only [cfk3_33, cfk3_34, cfk3_35, cfk3_36, cfk3_37, Bj]
    ring
  have g4 : (cfk3_39 l0 l1 l2 al be ga et) * ((al)^(3:ℕ)) + (cfk3_40 l0 l1 l2 al be ga et) * ((al) * ((be)^(2:ℕ))) + (cfk3_41 l0 l1 l2 al be ga et) * ((al) * ((ga)^(2:ℕ))) + (cfk3_42 l0 l1 l2 al be ga et) * ((al) * ((et)^(2:ℕ))) + (cfk3_43 l0 l1 l2 al be ga et) * ((f2) * (al)) + (cfk3_44 l0 l1 l2 al be ga et) * (al) + (cfk3_45 l0 l1 l2 al be ga et) * ((be) * (et) * (ga)) + (cfk3_46 l0 l1 l2 al be ga et) * ((f3) * (be)) + (cfk3_47 l0 l1 l2 al be ga et) * ((f0) * (ga)) + (cfk3_48 l0 l1 l2 al be ga et) * ((f1) * (et)) + 1 * (L0j l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) = 0 := by
    simp only [cfk3_39, cfk3_40, cfk3_41, cfk3_42, cfk3_43, cfk3_44, cfk3_45, cfk3_46, cfk3_47, cfk3_48, L0j]
    ring
  have k0 := cfk3_k0 l0 l1 l2 al be ga et
  have k1 := cfk3_k1 l0 l1 l2 al be ga et
  have k2 := cfk3_k2 l0 l1 l2 al be ga et
  have k3 := cfk3_k3 l0 l1 l2 al be ga et
  have k4 := cfk3_k4 l0 l1 l2 al be ga et
  have k5 := cfk3_k5 l0 l1 l2 al be ga et
  have k6 := cfk3_k6 l0 l1 l2 al be ga et
  have k7 := cfk3_k7 l0 l1 l2 al be ga et
  have k8 := cfk3_k8 l0 l1 l2 al be ga et
  have k9 := cfk3_k9 l0 l1 l2 al be ga et
  have k10 := cfk3_k10 l0 l1 l2 al be ga et
  have k11 := cfk3_k11 l0 l1 l2 al be ga et
  have k12 := cfk3_k12 l0 l1 l2 al be ga et
  have k13 := cfk3_k13 l0 l1 l2 al be ga et
  have k14 := cfk3_k14 l0 l1 l2 al be ga et
  have k15 := cfk3_k15 l0 l1 l2 al be ga et
  have k16 := cfk3_k16 l0 l1 l2 al be ga et
  have k17 := cfk3_k17 l0 l1 l2 al be ga et
  linear_combination ((cfk3_12 l0 l1 l2 al be ga et) * 1) * g0 + ((cfk3_22 l0 l1 l2 al be ga et) * 1) * g1 + ((cfk3_32 l0 l1 l2 al be ga et) * 1) * g2 + ((cfk3_38 l0 l1 l2 al be ga et) * (al)) * g3 + ((cfk3_49 l0 l1 l2 al be ga et) * 1) * g4 + (L0j l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k0 + (n11 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k1 + (n7 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k2 + (n3 l0 l1 l2 al be ga et f0 f1 f2 f3 E00 E01 E02 E03 E10 E11 E12 E13 E20 E21 E22 E23) * k3 + (E20) * k4 + (E13) * k5 + (E02) * k6 + ((f1) * (et)) * k7 + ((f0) * (ga)) * k8 + ((f3) * (be)) * k9 + ((be) * (et) * (ga)) * k10 + (al) * k11 + ((Bj l0 l1 l2 al be ga et) * (al)) * k12 + ((f2) * (al)) * k13 + ((al) * ((et)^(2:ℕ))) * k14 + ((al) * ((ga)^(2:ℕ))) * k15 + ((al) * ((be)^(2:ℕ))) * k16 + ((al)^(3:ℕ)) * k17

end Jet

end CFT.Cartan
