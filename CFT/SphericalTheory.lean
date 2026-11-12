/-
  球対称な EYM–Dirac 理論の入口(2026-11-12)

  このファイルは、球対称な部分に関するモジュールを一つにまとめて読み込む。内容の対応:
    作用 → 運動方程式・正準形式・拘束の質量の形 …… CFT.AlphaCanonical(CAN)
    量子の方程式(Wheeler–DeWitt)、帽子と首 …… CFT.AlphaQuantumSpherical(QS)、CFT.AlphaKS_WDW(KS)
    有名な方程式(Birkhoff、RN、JT、温度、面積則)…… CFT.AlphaFamous(FAM)
    Dirac 場、体積 …… CFT.AlphaFermion(FER)、CFT.AlphaSphericalClose(SC)
    ダンベルの形、接合 …… CFT.AlphaDumbbell_Shape、CFT.AlphaDumbbell_Bogomolny(DS)、CFT.AlphaJunction_Unique(JU)
    断面積一定の初期データ …… CFT.AlphaConstArea(CA)
    摂動、重力波、形の揺らぎ …… CFT.AlphaOpen_Split(OS)
    実関数での接合と拘束 …… CFT.AlphaReal_Junction(RJ)、CFT.AlphaReal_Rest(RR)
    Ω の量子幾何学 …… CFT.AlphaOmega_Quantum(OQ)、CFT.AlphaOmega_Close(OC)、CFT.AlphaOmega_Last(OL)
    アイデアの検証 …… CFT.AlphaIdeas_Check(ID)
-/
import CFT.AlphaCanonical
import CFT.AlphaQuantumSpherical
import CFT.AlphaKS_WDW
import CFT.AlphaFamous
import CFT.AlphaFermion
import CFT.AlphaSphericalClose
import CFT.AlphaDumbbell_Shape
import CFT.AlphaDumbbell_Bogomolny
import CFT.AlphaJunction_Unique
import CFT.AlphaConstArea
import CFT.AlphaOpen_Split
import CFT.AlphaReal_Junction
import CFT.AlphaReal_Rest
import CFT.AlphaOmega_Quantum
import CFT.AlphaOmega_Close
import CFT.AlphaOmega_Last
import CFT.AlphaIdeas_Check

namespace CFT.Spherical

/-- 作用から出る三つの運動方程式(Euler–Lagrange の式が 0 になる)をまとめたもの -/
theorem spherical_field_equations (r ru rv ruv Om Omu Omv Omuv W Wuv l : ℝ) (hr : r ≠ 0) (hO : Om ≠ 0)
    (h1 : ruv = 2⁻¹ * Om * (l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 2 - 1) / r - ru * rv / r)
    (h2 : Wuv = 2⁻¹ * Om * W * (1 - W ^ 2) / r ^ 2)
    (h3 : Omuv = Omu * Omv / Om - 2 * Om * ruv / r - Om ^ 2 * l ^ 2 * (1 - W ^ 2) ^ 2 / r ^ 4) :
    2 * (2 * r * ruv + 2 * ru * rv) + 2 * Om - 2 * l ^ 2 * Om * (1 - W ^ 2) ^ 2 / r ^ 2 = 0
      ∧ -16 * l ^ 2 * Wuv + 8 * l ^ 2 * Om * W * (1 - W ^ 2) / r ^ 2 = 0
      ∧ 4 * r * (Omuv / Om - Omu * Omv / Om ^ 2) + 8 * ruv
          + 4 * l ^ 2 * Om * (1 - W ^ 2) ^ 2 / r ^ 3 = 0 :=
  ⟨CFT.CAN.can_el_Om_of r ru rv ruv Om W l hr h1, CFT.CAN.can_el_W_of r Om W Wuv l h2,
    CFT.CAN.can_el_r_of r ruv Om Omu Omv Omuv W l hr hO h3⟩

end CFT.Spherical
