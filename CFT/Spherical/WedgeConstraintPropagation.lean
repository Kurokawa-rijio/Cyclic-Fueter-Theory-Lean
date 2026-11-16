/-
  命題集 `LEAN_GAP_TREES.md` 4-2（拘束の伝播、くさび版）：
  `CFT/Spherical/WedgeEYMSystem.lean` の二重ヌル系について、発展方程式が成り立てば
  拘束は微分恒等式として伝播する（解の存在は仮定する）。

  C_u = r_uu - (Ω_u/Ω) r_u + 2 W_u²/r,  C_v = r_vv - (Ω_v/Ω) r_v + 2 W_v²/r に対し、
    ∂_v C_u = -(r_v/r) C_u,   ∂_u C_v = -(r_u/r) C_v
  が成り立つ。つまり C_u は v 方向に、C_v は u 方向に純粋な輸送を受け、
  他方の拘束とも Ω, W の項とも結合しない。初期面で C_u = 0 なら領域全体で C_u = 0。
  （sympy による jet 空間での厳密な有理恒等式チェック済み：`cft/wedge42_check.py`。
  Ω_uv の式を摂動させると恒等式は壊れるので、3本の発展方程式すべてが本質的に使われる。）

  証明は `CFT/Spherical/ConstraintPropagation.lean`（ADM 版）と同じ導分代数の流儀：
  場を体 S の元、∂_u, ∂_v を可換な導分として扱い、発展方程式を仮定として
  微分恒等式を展開する。解析的な `deriv` 版への移行は別葉。
  代数核 `wedge_cu_algebraic` の `linear_combination` 係数は sympy の
  Groebner reduction（`cft/wedge42_groebner.py`）で得たもので、
  残差は (Ω * Ω⁻¹ - 1) の倍数のみ。
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace CFT.WedgePropagation

set_option maxHeartbeats 0

variable {S : Type*} [Field S] [CharZero S]

/-- 導分の逆元の公式 -/
theorem deriv_inv (d : Derivation ℤ S S) (a : S) (ha : a ≠ 0) : d a⁻¹ = -(a⁻¹ ^ 2 * d a) := by
  have h : d (a * a⁻¹) = 0 := by rw [mul_inv_cancel₀ ha]; exact d.map_one_eq_zero
  rw [Derivation.leibniz] at h
  simp only [smul_eq_mul] at h
  have e : d a⁻¹ = a⁻¹ * (a * d a⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [e, show a * d a⁻¹ = -(a⁻¹ * d a) by linear_combination h]
  ring

theorem deriv_ofNat (d : Derivation ℤ S S) (n : ℕ) [n.AtLeastTwo] : d (OfNat.ofNat n : S) = 0 := by
  have : (OfNat.ofNat n : S) = ((n : ℕ) : S) := (Nat.cast_ofNat).symm
  rw [this]; exact d.map_natCast n

variable (du dv : Derivation ℤ S S) (r Om W : S)

/-- r_uv の右辺（`WedgeEvolution.py` の F の第1成分）。 -/
noncomputable def wedgeRuv (Om W ru rv r : S) : S :=
  2⁻¹ * Om * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹ - ru * rv * r⁻¹

/-- Ω_uv の右辺（F の第2成分。r_uv の値を使う）。 -/
noncomputable def wedgeOuv (Om W Ou Ov ruv r : S) : S :=
  Ou * Ov * Om⁻¹ - 2 * Om * ruv * r⁻¹ - Om ^ 2 * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4

/-- W_uv の右辺（F の第3成分）。 -/
noncomputable def wedgeWuv (Om W r : S) : S :=
  2⁻¹ * Om * W * (1 - W ^ 2) * (r⁻¹) ^ 2

/-- u 方向の拘束 C_u。 -/
noncomputable def wedgeCu (du : Derivation ℤ S S) (r Om W : S) : S :=
  du (du r) - du Om * Om⁻¹ * du r + 2 * (du W) ^ 2 * r⁻¹

/-- v 方向の拘束 C_v。 -/
noncomputable def wedgeCv (dv : Derivation ℤ S S) (r Om W : S) : S :=
  dv (dv r) - dv Om * Om⁻¹ * dv r + 2 * (dv W) ^ 2 * r⁻¹

/-- r_uv の右辺の u 方向の連鎖律展開（du (wedgeRuv ...) の値）。 -/
noncomputable def wedgeRuuv (Om W ru rv r Ou Wu ruu : S) : S :=
  (2⁻¹ * ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * r⁻¹) * Ou
    + (2⁻¹ * Om * (-4 * W * (1 - W ^ 2)) * (r⁻¹) ^ 3) * Wu
    + (-rv * r⁻¹) * ruu
    + (-ru * r⁻¹) * (wedgeRuv Om W ru rv r)
    + (2⁻¹ * Om * (-2 * (1 - W ^ 2) ^ 2 * (r⁻¹) ^ 4
        - ((1 - W ^ 2) ^ 2 * (r⁻¹) ^ 2 - 1) * (r⁻¹) ^ 2)
      + ru * rv * (r⁻¹) ^ 2) * ru

/-- 4-2 の代数核：連鎖律展開を代入した ∂_v C_u の式は -(r_v/r) C_u に等しい。 -/
theorem wedge_cu_algebraic (r Om W ru rv Ou Ov Wu ruu : S) (hr : r ≠ 0) (hOm : Om ≠ 0) :
    wedgeRuuv Om W ru rv r Ou Wu ruu
      - (((wedgeOuv Om W Ou Ov (wedgeRuv Om W ru rv r) r) * Om⁻¹
          - Ou * Ov * (Om⁻¹) ^ 2) * ru
        + Ou * Om⁻¹ * (wedgeRuv Om W ru rv r))
      + 4 * Wu * (wedgeWuv Om W r) * r⁻¹ - 2 * Wu ^ 2 * rv * (r⁻¹) ^ 2
      = -(rv * r⁻¹) * (ruu - Ou * Om⁻¹ * ru + 2 * Wu ^ 2 * r⁻¹) := by
  have hb : Om * Om⁻¹ = 1 := mul_inv_cancel₀ hOm
  simp only [wedgeRuuv, wedgeRuv, wedgeOuv, wedgeWuv]
  linear_combination
    (2 * Om * W ^ 4 * (r⁻¹) ^ 4 * ru - 4 * Om * W ^ 2 * (r⁻¹) ^ 4 * ru
      + 2 * Om * (r⁻¹) ^ 4 * ru - Om * (r⁻¹) ^ 2 * ru
      - Ou * W ^ 4 * (r⁻¹) ^ 3 / 2 + Ou * W ^ 2 * (r⁻¹) ^ 3 - Ou * (r⁻¹) ^ 3 / 2
      + Ou * r⁻¹ / 2 - 2 * (r⁻¹) ^ 2 * ru ^ 2 * rv) * hb

section
variable (hOm : Om ≠ 0) (hr : r ≠ 0)
  (hc : ∀ f, du (dv f) = dv (du f))
  (eR : du (dv r) = wedgeRuv Om W (du r) (dv r) r)
  (eOm : du (dv Om) = wedgeOuv Om W (du Om) (dv Om) (du (dv r)) r)
  (eW : du (dv W) = wedgeWuv Om W r)
include hOm hr hc eR eOm eW

/-- 連鎖律：du (r_uv の右辺) = wedgeRuuv。 -/
theorem wedge_du_ruv_chain :
    du (wedgeRuv Om W (du r) (dv r) r)
      = wedgeRuuv Om W (du r) (dv r) r (du Om) (du W) (du (du r)) := by
  have hu2 : du (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat du 2]; ring
  simp only [wedgeRuv, wedgeRuuv, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hOm, deriv_inv _ _ hr,
    deriv_ofNat, Derivation.map_one_eq_zero, eR, hu2,
    deriv_ofNat du 2, deriv_ofNat du 4, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- 4-2（u 拘束の伝播）：∂_v C_u = -(r_v/r) C_u。 -/
theorem wedge_cu_propagation :
    dv (wedgeCu du r Om W) = -(dv r * r⁻¹) * wedgeCu du r Om W := by
  have hu2 : du (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat du 2]; ring
  have hv2 : dv (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dv 2]; ring
  have hcomm : dv (du (du r)) = du (du (dv r)) := by
    rw [← hc (du r), ← hc r]
  have hOm' : dv (du Om)
      = wedgeOuv Om W (du Om) (dv Om) (wedgeRuv Om W (du r) (dv r) r) r := by
    rw [← hc Om, eOm, eR]
  have hW' : dv (du W) = wedgeWuv Om W r := by rw [← hc W, eW]
  have hR' : dv (du r) = wedgeRuv Om W (du r) (dv r) r := by rw [← hc r, eR]
  have hchain := wedge_du_ruv_chain du dv r Om W hOm hr hc eR eOm eW
  have key : dv (wedgeCu du r Om W)
      = wedgeRuuv Om W (du r) (dv r) r (du Om) (du W) (du (du r))
        - (((wedgeOuv Om W (du Om) (dv Om) (wedgeRuv Om W (du r) (dv r) r) r) * Om⁻¹
            - du Om * dv Om * (Om⁻¹) ^ 2) * du r
          + du Om * Om⁻¹ * (wedgeRuv Om W (du r) (dv r) r))
        + 4 * du W * (wedgeWuv Om W r) * r⁻¹ - 2 * (du W) ^ 2 * dv r * (r⁻¹) ^ 2 := by
    simp only [wedgeCu, map_add, map_sub, map_neg, Derivation.leibniz,
      Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hOm, deriv_inv _ _ hr,
      deriv_ofNat, Derivation.map_one_eq_zero, hcomm, hOm', hW', hR', eR, hchain,
      hu2, hv2, deriv_ofNat du 2, deriv_ofNat dv 2, deriv_ofNat du 4, deriv_ofNat dv 4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [key]
  exact wedge_cu_algebraic r Om W (du r) (dv r) (du Om) (dv Om) (du W) (du (du r)) hr hOm

/-- 連鎖律（v 方向）：dv (r_uv の右辺) = wedgeRuuv（u/v を入れ替えた形）。 -/
theorem wedge_dv_ruv_chain :
    dv (wedgeRuv Om W (du r) (dv r) r)
      = wedgeRuuv Om W (dv r) (du r) r (dv Om) (dv W) (dv (dv r)) := by
  have hv2 : dv (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dv 2]; ring
  have hR' : dv (du r) = wedgeRuv Om W (du r) (dv r) r := by rw [← hc r, eR]
  simp only [wedgeRuv, wedgeRuuv, map_add, map_sub, map_neg, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hOm, deriv_inv _ _ hr,
    deriv_ofNat, Derivation.map_one_eq_zero, hR', hv2,
    deriv_ofNat dv 2, deriv_ofNat dv 4, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- 4-2（v 拘束の伝播）：∂_u C_v = -(r_u/r) C_v。 -/
theorem wedge_cv_propagation :
    du (wedgeCv dv r Om W) = -(du r * r⁻¹) * wedgeCv dv r Om W := by
  have hu2 : du (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat du 2]; ring
  have hv2 : dv (2⁻¹ : S) = 0 := by
    rw [deriv_inv _ _ two_ne_zero, deriv_ofNat dv 2]; ring
  have hcomm' : du (dv (dv r)) = dv (dv (du r)) := by rw [hc (dv r), hc r]
  have hOm'' : du (dv Om)
      = wedgeOuv Om W (du Om) (dv Om) (wedgeRuv Om W (du r) (dv r) r) r := by
    rw [eOm, eR]
  have hW'' : du (dv W) = wedgeWuv Om W r := eW
  have hR' : dv (du r) = wedgeRuv Om W (du r) (dv r) r := by rw [← hc r, eR]
  have hchain' := wedge_dv_ruv_chain du dv r Om W hOm hr hc eR eOm eW
  have hRuv_symm : wedgeRuv Om W (du r) (dv r) r = wedgeRuv Om W (dv r) (du r) r := by
    simp only [wedgeRuv]; ring
  have hOuv_symm : wedgeOuv Om W (du Om) (dv Om) (wedgeRuv Om W (du r) (dv r) r) r
      = wedgeOuv Om W (dv Om) (du Om) (wedgeRuv Om W (dv r) (du r) r) r := by
    simp only [wedgeOuv, wedgeRuv]; ring
  have key' : du (wedgeCv dv r Om W)
      = wedgeRuuv Om W (dv r) (du r) r (dv Om) (dv W) (dv (dv r))
        - (((wedgeOuv Om W (du Om) (dv Om) (wedgeRuv Om W (du r) (dv r) r) r) * Om⁻¹
            - dv Om * du Om * (Om⁻¹) ^ 2) * dv r
          + dv Om * Om⁻¹ * (wedgeRuv Om W (du r) (dv r) r))
        + 4 * dv W * (wedgeWuv Om W r) * r⁻¹ - 2 * (dv W) ^ 2 * du r * (r⁻¹) ^ 2 := by
    simp only [wedgeCv, map_add, map_sub, map_neg, Derivation.leibniz,
      Derivation.leibniz_pow, smul_eq_mul, deriv_inv _ _ hOm, deriv_inv _ _ hr,
      deriv_ofNat, Derivation.map_one_eq_zero, hcomm', hOm'', hW'', hR', eR, hchain',
      hu2, hv2, deriv_ofNat du 2, deriv_ofNat dv 2, deriv_ofNat du 4, deriv_ofNat dv 4,
      nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [key', hOuv_symm, hRuv_symm]
  exact wedge_cu_algebraic r Om W (dv r) (du r) (dv Om) (du Om) (dv W) (dv (dv r)) hr hOm

end

end CFT.WedgePropagation
