/-
  段階 1・6:縮約した Bianchi 恒等式 ∇^a G_ad = 0(Riemann 正規座標の点で、2026-11-18)

  点 p で Riemann 正規座標を取る(Γ(p) = 0、したがって ∂g(p) = 0、∂g⁻¹(p) = 0)。このとき p で
    ∂_b∂_c Γ_eda = ½(∂_d g_ea + ∂_a g_ed − ∂_e g_da)_{,bc}、 ∂_b∂_c Γ^x_da = g^xe ∂_b∂_c Γ_eda、
    ∂_b Ric_ad = Σ_c (∂_b∂_c Γ^c_da − ∂_b∂_d Γ^c_ca)、 ∂_d R = g^ab ∂_d Ric_ab、
    ∇^a G_ad = g^ab ∂_b Ric_ad − ½ ∂_d R
  となる(Γ(p) = 0 なので Γ を含む項はすべて消える)。計量の 3 階微分 H x y u v w = ∂_u∂_v∂_w g_xy は
  x, y について対称、u, v, w について完全対称。
  * `contracted_bianchi_normal`:これらから ∇^a G_ad = 0。
    展開した 12 項は、点ごとに消える 2 組と、和の添字の付け替え(`relabel_pairs`、`relabel_within`、
    `relabel_reverse`)で消える 3 組に分かれる。
  ∇^a G_ad はテンソルなので、正規座標の点で 0 なら任意の座標で 0(この「テンソル性」の段は未形式化)。
-/
import Mathlib.Tactic

namespace CFT.ContractedBianchi

open Finset

variable {n : ℕ}

/-- 4 重和 -/
def S4 (F : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ := ∑ a, ∑ b, ∑ c, ∑ e, F a b c e

theorem relabel_pairs (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    S4 (fun a b c e => F c e a b) = S4 F := by
  unfold S4
  calc ∑ a, ∑ b, ∑ c, ∑ e, F c e a b
      = ∑ a, ∑ c, ∑ b, ∑ e, F c e a b := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, ∑ e, F c e a b := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, F c e a b :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ c, ∑ e, ∑ a, ∑ b, F c e a b := Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

theorem relabel_within (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    S4 (fun a b c e => F b a e c) = S4 F := by
  unfold S4
  calc ∑ a, ∑ b, ∑ c, ∑ e, F b a e c
      = ∑ b, ∑ a, ∑ c, ∑ e, F b a e c := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ e, ∑ c, F b a e c :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))

theorem relabel_reverse (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    S4 (fun a b c e => F e c b a) = S4 F := by
  have h := relabel_within (fun a b c e => F c e a b)
  simp only at h
  rw [h, relabel_pairs]

theorem S4_congr {F G : Fin n → Fin n → Fin n → Fin n → ℝ} (h : ∀ a b c e, F a b c e = G a b c e) :
    S4 F = S4 G := by
  unfold S4
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => h a b c e

variable (gi : Fin n → Fin n → ℝ) (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)

/-- p での ∂_b∂_c Γ_eda -/
noncomputable def ddchr1 (b c e d a : Fin n) : ℝ :=
  (1/2 : ℝ) * (H e a d b c + H e d a b c - H d a e b c)

/-- p での ∂_b∂_c Γ^x_da = g^xe ∂_b∂_c Γ_eda -/
noncomputable def ddchr2 (b c x d a : Fin n) : ℝ := ∑ e, gi x e * ddchr1 H b c e d a

/-- p での ∂_b Ric_ad -/
noncomputable def dRic (b a d : Fin n) : ℝ :=
  ∑ c, (ddchr2 gi H b c c d a - ddchr2 gi H b d c c a)

/-- p での ∇^a G_ad = g^ab ∂_b Ric_ad − ½ ∂_d R(∂_d R = g^ab ∂_d Ric_ab) -/
noncomputable def divG (d : Fin n) : ℝ :=
  ∑ a, ∑ b, gi a b * dRic gi H b a d - (1/2 : ℝ) * ∑ a, ∑ b, gi a b * dRic gi H d a b

theorem contracted_bianchi_normal (hgi : ∀ a b, gi a b = gi b a)
    (hH1 : ∀ x y u v w, H x y u v w = H y x u v w)
    (hH2 : ∀ x y u v w, H x y u v w = H x y v u w)
    (hH3 : ∀ x y u v w, H x y u v w = H x y u w v) (d : Fin n) :
    divG gi H d = 0 := by
  -- 4 重和への展開
  have hexp : divG gi H d = S4 (fun a b c e => gi a b * gi c e *
      (ddchr1 H b c e d a - ddchr1 H b d e c a
        - (1/2 : ℝ) * ddchr1 H d c e b a + (1/2 : ℝ) * ddchr1 H d b e c a)) := by
    unfold divG dRic ddchr2 S4
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  -- 12 項の分解
  let W : Fin n → Fin n → Fin n → Fin n → ℝ := fun a b c e => gi a b * gi c e
  have hsplit : S4 (fun a b c e => gi a b * gi c e *
      (ddchr1 H b c e d a - ddchr1 H b d e c a
        - (1/2 : ℝ) * ddchr1 H d c e b a + (1/2 : ℝ) * ddchr1 H d b e c a))
      = (1/2 : ℝ) * (S4 (fun a b c e => W a b c e * H e a d b c)
          - S4 (fun a b c e => W a b c e * H e a c b d))
        + (1/2 : ℝ) * (S4 (fun a b c e => W a b c e * H e d a b c)
          - S4 (fun a b c e => W a b c e * H d a e b c))
        - (1/2 : ℝ) * S4 (fun a b c e => W a b c e * H e c a b d)
        + (1/2 : ℝ) * S4 (fun a b c e => W a b c e * H c a e b d)
        - (1/4 : ℝ) * (S4 (fun a b c e => W a b c e * H e a b d c)
          - S4 (fun a b c e => W a b c e * H e a c d b))
        - (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H e b a d c)
        + (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H b a e d c)
        + (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H e c a d b)
        - (1/4 : ℝ) * S4 (fun a b c e => W a b c e * H c a e d b) := by
    unfold S4
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [W, ddchr1]
    ring
  -- H の微分の添字の置換
  have hcyc : ∀ x y u v w, H x y u v w = H x y v w u := fun x y u v w => by
    rw [hH2 x y u v w, hH3 x y v u w]
  -- 点ごとに消える組
  have p1 : S4 (fun a b c e => W a b c e * H e a c b d)
      = S4 (fun a b c e => W a b c e * H e a d b c) := S4_congr fun a b c e => by
    rw [hH2 e a c b d, hH3 e a b c d, hH2 e a b d c]
  have p2 : S4 (fun a b c e => W a b c e * H e a c d b)
      = S4 (fun a b c e => W a b c e * H e a b d c) := S4_congr fun a b c e => by
    rw [hH3 e a c d b, hH2 e a c b d, hH3 e a b c d]
  have p3 : S4 (fun a b c e => W a b c e * H e c a d b)
      = S4 (fun a b c e => W a b c e * H e c a b d) := S4_congr fun a b c e => by
    rw [hH3 e c a d b]
  have p4 : S4 (fun a b c e => W a b c e * H c a e d b)
      = S4 (fun a b c e => W a b c e * H c a e b d) := S4_congr fun a b c e => by
    rw [hH3 c a e d b]
  -- 添字の付け替えで消える組
  have r1 : S4 (fun a b c e => W a b c e * H d a e b c)
      = S4 (fun a b c e => W a b c e * H e d a b c) := by
    rw [← relabel_reverse (fun a b c e => W a b c e * H d a e b c)]
    exact S4_congr fun a b c e => by
      simp only [W]
      rw [hgi e c, hgi b a, hH3 d e a c b, hH1 d e a b c]
      ring
  have r2 : S4 (fun a b c e => W a b c e * H b a e d c)
      = S4 (fun a b c e => W a b c e * H e c a b d) := by
    rw [← relabel_pairs (fun a b c e => W a b c e * H e c a b d)]
    exact S4_congr fun a b c e => by
      simp only [W]
      rw [hcyc b a e d c, hcyc b a d c e]
      ring
  have r3 : S4 (fun a b c e => W a b c e * H e b a d c)
      = S4 (fun a b c e => W a b c e * H c a e b d) := by
    rw [← relabel_within (fun a b c e => W a b c e * H c a e b d)]
    exact S4_congr fun a b c e => by
      simp only [W]
      (rw [hgi a b, hgi c e, hcyc e b a d c, hcyc e b d c a]) <;> ring
  rw [hexp, hsplit, p1, p2, p3, p4, r1, r2, r3]
  ring

end CFT.ContractedBianchi
