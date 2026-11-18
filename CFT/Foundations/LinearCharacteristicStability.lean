/-
  命題集 `LEAN_GAP_TREES.md` 4-12(線形化作用素の安定性評価)の局所版(2026-11-18)

  線形化した系(係数は背景解で決まる)
    ∂_u∂_v δ_i = Σ_j (c⁰_ij δ_j + c¹_ij ∂_u δ_j + c²_ij ∂_v δ_j)
  の係数が長方形の上で |c| ≤ M なら、長方形の上で
    Σ_j (|δ_j| + |∂_u δ_j| + |∂_v δ_j|) ≤ 6nE e^{λ(u+v)}(λ = 4 max(n(1+M), 1))。
  E は辺の上の C¹ トレースの大きさ(v = 0 の辺で |δ| と |∂_u δ|、u = 0 の辺で |∂_v δ|)。
  評価は角 (0,0) から指数的に増える Grönwall 型で、重み e^{−λ(u+v)} をかけると長方形の上で一様に ≤ 6nE と読める。
  命題集の「頂点近傍での重みつき評価」との対応はこの意味までで、角で特異になる重みは扱っていない。
  証明は 4-8 の `char_dependence` に係数の評価を入れるだけ。
-/
import CFT.Foundations.CharacteristicDependence

open Real Set
open CFT.CharUniqueness CFT.CharDependence

namespace CFT.LinearStability

/-- 線形の右辺のリプシッツ評価 -/
theorem linear_rhs_bound {n : ℕ} {M : ℝ} (hM : 0 ≤ M) (c : Fin n → Fin 3 → ℝ)
    (hc : ∀ j k, |c j k| ≤ M) (x y z : Fin n → ℝ) :
    |∑ j, (c j 0 * x j + c j 1 * y j + c j 2 * z j)| ≤ M * ∑ j, (|x j| + |y j| + |z j|) := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have h0 : |c j 0 * x j| ≤ M * |x j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc j 0) (abs_nonneg _)
  have h1 : |c j 1 * y j| ≤ M * |y j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc j 1) (abs_nonneg _)
  have h2 : |c j 2 * z j| ≤ M * |z j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc j 2) (abs_nonneg _)
  calc |c j 0 * x j + c j 1 * y j + c j 2 * z j|
      ≤ |c j 0 * x j + c j 1 * y j| + |c j 2 * z j| := abs_add _ _
    _ ≤ |c j 0 * x j| + |c j 1 * y j| + |c j 2 * z j| := by
        linarith [abs_add (c j 0 * x j) (c j 1 * y j)]
    _ ≤ M * (|x j| + |y j| + |z j|) := by linarith

/-- 線形化した特性初期値問題の安定性評価(4-12 の局所版) -/
theorem linear_stability {n : ℕ} {a b M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (d du dv duv : Fin n → ℝ → ℝ → ℝ)
    (hC : ∀ i, C2Data a b (d i) (du i) (dv i) (duv i))
    (c : Fin n → Fin n → Fin 3 → ℝ → ℝ → ℝ)
    (hc : ∀ i j k, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b, |c i j k u v| ≤ M)
    (heq : ∀ i, ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      duv i u v = ∑ j, (c i j 0 u v * d j u v + c i j 1 u v * du j u v + c i j 2 u v * dv j u v))
    (hE1 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, |d i u 0| ≤ E)
    (hE2 : ∀ i, ∀ u ∈ Icc (0:ℝ) a, |du i u 0| ≤ E)
    (hE3 : ∀ i, ∀ v ∈ Icc (0:ℝ) b, |dv i 0 v| ≤ E) :
    ∀ u ∈ Icc (0:ℝ) a, ∀ v ∈ Icc (0:ℝ) b,
      ∑ j, (|d j u v| + |du j u v| + |dv j u v|)
        ≤ 2 * (3 * n * E) * exp ((4 * max (n * (1 + M)) 1) * (u + v)) :=
  char_dependence hM hE d du dv duv hC hE1 hE2 hE3 (fun i u hu v hv => by
    rw [heq i u hu v hv]
    exact linear_rhs_bound hM (fun j k => c i j k u v) (fun j k => hc i j k u hu v hv)
      (fun j => d j u v) (fun j => du j u v) (fun j => dv j u v))

end CFT.LinearStability
