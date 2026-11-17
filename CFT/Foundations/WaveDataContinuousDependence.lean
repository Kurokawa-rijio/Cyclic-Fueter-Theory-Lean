import CFT.Foundations.WaveCharacteristicData

/-!
  命題集 `LEAN_GAP_TREES.md` 4-8（データへの連続依存性）のモデル 4-3 部分：
  線形波動方程式の特性初期値問題（4-3）の明示解
  φ(u, v) = p u + q v − p u₀ について、特性データ (p, q) への連続依存性を
  明示的なリプシッツ評価として示す。解が明示公式で与えられるため、
  連続依存性は三角不等式だけから出る。4-9 モデルへの拡張は 4-8 の残り。
-/

namespace CFT.WaveDataDependence

open CFT.WaveData

/-- 2つのデータに対する解の差の各点評価。 -/
theorem waveFromData_sub_le (p₁ p₂ q₁ q₂ : ℝ → ℝ) (u₀ u v : ℝ) :
    |waveFromData p₁ q₁ u₀ u v - waveFromData p₂ q₂ u₀ u v|
      ≤ |p₁ u - p₂ u| + |q₁ v - q₂ v| + |p₁ u₀ - p₂ u₀| := by
  have hdiff : waveFromData p₁ q₁ u₀ u v - waveFromData p₂ q₂ u₀ u v
      = (p₁ u - p₂ u) + (q₁ v - q₂ v) - (p₁ u₀ - p₂ u₀) := by
    simp only [waveFromData]
    ring
  rw [hdiff]
  calc |(p₁ u - p₂ u) + (q₁ v - q₂ v) - (p₁ u₀ - p₂ u₀)|
      ≤ |(p₁ u - p₂ u) + (q₁ v - q₂ v)| + |p₁ u₀ - p₂ u₀| := abs_sub _ _
    _ ≤ (|p₁ u - p₂ u| + |q₁ v - q₂ v|) + |p₁ u₀ - p₂ u₀| :=
        add_le_add_right (abs_add _ _) _

/-- データの一様な近さから解の一様な近さが出る（リプシッツ評価）。 -/
theorem waveFromData_uniform_le {p₁ p₂ q₁ q₂ : ℝ → ℝ} {A B : ℝ}
    (hp : ∀ t, |p₁ t - p₂ t| ≤ A) (hq : ∀ t, |q₁ t - q₂ t| ≤ B)
    (u₀ u v : ℝ) :
    |waveFromData p₁ q₁ u₀ u v - waveFromData p₂ q₂ u₀ u v| ≤ 2 * A + B := by
  have h1 := waveFromData_sub_le p₁ p₂ q₁ q₂ u₀ u v
  have h2 : |p₁ u - p₂ u| + |q₁ v - q₂ v| + |p₁ u₀ - p₂ u₀| ≤ A + B + A :=
    add_le_add (add_le_add (hp u) (hq v)) (hp u₀)
  have h3 : A + B + A = 2 * A + B := by ring
  exact le_trans (le_trans h1 h2) (le_of_eq h3)

/-- 連続依存性の ε–δ 形：データが ε/4 以内で近ければ解は ε 以内で近い。 -/
theorem waveFromData_continuousDependence {p₁ p₂ q₁ q₂ : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hp : ∀ t, |p₁ t - p₂ t| ≤ ε / 4) (hq : ∀ t, |q₁ t - q₂ t| ≤ ε / 4)
    (u₀ u v : ℝ) :
    |waveFromData p₁ q₁ u₀ u v - waveFromData p₂ q₂ u₀ u v| < ε := by
  have h := waveFromData_uniform_le hp hq u₀ u v
  linarith

/-- 関係する3点でデータが一致すれば解も一致する。 -/
theorem waveFromData_eq_of_agree {p₁ p₂ q₁ q₂ : ℝ → ℝ} (u₀ u v : ℝ)
    (hp : p₁ u = p₂ u) (hp₀ : p₁ u₀ = p₂ u₀) (hq : q₁ v = q₂ v) :
    waveFromData p₁ q₁ u₀ u v = waveFromData p₂ q₂ u₀ u v := by
  simp only [waveFromData, hp, hp₀, hq]

end CFT.WaveDataDependence
