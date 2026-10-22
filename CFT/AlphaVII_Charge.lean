/-
  α-VII.8(Z28-f)の「電荷の割り当て」を入力から定理へ

  SO(10) の Cartan 部分代数の元を係数 c ∈ ℚ⁵ で表す。重み μ(16 の重みは e/2、e ∈ {±1}⁵)への作用は
  c·μ。ルート α の生成子 E_α と可換 ⇔ c·α = 0([H_c, E_α] = (c·α)E_α、Lie 代数の標準事実)。
    * SU(3)_C のルート e₀ − e₁、e₁ − e₂、SU(2)_L のルート e₃ + e₄(T₃L = (w₃ + w₄)/2 の向き)
  定理:
    * hypercharge_commutant:c が三つのルートと直交 ⇔ Y = a·T₃R + b·(B − L)(a = 2c₃、b = −(3/2)c₀)。
      超電荷の候補は 2 次元で、T₃R と B − L が張る(SU(3) × SU(2)_L の可換子の Cartan 部分)
    * charge_unique:Q = T₃L + a·T₃R + b·(B − L) で ν_L(色一重項、T₃L = +½)と ν^c(色一重項、T₃R = −½)
      が中性 ⇔ a = 1、b = ½
    * charge_all_solutions:「色一重項の SU(2)_L 二重項と SU(2)_R 二重項がそれぞれ中性の成分を持つ」だけを
      要求すると解は (a, b) = (±1, ±½) の 4 つで、名前の付け替え(T₃L、T₃R の向き)で互いに移る
    * charge_formula:a = 1、b = ½ の Q は、16 のすべての重みで AlphaVII_SO10 の 6Q = 3e₃ − (e₀+e₁+e₂)
      と一致。spinor16_charges と合わせて、一世代の電荷の表全体が二つの中性条件から決まる
  外部に残るもの:Lie 代数の [H, E_α] = (c·α)E_α(標準)、超電荷が Cartan 部分に入ること
  (可換子 U(1) × U(1) の標準的な事実)、ν_L・ν^c を中性とする物理の入力。
  質量ゼロのカイラルな場(最低モード)と Yukawa の作用は扱わない(README の α-VII.8 の注意のまま)。
-/
import CFT.AlphaVII_SO10

namespace CFT.Charge

/-- 重み e/2 に対する T₃L、T₃R、B − L(e は 2 倍した符号) -/
def T3L (e : Fin 5 → ℚ) : ℚ := (e 3 + e 4) / 4
def T3R (e : Fin 5 → ℚ) : ℚ := (e 3 - e 4) / 4
def BL (e : Fin 5 → ℚ) : ℚ := -(e 0 + e 1 + e 2) / 3

/-- Cartan の元 c の重み e/2 への作用 -/
def act (c e : Fin 5 → ℚ) : ℚ := ∑ i, c i * (e i / 2)

/-- ルート α との内積 -/
def dot (c α : Fin 5 → ℚ) : ℚ := ∑ i, c i * α i

def rootC1 : Fin 5 → ℚ := ![1, -1, 0, 0, 0]
def rootC2 : Fin 5 → ℚ := ![0, 1, -1, 0, 0]
def rootL : Fin 5 → ℚ := ![0, 0, 0, 1, 1]

/-- SU(3)_C × SU(2)_L と可換な Cartan の元は T₃R と B − L の一次結合 -/
theorem hypercharge_commutant (c : Fin 5 → ℚ) :
    (dot c rootC1 = 0 ∧ dot c rootC2 = 0 ∧ dot c rootL = 0) ↔
      ∀ e, act c e = (2 * c 3) * T3R e + (-(3 / 2) * c 0) * BL e := by
  constructor
  · rintro ⟨h1, h2, h3⟩ e
    simp [dot, rootC1, rootC2, rootL, Fin.sum_univ_five] at h1 h2 h3
    simp only [act, T3R, BL, Fin.sum_univ_five]
    have e1 : c 1 = c 0 := by linarith
    have e2 : c 2 = c 0 := by linarith
    have e4 : c 4 = -c 3 := by linarith
    rw [e1, e2, e4]; ring
  · intro h
    have v : ∀ i : Fin 5, act c (Pi.single i 1) = c i / 2 := by
      intro i; simp [act, Pi.single_apply, Fin.sum_univ_five]; fin_cases i <;> simp <;> ring
    have h0 := h (Pi.single 0 1); have h1 := h (Pi.single 1 1); have h2 := h (Pi.single 2 1)
    have h3 := h (Pi.single 3 1); have h4 := h (Pi.single 4 1)
    rw [v] at h0 h1 h2 h3 h4
    simp [T3R, BL, Pi.single_apply] at h0 h1 h2 h3 h4
    refine ⟨?_, ?_, ?_⟩ <;> simp [dot, rootC1, rootC2, rootL, Fin.sum_univ_five] <;> linarith

/-- 電荷 Q = T₃L + a T₃R + b(B − L) -/
def Q (a b : ℚ) (e : Fin 5 → ℚ) : ℚ := T3L e + a * T3R e + b * BL e

/-- ν_L:色一重項(e₀ = e₁ = e₂ = 1)、T₃L = +½ -/
def nuL : Fin 5 → ℚ := ![1, 1, 1, 1, 1]
/-- e_L:色一重項、T₃L = −½ -/
def eL : Fin 5 → ℚ := ![1, 1, 1, -1, -1]
/-- ν^c:色一重項(e₀ = e₁ = e₂ = −1)、T₃R = −½ -/
def nuc : Fin 5 → ℚ := ![-1, -1, -1, -1, 1]
/-- e^c:色一重項、T₃R = +½ -/
def ec : Fin 5 → ℚ := ![-1, -1, -1, 1, -1]

/-- 二つの中性条件で係数が一意に決まる -/
theorem charge_unique (a b : ℚ) : (Q a b nuL = 0 ∧ Q a b nuc = 0) ↔ (a = 1 ∧ b = 1 / 2) := by
  simp only [Q, T3L, T3R, BL, nuL, nuc]
  simp
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- 名前を付けずに「各レプトン二重項に中性の成分がある」だけを要求すると、解は 4 つ -/
theorem charge_all_solutions (a b : ℚ) :
    ((Q a b nuL = 0 ∨ Q a b eL = 0) ∧ (Q a b nuc = 0 ∨ Q a b ec = 0)) ↔
      ((a = 1 ∧ b = 1 / 2) ∨ (a = -1 ∧ b = 1 / 2) ∨ (a = 1 ∧ b = -1 / 2) ∨ (a = -1 ∧ b = -1 / 2)) := by
  simp only [Q, T3L, T3R, BL, nuL, eL, nuc, ec]
  simp
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · left; constructor <;> linarith
    · right; left; constructor <;> linarith
    · right; right; right; constructor <;> linarith
    · right; right; left; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- a = 1、b = ½ の Q は 16 の重みで 6Q = 3e₃ − (e₀ + e₁ + e₂)(AlphaVII_SO10 の charges の第 1 成分) -/
theorem charge_formula (e : Fin 5 → ℚ) : 6 * Q 1 (1 / 2) e = 3 * e 3 - (e 0 + e 1 + e 2) := by
  simp only [Q, T3L, T3R, BL]; ring

/-- 同じく B − L、T₃L、T₃R も charges の残りの成分と一致 -/
theorem charge_components (e : Fin 5 → ℚ) :
    3 * BL e = -(e 0 + e 1 + e 2) ∧ 4 * T3L e = e 3 + e 4 ∧ 4 * T3R e = e 3 - e 4 := by
  simp only [BL, T3L, T3R]; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- まとめ:二つの中性条件 ⇒ 16 の電荷の表(並べ替えを除いて一世代) -/
theorem generation_from_neutrality (a b : ℚ) (h : Q a b nuL = 0 ∧ Q a b nuc = 0) :
    (∀ e, 6 * Q a b e = 3 * e 3 - (e 0 + e 1 + e 2)) ∧
      (CFT.SO10.signs.map CFT.SO10.charges).Perm CFT.SO10.oneGeneration := by
  obtain ⟨rfl, rfl⟩ := (charge_unique a b).mp h
  exact ⟨charge_formula, CFT.SO10.spinor16_charges⟩

end CFT.Charge
