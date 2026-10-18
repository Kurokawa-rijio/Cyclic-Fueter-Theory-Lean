/-
  α-VIII.7(Z44)の仮定を分ける:監査の指摘「三つの外部の事実をリテラル `* 0` を含む一つの仮定に
  まとめている」への対応

  旧 no_killing_spinor の仮定 hiso は (i) 双線形が Killing ベクトル、(ii) 等長変換は r を保つ、
  (iii) 喉で ∂_s r = 0、をまとめていた。ここでは (iii) を証明する:
    * throat_ds_zero:ダンベルは首の中心 s = 0 で鏡映対称 r(t, s) = r(t, −s)。偶関数の微分は 0 なので
      ∂_s r(t, 0) = 0(仮定ではなく対称性からの帰結)
  残る外部の事実は (i)(ii) を合わせた一つ:Killing ベクトル K = (K^t, K^s) は r を保つ、
    K^t ∂_t r + K^s ∂_s r = 0(hKill、Tod の定理と球対称な等長変換の性質)。
    * no_killing_spinor_sym:鏡映対称なダンベルで、喉の半径 r(t, 0) が正から 0 になる(崩壊する)なら、
      Killing スピノルはない
    * z44_full:喉の半径が中心の式に従い、類 (rW)² ≥ κ、2κ ≥ ℓ² にあるなら、Z9 の崩壊(z9_reaches_zero)
      と合わせて Killing スピノルはない(崩壊は仮定でなく定理から)
-/
import CFT.AlphaVIII_Z44
import CFT.AlphaIV_Z9

open Real Set

namespace CFT.Z44b

/-- 偶関数の原点での微分は 0 -/
theorem throat_ds_zero (f : ℝ → ℝ) (d : ℝ) (hd : HasDerivAt f d 0) (hsym : ∀ s, f s = f (-s)) :
    d = 0 := by
  have h2 : HasDerivAt (fun s => f (-s)) (d * (-1)) 0 := by
    have hd' : HasDerivAt f d (-id (0 : ℝ)) := by simpa using hd
    have := hd'.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
    simpa [Function.comp_def] using this
  have hfeq : (fun s => f (-s)) = f := funext fun s => (hsym s).symm
  rw [hfeq] at h2
  have := hd.unique h2
  linarith

/-- 鏡映対称なダンベルで喉が崩壊するなら Killing スピノルはない -/
theorem no_killing_spinor_sym (r : ℝ → ℝ → ℝ) (rt rs : ℝ → ℝ)
    (hds : ∀ t, HasDerivAt (fun s => r t s) (rs t) 0)
    (hsym : ∀ t s, r t s = r t (-s))
    (hdt : ∀ t, HasDerivAt (fun τ => r τ 0) (rt t) t)
    (ε : ℝ → Fin 4 → ℝ × ℝ) (hε : ∀ t, ε t ≠ 0) (Ks : ℝ → ℝ)
    (hKill : ∀ t, (∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) * rt t + Ks t * rs t = 0)
    (hcollapse : 0 < r 0 0 ∧ ∃ T, r T 0 = 0) : False := by
  have hz : ∀ t, rs t = 0 := fun t => throat_ds_zero _ _ (hds t) (hsym t)
  have hiso : ∀ t, (∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) * rt t + Ks t * 0 = 0 := by
    intro t; have := hKill t; rw [hz t] at this; exact this
  exact CFT.Z44.no_killing_spinor (fun τ => r τ 0) rt hdt hcollapse ε hε Ks hiso

/-- Z9 と合わせる:喉の半径が中心の式に従えば、崩壊は定理として出て、Killing スピノルはない -/
theorem z44_full (r : ℝ → ℝ → ℝ) (rt rs rtt W : ℝ → ℝ) (l κ r1 : ℝ) (hr1p : 0 < r1)
    (hds : ∀ t, HasDerivAt (fun s => r t s) (rs t) 0)
    (hsym : ∀ t s, r t s = r t (-s))
    (hdt : ∀ t, HasDerivAt (fun τ => r τ 0) (rt t) t)
    (hdtt : ∀ t, HasDerivAt rt (CFT.Z9.acc l (r t 0) (rt t) (W t)) t)
    (hk : l ^ 2 ≤ 2 * κ) (hW : ∀ t, κ ≤ W t ^ 2 * r t 0 ^ 2)
    (h0 : rt 0 = 0) (hr1 : r 0 0 = r1)
    (ε : ℝ → Fin 4 → ℝ × ℝ) (hε : ∀ t, ε t ≠ 0) (Ks : ℝ → ℝ)
    (hKill : ∀ t, (∑ a, ((ε t a).1 ^ 2 + (ε t a).2 ^ 2)) * rt t + Ks t * rs t = 0) : False := by
  obtain ⟨T, -, hT⟩ := CFT.Z9.z9_reaches_zero (fun τ => r τ 0) rt W l κ 0 r1 hr1p
    (fun τ _ => hdt τ) (fun τ _ => hdtt τ) hk (fun τ _ => hW τ) h0 hr1
  exact no_killing_spinor_sym r rt rs hds hsym hdt ε hε Ks hKill ⟨by rw [hr1]; exact hr1p, T, hT⟩

end CFT.Z44b
