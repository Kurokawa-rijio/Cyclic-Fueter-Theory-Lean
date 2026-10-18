/-
  α-II.6(Z4-D, E)⊘:対角クラスの非存在

  計量 g = dt² + a(t)²dx² + b(t)²dy²。α = a′/a、β = b′/b、A = α′、B = β′ とおくと、
  Ricci の固有値(正規直交枠)は
    λ_t = −(A + α² + B + β²)、λ_x = −(A + α² + αβ)、λ_y = −(B + β² + αβ)。
  仮定:Ricci の Codazzi 条件 λ_x′ = α(λ_t − λ_x)、λ_y′ = β(λ_t − λ_y)、
        σ₂ = λ_tλ_x + λ_xλ_y + λ_yλ_t が一定(|Ric|² = R² − 2σ₂ が一定)。
  結論:区間上の各点で Δ = α(λ_t − λ_x)(λ_t − λ_y)(λ_x − λ_y) = 0。
        つまり α ≠ 0 かつ固有値が相異なる解はない。
  なお σ₁ = R は Codazzi から自動的に一定(flow_s1)。

  証明の流れ:
    1. Codazzi を A′、B′ について解く(codazzi_to_flow)
    2. 流れに沿った微分 D を 1 回ずつ計算:σ₂ ↦ e1 ↦ e2 ↦ e3 ↦ e4(flow_s2, flow_e1〜e3)
    3. σ₂ 一定から e1 = e2 = e3 = e4 = 0
    4. 代数的証明書 Δ² = c1·e1 + c2·e2 + c3·e3 + c4·e4(cert)
  証明書の求め方:系は重み (α,β,A,B) = (1,1,2,2) で斉次なので、重み 14 の成分だけで
  195 未知数の線形方程式を解いた(aux/diag/mac.py)。sympy の Gröbner 基底 {1} の
  判定(Z14/z4_diag3.py、4 階で {1})の Lean で検証可能な形。
-/
import CFT.Basic

open Set

namespace CFT.Diagonal

noncomputable section

def lt (a b A B : ℝ) : ℝ := -(A + a^2 + B + b^2)
def lx (a b A B : ℝ) : ℝ := -(A + a^2 + a*b)
def ly (a b A B : ℝ) : ℝ := -(B + b^2 + a*b)
/-- Codazzi を解いた A′ -/
def Ap (a b A B : ℝ) : ℝ := -a*(lt a b A B - lx a b A B) - 2*a*A - A*b - a*B
/-- Codazzi を解いた B′ -/
def Bp (a b A B : ℝ) : ℝ := -b*(lt a b A B - ly a b A B) - 2*b*B - a*B - A*b
def sig1 (a b A B : ℝ) : ℝ := lt a b A B + lx a b A B + ly a b A B
def sig2 (a b A B : ℝ) : ℝ :=
  lt a b A B * lx a b A B + lx a b A B * ly a b A B + ly a b A B * lt a b A B
def Delta (a b A B : ℝ) : ℝ :=
  a * (lt a b A B - lx a b A B) * (lt a b A B - ly a b A B) * (lx a b A B - ly a b A B)

-- 自動生成:aux/diag/gen_lean.py(証明書は aux/diag/mac.py の重み付き Macaulay 行列で求めた)
/-- e1 = D^1 σ₂(流れに沿った 1 階微分) -/
def e1 (a b A B : ℝ) : ℝ := (1)*a^4*b + (-1)*a^3*b^2 + (-1)*a^2*b^3 + (2)*a^2*b*A + (-2)*a^2*b*B + (1)*a*b^4 + (-2)*a*b^2*A + (2)*a*b^2*B + (1)*a*B^2 + (1)*b*A^2

/-- e2 = D^2 σ₂(流れに沿った 2 階微分) -/
def e2 (a b A B : ℝ) : ℝ := (-4)*a^4*b^2 + (1)*a^4*B + (8)*a^3*b^3 + (2)*a^3*b*B + (-4)*a^2*b^4 + (-3)*a^2*b^2*A + (-3)*a^2*b^2*B + (2)*a^2*A*B + (-4)*a^2*B^2 + (2)*a*b^3*A + (-8)*a*b*A*B + (1)*b^4*A + (-4)*b^2*A^2 + (2)*b^2*A*B + (1)*A^2*B + (1)*A*B^2

/-- e3 = D^3 σ₂(流れに沿った 3 階微分) -/
def e3 (a b A B : ℝ) : ℝ := (1)*a^6*b + (1)*a^5*b^2 + (-1)*a^5*B + (-2)*a^4*b^3 + (2)*a^4*b*A + (-22)*a^4*b*B + (-2)*a^3*b^4 + (-20)*a^3*b^2*A + (41)*a^3*b^2*B + (-2)*a^3*A*B + (10)*a^3*B^2 + (1)*a^2*b^5 + (41)*a^2*b^3*A + (-20)*a^2*b^3*B + (1)*a^2*b*A^2 + (18)*a^2*b*A*B + (9)*a^2*b*B^2 + (1)*a*b^6 + (-22)*a*b^4*A + (2)*a*b^4*B + (9)*a*b^2*A^2 + (18)*a*b^2*A*B + (1)*a*b^2*B^2 + (-1)*a*A^2*B + (-20)*a*A*B^2 + (-1)*b^5*A + (10)*b^3*A^2 + (-2)*b^3*A*B + (-20)*b*A^2*B + (-1)*b*A*B^2

/-- e4 = D^4 σ₂(流れに沿った 4 階微分) -/
def e4 (a b A B : ℝ) : ℝ := (-1)*a^7*b + (-23)*a^6*b^2 + (2)*a^6*B + (85)*a^5*b^3 + (48)*a^5*b*B + (-122)*a^4*b^4 + (61)*a^4*b^2*A + (-25)*a^4*b^2*B + (3)*a^4*A*B + (-42)*a^4*B^2 + (85)*a^3*b^5 + (-86)*a^3*b^3*A + (-86)*a^3*b^3*B + (3)*a^3*b*A^2 + (-214)*a^3*b*A*B + (44)*a^3*b*B^2 + (-23)*a^2*b^6 + (-25)*a^2*b^4*A + (61)*a^2*b^4*B + (-117)*a^2*b^2*A^2 + (214)*a^2*b^2*A*B + (-117)*a^2*b^2*B^2 + (128)*a^2*A*B^2 + (9)*a^2*B^3 + (-1)*a*b^7 + (48)*a*b^5*A + (44)*a*b^3*A^2 + (-214)*a*b^3*A*B + (3)*a*b^3*B^2 + (2)*a*b*A^3 + (158)*a*b*A^2*B + (158)*a*b*A*B^2 + (2)*a*b*B^3 + (2)*b^6*A + (-42)*b^4*A^2 + (3)*b^4*A*B + (9)*b^2*A^3 + (128)*b^2*A^2*B + (-1)*A^3*B + (-40)*A^2*B^2 + (-1)*A*B^3

def c1 (a b A B : ℝ) : ℝ := (1)*a^8*b + (-3)*a^7*b^2 + (-2)*a^7*B + (2)*a^6*b^3 + (2)*a^6*b*A + (8)*a^6*b*B + (2)*a^5*b^4 + (-4)*a^5*b^2*A + (-4)*a^5*b^2*B + ((134930880/388531))*a^5*A^2 + (-4)*a^5*A*B + (-5)*a^5*B^2 + (-3)*a^4*b^5 + ((-5826703823/2719717))*a^4*b*A^2 + (5)*a^4*b*A*B + (25)*a^4*b*B^2 + ((289931177573/18543525))*a^3*b^6 + ((-624094350358/13598585))*a^3*b^4*A + ((387223665548/40795755))*a^3*b^4*B + ((21508051210/741741))*a^3*b^2*A^2 + ((70573773994/13598585))*a^3*b^2*A*B + ((-342125523171/67992925))*a^3*b^2*B^2 + ((627721920/388531))*a^3*A^3 + ((-41430507530/2719717))*a^3*A^2*B + ((8281564054/2719717))*a^3*A*B^2 + ((38007047626/67992925))*a^3*B^3 + ((-869737902144/67992925))*a^2*b^7 + ((-434929369152/9713275))*a^2*b^5*A + ((538779821806/203978775))*a^2*b^5*B + ((42709938307/2719717))*a^2*b^3*A^2 + ((-5333913944/247247))*a^2*b^3*A*B + ((2105161260484/203978775))*a^2*b^3*B^2 + ((-39164684100/2719717))*a^2*b*A^3 + ((149262344164/8159151))*a^2*b*A^2*B + ((126368907233/3708705))*a^2*b*A*B^2 + ((-422651843421/67992925))*a^2*b*B^3 + ((-289912634048/67992925))*a*b^8 + ((3423730106122/29139825))*a*b^6*A + ((-7344902048434/203978775))*a*b^6*B + ((-8512715016331/40795755))*a*b^4*A^2 + ((2236170749962/29139825))*a*b^4*A*B + ((-950142489941/29139825))*a*b^4*B^2 + ((1061494092/22477))*a*b^2*A^3 + ((785912228449/40795755))*a*b^2*A^2*B + ((-23472544932952/203978775))*a*b^2*A*B^2 + ((214265228843/203978775))*a*b^2*B^3 + ((140797440/388531))*a*A^4 + ((-211311504/13013))*a*A^3*B + ((407855112062/8159151))*a*A^2*B^2 + ((-1104516419399/67992925))*a*A*B^3 + ((1418888160/2719717))*a*B^4 + ((289912634048/203978775))*b^9 + ((-457393172374/15690675))*b^7*A + ((915303869642/203978775))*b^7*B + ((15704222280853/203978775))*b^5*A^2 + ((-2028181677/883025))*b^5*A*B + ((33057328124/5827965))*b^5*B^2 + ((-160569133652/8159151))*b^3*A^3 + ((-35866669879/561925))*b^3*A^2*B + ((119450927639/67992925))*b^3*A*B^2 + ((527801509546/203978775))*b^3*B^3 + ((351993600/388531))*b*A^4 + ((24418551373/741741))*b*A^3*B + ((-217712421032/5827965))*b*A^2*B^2 + ((-4639532851498/203978775))*b*A*B^3 + ((567555264/2719717))*b*B^4

def c2 (a b A B : ℝ) : ℝ := (1)*a^6*B + ((-134930880/388531))*a^4*A^2 + (2)*a^4*A*B + (4)*a^4*B^2 + ((289912634048/67992925))*a^3*b^5 + ((-564458861996/40795755))*a^3*b^3*A + ((282670309814/67992925))*a^3*b^3*B + ((21952872132/2719717))*a^3*b*A^2 + ((-32587900880/8159151))*a^3*b*A*B + ((-25017009/715715))*a^3*b*B^2 + ((289912634048/203978775))*a^2*b^6 + ((-98196683374/3578575))*a^2*b^4*A + ((80898530023/9713275))*a^2*b^4*B + ((89817586766/8159151))*a^2*b^2*A^2 + ((-761597671141/29139825))*a^2*b^2*A*B + ((124973174399/18543525))*a^2*b^2*B^2 + ((-29332800/20449))*a^2*A^3 + ((10852819189/2719717))*a^2*A^2*B + ((903135665/1165593))*a^2*A*B^2 + ((-28671976821/67992925))*a^2*B^3 + ((-289912634048/67992925))*a*b^7 + ((4765714085788/203978775))*a*b^5*A + ((-609710697646/29139825))*a*b^5*B + ((-2953532452154/40795755))*a*b^3*A^2 + ((241780626118/3708705))*a*b^3*A*B + ((-5861054373773/203978775))*a*b^3*B^2 + ((25227879252/2719717))*a*b*A^3 + ((-1713713290/89661))*a*b*A^2*B + ((4725188801689/203978775))*a*b*A*B^2 + ((-60979377821/5827965))*a*b*B^3 + ((-289912634048/203978775))*b^8 + ((667379506886/40795755))*b^6*A + ((-915303869642/203978775))*b^6*B + ((-1916165111893/203978775))*b^4*A^2 + ((-1682878010887/203978775))*b^4*A*B + ((-17329955156/3138135))*b^4*B^2 + ((816289339/429429))*b^2*A^3 + ((1204899357919/40795755))*b^2*A^2*B + ((-540488292787/18543525))*b^2*A*B^2 + ((-475958787946/203978775))*b^2*B^3 + ((-70398720/388531))*A^4 + ((-18935072928/2719717))*A^3*B + ((211791456/19019))*A^2*B^2 + ((-10574536608/2719717))*A*B^3 + ((-283777632/2719717))*B^4

def c3 (a b A B : ℝ) : ℝ := ((-134930880/388531))*a^3*A^2 + ((3940391220/2719717))*a^2*b*A^2 + ((289912634048/203978775))*a*b^6 + ((-77077842778/8159151))*a*b^4*A + ((585779530334/203978775))*a*b^4*B + ((17189080396/8159151))*a*b^2*A^2 + ((-291630351161/40795755))*a*b^2*A*B + ((37722495787/67992925))*a*b^2*B^2 + ((-698120640/388531))*a*A^3 + ((6695073936/2719717))*a*A^2*B + ((1329024764/1165593))*a*A*B^2 + ((-44356702771/67992925))*a*B^3 + ((-289912634048/203978775))*b^7 + ((11438390086/1236235))*b^5*A + ((-915303869642/203978775))*b^5*B + ((-31264237085/2719717))*b^3*A^2 + ((443496551899/40795755))*b^3*A*B + ((-237513176708/40795755))*b^3*B^2 + ((5449563780/2719717))*b*A^3 + ((-20708882372/8159151))*b*A^2*B + ((18048102143/10735725))*b*A*B^2 + ((-487966033546/203978775))*b*B^3

def c4 (a b A B : ℝ) : ℝ := ((-718176/35321))*b^2*A^2 + ((3824448/22477))*b^2*A*B + ((-37041696/247247))*b^2*B^2 + ((-70398720/388531))*A^3 + ((283777632/2719717))*A^2*B + ((70398720/388531))*A*B^2 + ((-283777632/2719717))*B^3

/-- 区間上で一定の関数の微分は 0 -/
theorem deriv_zero_of_const {g : ℝ → ℝ} {p q c v t : ℝ} (hc : ∀ u ∈ Ioo p q, g u = c)
    (ht : t ∈ Ioo p q) (hg : HasDerivAt g v t) : v = 0 := by
  have hev : g =ᶠ[nhds t] fun _ => c :=
    Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) (fun u hu => hc u hu)
  have h0 : HasDerivAt g 0 t := (hasDerivAt_const t c).congr_of_eventuallyEq hev
  exact hg.unique h0

set_option maxHeartbeats 0 in
/-- 証明書 Δ² = Σ cₖ eₖ -/
theorem cert (a b A B : ℝ) :
    Delta a b A B ^ 2 = c1 a b A B * e1 a b A B + c2 a b A B * e2 a b A B
      + c3 a b A B * e3 a b A B + c4 a b A B * e4 a b A B := by
  simp only [Delta, lt, lx, ly, c1, c2, c3, c4, e1, e2, e3, e4]; ring

variable (a b A B : ℝ → ℝ)

/-- Codazzi 条件(λ_x′ = α(λ_t − λ_x) など)から A′ = Ap、B′ = Bp -/
theorem codazzi_to_flow (t : ℝ) (ha : HasDerivAt a (A t) t) (hb : HasDerivAt b (B t) t)
    (hx : HasDerivAt (fun t => lx (a t) (b t) (A t) (B t))
      (a t * (lt (a t) (b t) (A t) (B t) - lx (a t) (b t) (A t) (B t))) t)
    (hy : HasDerivAt (fun t => ly (a t) (b t) (A t) (B t))
      (b t * (lt (a t) (b t) (A t) (B t) - ly (a t) (b t) (A t) (B t))) t) :
    HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t ∧ HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t := by
  have eA : A = fun t => -lx (a t) (b t) (A t) (B t) - a t ^ 2 - a t * b t := by
    funext u; simp only [lx]; ring
  have eB : B = fun t => -ly (a t) (b t) (A t) (B t) - b t ^ 2 - a t * b t := by
    funext u; simp only [ly]; ring
  constructor
  · rw [eA]
    convert ((hx.neg.sub (ha.pow 2)).sub (ha.mul hb)) using 1
    simp only [Ap, lt, lx, ly]; push_cast; ring
  · rw [eB]
    convert ((hy.neg.sub (hb.pow 2)).sub (ha.mul hb)) using 1
    simp only [Bp, lt, lx, ly]; push_cast; ring

set_option maxHeartbeats 0 in
theorem flow_s1 (t : ℝ) (ha : HasDerivAt a (A t) t) (hb : HasDerivAt b (B t) t)
    (hA : HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t) (hB : HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t) :
    HasDerivAt (fun t => sig1 (a t) (b t) (A t) (B t)) (0) t := by
  convert (((((((hasDerivAt_const t (-2:ℝ)).mul ha).mul ha).add (((hasDerivAt_const t (-2:ℝ)).mul ha).mul hb)).add (((hasDerivAt_const t (-2:ℝ)).mul hb).mul hb)).add ((hasDerivAt_const t (-2:ℝ)).mul hA)).add ((hasDerivAt_const t (-2:ℝ)).mul hB)) using 1
  · funext u; simp only [sig1, lt, lx, ly]; ring
  · simp only [Ap, Bp, lt, lx, ly]; ring

set_option maxHeartbeats 0 in
theorem flow_s2 (t : ℝ) (ha : HasDerivAt a (A t) t) (hb : HasDerivAt b (B t) t)
    (hA : HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t) (hB : HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t) :
    HasDerivAt (fun t => sig2 (a t) (b t) (A t) (B t)) (e1 (a t) (b t) (A t) (B t)) t := by
  convert ((((((((((((((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul ha).mul ha).add (((((hasDerivAt_const t (3:ℝ)).mul ha).mul ha).mul ha).mul hb)).add (((((hasDerivAt_const t (4:ℝ)).mul ha).mul ha).mul hb).mul hb)).add ((((hasDerivAt_const t (2:ℝ)).mul ha).mul ha).mul hA)).add ((((hasDerivAt_const t (3:ℝ)).mul ha).mul ha).mul hB)).add (((((hasDerivAt_const t (3:ℝ)).mul ha).mul hb).mul hb).mul hb)).add ((((hasDerivAt_const t (3:ℝ)).mul ha).mul hb).mul hA)).add ((((hasDerivAt_const t (3:ℝ)).mul ha).mul hb).mul hB)).add (((((hasDerivAt_const t (1:ℝ)).mul hb).mul hb).mul hb).mul hb)).add ((((hasDerivAt_const t (3:ℝ)).mul hb).mul hb).mul hA)).add ((((hasDerivAt_const t (2:ℝ)).mul hb).mul hb).mul hB)).add (((hasDerivAt_const t (1:ℝ)).mul hA).mul hA)).add (((hasDerivAt_const t (3:ℝ)).mul hA).mul hB)).add (((hasDerivAt_const t (1:ℝ)).mul hB).mul hB)) using 1
  · funext u; simp only [sig2, lt, lx, ly]; ring
  · simp only [e1, Ap, Bp, lt, lx, ly]; ring

set_option maxHeartbeats 0 in
theorem flow_e1 (t : ℝ) (ha : HasDerivAt a (A t) t) (hb : HasDerivAt b (B t) t)
    (hA : HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t) (hB : HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t) :
    HasDerivAt (fun t => e1 (a t) (b t) (A t) (B t)) (e2 (a t) (b t) (A t) (B t)) t := by
  convert (((((((((((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul ha).mul ha).mul hb).add ((((((hasDerivAt_const t (-1:ℝ)).mul ha).mul ha).mul ha).mul hb).mul hb)).add ((((((hasDerivAt_const t (-1:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hb)).add (((((hasDerivAt_const t (2:ℝ)).mul ha).mul ha).mul hb).mul hA)).add (((((hasDerivAt_const t (-2:ℝ)).mul ha).mul ha).mul hb).mul hB)).add ((((((hasDerivAt_const t (1:ℝ)).mul ha).mul hb).mul hb).mul hb).mul hb)).add (((((hasDerivAt_const t (-2:ℝ)).mul ha).mul hb).mul hb).mul hA)).add (((((hasDerivAt_const t (2:ℝ)).mul ha).mul hb).mul hb).mul hB)).add ((((hasDerivAt_const t (1:ℝ)).mul ha).mul hB).mul hB)).add ((((hasDerivAt_const t (1:ℝ)).mul hb).mul hA).mul hA)) using 1
  · funext u; simp only [e1]; ring
  · simp only [e2, Ap, Bp, lt, lx, ly]; ring

set_option maxHeartbeats 0 in
theorem flow_e2 (t : ℝ) (ha : HasDerivAt a (A t) t) (hb : HasDerivAt b (B t) t)
    (hA : HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t) (hB : HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t) :
    HasDerivAt (fun t => e2 (a t) (b t) (A t) (B t)) (e3 (a t) (b t) (A t) (B t)) t := by
  convert ((((((((((((((((((((((hasDerivAt_const t (-4:ℝ)).mul ha).mul ha).mul ha).mul ha).mul hb).mul hb).add ((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul ha).mul ha).mul hB)).add (((((((hasDerivAt_const t (8:ℝ)).mul ha).mul ha).mul ha).mul hb).mul hb).mul hb)).add ((((((hasDerivAt_const t (2:ℝ)).mul ha).mul ha).mul ha).mul hb).mul hB)).add (((((((hasDerivAt_const t (-4:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hb).mul hb)).add ((((((hasDerivAt_const t (-3:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hA)).add ((((((hasDerivAt_const t (-3:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hB)).add (((((hasDerivAt_const t (2:ℝ)).mul ha).mul ha).mul hA).mul hB)).add (((((hasDerivAt_const t (-4:ℝ)).mul ha).mul ha).mul hB).mul hB)).add ((((((hasDerivAt_const t (2:ℝ)).mul ha).mul hb).mul hb).mul hb).mul hA)).add (((((hasDerivAt_const t (-8:ℝ)).mul ha).mul hb).mul hA).mul hB)).add ((((((hasDerivAt_const t (1:ℝ)).mul hb).mul hb).mul hb).mul hb).mul hA)).add (((((hasDerivAt_const t (-4:ℝ)).mul hb).mul hb).mul hA).mul hA)).add (((((hasDerivAt_const t (2:ℝ)).mul hb).mul hb).mul hA).mul hB)).add ((((hasDerivAt_const t (1:ℝ)).mul hA).mul hA).mul hB)).add ((((hasDerivAt_const t (1:ℝ)).mul hA).mul hB).mul hB)) using 1
  · funext u; simp only [e2]; ring
  · simp only [e3, Ap, Bp, lt, lx, ly]; ring

set_option maxHeartbeats 0 in
theorem flow_e3 (t : ℝ) (ha : HasDerivAt a (A t) t) (hb : HasDerivAt b (B t) t)
    (hA : HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t) (hB : HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t) :
    HasDerivAt (fun t => e3 (a t) (b t) (A t) (B t)) (e4 (a t) (b t) (A t) (B t)) t := by
  convert (((((((((((((((((((((((((((((((((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul ha).mul ha).mul ha).mul ha).mul hb).add ((((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul ha).mul ha).mul ha).mul hb).mul hb)).add (((((((hasDerivAt_const t (-1:ℝ)).mul ha).mul ha).mul ha).mul ha).mul ha).mul hB)).add ((((((((hasDerivAt_const t (-2:ℝ)).mul ha).mul ha).mul ha).mul ha).mul hb).mul hb).mul hb)).add (((((((hasDerivAt_const t (2:ℝ)).mul ha).mul ha).mul ha).mul ha).mul hb).mul hA)).add (((((((hasDerivAt_const t (-22:ℝ)).mul ha).mul ha).mul ha).mul ha).mul hb).mul hB)).add ((((((((hasDerivAt_const t (-2:ℝ)).mul ha).mul ha).mul ha).mul hb).mul hb).mul hb).mul hb)).add (((((((hasDerivAt_const t (-20:ℝ)).mul ha).mul ha).mul ha).mul hb).mul hb).mul hA)).add (((((((hasDerivAt_const t (41:ℝ)).mul ha).mul ha).mul ha).mul hb).mul hb).mul hB)).add ((((((hasDerivAt_const t (-2:ℝ)).mul ha).mul ha).mul ha).mul hA).mul hB)).add ((((((hasDerivAt_const t (10:ℝ)).mul ha).mul ha).mul ha).mul hB).mul hB)).add ((((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hb).mul hb).mul hb)).add (((((((hasDerivAt_const t (41:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hb).mul hA)).add (((((((hasDerivAt_const t (-20:ℝ)).mul ha).mul ha).mul hb).mul hb).mul hb).mul hB)).add ((((((hasDerivAt_const t (1:ℝ)).mul ha).mul ha).mul hb).mul hA).mul hA)).add ((((((hasDerivAt_const t (18:ℝ)).mul ha).mul ha).mul hb).mul hA).mul hB)).add ((((((hasDerivAt_const t (9:ℝ)).mul ha).mul ha).mul hb).mul hB).mul hB)).add ((((((((hasDerivAt_const t (1:ℝ)).mul ha).mul hb).mul hb).mul hb).mul hb).mul hb).mul hb)).add (((((((hasDerivAt_const t (-22:ℝ)).mul ha).mul hb).mul hb).mul hb).mul hb).mul hA)).add (((((((hasDerivAt_const t (2:ℝ)).mul ha).mul hb).mul hb).mul hb).mul hb).mul hB)).add ((((((hasDerivAt_const t (9:ℝ)).mul ha).mul hb).mul hb).mul hA).mul hA)).add ((((((hasDerivAt_const t (18:ℝ)).mul ha).mul hb).mul hb).mul hA).mul hB)).add ((((((hasDerivAt_const t (1:ℝ)).mul ha).mul hb).mul hb).mul hB).mul hB)).add (((((hasDerivAt_const t (-1:ℝ)).mul ha).mul hA).mul hA).mul hB)).add (((((hasDerivAt_const t (-20:ℝ)).mul ha).mul hA).mul hB).mul hB)).add (((((((hasDerivAt_const t (-1:ℝ)).mul hb).mul hb).mul hb).mul hb).mul hb).mul hA)).add ((((((hasDerivAt_const t (10:ℝ)).mul hb).mul hb).mul hb).mul hA).mul hA)).add ((((((hasDerivAt_const t (-2:ℝ)).mul hb).mul hb).mul hb).mul hA).mul hB)).add (((((hasDerivAt_const t (-20:ℝ)).mul hb).mul hA).mul hA).mul hB)).add (((((hasDerivAt_const t (-1:ℝ)).mul hb).mul hA).mul hB).mul hB)) using 1
  · funext u; simp only [e3]; ring
  · simp only [e4, Ap, Bp, lt, lx, ly]; ring

/-- α-II.6:Codazzi + σ₂ 一定 ⇒ 区間上で Δ = 0 -/
theorem diagonal_class_degenerate (p q s0 : ℝ)
    (ha : ∀ t ∈ Ioo p q, HasDerivAt a (A t) t) (hb : ∀ t ∈ Ioo p q, HasDerivAt b (B t) t)
    (hx : ∀ t ∈ Ioo p q, HasDerivAt (fun t => lx (a t) (b t) (A t) (B t))
      (a t * (lt (a t) (b t) (A t) (B t) - lx (a t) (b t) (A t) (B t))) t)
    (hy : ∀ t ∈ Ioo p q, HasDerivAt (fun t => ly (a t) (b t) (A t) (B t))
      (b t * (lt (a t) (b t) (A t) (B t) - ly (a t) (b t) (A t) (B t))) t)
    (hs : ∀ t ∈ Ioo p q, sig2 (a t) (b t) (A t) (B t) = s0) :
    ∀ t ∈ Ioo p q, Delta (a t) (b t) (A t) (B t) = 0 := by
  have hAB := fun t ht => codazzi_to_flow a b A B t (ha t ht) (hb t ht) (hx t ht) (hy t ht)
  have z1 : ∀ t ∈ Ioo p q, e1 (a t) (b t) (A t) (B t) = 0 := fun t ht =>
    deriv_zero_of_const hs ht (flow_s2 a b A B t (ha t ht) (hb t ht) (hAB t ht).1 (hAB t ht).2)
  have z2 : ∀ t ∈ Ioo p q, e2 (a t) (b t) (A t) (B t) = 0 := fun t ht =>
    deriv_zero_of_const z1 ht (flow_e1 a b A B t (ha t ht) (hb t ht) (hAB t ht).1 (hAB t ht).2)
  have z3 : ∀ t ∈ Ioo p q, e3 (a t) (b t) (A t) (B t) = 0 := fun t ht =>
    deriv_zero_of_const z2 ht (flow_e2 a b A B t (ha t ht) (hb t ht) (hAB t ht).1 (hAB t ht).2)
  have z4 : ∀ t ∈ Ioo p q, e4 (a t) (b t) (A t) (B t) = 0 := fun t ht =>
    deriv_zero_of_const z3 ht (flow_e3 a b A B t (ha t ht) (hb t ht) (hAB t ht).1 (hAB t ht).2)
  intro t ht
  have h := cert (a t) (b t) (A t) (B t)
  rw [z1 t ht, z2 t ht, z3 t ht, z4 t ht] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by simpa using h)

/-- R = σ₁ は Codazzi から自動的に保存される(区間上で一定) -/
theorem scalar_conserved (p q : ℝ)
    (ha : ∀ t ∈ Ioo p q, HasDerivAt a (A t) t) (hb : ∀ t ∈ Ioo p q, HasDerivAt b (B t) t)
    (hA : ∀ t ∈ Ioo p q, HasDerivAt A (Ap (a t) (b t) (A t) (B t)) t)
    (hB : ∀ t ∈ Ioo p q, HasDerivAt B (Bp (a t) (b t) (A t) (B t)) t) :
    ∀ t ∈ Ioo p q, HasDerivAt (fun t => sig1 (a t) (b t) (A t) (B t)) 0 t :=
  fun t ht => flow_s1 a b A B t (ha t ht) (hb t ht) (hA t ht) (hB t ht)

end

end CFT.Diagonal
