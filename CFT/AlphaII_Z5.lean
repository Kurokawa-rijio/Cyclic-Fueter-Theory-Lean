/-
  α-II.9(Z5)⊘:静的ダンベルの不存在(静的方程式の完全な形)

  計量 −N(s)²dt² + ds² + r(s)²dΩ²、W = r′(公理)、V = W′。ℓ は定数(ℓ ≠ 0)。
    ρ  = 2ℓ²(V²/r² + (1−W²)²/(2r⁴))、 p_r = 2ℓ²(V²/r² − (1−W²)²/(2r⁴))
    (a) ハミルトン拘束  (1 − W² − 2rV)/r² = ρ
    (b) 動径 Einstein   2W(N′/N)/r + (W² − 1)/r² = p_r
    (d) YM(W = r′)      (N W′)′ = N W(W² − 1)/r²
  ((c) ΔN = 8πGρN は使わない。)

  結論(static_W_trichotomy, static_classification):
    区間上で W ≡ 0(このとき r ≡ ±ℓ:Bertotti–Robinson の首)か W ≡ ±1(V ≡ 0、ρ ≡ 0:平坦)。
    したがって首と帽子をつなぐ静的なダンベルはない。

  証明の流れ:
    1. (b)(d) から V′ = r3f(r, W, V)(N は消える)            : dV_from_bd
    2. (a) ⇔ E0 = r⁴·(拘束) = 0                               : E0_eq
    3. W ≠ 0, W² ≠ 1 となる開集合 U 上で E0 = 0 を流れに沿って 3 回微分:E1 = E2 = E3 = 0
    4. 証明書 ℓ²(rW(W²−1))⁴ = k0·E0 + k1·E1 + k2·E2 + k3·E3   : cert
       (sympy:ℓ = 1 で Gröbner 基底 {1} を確認し、次数 16 の Macaulay 行列から係数を取り出し、
        重み (r, ℓ, W, V) = (1, 1, 0, −1) で ℓ を戻した。aux/z5/macA.py, homog2.py)
    5. よって U は空。W は連続で値が {0, ±1} に入るから中間値の定理で一定。
  以前の版にあった「P(x, u) > 0 を格子点で数値確認」の段は不要になった
  (P = 0 となる開集合上でも、さらに微分すれば矛盾が出るため)。
-/
import CFT.Basic

open Set

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFT.Z5

noncomputable section

def rho (l r W V : ℝ) : ℝ := 2 * l^2 * (V^2 / r^2 + (1 - W^2)^2 / (2 * r^4))
def prf (l r W V : ℝ) : ℝ := 2 * l^2 * (V^2 / r^2 - (1 - W^2)^2 / (2 * r^4))
/-- ハミルトン拘束 (a) は ham = 0 -/
def ham (l r W V : ℝ) : ℝ := (1 - W^2 - 2 * r * V) / r^2 - rho l r W V
/-- (b) を解いた N′/N -/
def nfun (l r W V : ℝ) : ℝ := (prf l r W V - (W^2 - 1) / r^2) * r / (2 * W)
/-- (d) を解いた V′ = W(W²−1)/r² − (N′/N)V -/
def r3f (l r W V : ℝ) : ℝ := W * (W^2 - 1) / r^2 - nfun l r W V * V

/-- E0(= r⁴ × ハミルトン拘束) -/
def E0 (l r W V : ℝ) : ℝ := (-2:ℝ) * l^2 * r^2 * V^2 + (-1:ℝ) * l^2 * W^4 + (2:ℝ) * l^2 * W^2 + (-1:ℝ) * l^2 + (-2:ℝ) * r^3 * V + (-1:ℝ) * r^2 * W^2 + (1:ℝ) * r^2

/-- E1 = 流れに沿った微分の分子 -/
def E1 (l r W V : ℝ) : ℝ := (4:ℝ) * l^4 * r^2 * V^4 + (-2:ℝ) * l^4 * W^4 * V^2 + (4:ℝ) * l^4 * W^2 * V^2 + (-2:ℝ) * l^4 * V^2 + (2:ℝ) * l^2 * r^3 * V^3 + (-6:ℝ) * l^2 * r^2 * W^2 * V^2 + (2:ℝ) * l^2 * r^2 * V^2 + (-9:ℝ) * l^2 * r * W^4 * V + (10:ℝ) * l^2 * r * W^2 * V + (-1:ℝ) * l^2 * r * V + (-9:ℝ) * r^3 * W^2 * V + (1:ℝ) * r^3 * V + (-4:ℝ) * r^2 * W^4 + (4:ℝ) * r^2 * W^2

/-- E2 = 流れに沿った微分の分子 -/
def E2 (l r W V : ℝ) : ℝ := (-32:ℝ) * l^6 * r^4 * V^6 + (24:ℝ) * l^6 * r^2 * W^4 * V^4 + (-48:ℝ) * l^6 * r^2 * W^2 * V^4 + (24:ℝ) * l^6 * r^2 * V^4 + (-4:ℝ) * l^6 * W^8 * V^2 + (16:ℝ) * l^6 * W^6 * V^2 + (-24:ℝ) * l^6 * W^4 * V^2 + (16:ℝ) * l^6 * W^2 * V^2 + (-4:ℝ) * l^6 * V^2 + (-12:ℝ) * l^4 * r^5 * V^5 + (56:ℝ) * l^4 * r^4 * W^2 * V^4 + (-24:ℝ) * l^4 * r^4 * V^4 + (40:ℝ) * l^4 * r^3 * W^4 * V^3 + (-48:ℝ) * l^4 * r^3 * W^2 * V^3 + (8:ℝ) * l^4 * r^3 * V^3 + (-16:ℝ) * l^4 * r^2 * W^6 * V^2 + (40:ℝ) * l^4 * r^2 * W^4 * V^2 + (-32:ℝ) * l^4 * r^2 * W^2 * V^2 + (8:ℝ) * l^4 * r^2 * V^2 + (-17:ℝ) * l^4 * r * W^8 * V + (52:ℝ) * l^4 * r * W^6 * V + (-54:ℝ) * l^4 * r * W^4 * V + (20:ℝ) * l^4 * r * W^2 * V + (-1:ℝ) * l^4 * r * V + (12:ℝ) * l^2 * r^5 * W^2 * V^3 + (-8:ℝ) * l^2 * r^5 * V^3 + (-96:ℝ) * l^2 * r^4 * W^4 * V^2 + (52:ℝ) * l^2 * r^4 * W^2 * V^2 + (-4:ℝ) * l^2 * r^4 * V^2 + (-60:ℝ) * l^2 * r^3 * W^6 * V + (90:ℝ) * l^2 * r^3 * W^4 * V + (-32:ℝ) * l^2 * r^3 * W^2 * V + (2:ℝ) * l^2 * r^3 * V + (-18:ℝ) * l^2 * r^2 * W^8 + (38:ℝ) * l^2 * r^2 * W^6 + (-22:ℝ) * l^2 * r^2 * W^4 + (2:ℝ) * l^2 * r^2 * W^2 + (-36:ℝ) * r^6 * W^2 * V^2 + (-95:ℝ) * r^5 * W^4 * V + (32:ℝ) * r^5 * W^2 * V + (-1:ℝ) * r^5 * V + (-34:ℝ) * r^4 * W^6 + (36:ℝ) * r^4 * W^4 + (-2:ℝ) * r^4 * W^2

/-- E3 = 流れに沿った微分の分子 -/
def E3 (l r W V : ℝ) : ℝ := (384:ℝ) * l^8 * r^6 * V^8 + (-384:ℝ) * l^8 * r^4 * W^4 * V^6 + (768:ℝ) * l^8 * r^4 * W^2 * V^6 + (-384:ℝ) * l^8 * r^4 * V^6 + (112:ℝ) * l^8 * r^2 * W^8 * V^4 + (-448:ℝ) * l^8 * r^2 * W^6 * V^4 + (672:ℝ) * l^8 * r^2 * W^4 * V^4 + (-448:ℝ) * l^8 * r^2 * W^2 * V^4 + (112:ℝ) * l^8 * r^2 * V^4 + (-8:ℝ) * l^8 * W^12 * V^2 + (48:ℝ) * l^8 * W^10 * V^2 + (-120:ℝ) * l^8 * W^8 * V^2 + (160:ℝ) * l^8 * W^6 * V^2 + (-120:ℝ) * l^8 * W^4 * V^2 + (48:ℝ) * l^8 * W^2 * V^2 + (-8:ℝ) * l^8 * V^2 + (120:ℝ) * l^6 * r^7 * V^7 + (-896:ℝ) * l^6 * r^6 * W^2 * V^6 + (384:ℝ) * l^6 * r^6 * V^6 + (-492:ℝ) * l^6 * r^5 * W^4 * V^5 + (600:ℝ) * l^6 * r^5 * W^2 * V^5 + (-108:ℝ) * l^6 * r^5 * V^5 + (480:ℝ) * l^6 * r^4 * W^6 * V^4 + (-1184:ℝ) * l^6 * r^4 * W^4 * V^4 + (928:ℝ) * l^6 * r^4 * W^2 * V^4 + (-224:ℝ) * l^6 * r^4 * V^4 + (282:ℝ) * l^6 * r^3 * W^8 * V^3 + (-872:ℝ) * l^6 * r^3 * W^6 * V^3 + (924:ℝ) * l^6 * r^3 * W^4 * V^3 + (-360:ℝ) * l^6 * r^3 * W^2 * V^3 + (26:ℝ) * l^6 * r^3 * V^3 + (-40:ℝ) * l^6 * r^2 * W^10 * V^2 + (184:ℝ) * l^6 * r^2 * W^8 * V^2 + (-336:ℝ) * l^6 * r^2 * W^6 * V^2 + (304:ℝ) * l^6 * r^2 * W^4 * V^2 + (-136:ℝ) * l^6 * r^2 * W^2 * V^2 + (24:ℝ) * l^6 * r^2 * V^2 + (-33:ℝ) * l^6 * r * W^12 * V + (166:ℝ) * l^6 * r * W^10 * V + (-335:ℝ) * l^6 * r * W^8 * V + (340:ℝ) * l^6 * r * W^6 * V + (-175:ℝ) * l^6 * r * W^4 * V + (38:ℝ) * l^6 * r * W^2 * V + (-1:ℝ) * l^6 * r * V + (-28:ℝ) * l^4 * r^7 * W^2 * V^5 + (108:ℝ) * l^4 * r^7 * V^5 + (1256:ℝ) * l^4 * r^6 * W^4 * V^4 + (-792:ℝ) * l^4 * r^6 * W^2 * V^4 + (112:ℝ) * l^4 * r^6 * V^4 + (772:ℝ) * l^4 * r^5 * W^6 * V^3 + (-1148:ℝ) * l^4 * r^5 * W^4 * V^3 + (428:ℝ) * l^4 * r^5 * W^2 * V^3 + (-52:ℝ) * l^4 * r^5 * V^3 + (-320:ℝ) * l^4 * r^4 * W^8 * V^2 + (856:ℝ) * l^4 * r^4 * W^6 * V^2 + (-776:ℝ) * l^4 * r^4 * W^4 * V^2 + (264:ℝ) * l^4 * r^4 * W^2 * V^2 + (-24:ℝ) * l^4 * r^4 * V^2 + (-175:ℝ) * l^4 * r^3 * W^10 * V + (607:ℝ) * l^4 * r^3 * W^8 * V + (-774:ℝ) * l^4 * r^3 * W^6 * V + (430:ℝ) * l^4 * r^3 * W^4 * V + (-91:ℝ) * l^4 * r^3 * W^2 * V + (3:ℝ) * l^4 * r^3 * V + (-34:ℝ) * l^4 * r^2 * W^12 + (138:ℝ) * l^4 * r^2 * W^10 + (-212:ℝ) * l^4 * r^2 * W^8 + (148:ℝ) * l^4 * r^2 * W^6 + (-42:ℝ) * l^4 * r^2 * W^4 + (2:ℝ) * l^4 * r^2 * W^2 + (192:ℝ) * l^2 * r^8 * W^2 * V^4 + (-422:ℝ) * l^2 * r^7 * W^4 * V^3 + (4:ℝ) * l^2 * r^7 * W^2 * V^3 + (26:ℝ) * l^2 * r^7 * V^3 + (-1680:ℝ) * l^2 * r^6 * W^6 * V^2 + (1456:ℝ) * l^2 * r^6 * W^4 * V^2 + (-296:ℝ) * l^2 * r^6 * W^2 * V^2 + (8:ℝ) * l^2 * r^6 * V^2 + (-1187:ℝ) * l^2 * r^5 * W^8 * V + (1960:ℝ) * l^2 * r^5 * W^6 * V + (-874:ℝ) * l^2 * r^5 * W^4 * V + (104:ℝ) * l^2 * r^5 * W^2 * V + (-3:ℝ) * l^2 * r^5 * V + (-192:ℝ) * l^2 * r^4 * W^10 + (452:ℝ) * l^2 * r^4 * W^8 + (-332:ℝ) * l^2 * r^4 * W^6 + (76:ℝ) * l^2 * r^4 * W^4 + (-4:ℝ) * l^2 * r^4 * W^2 + (-144:ℝ) * r^9 * W^2 * V^3 + (-1264:ℝ) * r^8 * W^4 * V^2 + (200:ℝ) * r^8 * W^2 * V^2 + (-1597:ℝ) * r^7 * W^6 * V + (879:ℝ) * r^7 * W^4 * V + (-51:ℝ) * r^7 * W^2 * V + (1:ℝ) * r^7 * V + (-462:ℝ) * r^6 * W^8 + (542:ℝ) * r^6 * W^6 + (-82:ℝ) * r^6 * W^4 + (2:ℝ) * r^6 * W^2

def k0 (l r W V : ℝ) : ℝ := (6878/2349:ℝ) * l^12 * r^2 * V^10 + (-3439/2349:ℝ) * l^12 * W^4 * V^8 + (6878/2349:ℝ) * l^12 * W^2 * V^8 + (-3439/2349:ℝ) * l^12 * V^8 + (7456/7047:ℝ) * l^10 * r^3 * V^9 + (-48034/7047:ℝ) * l^10 * r^2 * W^2 * V^8 + (118801/84564:ℝ) * l^10 * r^2 * V^8 + (-95944/21141:ℝ) * l^10 * r * W^4 * V^7 + (107128/21141:ℝ) * l^10 * r * W^2 * V^7 + (-3728/7047:ℝ) * l^10 * r * V^7 + (17083/14094:ℝ) * l^10 * W^6 * V^6 + (-404989/169128:ℝ) * l^10 * W^4 * V^6 + (97495/84564:ℝ) * l^10 * W^2 * V^6 + (5003/169128:ℝ) * l^10 * V^6 + (-65/2349:ℝ) * l^8 * r^4 * V^8 + (-7091/14094:ℝ) * l^8 * r^3 * W^2 * V^7 + (-36317/169128:ℝ) * l^8 * r^3 * V^7 + (507089/21141:ℝ) * l^8 * r^2 * W^4 * V^6 + (-1106387/169128:ℝ) * l^8 * r^2 * W^2 * V^6 + (827/1944:ℝ) * l^8 * r^2 * V^6 + (337595/84564:ℝ) * l^8 * r * W^6 * V^5 + (-194209/112752:ℝ) * l^8 * r * W^4 * V^5 + (-446771/169128:ℝ) * l^8 * r * W^2 * V^5 + (125789/338256:ℝ) * l^8 * r * V^5 + (-36436/7047:ℝ) * l^8 * W^8 * V^4 + (257794/21141:ℝ) * l^8 * W^6 * V^4 + (-769309/84564:ℝ) * l^8 * W^4 * V^4 + (97009/42282:ℝ) * l^8 * W^2 * V^4 + (-18653/84564:ℝ) * l^8 * V^4 + (26174/7047:ℝ) * l^6 * r^4 * W^2 * V^6 + (-4003/18792:ℝ) * l^6 * r^4 * V^6 + (1724617/169128:ℝ) * l^6 * r^3 * W^4 * V^5 + (41987/37584:ℝ) * l^6 * r^3 * W^2 * V^5 + (-88003/112752:ℝ) * l^6 * r^3 * V^5 + (-4279085/169128:ℝ) * l^6 * r^2 * W^6 * V^4 + (79259/9396:ℝ) * l^6 * r^2 * W^4 * V^4 + (6169/56376:ℝ) * l^6 * r^2 * W^2 * V^4 + (-1378/21141:ℝ) * l^6 * r^2 * V^4 + (-6160387/338256:ℝ) * l^6 * r * W^8 * V^3 + (7569359/338256:ℝ) * l^6 * r * W^6 * V^3 + (-458405/112752:ℝ) * l^6 * r * W^4 * V^3 + (-34289/112752:ℝ) * l^6 * r * W^2 * V^3 + (34555/169128:ℝ) * l^6 * r * V^3 + (31529/112752:ℝ) * l^6 * W^10 * V^2 + (2688683/676512:ℝ) * l^6 * W^8 * V^2 + (-155011/14094:ℝ) * l^6 * W^6 * V^2 + (35567/3888:ℝ) * l^6 * W^4 * V^2 + (-878167/338256:ℝ) * l^6 * W^2 * V^2 + (14483/75168:ℝ) * l^6 * V^2 + (-182/2349:ℝ) * l^4 * r^5 * W^2 * V^5 + (-974/261:ℝ) * l^4 * r^4 * W^4 * V^4 + (-3382/7047:ℝ) * l^4 * r^4 * W^2 * V^4 + (-8603/28188:ℝ) * l^4 * r^4 * V^4 + (-39269/2916:ℝ) * l^4 * r^3 * W^6 * V^3 + (-418595/676512:ℝ) * l^4 * r^3 * W^4 * V^3 + (33707/12528:ℝ) * l^4 * r^3 * W^2 * V^3 + (-223663/676512:ℝ) * l^4 * r^3 * V^3 + (9343661/338256:ℝ) * l^4 * r^2 * W^8 * V^2 + (-4874447/338256:ℝ) * l^4 * r^2 * W^6 * V^2 + (-19985/84564:ℝ) * l^4 * r^2 * W^4 * V^2 + (343205/338256:ℝ) * l^4 * r^2 * W^2 * V^2 + (-10133/112752:ℝ) * l^4 * r^2 * V^2 + (374093/225504:ℝ) * l^4 * r * W^10 * V + (7904177/451008:ℝ) * l^4 * r * W^8 * V + (-2571995/84564:ℝ) * l^4 * r * W^6 * V + (300013/23328:ℝ) * l^4 * r * W^4 * V + (-1145683/676512:ℝ) * l^4 * r * W^2 * V + (28481/451008:ℝ) * l^4 * r * V + (26/783:ℝ) * l^2 * r^6 * W^2 * V^4 + (7334/7047:ℝ) * l^2 * r^5 * W^4 * V^3 + (-29195/56376:ℝ) * l^2 * r^5 * W^2 * V^3 + (15052/783:ℝ) * l^2 * r^4 * W^6 * V^2 + (-479969/75168:ℝ) * l^2 * r^4 * W^4 * V^2 + (3061/3888:ℝ) * l^2 * r^4 * W^2 * V^2 + (-23183/225504:ℝ) * l^2 * r^4 * V^2 + (19649515/676512:ℝ) * l^2 * r^3 * W^8 * V + (-3838543/1353024:ℝ) * l^2 * r^3 * W^6 * V + (-709087/150336:ℝ) * l^2 * r^3 * W^4 * V + (1261331/1353024:ℝ) * l^2 * r^3 * W^2 * V + (-28481/451008:ℝ) * l^2 * r^3 * V + (-63739/18792:ℝ) * l^2 * r^2 * W^10 + (4295885/338256:ℝ) * l^2 * r^2 * W^8 + (-4185967/338256:ℝ) * l^2 * r^2 * W^6 + (1108943/338256:ℝ) * l^2 * r^2 * W^4 + (-7951/37584:ℝ) * l^2 * r^2 * W^2 + (-257/783:ℝ) * r^6 * W^4 * V^2 + (119/261:ℝ) * r^6 * W^2 * V^2 + (-38293/14094:ℝ) * r^5 * W^6 * V + (57305/14094:ℝ) * r^5 * W^4 * V + (-1552/2349:ℝ) * r^5 * W^2 * V + (-19789/28188:ℝ) * r^4 * W^8 + (47021/28188:ℝ) * r^4 * W^6 + (-26075/28188:ℝ) * r^4 * W^4 + (-1157/28188:ℝ) * r^4 * W^2

def k1 (l r W V : ℝ) : ℝ := (-8093/21141:ℝ) * l^10 * r^2 * V^8 + (50473/42282:ℝ) * l^10 * W^4 * V^6 + (-50473/21141:ℝ) * l^10 * W^2 * V^6 + (50473/42282:ℝ) * l^10 * V^6 + (548/243:ℝ) * l^8 * r^2 * W^2 * V^6 + (-279055/169128:ℝ) * l^8 * r^2 * V^6 + (-16223/21141:ℝ) * l^8 * r * W^4 * V^5 + (1436/2349:ℝ) * l^8 * r * W^2 * V^5 + (3299/21141:ℝ) * l^8 * r * V^5 + (-99313/84564:ℝ) * l^8 * W^6 * V^4 + (825581/338256:ℝ) * l^8 * W^4 * V^4 + (-229703/169128:ℝ) * l^8 * W^2 * V^4 + (1151/12528:ℝ) * l^8 * V^4 + (-79195/28188:ℝ) * l^6 * r^2 * W^4 * V^4 + (1463753/338256:ℝ) * l^6 * r^2 * W^2 * V^4 + (-253777/338256:ℝ) * l^6 * r^2 * V^4 + (47875/84564:ℝ) * l^6 * r * W^6 * V^3 + (-649973/338256:ℝ) * l^6 * r * W^4 * V^3 + (9815/5832:ℝ) * l^6 * r * W^2 * V^3 + (-110797/338256:ℝ) * l^6 * r * V^3 + (712693/169128:ℝ) * l^6 * W^8 * V^2 + (-214844/21141:ℝ) * l^6 * W^6 * V^2 + (1354969/169128:ℝ) * l^6 * W^4 * V^2 + (-67409/28188:ℝ) * l^6 * W^2 * V^2 + (6943/21141:ℝ) * l^6 * V^2 + (2639735/338256:ℝ) * l^4 * r^2 * W^6 * V^2 + (-9549221/676512:ℝ) * l^4 * r^2 * W^4 * V^2 + (360079/56376:ℝ) * l^4 * r^2 * W^2 * V^2 + (-536525/676512:ℝ) * l^4 * r^2 * V^2 + (-317261/338256:ℝ) * l^4 * r * W^8 * V + (1519081/676512:ℝ) * l^4 * r * W^6 * V + (-1220039/676512:ℝ) * l^4 * r * W^4 * V + (420923/676512:ℝ) * l^4 * r * W^2 * V + (-28481/225504:ℝ) * l^4 * r * V + (-210137/225504:ℝ) * l^4 * W^10 + (42857/46656:ℝ) * l^4 * W^8 + (10433/7047:ℝ) * l^4 * W^6 + (-458203/225504:ℝ) * l^4 * W^4 + (410863/676512:ℝ) * l^4 * W^2 + (-19225/451008:ℝ) * l^4 + (-205511/75168:ℝ) * l^2 * r^2 * W^8 + (4235743/1353024:ℝ) * l^2 * r^2 * W^6 + (-90353/1353024:ℝ) * l^2 * r^2 * W^4 + (-476099/1353024:ℝ) * l^2 * r^2 * W^2 + (3323/150336:ℝ) * l^2 * r^2 + (-19789/56376:ℝ) * r^4 * W^6 + (7621/18792:ℝ) * r^4 * W^4 + (-1031/56376:ℝ) * r^4 * W^2 + (1157/56376:ℝ) * r^4

def k2 (l r W V : ℝ) : ℝ := (-9761/42282:ℝ) * l^8 * V^6 + (-7885/42282:ℝ) * l^6 * r * V^5 + (6008/21141:ℝ) * l^6 * W^2 * V^4 + (-2255/42282:ℝ) * l^6 * V^4 + (6491/42282:ℝ) * l^4 * r * W^2 * V^3 + (5173/84564:ℝ) * l^4 * r * V^3 + (-275149/338256:ℝ) * l^4 * W^4 * V^2 + (68015/169128:ℝ) * l^4 * W^2 * V^2 + (-12193/112752:ℝ) * l^4 * V^2 + (-3605/112752:ℝ) * l^2 * r^2 * V^2 + (-337721/338256:ℝ) * l^2 * r * W^4 * V + (57931/169128:ℝ) * l^2 * r * W^2 * V + (-4835/112752:ℝ) * l^2 * r * V + (5453/14094:ℝ) * l^2 * W^6 + (-35513/56376:ℝ) * l^2 * W^4 + (14501/56376:ℝ) * l^2 * W^2 + (-100/7047:ℝ) * l^2 + (100/7047:ℝ) * r^2

def k3 (l r W V : ℝ) : ℝ := (-13/28188:ℝ) * l^2 * V^2 + (257/56376:ℝ) * W^2 + (-119/18792:ℝ)

theorem E0_eq (l r W V : ℝ) (hr : r ≠ 0) : E0 l r W V = r^4 * ham l r W V := by
  simp only [E0, ham, rho]; field_simp; ring

set_option maxHeartbeats 0 in
/-- 証明書 ℓ²(rW(W²−1))⁴ = Σ kᵢ Eᵢ -/
theorem cert (l r W V : ℝ) :
    l^2 * (r * W * (W^2 - 1))^4 = k0 l r W V * E0 l r W V + k1 l r W V * E1 l r W V
      + k2 l r W V * E2 l r W V + k3 l r W V * E3 l r W V := by
  simp only [E0, E1, E2, E3, k0, k1, k2, k3]; ring

/-- 開集合上で一定の関数の微分は 0 -/
theorem deriv_zero_on_open {U : Set ℝ} (hU : IsOpen U) {g : ℝ → ℝ} {c v t : ℝ}
    (hc : ∀ u ∈ U, g u = c) (ht : t ∈ U) (hg : HasDerivAt g v t) : v = 0 := by
  have hev : g =ᶠ[nhds t] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds ht) hc
  exact hg.unique ((hasDerivAt_const t c).congr_of_eventuallyEq hev)

variable {l : ℝ} {r W V N Np : ℝ → ℝ}

/-- (b) と (d) から V′ を求める(N は消える) -/
theorem dV_from_bd (s : ℝ) (hr0 : r s ≠ 0) (hW0 : W s ≠ 0) (hN0 : N s ≠ 0)
    (hN : HasDerivAt N (Np s) s)
    (hd : HasDerivAt (fun s => N s * V s) (N s * W s * (W s^2 - 1) / r s^2) s)
    (hb : 2 * W s * (Np s / N s) / r s + (W s^2 - 1) / r s^2 = prf l (r s) (W s) (V s)) :
    HasDerivAt V (r3f l (r s) (W s) (V s)) s := by
  have hn : Np s / N s = nfun l (r s) (W s) (V s) := by
    unfold nfun; rw [← hb]; field_simp; ring
  have hev : V =ᶠ[nhds s] fun u => (N u * V u) / N u :=
    (hN.continuousAt.eventually_ne hN0).mono fun u hu => by field_simp
  have h := (hd.div hN hN0).congr_of_eventuallyEq hev
  convert h using 1
  have e : (N s * W s * (W s^2 - 1) / r s^2 * N s - N s * V s * Np s) / N s^2
      = W s * (W s^2 - 1) / r s^2 - Np s / N s * V s := by field_simp; ring
  rw [e, hn, r3f]

set_option maxHeartbeats 0 in
theorem flow_E0 (s : ℝ) (hr0 : r s ≠ 0) (hW0 : W s ≠ 0) (hr : HasDerivAt r (W s) s)
    (hW : HasDerivAt W (V s) s) (hV : HasDerivAt V (r3f l (r s) (W s) (V s)) s) :
    HasDerivAt (fun s => E0 l (r s) (W s) (V s))
      (E1 l (r s) (W s) (V s) / (W s * r s)) s := by
  convert (((((((((((hasDerivAt_const s ((-2:ℝ) * l^2)).mul hr).mul hr).mul hV).mul hV).add (((((hasDerivAt_const s ((-1:ℝ) * l^2)).mul hW).mul hW).mul hW).mul hW)).add (((hasDerivAt_const s ((2:ℝ) * l^2)).mul hW).mul hW)).add (hasDerivAt_const s ((-1:ℝ) * l^2))).add (((((hasDerivAt_const s ((-2:ℝ))).mul hr).mul hr).mul hr).mul hV)).add (((((hasDerivAt_const s ((-1:ℝ))).mul hr).mul hr).mul hW).mul hW)).add (((hasDerivAt_const s ((1:ℝ))).mul hr).mul hr)) using 1
  · funext u; simp only [E0]; ring
  · simp only [E1, r3f, nfun, prf]; field_simp; ring

set_option maxHeartbeats 0 in
theorem flow_E1 (s : ℝ) (hr0 : r s ≠ 0) (hW0 : W s ≠ 0) (hr : HasDerivAt r (W s) s)
    (hW : HasDerivAt W (V s) s) (hV : HasDerivAt V (r3f l (r s) (W s) (V s)) s) :
    HasDerivAt (fun s => E1 l (r s) (W s) (V s))
      (E2 l (r s) (W s) (V s) / (2 * W s * (r s)^3)) s := by
  convert ((((((((((((((((((((hasDerivAt_const s ((4:ℝ) * l^4)).mul hr).mul hr).mul hV).mul hV).mul hV).mul hV).add (((((((hasDerivAt_const s ((-2:ℝ) * l^4)).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((hasDerivAt_const s ((4:ℝ) * l^4)).mul hW).mul hW).mul hV).mul hV)).add (((hasDerivAt_const s ((-2:ℝ) * l^4)).mul hV).mul hV)).add (((((((hasDerivAt_const s ((2:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hV).mul hV).mul hV)).add (((((((hasDerivAt_const s ((-6:ℝ) * l^2)).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV)).add (((((hasDerivAt_const s ((2:ℝ) * l^2)).mul hr).mul hr).mul hV).mul hV)).add (((((((hasDerivAt_const s ((-9:ℝ) * l^2)).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((hasDerivAt_const s ((10:ℝ) * l^2)).mul hr).mul hW).mul hW).mul hV)).add (((hasDerivAt_const s ((-1:ℝ) * l^2)).mul hr).mul hV)).add (((((((hasDerivAt_const s ((-9:ℝ))).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV)).add (((((hasDerivAt_const s ((1:ℝ))).mul hr).mul hr).mul hr).mul hV)).add (((((((hasDerivAt_const s ((-4:ℝ))).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW)).add (((((hasDerivAt_const s ((4:ℝ))).mul hr).mul hr).mul hW).mul hW)) using 1
  · funext u; simp only [E1]; ring
  · simp only [E2, r3f, nfun, prf]; field_simp; ring

set_option maxHeartbeats 0 in
theorem flow_E2 (s : ℝ) (hr0 : r s ≠ 0) (hW0 : W s ≠ 0) (hr : HasDerivAt r (W s) s)
    (hW : HasDerivAt W (V s) s) (hV : HasDerivAt V (r3f l (r s) (W s) (V s)) s) :
    HasDerivAt (fun s => E2 l (r s) (W s) (V s))
      (E3 l (r s) (W s) (V s) / (2 * W s * (r s)^3)) s := by
  convert ((((((((((((((((((((((((((((((((((((((((((((((((((((((hasDerivAt_const s ((-32:ℝ) * l^6)).mul hr).mul hr).mul hr).mul hr).mul hV).mul hV).mul hV).mul hV).mul hV).mul hV).add (((((((((((hasDerivAt_const s ((24:ℝ) * l^6)).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((-48:ℝ) * l^6)).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV).mul hV).mul hV)).add (((((((hasDerivAt_const s ((24:ℝ) * l^6)).mul hr).mul hr).mul hV).mul hV).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-4:ℝ) * l^6)).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((16:ℝ) * l^6)).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((((hasDerivAt_const s ((-24:ℝ) * l^6)).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((hasDerivAt_const s ((16:ℝ) * l^6)).mul hW).mul hW).mul hV).mul hV)).add (((hasDerivAt_const s ((-4:ℝ) * l^6)).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-12:ℝ) * l^4)).mul hr).mul hr).mul hr).mul hr).mul hr).mul hV).mul hV).mul hV).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((56:ℝ) * l^4)).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((-24:ℝ) * l^4)).mul hr).mul hr).mul hr).mul hr).mul hV).mul hV).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((40:ℝ) * l^4)).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((-48:ℝ) * l^4)).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV).mul hV)).add (((((((hasDerivAt_const s ((8:ℝ) * l^4)).mul hr).mul hr).mul hr).mul hV).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-16:ℝ) * l^4)).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((40:ℝ) * l^4)).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((((hasDerivAt_const s ((-32:ℝ) * l^4)).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV)).add (((((hasDerivAt_const s ((8:ℝ) * l^4)).mul hr).mul hr).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-17:ℝ) * l^4)).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((((((hasDerivAt_const s ((52:ℝ) * l^4)).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((((hasDerivAt_const s ((-54:ℝ) * l^4)).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((hasDerivAt_const s ((20:ℝ) * l^4)).mul hr).mul hW).mul hW).mul hV)).add (((hasDerivAt_const s ((-1:ℝ) * l^4)).mul hr).mul hV)).add (((((((((((hasDerivAt_const s ((12:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((-8:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hr).mul hr).mul hV).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-96:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV).mul hV)).add (((((((((hasDerivAt_const s ((52:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV)).add (((((((hasDerivAt_const s ((-4:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hr).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-60:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((((((hasDerivAt_const s ((90:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((((hasDerivAt_const s ((-32:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV)).add (((((hasDerivAt_const s ((2:ℝ) * l^2)).mul hr).mul hr).mul hr).mul hV)).add (((((((((((hasDerivAt_const s ((-18:ℝ) * l^2)).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW)).add (((((((((hasDerivAt_const s ((38:ℝ) * l^2)).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW)).add (((((((hasDerivAt_const s ((-22:ℝ) * l^2)).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW)).add (((((hasDerivAt_const s ((2:ℝ) * l^2)).mul hr).mul hr).mul hW).mul hW)).add (((((((((((hasDerivAt_const s ((-36:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV).mul hV)).add (((((((((((hasDerivAt_const s ((-95:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hV)).add (((((((((hasDerivAt_const s ((32:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hV)).add (((((((hasDerivAt_const s ((-1:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hr).mul hV)).add (((((((((((hasDerivAt_const s ((-34:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW).mul hW).mul hW)).add (((((((((hasDerivAt_const s ((36:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW).mul hW).mul hW)).add (((((((hasDerivAt_const s ((-2:ℝ))).mul hr).mul hr).mul hr).mul hr).mul hW).mul hW)) using 1
  · funext u; simp only [E2]; ring
  · simp only [E3, r3f, nfun, prf]; field_simp; ring

/-- 主定理(各点版):区間上で W = 0 か W² = 1 -/
theorem static_W_trichotomy (p q : ℝ) (hl : l ≠ 0)
    (hr0 : ∀ s ∈ Ioo p q, r s ≠ 0) (hN0 : ∀ s ∈ Ioo p q, N s ≠ 0)
    (hr : ∀ s ∈ Ioo p q, HasDerivAt r (W s) s) (hW : ∀ s ∈ Ioo p q, HasDerivAt W (V s) s)
    (hN : ∀ s ∈ Ioo p q, HasDerivAt N (Np s) s)
    (ha : ∀ s ∈ Ioo p q, ham l (r s) (W s) (V s) = 0)
    (hb : ∀ s ∈ Ioo p q,
      2 * W s * (Np s / N s) / r s + (W s^2 - 1) / r s^2 = prf l (r s) (W s) (V s))
    (hd : ∀ s ∈ Ioo p q,
      HasDerivAt (fun s => N s * V s) (N s * W s * (W s^2 - 1) / r s^2) s) :
    ∀ s ∈ Ioo p q, W s = 0 ∨ W s^2 = 1 := by
  intro s0 hs0
  by_contra hcon
  push_neg at hcon
  set U := Ioo p q ∩ W ⁻¹' {w : ℝ | w ≠ 0 ∧ w^2 ≠ 1} with hUdef
  have hcont : ContinuousOn W (Ioo p q) := fun s hs => (hW s hs).continuousAt.continuousWithinAt
  have hopen : IsOpen {w : ℝ | w ≠ 0 ∧ w^2 ≠ 1} :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun (continuous_pow 2) continuous_const)
  have hU : IsOpen U := hcont.isOpen_inter_preimage isOpen_Ioo hopen
  have hmem : ∀ t ∈ U, t ∈ Ioo p q ∧ W t ≠ 0 ∧ W t^2 ≠ 1 := fun t ht => ⟨ht.1, ht.2.1, ht.2.2⟩
  have hV : ∀ t ∈ U, HasDerivAt V (r3f l (r t) (W t) (V t)) t := fun t ht =>
    dV_from_bd t (hr0 t (hmem t ht).1) (hmem t ht).2.1 (hN0 t (hmem t ht).1) (hN t (hmem t ht).1)
      (hd t (hmem t ht).1) (hb t (hmem t ht).1)
  have z0 : ∀ t ∈ U, E0 l (r t) (W t) (V t) = 0 := fun t ht => by
    rw [E0_eq _ _ _ _ (hr0 t (hmem t ht).1), ha t (hmem t ht).1, mul_zero]
  have z1 : ∀ t ∈ U, E1 l (r t) (W t) (V t) = 0 := fun t ht => by
    have h := deriv_zero_on_open hU z0 ht (flow_E0 t (hr0 t (hmem t ht).1) (hmem t ht).2.1
      (hr t (hmem t ht).1) (hW t (hmem t ht).1) (hV t ht))
    have hd0 : W t * r t ≠ 0 := mul_ne_zero (hmem t ht).2.1 (hr0 t (hmem t ht).1)
    exact (div_eq_zero_iff.mp h).resolve_right hd0
  have z2 : ∀ t ∈ U, E2 l (r t) (W t) (V t) = 0 := fun t ht => by
    have h := deriv_zero_on_open hU z1 ht (flow_E1 t (hr0 t (hmem t ht).1) (hmem t ht).2.1
      (hr t (hmem t ht).1) (hW t (hmem t ht).1) (hV t ht))
    have hd0 : 2 * W t * (r t)^3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (hmem t ht).2.1) (pow_ne_zero 3 (hr0 t (hmem t ht).1))
    exact (div_eq_zero_iff.mp h).resolve_right hd0
  have z3 : ∀ t ∈ U, E3 l (r t) (W t) (V t) = 0 := fun t ht => by
    have h := deriv_zero_on_open hU z2 ht (flow_E2 t (hr0 t (hmem t ht).1) (hmem t ht).2.1
      (hr t (hmem t ht).1) (hW t (hmem t ht).1) (hV t ht))
    have hd0 : 2 * W t * (r t)^3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (hmem t ht).2.1) (pow_ne_zero 3 (hr0 t (hmem t ht).1))
    exact (div_eq_zero_iff.mp h).resolve_right hd0
  have hs0U : s0 ∈ U := ⟨hs0, hcon.1, hcon.2⟩
  have hc := cert l (r s0) (W s0) (V s0)
  rw [z0 s0 hs0U, z1 s0 hs0U, z2 s0 hs0U, z3 s0 hs0U] at hc
  simp only [mul_zero, add_zero] at hc
  have h1 : W s0^2 - 1 ≠ 0 := sub_ne_zero.mpr hcon.2
  have : l^2 * (r s0 * W s0 * (W s0^2 - 1))^4 ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero 2 hl)
    exact pow_ne_zero 4 (mul_ne_zero (mul_ne_zero (hr0 s0 hs0) hcon.1) h1)
  exact this hc

/-- 値が {0, ±1} に入る連続関数は区間上で一定 -/
theorem const_of_discrete (p q : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo p q))
    (hv : ∀ s ∈ Ioo p q, f s = 0 ∨ f s^2 = 1) :
    ∀ s1 ∈ Ioo p q, ∀ s2 ∈ Ioo p q, f s1 = f s2 := by
  have three : ∀ s ∈ Ioo p q, f s = 0 ∨ f s = 1 ∨ f s = -1 := by
    intro s hs
    rcases hv s hs with h | h
    · exact Or.inl h
    · have : (f s - 1) * (f s + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  intro s1 h1 s2 h2
  by_contra hne
  have hsub : uIcc s1 s2 ⊆ Ioo p q := by
    intro x hx
    exact ⟨by
      rcases le_total s1 s2 with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.1, h1.1]
      · rw [uIcc_of_ge h] at hx; linarith [hx.1, h2.1], by
      rcases le_total s1 s2 with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.2, h2.2]
      · rw [uIcc_of_ge h] at hx; linarith [hx.2, h1.2]⟩
  set m := (3 * f s1 + f s2) / 4 with hm
  have hmI : m ∈ uIcc (f s1) (f s2) := by
    rcases le_total (f s1) (f s2) with h | h
    · rw [uIcc_of_le h]; constructor <;> linarith
    · rw [uIcc_of_ge h]; constructor <;> linarith
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc (hf.mono hsub) hmI
  have hcI := hsub hc
  rcases three s1 h1 with a | a | a <;> rcases three s2 h2 with b | b | b <;>
    rcases three c hcI with e | e | e <;>
    · rw [a, b] at hm hne
      first | exact hne rfl | (rw [hfc] at e; rw [hm] at e; norm_num at e)

/-- 分類:W ≡ 0 なら r² = ℓ²(BR の首)。W ≡ ±1 なら V ≡ 0 かつ ρ ≡ 0(平坦) -/
theorem static_classification (p q : ℝ) (hpq : p < q) (hl : l ≠ 0)
    (hr0 : ∀ s ∈ Ioo p q, r s ≠ 0) (hN0 : ∀ s ∈ Ioo p q, N s ≠ 0)
    (hr : ∀ s ∈ Ioo p q, HasDerivAt r (W s) s) (hW : ∀ s ∈ Ioo p q, HasDerivAt W (V s) s)
    (hN : ∀ s ∈ Ioo p q, HasDerivAt N (Np s) s)
    (ha : ∀ s ∈ Ioo p q, ham l (r s) (W s) (V s) = 0)
    (hb : ∀ s ∈ Ioo p q,
      2 * W s * (Np s / N s) / r s + (W s^2 - 1) / r s^2 = prf l (r s) (W s) (V s))
    (hd : ∀ s ∈ Ioo p q,
      HasDerivAt (fun s => N s * V s) (N s * W s * (W s^2 - 1) / r s^2) s) :
    (∀ s ∈ Ioo p q, W s = 0 ∧ V s = 0 ∧ r s ^ 2 = l ^ 2) ∨
    (∀ s ∈ Ioo p q, W s ^ 2 = 1 ∧ V s = 0 ∧ rho l (r s) (W s) (V s) = 0) := by
  have tri := static_W_trichotomy p q hl hr0 hN0 hr hW hN ha hb hd
  have hcont : ContinuousOn W (Ioo p q) := fun s hs => (hW s hs).continuousAt.continuousWithinAt
  have hconst := const_of_discrete p q W hcont tri
  have hm : (p + q) / 2 ∈ Ioo p q := ⟨by linarith, by linarith⟩
  -- W は一定なので V = W′ = 0
  have hV0 : ∀ s ∈ Ioo p q, V s = 0 := by
    intro s hs
    exact deriv_zero_on_open isOpen_Ioo (fun u hu => hconst u hu ((p + q) / 2) hm) hs (hW s hs)
  rcases tri _ hm with h0 | h1
  · left
    intro s hs
    have hWs : W s = 0 := by rw [hconst s hs _ hm, h0]
    refine ⟨hWs, hV0 s hs, ?_⟩
    have h := ha s hs
    have hr2 : r s ≠ 0 := hr0 s hs
    have e : ham l (r s) (W s) (V s) = (r s ^ 2 - l ^ 2) / r s ^ 4 := by
      simp only [ham, rho, hWs, hV0 s hs]; field_simp; ring
    rw [e, div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · exact absurd h (pow_ne_zero 4 hr2)
  · right
    intro s hs
    have hWs : W s ^ 2 = 1 := by rw [hconst s hs _ hm, h1]
    refine ⟨hWs, hV0 s hs, ?_⟩
    simp only [rho, hWs, hV0 s hs]; ring

end

end CFT.Z5
