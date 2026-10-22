# Stage 5 — 独立導出・厳密性監査

**基準アーカイブ:** `CFT_alpha_lean_2026-10-21e.zip`  
**対象:** α-IV.1、IV.2、IV.4、IV.5、IV.7、IV.8、IV.9  
**方針:** 既存の Lean 定理の名前や README の判定を証明の根拠にはせず、命題・仮定・導出・適用範囲を分けて再構成する。

## 0. 結論

Gudermann 関数とヌル特性曲線の関係（IV.7）、および平坦極限（IV.9）は、解析的には自然に厳密化できる。IV.2、IV.4、IV.5 にある既存の式も、記載した前提のもとでは数学的に妥当である。ただし、**Stage 5 全体を無条件に「完全」とするには不足が残る**。

主な理由は次の2点である。

1. IV.1 の拘束伝播の代数計算と、折れ目付き EYM 初期値問題の局所存在・一意性は別の主張である。README が挙げる Rauch–Reed (1981) は、半線形・厳密双曲系における跳びの生成・伝播が主題であり、それだけでは、ここで必要な C¹,¹ 初期データを持つ結合 EYM 系全体の適切性を確立したことにならない。
2. IV.5 の比較定理は、区間全体で \(\kappa\le r^2W^2\) が成立する正の半径の軌道についての条件付き定理である。結合 EYM 発展がこの条件を初期値から保存する証明、および最大解が実際に \(r\to0\) に到達する延長不能性の議論とは分ける必要がある。特に、`z9_reaches_zero` のように \(r=0\) も含めた閉区間全体に同じ正の下限制約を課す定式化は、\(\kappa>0\) では \(r=0\) と両立しない。

ここでの SymPy 検算は式の整合性検査であり、PDE の存在・一意性定理でも Lean のビルドでもない。

---

## 1. α-IV.1 — 拘束伝播と適切性を分ける

### 1.1 既存の代数的な拘束伝播式

README と `AlphaIV_Propagation.lean` の記法で、ハミルトン拘束を \(H\)、運動量拘束を \(M\)、\(a=DR/R\)、\(K=K_x+2K_T\)、\(b=K_x+K_T\) と書く。発展方程式を仮定すると、次の斉次系が得られる。

\[
\partial_t H=2KH-4aM-2DM,\qquad
\partial_t M=2bM-\tfrac12 DH.
\]

この2式が成り立つ解に対して \(\mathcal E=H^2+4M^2\) を作ると、積の微分法則から

\[
\partial_t\mathcal E
=4KH^2-8aHM+16bM^2-4D(HM).
\]

ここで \(D=A^{-1}\partial_x\) なので、\(A>0\) と置けば

\[
\partial_t(A\mathcal E)+4\partial_x(HM)
=A_t\mathcal E+A\bigl(4KH^2-8aHM+16bM^2\bigr).
\]

係数 \(A,A^{-1},A_t,K,a,b\) が局所的に有界で、境界流束を制御できる区間では、積分エネルギーに対する Grönwall 評価が得られる。初期時刻で \(H=M=0\) なら、線形斉次拘束系の一意性によって後の時刻でも \(H=M=0\) となる。

### 1.2 何がまだ別途必要か

上の計算は、発展解が存在し、その正則性の範囲で微分・積分を行えることを前提にしている。従って、次の3項目を区別する。

- 発展方程式から拘束伝播系を代数的に導くこと。
- その線形斉次拘束系のゼロ解の一意性をエネルギー評価で示すこと。
- 折れ目を持つ初期データに対し、球対称 EYM の弱解が存在し、その解が必要な正則性を持つこと。

Lean の `hamiltonian_propagation` と `momentum_propagation` は1番目の部分を形式化する。しかし、それ自体で3番目を示したことにはならない。

### 1.3 外部定理について

README の Rauch–Reed (1981) の引用は、跳びの生成・伝播を扱う論文としては適切な文献だが、タイトルおよび要旨からは、C¹,¹ の折れ目付き EYM 初期値問題全体に対する存在・一意性を直接与える定理だとは確認できない。適切性を閉じるには、球対称二重ヌル還元の方程式が属する正確なクラス、データの関数空間、接合点・軸 \(r=0\) の扱いを固定し、その仮定に合致する局所解定理を引用する必要がある。

たとえば Einstein–Yang–Mills–Higgs 系の特性初期値問題を加重 Sobolev 空間で扱う研究は存在するが、データの正則性やゲージ条件が今回の初期データに合うかは別途照合が必要である（Choquet-Bruhat, Dossa, Tadmon, 2010, DOI: `10.1016/j.crma.2009.11.014`; また 2010 年の Goursat 問題の結果）。

**判定:** 拘束伝播の形式的導出は成立。Stage 5 の「適切性」全体を完全とするには、外部定理の仮定照合が未了。

---

## 2. α-IV.2 — ヌル面上の弱い不連続

二重ヌル座標で、両側の場が

\[
W_{uv}=F(W,r,\sigma),\qquad
F(W,r,\sigma)=\frac{e^{2\sigma}W(1-W^2)}{2r^2}
\]

を満たすとする。波面上で \(W,r,\sigma\) のトレースが共通なら \([F]=0\) である。したがって、各側で必要な片側微分が存在する範囲で

\[
\partial_v[W_u]=[W_{uv}]=[F]=0,
\qquad [W_u](v)=\text{constant}.
\]

さらに拘束

\[
r_{uu}-2\sigma_u r_u+\frac{2W_u^2}{r}=0
\]

の両側で \(\sigma_u\) と \(r_u\) のトレースが共通なら、引き算によって

\[
[r_{uu}]=-rac2r[W_u^2].
\]

ここで大事な条件は、単に \([r_u]=0\) でなく、積 \(\sigma_u r_u\) の跳びがゼロであることだ。例えば \([\sigma_u]=0\) と \([r_u]=0\) は十分条件となる。

これは、適切な片側正則性と共通トレースを仮定したときの正しい輸送則である。弱解の存在および特性面を横切る正則性を得るには、IV.1 で指摘した PDE の適切性の入力が別途必要になる。

**判定:** 条件付き数学命題として成立。適用先の弱解を構成する定理とは区別する。

---

## 3. α-IV.4 — 中心 ODE とエネルギー恒等式

中心の ODE を

\[
\ddot r=-\frac{\dot r^2+1-\ell^2/r^2}{2r}-\frac{W^2}{r},\qquad r\ne0
\]

とし、

\[
E=r(1+\dot r^2)+\frac{\ell^2}{r}
\]

を定義する。積の微分と ODE の代入だけで

\[
\begin{aligned}
\dot E
&=\dot r(1+\dot r^2)+2r\dot r\ddot r
   -\frac{\ell^2\dot r}{r^2}\\
&=-2W^2\dot r.
\end{aligned}
\]

従って \(\dot r\le0\) の崩壊区間では \(\dot E\ge0\) である。

注意：これは \(E\) の微分恒等式であって、\(E\) を Misner–Sharp 質量そのものと同一視してはいけない。また ODE は既に α-IV.3 から与えられたものとしているので、4次元の作用から ODE を導く作業とは別である。

**判定:** 前提のもとで完全。

---

## 4. α-IV.5 — 比較崩壊定理の正確な適用範囲

### 4.1 条件付きで成立する比較定理

\(r(\tau)>0\)、転回点 \(r(\tau_1)=r_1>0\)、\(\dot r(\tau_1)=0\) とし、解が正のまま存在する区間の全域で

\[
\ell^2\le 2\kappa,
\qquad \kappa\le r^2W^2
\]

を仮定する。すると

\[
\begin{aligned}
\ddot r
&=-\frac{\dot r^2}{2r}-\frac1{2r}
  +\frac{\ell^2-2r^2W^2}{2r^3}\\
&\le -\frac1{2r}<0.
\end{aligned}
\]

初期加速度は負であり、比較定理で \(\dot r\le0\)、以後の \(r\) の単調減少が導ける。エネルギー不等式から

\[
r\dot r^2\ge r_1-r.
\]

\[
\Psi(x)=r_1\arccos\sqrt{x/r_1}+\sqrt{x(r_1-x)}
\]

と置くと、\(0<x<r_1\) で

\[
\Psi'(x)=-\frac{\sqrt{x}}{\sqrt{r_1-x}}.
\]

よって

\[
\frac{d}{d\tau}\bigl(\Psi(r(\tau))-\tau\bigr)
=-\frac{\sqrt r}{\sqrt{r_1-r}}\dot r-1\ge0.
\]

一方 \(0<x\le r_1\) なら \(\Psi(x)<\pi r_1/2\)。従って、半径が正である軌道が条件を満たしたまま存在できる区間長は

\[
\boxed{\tau_2-\tau_1<\frac{\pi r_1}{2}}
\]

である。これは現行 `z9_collapse` が主張する条件付きの寿命上界として正しい。

### 4.2 これは一般の EYM 特異点形成証明ではない

- \(\kappa\le r^2W^2\) を区間全体で仮定している。\(W\) はこの ODE 定理では外部関数として扱われ、YＭ 方程式から同条件が伝播することは示していない。
- \(W=0\) の首ではこの仮定が正の \(\kappa\) に対して成立しない。従ってこの定理を首の崩壊に適用することはできない。
- 正の解がその時間まで延長できないことと、最大 EYM 解の延長不能性が必ず \(r\to0\) で起こることは違う。後者には上からの制御・延長判定などが必要である。
- `z9_reaches_zero` 型の結論を述べるなら、正の半径の最大存在区間の端点を使い、下限制約を \(r=0\) の端点そのものには課さない定式化が必要である。\(\kappa>0\) のとき \(r=0\) と \(\kappa\le r^2W^2\) は両立しない。

**判定:** 条件付き比較定理は成立。結合 EYM 方程式の不変量制御と真の特異点形成は未閉鎖。

---

## 5. α-IV.7 — Gudermann 関数とヌル特性曲線を厳密に同一視する

\[
\operatorname{gd}(x)=\arctan(\sinh x),\qquad
z_\ell(t)=\ell\,\operatorname{arsinh}\!\left(\tan\frac{t}{\ell}\right)
\]

と定める。既存の微分公式は定義から直接得られる。

\[
\operatorname{gd}'(x)=\operatorname{sech}x,
\qquad
z_\ell'(t)=\sec(t/\ell)
\]

後者は \(-\pi\ell/2<t<\pi\ell/2\) で成立する。この範囲は首の背景 \(ds^2=-dt^2+\cos^2(t/\ell)dz^2\) の正規な一周期内の座標パッチである。単に \(\cos(t/\ell)>0\) とするだけでは、周期性のため逆関数の主値枝を固定できない。

### 5.1 逆写像の正確な公式

任意の \(z\in\mathbb R\) について、

\[
\begin{aligned}
z_\ell\bigl(\ell\operatorname{gd}(z/\ell)\bigr)
&=\ell\operatorname{arsinh}\bigl(\tan(\operatorname{gd}(z/\ell))\bigr)\\
&=\ell\operatorname{arsinh}(\sinh(z/\ell))=z.
\end{aligned}
\]

ここでは \(\tan(\arctan y)=y\)、\(\operatorname{arsinh}(\sinh x)=x\) を使った。

逆方向では、\(-\pi\ell/2<t<\pi\ell/2\) のとき \(t/\ell\in(-\pi/2,\pi/2)\) であるから、主値の枝で \(\arctan(\tan(t/\ell))=t/\ell\)。従って

\[
\boxed{\ell\operatorname{gd}\bigl(z_\ell(t)/\ell\bigr)=t}.
\]

よって \(z_\ell:\,(-\pi\ell/2,\pi\ell/2)\to\mathbb R\) と \(t_\ell(z)=\ell\operatorname{gd}(z/\ell)\) は互いに逆な全単射である。

### 5.2 ヌル曲線との接続

\(ds^2=-dt^2+\cos^2(t/\ell)dz^2\) のヌル曲線は

\[
\frac{dz}{dt}=\pm\sec(t/\ell).
\]

積分し初期点を固定すると \(z(t)=z_0\pm z_\ell(t)\) となる。長さ \(L\ge0\) の首の両端 \(z=\pm L/2\) から出る対称な波面については、出会い条件 \(2z_\ell(t_*)=L\) から

\[
\boxed{t_*=\ell\operatorname{gd}\left(\frac{L}{2\ell}\right)<\frac{\pi\ell}{2}}
\]

を得る。この式は単なる上界でなく、実際の特性曲線の交点条件を解いた式である。

### 5.3 Mercator 変換との正確な対応と限界

球面の緯度 \(\varphi\in(-\pi/2,\pi/2)\) と Mercator 座標 \(y\in\mathbb R\) の間に

\[
y=\operatorname{arsinh}(\tan\varphi),\qquad \varphi=\operatorname{gd}(y)
\]

を置くと、\(d\varphi/dy=\operatorname{sech}y\)、\(\cos\varphi=\operatorname{sech}y\) なので

\[
d\varphi^2+\cos^2\varphi\,d\lambda^2
=\operatorname{sech}^2y\,(dy^2+d\lambda^2).
\]

したがって Mercator の座標関係と首のヌル特性曲線には、同じ互いに逆な Gudermann 写像が現れる。ただし、**座標関係が一致することは、球面幾何と首の時空幾何が動力学的に同値という意味ではない**。後者には方程式を保存する写像が別途必要である。

**判定:** Z10 の座標・特性曲線の数学的対応は、上記の枝条件を明記すれば閉じられる。動力学的同値性は主張しない。

---

## 6. α-IV.8 — 波面の出会い時刻とキャップ寿命

### 6.1 波面の出会い

\(L\ge0,\ell>0\) で、対称な2本のヌル波面を

\[
z_L(t)=-\frac L2+z_\ell(t),\qquad
z_R(t)=\frac L2-z_\ell(t)
\]

と置く。これはそれぞれ \(dz/dt=+\sec(t/\ell)\)、\(dz/dt=-\sec(t/\ell)\) を満たす。\(z_L(t_*)=z_R(t_*)\) は \(2z_\ell(t_*)=L\) と同値なので

\[
t_*=\ell\operatorname{gd}(L/(2\ell)).
\]

\(\operatorname{gd}(x)=\arctan(\sinh x)\in(-\pi/2,\pi/2)\) と \(\ell>0\) から \(t_*<\pi\ell/2\)。

### 6.2 到着時計

\[
\tau_\ell(z)=\int_0^z\operatorname{sech}(t/\ell)\,dt
\]

の被積分関数は連続であり、原始関数は \(\ell\operatorname{gd}(z/\ell)\)。従って

\[
\boxed{\tau_\ell(z)=\ell\operatorname{gd}(z/\ell)}.
\]

\(\ell>0\) なら、任意の有限な \(z\) に対して \(\tau_\ell(z)<\pi\ell/2\)。物理的な出会い時刻として読む場合は \(L\ge0\) を明記する。

### 6.3 キャップ寿命

キャップのパラメータ表示を \(a(\eta)=\ell\cos\eta\)、\(t(\eta)=\ell\sin\eta\)、\(0\le\eta\le\pi/2\) とする。すると \(a(\pi/2)=0\)、\(t(\pi/2)=\ell\)。固有時間をこの時間座標 \(t\) で測るモデルでは、中心の固有時間は \(\ell\) である。これをパラメータ \(\eta\) 自体の長さと取り違えない。

**判定:** 積分時計と対称な波面の出会いは、幾何学的な曲線を明示すれば閉じられる。旧 `fronts_meet_before` は上界だけだったので、上記はより強い等式を与える。

---

## 7. α-IV.9 — 平坦極限の厳密化

### 7.1 点ごとの極限

\[
\tau_\ell(z)=\ell\operatorname{gd}(z/\ell)
\]

とする。\(\operatorname{gd}(0)=0\)、\(\operatorname{gd}'(0)=1\) より

\[
\lim_{x\to0}\frac{\operatorname{gd}(x)}x=1.
\]

固定した \(z\ne0\) について

\[
\tau_\ell(z)=z\,\frac{\operatorname{gd}(z/\ell)}{z/\ell},\qquad z/\ell\to0,
\]

なので

\[
\boxed{\lim_{\ell\to\infty}\tau_\ell(z)=z}.
\]

\(z=0\) では \(\tau_\ell(0)=0\) だから同じ結論である。

### 7.2 コンパクト集合上一様な極限

\(h(x)=\operatorname{gd}(x)/x\)（\(x\ne0\)）、\(h(0)=1\) と定めると、導関数の極限から \(h\) は0で連続である。任意の \(M>0\) に対し

\[
\sup_{|z|\le M}|\tau_\ell(z)-z|
\le M\sup_{|x|\le M/\ell}|h(x)-1|\longrightarrow0.
\]

従って到着時計は有限長の任意のコンパクト領域上で一様に平坦時計へ収束する。さらに

\[
\partial_z\tau_\ell(z)=\operatorname{sech}(z/\ell)\to1
\]

もコンパクト集合上一様である。

### 7.3 計量とヌル前線の極限

\[
g_\ell=-dt^2+\cos^2(t/\ell)dz^2
\]

について、固定した時間区間 \(|t|\le T\) では \(\cos^2(t/\ell)\to1\) が一様に成立する。従って計量係数はコンパクト集合上で Minkowski 計量へ収束する。

また \(z_\ell(t)=\ell\operatorname{arsinh}(\tan(t/\ell))\) とし、\(p(x)=\operatorname{arsinh}(\tan x)/x\)、\(p(0)=1\) とすると

\[
\sup_{|t|\le T}|z_\ell(t)-t|
\le T\sup_{|x|\le T/\ell}|p(x)-1|\to0.
\]

従ってヌル前線もコンパクトな時間領域で平坦時空の \(z=\pm t\) へ一様収束する。

### 7.4 先頭補正項

定義からの Taylor 展開は

\[
\operatorname{gd}(x)=x-\frac{x^3}{6}+\frac{x^5}{24}+O(x^7),
\]

\[
\operatorname{arsinh}(\tan x)=x+\frac{x^3}{6}+\frac{x^5}{24}+O(x^7).
\]

よって固定した \(z,t\) に対し

\[
\tau_\ell(z)=z-\frac{z^3}{6\ell^2}+\frac{z^5}{24\ell^4}+O(\ell^{-6}),
\]

\[
z_\ell(t)=t+\frac{t^3}{6\ell^2}+\frac{t^5}{24\ell^4}+O(\ell^{-6}),
\]

\[
\cos^2(t/\ell)=1-\frac{t^2}{\ell^2}+\frac{t^4}{3\ell^4}+O(\ell^{-6}).
\]

これは導関数が0で1になることだけではなく、時計・波面・計量係数のそれぞれに対する実際の極限と先頭誤差を示す。

**判定:** IV.9 の「平坦極限」は点ごとだけでなくコンパクト上一様に閉じられる。定義からの漸近係数も独立に照合した。

---

## 8. Stage 5 の監査後ステータス

| 項目 | 独立監査の結論 | 正確な閉鎖範囲 |
|---|---|---|
| IV.1 | **部分／外部定理の照合が必要** | 拘束伝播の代数式はある。弱解の存在・一意性と初期データの関数空間は別途必要 |
| IV.2 | **条件付きで成立** | 共通トレースと片側微分の存在のもとで跳び輸送が成立 |
| IV.4 | **完全（条件付き ODE 恒等式）** | ODE、\(r\ne0\) のもとでエネルギー微分式が成立 |
| IV.5 | **条件付き比較定理は完全、EYM 崩壊全体は未閉鎖** | \(\kappa\le r^2W^2\) が発展全体で成立する正の軌道の寿命上界。条件の伝播と最大解の延長不能性は別問題 |
| IV.7 | **解析的には閉鎖可能** | Gudermann 写像の逆写像、ヌル特性曲線、Mercator 座標の対応。主値枝を明記 |
| IV.8 | **幾何学的に閉鎖可能** | 波面の出会い時刻の等式、積分時計、キャップの時間端点 |
| IV.9 | **解析的には閉鎖可能** | 固定点の極限、コンパクト上一様極限、計量・波面の平坦極限と先頭補正 |

従って、Stage 5 の数学的な幾何部分（特に IV.7 と IV.9）は閉じられる。ただし、台帳の閉鎖条件でいう「結合 EYM 初期値問題の適切性」「崩壊条件の場の方程式からの伝播」までを含む Stage 5 全体については、**無条件の完全判定にはしない**のが正確である。

## 9. 再現可能な検算

`stage5_independent_checks.py` は、定義からの微分恒等式、中心エネルギー式、跳びの代数、Taylor 係数を SymPy で検算する。ログは `stage5_independent_checks_results.txt`。検算数は11件であり、これは形式証明の件数ではない。特に枝条件、PDE 適切性、弱解の延長判定は記号計算で証明したものではない。

**Lean 状態:** この実行環境では `lean` / `lake` が見つからなかったため、ソースを変更した Lean のコンパイルや新定理のビルドは実施していない。今回の成果は、独立した解析導出・範囲監査・記号検算であり、未コンパイルのコードを「ビルド済み」とは報告しない。
