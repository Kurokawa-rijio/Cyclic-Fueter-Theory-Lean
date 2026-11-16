# FILE GUIDE — v0.6.0 → v1.6.1 ファイル名対応表

v1.6.1 では、初めて見る人がファイル名から内容を判断できるよう、全モジュールを内容を表す名前＋テーマ別フォルダに再編した。
定理名（名前空間）は変更していないので、台帳・別名・監査の参照はそのまま有効。
掃除内容: `cyclic_momentum`（トートロジー）削除、RealLine finals 7件に `@[deprecated]`、α-XV.11 を 完→完（外）、
ルートの `0.3.0` ダンプを除外、生成スクリプトの絶対パスを相対化。

| 新しいパス | 内容 | 旧パス (v0.6.0) |
|---|---|---|
| `CFT/Cartan/AlignedNoGo.lean` | 整列型のC2解は存在しない（Z4-E） | `CFT/Cartan/Aligned.lean` |
| `CFT/Cartan/BjVanishesOnC2.lean` | α-II.5のまとめ：任意のC2枠で Bj = 0 | `CFT/Cartan/SecondStage.lean` |
| `CFT/Cartan/BochnerKappaSign.lean` | Bochner恒等式の各点での帰結 κ(p) ≤ 0（α-II.4） | `CFT/Cartan/BochnerSign.lean` |
| `CFT/Cartan/C2FirstStage.lean` | C2クラス（Codazzi）の1段目：接続係数の一般解 | `CFT/Cartan/C2.lean` |
| `CFT/Cartan/CoefSplitBj.lean` | α-II.5：Bj 多項式の係数分割（生成ファイル） | `CFT/Cartan/SSCoefBj.lean` |
| `CFT/Cartan/CoefSplitK0.lean` | α-II.5：K0 の係数分割（生成ファイル） | `CFT/Cartan/SSCoefK0.lean` |
| `CFT/Cartan/CoefSplitK1.lean` | α-II.5：K1 の係数分割（生成ファイル） | `CFT/Cartan/SSCoefK1.lean` |
| `CFT/Cartan/CoefSplitK2.lean` | α-II.5：K2 の係数分割（生成ファイル） | `CFT/Cartan/SSCoefK2.lean` |
| `CFT/Cartan/CoefSplitK3.lean` | α-II.5：K3 の係数分割（生成ファイル） | `CFT/Cartan/SSCoefK3.lean` |
| `CFT/Cartan/CoefSplitRow3.lean` | α-II.5：row3 の係数分割（生成ファイル） | `CFT/Cartan/SSCoefR3.lean` |
| `CFT/Cartan/CoefSplitRow6.lean` | α-II.5：row6 の係数分割（生成ファイル） | `CFT/Cartan/SSCoefR6.lean` |
| `CFT/Cartan/FirstStageSolution.lean` | α-II.5：1段目の解（e₀v, e₁v を e₂v で表す）と単元の補題 | `CFT/Cartan/SSFirst.lean` |
| `CFT/Cartan/MovingFrame.lean` | Cartan動標構の代数的な形式化（接続・曲率の公理） | `CFT/Cartan/Frame.lean` |
| `CFT/Cartan/SecondStageCompatibility.lean` | α-II.5：2段目の両立条件 rank C ≤ 2 の証明（Z4-3） | `CFT/Cartan/SSJet.lean` |
| `CFT/Cartan/SecondStageRank12.lean` | α-II.5：2段目の係数行列の階数12（Z4-3） | `CFT/Cartan/SSRank.lean` |
| `CFT/Cartan/TorsionLeftKernel.lean` | α-II.5：捩れの行だけの左核 K0〜K3 の恒等式 | `CFT/Cartan/SSK.lean` |
| `CFT/Cartan/TorsionRow3.lean` | α-II.5：2段目の捩れの式 row3 | `CFT/Cartan/SSRows1a.lean` |
| `CFT/Cartan/TorsionRow6.lean` | α-II.5：2段目の捩れの式 row6 | `CFT/Cartan/SSRows2a.lean` |
| `CFT/Cartan/TorsionRows0To2.lean` | α-II.5：2段目の捩れの式 row0〜row2 | `CFT/Cartan/SSRows0.lean` |
| `CFT/Cartan/TorsionRows4To5.lean` | α-II.5：2段目の捩れの式 row4・row5 | `CFT/Cartan/SSRows1b.lean` |
| `CFT/Cartan/TorsionRows7To8.lean` | α-II.5：2段目の捩れの式 row7・row8 | `CFT/Cartan/SSRows2b.lean` |
| `CFT/Cartan/TorsionRows9To11.lean` | α-II.5：2段目の捩れの式 row9〜row11 | `CFT/Cartan/SSRows3.lean` |
| `CFT/Foundations/Basic.lean` | 命題群αの共通importのみ（基礎ファイル、名前は現行維持） | `CFT/Basic.lean` |
| `CFT/Foundations/BerryWignerConnections.lean` | Berry接続とWigner接続はゲージ同値でない:曲率の公式 | `CFT/AlphaI_AW.lean` |
| `CFT/Foundations/CliffordDiracInputs.lean` | Z28-d の入力をClifford代数とKillingスピノルから定理化 | `CFT/AlphaVII_Z28Input.lean` |
| `CFT/Foundations/CyclicFamilyOperators.lean` | 係数行列Cを巡回作用素族 D_m から導き、核を作用素の言葉で読む | `CFT/AlphaI_CFamily.lean` |
| `CFT/Foundations/CyclicMatrixKernels.lean` | 巡回Fueter係数行列Cの階数3と左右の核 γ(−k)ℍ、ℍγ(i) | `CFT/AlphaI_C.lean` |
| `CFT/Foundations/FactorizationClosure.lean` | 巡回族をLaplacianの因数分解から導く:ℤ₄とV₄の分類(段階0・1の閉鎖) | `CFT/AlphaS1_Closure.lean` |
| `CFT/Foundations/FueterOperatorSquares.lean` | Fueter作用素の規約と二乗の公式:D̄_R D_R=Δ₄、双四元数で □ | `CFT/AlphaI_Operators.lean` |
| `CFT/Foundations/LichnerowiczIndexZero.lean` | Lichnerowicz公式のClifford代数と奇数次元の指数0 | `CFT/AlphaVII_Lichnerowicz.lean` |
| `CFT/Foundations/LorentzPolarDecomposition.lean` | ローレンツ群 SL(2,ℂ) の極分解:回転×ブーストの一意性 | `CFT/AlphaPillar_Polar.lean` |
| `CFT/Foundations/PerturbationGeneralLevels.lean` | 非縮退多準位の二次摂動公式（一般形） | `CFT/AlphaVII_RSGeneral.lean` |
| `CFT/Foundations/QuaternionBasics.lean` | α-Iの代数的起点:四元数の規約、二つの実形、射影、Hopf写像 | `CFT/AlphaI.lean` |
| `CFT/Foundations/QuaternionCommutantSO4.lean` | so(4) における SU(2)_L の可換子 = R(Im ℍ)（障害N1の代数） | `CFT/AlphaVII_Commutant.lean` |
| `CFT/Foundations/RayleighSchrodingerPerturbation.lean` | 二次の摂動公式（Rayleigh–Schrödinger）とZ28-dへの適用 | `CFT/AlphaVII_Perturb.lean` |
| `CFT/Foundations/RealFormsQuantumMetric.lean` | 完全化2：四元数の実形とSU(2)、Maurer–Cartan形式と量子球面の量子計量 | `CFT/AlphaCompleteB.lean` |
| `CFT/Foundations/SphereHyperboloidDuality.lean` | 量子球面と質量殻H³は一つの複素構造の二つの顔(Wick回転で接続) | `CFT/AlphaRoot_Duality.lean` |
| `CFT/Geometry/DiagonalClassNonexistence.lean` | 対角計量の類ではRicci固有値の相異なる解はない | `CFT/AlphaII_Diagonal.lean` |
| `CFT/Geometry/EllipsoidConformalEigenvalue.lean` | 楕円体族と共形族でS⁹の規格化最低固有値の2次係数が一致すること | `CFT/AlphaFix_Z28.lean` |
| `CFT/Geometry/GaussMapEmbedding.lean` | 埋め込みと誘導計量から作るGauss写像とその一意性（Z19） | `CFT/AlphaV_GaussMap.lean` |
| `CFT/Geometry/GaussMapMassAngle.lean` | Gauss写像から sin²χ = 2Gm/r を導く（Z19） | `CFT/AlphaV_Gauss.lean` |
| `CFT/Geometry/HyperbolicBPSMonopole.lean` | 完全化3：H³上のBerry接続とHiggs場がBPS方程式を満たすことの検算 | `CFT/AlphaCompleteC.lean` |
| `CFT/Geometry/HyperbolicBPSMonopoleClosed.lean` | BPS方程式の成分恒等式（閉じた形）を複素数上で検算（CompleteCの続き） | `CFT/AlphaCompleteC2.lean` |
| `CFT/Geometry/HyperbolicCurvature.lean` | BPS方程式の舞台の計量 h の断面曲率がすべて −1(H³模型) | `CFT/AlphaI_H3.lean` |
| `CFT/Geometry/OpenHemisphereBijection.lean` | Q(p)=(m/E, p/E) は ℝ³ から開いた上半球 S³₊ への全単射 | `CFT/AlphaI_QBij.lean` |
| `CFT/Geometry/QuantumSphereHyperboloid.lean` | 運動量空間の量子球面Qと質量殻双曲面Hの逆数関係とGudermann関数 | `CFT/AlphaB_QH.lean` |
| `CFT/Geometry/S3ParallelizingTorsion.lean` | S³ = SU(2) の平行化の捩れ・Ricci恒等式と流束量子化 | `CFT/AlphaVIII_WZW.lean` |
| `CFT/Geometry/StrictWindowFlatLimit.lean` | α-II.4の厳密な窓（0 < Rℓ² < 2）とα-III.6の平坦極限 | `CFT/AlphaS3_Closure.lean` |
| `CFT/Geometry/TangentBundleWinding.lean` | S²の接束の遷移関数の回転数 −2（c₁ = χ の同一視） | `CFT/AlphaVII_Tangent.lean` |
| `CFT/Junction/CapNeckGluing.lean` | 帽子と首のC¹貼り合わせと拘束から a=ℓ、首は平坦へ開けない | `CFT/AlphaIII_Glue.lean` |
| `CFT/Junction/CodazziMomentumConstraint.lean` | 球対称切り口のCodazziの式と運動量拘束 | `CFT/AlphaIII_Codazzi.lean` |
| `CFT/Junction/DistributionalShellEquations.lean` | 分布としての接合方程式とδ係数 κ(x₀)[g] の導出 | `CFT/AlphaS4_Distrib.lean` |
| `CFT/Junction/DumbbellJunctionNecessity.lean` | 赤道でのIsrael条件、Penrose型定理からダンベルの必然性 | `CFT/AlphaIII.lean` |
| `CFT/Junction/IsraelGeneral.lean` | 一般の非ヌル超曲面に対するIsrael条件(Lanczos方程式) | `CFT/AlphaIII_Israel.lean` |
| `CFT/Junction/IsraelJunctionFromCurvature.lean` | 曲率とYM応力からIsrael接合条件を閉じる（α-III.1/2/9） | `CFT/AlphaS4_Junction.lean` |
| （v1.6.1 で削除） | RealLine版の最終接合定理（空虚・実関数版に置換済みのため削除） | `CFT/AlphaS4_Final.lean` |
| `CFT/Junction/JunctionUniqueness.lean` | 定理A:帽子と首のつなぎ方の一意性(場所は赤道だけ、C²不可) | `CFT/AlphaJunction_Unique.lean` |
| `CFT/Junction/NullDiscontinuityStress.lean` | ヌルな弱不連続 [F]=k∧α での応力の跳び k^μ[T_μν]=0 | `CFT/AlphaIII_P1.lean` |
| `CFT/Junction/NullShellJunction.lean` | ヌルな殻の接合(球対称Barrabès–Israel)を分布のEinstein方程式から導出 | `CFT/AlphaIII_Null.lean` |
| `CFT/Junction/RealFunctionClosings.lean` | 実関数版の残り:Misner–Sharp全エネルギー0、共形の跳びの二値性 | `CFT/AlphaReal_Rest.lean` |
| `CFT/Junction/RealFunctionJunction.lean` | 接合の最終定理を実関数と弱い形で証明し直す(RealLine不使用) | `CFT/AlphaReal_Junction.lean` |
| `CFT/Junction/RootJunctionJump.lean` | 根幹の見直し1:接合で r″・曲率・応力が跳ぶことの診断 | `CFT/AlphaRoot_Junction.lean` |
| `CFT/Junction/SphericalJunction.lean` | 球対称接合の統一:殻の表面密度 σ=−[r′]/(4πGr₀)、殻なし⇔[r′]=0 | `CFT/AlphaIII_Junction.lean` |
| `CFT/Quantum/AffineQuantizationInnerProduct.lean` | reality条件からaffine群のユニタリ表現で物理的内積を決める | `CFT/AlphaVI_Affine.lean` |
| `CFT/Quantum/BlackHoleThermodynamics.lean` | Hawking温度、第一法則とSmarrの式、Euclid作用 | `CFT/AlphaIX_Thermo.lean` |
| `CFT/Quantum/DiracEndpointAsymptotics.lean` | 動径Dirac方程式の端点漸近形 s^{∓κ} の摂動評価（Z29） | `CFT/AlphaV_Endpoint.lean` |
| `CFT/Quantum/FRWQuantumStress.lean` | 閉じたFRW上の量子応力と半古典的反作用（曲率から計算） | `CFT/AlphaV_FRW.lean` |
| `CFT/Quantum/FermionDiracSpectrum.lean` | 帽子のDirac作用素のスペクトルとゼロモード（スファレロン）、2次元縮約Dirac場 | `CFT/AlphaFermion.lean` |
| `CFT/Quantum/FoldyWouthuysenExact.lean` | 自由Dirac作用素のFoldy–Wouthuysen変換（厳密形） | `CFT/AlphaV_FW.lean` |
| `CFT/Quantum/FoldyWouthuysenExpansion.lean` | FW展開の各項と 1/m の次数（Pauli方程式へ） | `CFT/AlphaV_FWOrder.lean` |
| `CFT/Quantum/FoldyWouthuysenSecond.lean` | Foldy–Wouthuysen変換の2回目：1/m²まで偶部分は不変、運動量と場の交換子 | `CFT/AlphaFix_FW.lean` |
| `CFT/Quantum/HeatKernelA4Derivation.lean` | Gilkeyの公式による熱核係数 a₄ の閉じた導出（Z31） | `CFT/AlphaV_A4.lean` |
| `CFT/Quantum/HemisphereDiracHeatKernel.lean` | 量子半球の共形対応・S³ Dirac準位・熱核係数a₄（α-V集成） | `CFT/AlphaV.lean` |
| `CFT/Quantum/JTFromReduction.lean` | 球対称縮約からJT重力へ:首のエントロピーとSchwarzian | `CFT/AlphaIX_JT.lean` |
| `CFT/Quantum/KMSFluctuationDissipation.lean` | 有限系のKMS条件、揺動散逸の関係、Planck積分 | `CFT/AlphaIX_Stat.lean` |
| `CFT/Quantum/KantowskiSachsWDW.lean` | KS型ミニ超空間のWDW方程式:Hamilton–Jacobi解と首の折り目 | `CFT/AlphaKS_WDW.lean` |
| `CFT/Quantum/MagneticChargeThermo.lean` | 磁荷のEuclid作用を実際に積分して得るI＝β(M＋ΦQ)/2とエントロピーA/4、相比較 | `CFT/AlphaFix_Thermo.lean` |
| `CFT/Quantum/MinisuperspaceBoundaryTerms.lean` | 縮約作用の補強:GHY境界項、規格化、超計量とLB作用素 | `CFT/AlphaIV_Reduction.lean` |
| `CFT/Quantum/MinisuperspaceNeckAction.lean` | 首の縮約作用を4次元作用から導き、Legendre変換でHamiltonianへ | `CFT/AlphaIV_Minisuperspace.lean` |
| `CFT/Quantum/MonopoleZeroModes.lean` | 単位S²上の単極子ゼロモードの厳密解と数え上げ（全部で2q個） | `CFT/AlphaCompleteD.lean` |
| `CFT/Quantum/NeckQuantumStress.lean` | 首 AdS₂×S² 上の共形場の量子応力と反作用（α-V.7-N） | `CFT/AlphaV_NeckQuantum.lean` |
| `CFT/Quantum/NeckWDWReducedPhase.lean` | 首のWDW厳密解と縮約位相空間のPoisson括弧（α-VI） | `CFT/AlphaVI.lean` |
| `CFT/Quantum/OmegaQuantumGeometry.lean` | Ωの量子幾何学(α-XV)と帽子・首の重ね合わせの否定 | `CFT/AlphaOmega_Quantum.lean` |
| `CFT/Quantum/PhysicalBranchAffine.lean` | 物理的な枝・affine量子化・停留位相の条件の補強 | `CFT/AlphaVI_Physical2.lean` |
| `CFT/Quantum/PhysicalInnerProductStates.lean` | 縮約位相空間の物理的内積と K̂ の固有状態 Ψ_C | `CFT/AlphaVI_Physical.lean` |
| `CFT/Quantum/QuantumSphericalWDW.lean` | 球対称WDW方程式:拘束の質量形(Kuchař)、帽子ではFriedmann拘束 | `CFT/AlphaQuantumSpherical.lean` |
| `CFT/Quantum/QuantumStressBackreaction.lean` | 量子場の応力と重力の反作用（閉じた輻射FRW・ESU） | `CFT/AlphaV_Backreaction.lean` |
| `CFT/Quantum/S3DiracReduction.lean` | S³ Dirac作用素の準位 3/2 − 3λ、3/2 + λ への還元 | `CFT/AlphaV_S3Dirac.lean` |
| `CFT/Quantum/S9DiracPerturbation.lean` | S⁹ の Dirac 作用素の二次摂動 λ₂ の導出（Z28-d） | `CFT/AlphaVII_Z28d.lean` |
| `CFT/Quantum/SchwarzianDensityEnsembles.lean` | Schwarzianの厳密な状態密度sinh(2π√(2CE))と微視・正準集団の比較、反作用の保存 | `CFT/AlphaFix_Dyn.lean` |
| `CFT/Quantum/SechFourthIntegral.lean` | 積分 ∫ 2 sech⁴x dx = 8/3（インスタントン作用の 8/3） | `CFT/AlphaVI_Sech.lean` |
| `CFT/Quantum/SecondLawPhaseTransitions.lean` | 焦点化定理、エルゴード性、Landau相転移とHawking–Page型 | `CFT/AlphaIX_Second.lean` |
| `CFT/Quantum/StationaryPhaseConditions.lean` | 波束への停留位相の定理の適用条件（H1〜H3） | `CFT/AlphaVI_Semiclassical.lean` |
| `CFT/Quantum/TraceAnomalyFRWDensity.lean` | トレースアノマリーと保存則からFRW量子応力の密度を決める | `CFT/AlphaV_Anomaly.lean` |
| `CFT/Quantum/WDWExactWKB.lean` | 首のWDW方程式:WKB級数がħ¹で終わり厳密解になる | `CFT/AlphaIV_WKB.lean` |
| `CFT/Quantum/WDWTwoBranches.lean` | WDWの二つの枝、Laplace–Beltrami順序、解の重ね合わせ | `CFT/AlphaIV_WKB2.lean` |
| `CFT/Quantum/WignerRotationHolonomy.lean` | H³と量子半球の共形対応（Gudermann）とWigner回転 | `CFT/AlphaV_Wigner.lean` |
| `CFT/Quantum/ZeroModeL2Condition.lean` | 単極子ゼロモードが L² になる条件 m + q > −1/2 等 | `CFT/ZeroModeL2.lean` |
| `CFT/Spherical/AttractorNeckRadius.lean` | 台帳の作用から導くアトラクターと首の半径 √v₂ = ℓ* | `CFT/AlphaVIII_Z41.lean` |
| `CFT/Spherical/CapKretschmannBlowup.lean` | 帽子のKretschmann不変量 K = 24ℓ⁴/a⁸ と崩壊、波面の軌道 | `CFT/AlphaS5_Curvature.lean` |
| `CFT/Spherical/CapNeckIntegrals.lean` | 積分で示す項目:帽子と首の拘束・YMエネルギー、Beta分布の積率 | `CFT/AlphaIntegrals.lean` |
| `CFT/Spherical/CompletionNeckDynamics.lean` | 完全化1：首の波面到着・有限時間崩壊・中心ODE、HJとPoisson括弧の検算 | `CFT/AlphaCompleteA.lean` |
| `CFT/Spherical/ConformalFrameOmega.lean` | 共形の枠:物理時空=Ω²×静的宇宙、帽子と首は □̂Ω=Ω の解 | `CFT/AlphaPillar_Conformal.lean` |
| `CFT/Spherical/ConstantAreaSlices.lean` | 断面積一定の初期データでの拘束とWの孤立波、首だけが面積を保つこと | `CFT/AlphaConstArea.lean` |
| `CFT/Spherical/ConstraintPropagation.lean` | 球対称EYMの発展で拘束が保たれる(微分体での伝播定理) | `CFT/AlphaIV_Propagation.lean` |
| `CFT/Spherical/DumbbellBogomolnyBound.lean` | ダンベルでW=r′はBogomol'nyi等号の場合：r′²≤W²と質量の微分 | `CFT/AlphaDumbbell_Bogomolny.lean` |
| `CFT/Spherical/DumbbellShapeBasics.lean` | ダンベルの基礎:傾き・帯の面積・帽子の体積・Gauss–Bonnet | `CFT/AlphaIII_Shape.lean` |
| `CFT/Spherical/DumbbellShapeCircle.lean` | (r,W)平面での円r²+ℓ²W²=ℓ²と包絡線、Weyl曲率＝質量−磁気エネルギー | `CFT/AlphaDumbbell_Shape.lean` |
| `CFT/Spherical/ELAlphaMatching.lean` | 同期ゲージで作用のEL方程式⇔αの五方程式(段階2-2) | `CFT/AlphaS2_Match.lean` |
| `CFT/Spherical/EinsteinTensorSphericalMetrics.lean` | 球対称計量のEinsteinテンソルをLevi-Civita公式から計算 | `CFT/AlphaS4_Curv.lean` |
| （v1.6.1 で削除） | RealLine版の発展の最終定理（波面の跳び・帽子崩壊、空虚のため削除） | `CFT/AlphaS5_Final.lean` |
| `CFT/Spherical/FourDimensionalMatch.lean` | 縮約した方程式と4次元EYM方程式の全成分の直接照合(Palais不使用) | `CFT/AlphaS2_4DMatch.lean` |
| `CFT/Spherical/GeneralShapeModes.lean` | 対称性を仮定しない2+2分解:断面の形(β,θ)、ずれ、集束、回転する首 | `CFT/AlphaGeneral.lean` |
| `CFT/Spherical/GoursatEvolutionConstraints.lean` | 二重ヌル発展（Goursat形）と拘束の伝播（α-IV） | `CFT/AlphaS5_Evolution.lean` |
| `CFT/Spherical/HiggsSupportedNeck.lean` | 随伴Higgs場で支える首（EYM–Higgs、α-XI.4） | `CFT/AlphaXI_HiggsNeck.lean` |
| `CFT/Spherical/MinMassFromConstraints.lean` | 拘束条件から導く質量の下限 √π M_Pl/g（α-III.7） | `CFT/AlphaS3_Mass.lean` |
| `CFT/Spherical/NeckDilatonEquation.lean` | 首のJT dilaton方程式の解φ＝A sin＋cos(B cosh＋C sinh)と静的解の不存在 | `CFT/AlphaFix_Neck.lean` |
| `CFT/Spherical/NeckInstabilityThreshold.lean` | 首のWモード不安定性の長さのしきい値（α-XI.1） | `CFT/AlphaXI_NeckInstability.lean` |
| `CFT/Spherical/NeckThroatCollapse.lean` | 首の喉の有限時間崩壊を微分不等式から導いて証明 | `CFT/AlphaIV_Z9.lean` |
| `CFT/Spherical/NoKillingSpinorCap.lean` | 帽子の厳密な崩壊 a = ℓ cos η からKillingスピノルの不存在 | `CFT/AlphaVIII_Z44Cap.lean` |
| `CFT/Spherical/NoKillingSpinorCollapse.lean` | 崩壊するダンベルにKillingスピノルが無いこと（Z44） | `CFT/AlphaVIII_Z44.lean` |
| `CFT/Spherical/NoKillingSpinorSymmetric.lean` | 喉の鏡映対称性から ∂_s r = 0 を証明し仮定を分けたZ44 | `CFT/AlphaVIII_Z44b.lean` |
| `CFT/Spherical/OmegaCloseItems.lean` | 部分項目を閉じる:くさびの捕捉領域、dyonの首、Higgs、共通の時計 | `CFT/AlphaOmega_Close.lean` |
| `CFT/Spherical/OmegaLastItems.lean` | 残り項目を閉じる:スファレロン方向、Hawking–Page型、単極子の芯 | `CFT/AlphaOmega_Last.lean` |
| `CFT/Spherical/OpenItemsSplit.lean` | 未着手項目の分割:反作用の構造、線形重力波、形の揺らぎの二次 | `CFT/AlphaOpen_Split.lean` |
| `CFT/Spherical/ReducedActionVariation.lean` | 球対称の縮約作用の変分から五つの方程式をすべて導く(段階2-1) | `CFT/AlphaS2_Action.lean` |
| `CFT/Spherical/ShapeFluctuationsAreaVolume.lean` | 形の揺らぎ（重力子偏極）と体積・断面積一定の条件 | `CFT/AlphaShapeFluct.lean` |
| `CFT/Spherical/SliceGlobalPhases.lean` | 球対称な断面の大域的分類：S³相・平坦相・首の三つの相と極の正則性 | `CFT/AlphaFix_Geo.lean` |
| `CFT/Spherical/SphericalCanonicalAction.lean` | 球対称EYMの作用→EL方程式と正準ハミルトニアン・質量拘束 | `CFT/AlphaCanonical.lean` |
| `CFT/Spherical/SphericalDiracThermoClose.lean` | 球対称EYM–Dirac系の整合性と熱力学（球対称部分の締め） | `CFT/AlphaSphericalClose.lean` |
| `CFT/Spherical/StaticDumbbellNonexistence.lean` | 静的ダンベルの不存在:W≡0の首か W≡±1の平坦のみ | `CFT/AlphaII_Z5.lean` |
| `CFT/Spherical/StaticSmoothnessMap.lean` | 静的EYMの滑らかさの地図:静的な喉なし、円柱の族、静的宇宙解 | `CFT/AlphaPillar_Smooth.lean` |
| `CFT/Spherical/UltrastaticSphereNoGo.lean` | 超静的なS³相は宇宙定数なしでは静的解にならない | `CFT/AlphaVI_Static.lean` |
| `CFT/Spherical/WavefrontEvolution.lean` | 二重ヌル発展:波面に沿う[W_u]の保存、崩壊、Gudermannian時計 | `CFT/AlphaIV.lean` |
| `CFT/Index.lean` | 命題群αの索引:各項目への仮定を加えない別名(alias)556件 | `CFT/AlphaIndex.lean` |
| `CFT/SphericalTheory.lean` | 球対称EYM–Dirac部門の入口（部門モジュールを一括import） | `CFT/SphericalTheory.lean` |
| `CFT/Unification/AbelianProjection.lean` | 方向場 n によるSU(2)曲率のAbelian射影（Z26） | `CFT/AlphaVII_Abelian.lean` |
| `CFT/Unification/ActionFromAxioms.lean` | 幾何の公理からゲージ群と作用(Maxwell/YM)を一意に導く(段階1) | `CFT/AlphaS1_Derivation.lean` |
| `CFT/Unification/ActionSpinConnection.lean` | 作用を幾何から導く:スピン接続=Wittenの形、W=r′と同値 | `CFT/AlphaII_Action.lean` |
| `CFT/Unification/BFBoundLinearModes.lean` | 線形モードのBF境界と振動解、Z42の条件つき算術 | `CFT/AlphaVIII_BF.lean` |
| `CFT/Unification/BMinusLDirection.lean` | Pati–Salam SU(4) から B−L の向きと電荷を導く | `CFT/AlphaVII_BL.lean` |
| `CFT/Unification/BPSPositivityNoGo.lean` | 超対称ハミルトニアン H = Q†Q + QQ† の正値性とBPS条件 | `CFT/AlphaVIII_BPS.lean` |
| `CFT/Unification/BridgeCommonClock.lean` | 帽子と首の共通の時計は共形時間でなくガウス正規時間であること | `CFT/AlphaBridge_Clock.lean` |
| `CFT/Unification/BridgeNeckTemperature.lean` | 首のJT dilaton不変量と表面重力・加速度の恒等式（Deser–Levin型） | `CFT/AlphaBridge_Thermal.lean` |
| `CFT/Unification/BridgeTwistDirac.lean` | W=r′を「ねじれ」とみる橋：はりねずみ上のDirac一重項と共形移行 | `CFT/AlphaBridge_Twist.lean` |
| `CFT/Unification/DomainWallZeroModes.lean` | Jackiw–Rebbi壁のカイラルなゼロモードと質量殻 | `CFT/AlphaVII_Chirality.lean` |
| `CFT/Unification/EYMInitialData.lean` | ダンベルはSU(2) EYMの初期データ:YM応力の公式と発展での保存 | `CFT/AlphaII_EYM.lean` |
| `CFT/Unification/EntropyFunctionAttractor.lean` | Senのエントロピー関数によるアトラクター（Einstein–Maxwell比較模型） | `CFT/AlphaVIII_Attractor.lean` |
| `CFT/Unification/FamousEquationsCheck.lean` | Birkhoff・Reissner–Nordström・JT重力・Hawking温度が理論から出るかの点検 | `CFT/AlphaFamous.lean` |
| `CFT/Unification/GaugeCovariance.lean` | ゲージ共変性(既に内容を表す名前のため維持) | `CFT/GaugeCovariance.lean` |
| `CFT/Unification/GaugeStandardEmbedding.lean` | 標準埋め込みとEuclidスピン接続so(4)、α′項・H·F項、S²のひねり電荷1/2 | `CFT/AlphaFix_Gauge.lean` |
| `CFT/Unification/IdeaChecks.lean` | アイデア検証集:単極子の統計力学、TTテンソル数、反転対称性 | `CFT/AlphaIdeas_Check.lean` |
| `CFT/Unification/MaxwellEquationsDerivation.lean` | Maxwell方程式の幾何学的導出（Bianchiと変分の区別） | `CFT/AlphaVII_Maxwell.lean` |
| `CFT/Unification/MaxwellFromAction.lean` | 作用の変分からMaxwell方程式(電気の側)と解析力学へ | `CFT/AlphaIX_Classical.lean` |
| `CFT/Unification/MonopoleBundleChern.lean` | 単極子の束・Dirac量子化・Chern数 c₁ = N（Z24/25） | `CFT/AlphaVII_Bundle.lean` |
| `CFT/Unification/MonopoleDiracGenerations.lean` | S²単極子Diracの固有値と世代数（α-VII.7/9） | `CFT/AlphaVII.lean` |
| `CFT/Unification/N1ObstructionBreaking.lean` | 表現論の障害N1とその解消 N1-break（Z28/Z28-f） | `CFT/AlphaVII_N1.lean` |
| `CFT/Unification/NoetherWkbNeck.lean` | Noetherの定理の一般形と循環座標、首の計量でのWKBアイコナール方程式 | `CFT/AlphaFix_Unify.lean` |
| `CFT/Unification/RelativisticFluidMHD.lean` | 完全流体のエネルギー式とEuler方程式、Kelvin循環、帽子=輻射宇宙 | `CFT/AlphaIX_Fluid.lean` |
| `CFT/Unification/S9ToPatiSalam.lean` | S⁹ から Pati–Salam への写像と一世代の電荷表 | `CFT/AlphaVII_SO10.lean` |
| `CFT/Unification/SO10ChargeUniqueness.lean` | SO(10) の超電荷 Y の一意性と電荷公式（Z28-f） | `CFT/AlphaVII_Charge.lean` |
| `CFT/Unification/SelfDualConnection.lean` | Ashtekarの自己双対接続 A=Γ+iK で帽子と首を書き直す | `CFT/AlphaPillar_SelfDual.lean` |
| `CFT/Unification/StandardEmbeddingBianchi.lean` | 標準埋め込みでGreen–Schwarz Bianchi恒等式の右辺が消えること | `CFT/AlphaVIII_Embedding.lean` |
| `CFT/Unification/StandardEmbeddingEOM.lean` | 標準埋め込みでα′項が運動方程式レベルで消えること | `CFT/AlphaVIII_EOM.lean` |
| `CFT/Unification/StringAttractorDilaton.lean` | ディラトンを含む弦の作用でのアトラクター | `CFT/AlphaVIII_StringAttractor.lean` |
| `CFT/Unification/THooftTensor.lean` | 't Hooftテンソルと微分まで含めたAbelian射影（Z26） | `CFT/AlphaVII_Thooft.lean` |
| `CFT/Unification/UnificationConsistencyChecks.lean` | Noether・WKB・ゲージ=接続の統一と整合性（α-X.1〜X.6） | `CFT/AlphaX_Unify.lean` |
| `CFT/Unification/UnifiedEquationPhases.lean` | 統一方程式U21′の係数、満たす三つの相、κの窓定理 | `CFT/AlphaII.lean` |
| `CFT/Unification/WZWLevelObstruction.lean` | ℓ*² = α′/4 の規約とSU(2)_k WZWレベルの障害（Z38/Z42） | `CFT/AlphaVIII_Z38.lean` |
| `CFT/Unification/WeakGravityWindow.lean` | WGCと首の安定条件の窓・Festina Lente（α-XI.8） | `CFT/AlphaWGC.lean` |
| `CFT/Unification/YangMillsVariation.lean` | SU(2) Yang–Mills作用の第一変分と非可換のGauss・Ampère | `CFT/AlphaIX_YM.lean` |

## 第2ラウンド: scripts/ · numerics/ · docs/ · review/ · ルート

生成スクリプトと部品ファイル、数値計算、記録ファイルも内容を表す名前に統一した。Python の相互 import（`from gen3 import …` 等）と生成スクリプトの読み書き先も追随済み。版番号・日付が識別子のファイル（ZENODO_DESCRIPTION_v*.md、監査表 2026-10-21 版など）は改名していない。

| 新しいパス | 内容 | 旧パス |
|---|---|---|
| `audit_raw_v0.2.0.txt` | v0.2.0 時代の `#print axioms` 生出力(1,074行 = v0.2.0 の定理宣言数と一致。現行 `audit.txt` は 2,421行) | `audit_raw.txt` |
| `docs/archive/ArchiveProvenanceNote.md` | archive 内の README と build log が歴史的資料である旨の注記 | `docs/archive/README_NOTE.md` |
| `docs/archive/build_all_2026-10-17b.log` | 日付なしの全体 build log(2,162 steps)。README_NOTE の記述から 2026-10-17b スナップショット期のものと推定(確定ではない) | `docs/archive/build_all.log` |
| `numerics/BartnikMcKinnonBrackets.py` | b_n の括り込みを n ≥ 6 まで延長し bn.npy に保存 | `numerics/bm6.py` |
| `numerics/BartnikMcKinnonMasses.py` | bn.npy から質量 1 − M_n、首の節間隔・長さを集計 | `numerics/bm7.py` |
| `numerics/BartnikMcKinnonShooting.py` | Bartnik–McKinnon 解の分類(節の数)と二分法による射撃の中核 | `numerics/bmS3.py` |
| `numerics/ClosedSolutionsFamily.py` | 閉じた (S³) 解の族 n = 1..10 を反射点条件で射撃、family.pkl を書く(XIV.4) | `numerics/family.py` |
| `numerics/ClosedSolutionsShape.py` | 閉じた解の形状(円柱部分の割合、節間隔) | `numerics/shape.py` |
| `numerics/ConformalSuperpositionCheck.py` | 共形因子の重ね合わせ Ω = A cos η + B/sin u の null–null / +− 成分と YM 実現可能性(XIV.8) | `numerics/omega2.py` |
| `numerics/EllipsoidCurvature.py` | R¹⁰ 内の楕円体の正規化スカラー曲率(Pati–Salam 棄却の数値側) | `numerics/ellipsoid_curvature.py` |
| `numerics/StaticConformalFlatResidual.py` | 静的共形平坦 Ω = Bu/sin u の拘束残差(XIII.4) | `numerics/static_cf.py` |
| `numerics/StaticEYMProperDistance.py` | 静的 EYM+Λ、固有距離ゲージの ODE 系 (rhs, init)。基盤モジュール(台帳 XIV.3, XIV.4) | `numerics/closed.py` |
| `numerics/StaticEYMSpiralShooting.py` | 静的 EYM を正則中心から射撃し (r,W) = (1,0) への螺旋接近を見る | `numerics/static_spiral.py` |
| `numerics/WedgeEvolution.py` | 二重ヌルの楔領域の発展(帽子+首の初期データ) | `numerics/wedge_evolution.py` |
| `numerics/WeylGrowthPerturbedWedge.py` | 摂動した楔発展で Weyl 不変量の増大(クランチ方向)を見る | `numerics/weyl_growth.py` |
| `review/AuditTable_2026-10-16.md` | 2026-10-16 の独立監査表(573個版ソース対象。2026-10-21 版に置換済み) | `review/audit_table.md` |
| `review/DepCheckOutput.txt` | DepCheck.lean の実行出力(最終定理の推移的依存チェック結果) | `review/depcheck.txt` |
| `review/PropositionGroupY_Ledger.md` | 命題群 Y (Y1〜Y32) の研究台帳: CFT 幾何から Berry 接続・BPS・インスタントンへの連鎖の整理 | `review/Y_ledger.md` |
| `review/PropositionGroupZ_Ledger.md` | 命題群 Z: 黒河ダンベルを中心とする幾何学的統合計画 | `review/Z_ledger.md` |
| `review/SnapshotReadme_2026-10-16.md` | 2026-10-16 時点のスナップショット README(α-I〜VIII、定理573個版。docs/archive 側の706個版とは別物) | `review/README_snapshot.md` |
| `review/stage3_2026-10-21/Stage3IndependentChecks.py` | 段階3の独立記号検算スクリプト(23項目) | `review/stage3_2026-10-21/stage3_independent_checks.py` |
| `review/stage3_2026-10-21/Stage3IndependentChecksResults.txt` | 上記検算の結果(PASS 一覧) | `review/stage3_2026-10-21/stage3_independent_checks_results.txt` |
| `review/stage3_2026-10-21/Stage3Summary.md` | 段階3の独立計算と補完の要約 | `review/stage3_2026-10-21/summary.md` |
| `review/stage4_2026-10-21/Stage4IndependentDerivation.py` | 段階4の接合恒等式の独立記号検算 | `review/stage4_2026-10-21/stage4_independent_derivation.py` |
| `review/stage4_2026-10-21/Stage4IndependentDerivationResults.txt` | 上記検算の結果 | `review/stage4_2026-10-21/stage4_independent_derivation_results.txt` |
| `review/stage4_2026-10-21/Stage4Summary.md` | 段階4の独立導出の要約(III.1, III.2, III.9) | `review/stage4_2026-10-21/summary.md` |
| `review/stage5_2026-10-21/Stage5IndependentChecks.py` | 段階5の独立記号検算(微分恒等式・Taylor 係数) | `review/stage5_2026-10-21/stage5_independent_checks.py` |
| `review/stage5_2026-10-21/Stage5IndependentChecksResults.txt` | 上記検算の結果 | `review/stage5_2026-10-21/stage5_independent_checks_results.txt` |
| `scripts/GenerateAuditIndex.py` | モジュール一覧から Audit.lean と CFT.lean を再生成する | `scripts/gen_audit.py` |
| `scripts/S1/QuaternionFamilyRank.py` | 四元数族 Z4(巡回)と V4(Klein)の右加群としての実ランク計算 | `scripts/S1/fam.py` |
| `scripts/S1/ScalarCurvatureGHY.py` | 球対称計量のスカラー曲率と GHY 境界項、1階ラグランジアンへの帰着(段階1) | `scripts/S1/ghy.py` |
| `scripts/S1/ScalarCurvatureWithShift.py` | シフトベクトル b を入れた球対称計量のスカラー曲率と境界項 | `scripts/S1/shift.py` |
| `scripts/S1/YangMillsGaugeCovariance.py` | YM 場の強さ F の無限小ゲージ変換に対する共変性の toy 検算 | `scripts/S1/ymc.py` |
| `scripts/S2/GenerateMatchModule.py` | 拘束・発展方程式の照合モジュール(CFT 本体側)を生成するスクリプト | `scripts/S2/genmatch.py` |
| `scripts/S2/ReducedActionDefinitions.lean` | 生成された Lean 定義群: 縮約ラグランジアン Lag と EL 式 EN/EA/ER/Eb/EW、変分 Tht/Thx | `scripts/S2/defs.lean` |
| `scripts/S2/ReducedVariationEngine.py` | jet 空間での変分計算エンジン。defs.lean と stage2.pkl を生成 | `scripts/S2/gen.py` |
| `scripts/S2/VerifyFieldEquationMatch.py` | 同期ゲージで EL 式と α 側の拘束・発展方程式の一致を検証し certs.pkl を出す | `scripts/S2/match.py` |
| `scripts/S4/AnalysisConstraintTransport.lean` | 実解析: 拘束の輸送、Gudermann/Mercator、波面の出会い、帽子の崩壊、平坦極限 | `scripts/S4/analysis.lean` |
| `scripts/S4/AssembleAllComponentProofs.py` | certall.pkl + certTall.pkl、全成分版の組立(mklean のヘルパを exec) | `scripts/S4/mkall.py` |
| `scripts/S4/AssembleComponentProofs.py` | cert.pkl → 成分証明の組立基盤 → lean.pkl | `scripts/S4/mklean.py` |
| `scripts/S4/AssembleDiagonalRicci.py` | closed.pkl → ric.lean を組立 | `scripts/S4/mk.py` |
| `scripts/S4/AssembleFourDimMatch.py` | cert4dall.pkl + ymdall.pkl + all.lean → 4次元照合モジュールを組立(round 1 で出力先は相対パス化済み) | `scripts/S4/mk4d.py` |
| `scripts/S4/AssembleKretschmann.py` | kret_cert.pkl + kret_cap.pkl → kret.lean を組立 | `scripts/S4/mk7.py` |
| `scripts/S4/AssembleStage5Sections.py` | ym_eq.pkl + cert6/7 → ymeq.lean, goursat.lean, exact.lean を組立 | `scripts/S4/mk5.py` |
| `scripts/S4/AssembleYMDiagonal.py` | ymd.pkl → ymd.lean を組立 | `scripts/S4/mk6.py` |
| `scripts/S4/AssembleYMStressTensor.py` | certT.pkl → ym.lean を組立 | `scripts/S4/mkT.py` |
| `scripts/S4/CapSolutionCertificates.py` | 帽子解の代入証明書 → cert7.pkl | `scripts/S4/cert7.py` |
| `scripts/S4/CertificateAtoms.py` | Lean 式への原子名対応表(A_, names)と変換の基盤 → cert5.pkl | `scripts/S4/cert5.py` |
| `scripts/S4/ChristoffelRicciTables.py` | 対角計量 (N,A,R) とヌル計量 (Om,r) の Christoffel 表を印字する基礎計算 | `scripts/S4/gen.py` |
| `scripts/S4/ClosedFormCertificates.py` | 両計量の曲率の閉形式計算 → closed.pkl | `scripts/S4/gen2.py` |
| `scripts/S4/ConstraintPropagationCertificates.py` | ヌル拘束の伝播の証明書 → cert6.pkl | `scripts/S4/cert6.py` |
| `scripts/S4/DiagonalChristoffelCheck.py` | 対角計量の Christoffel 表 GD を明示した独立検算 | `scripts/S4/chk.py` |
| `scripts/S4/DoubleNullEvolutionJets.py` | 段階5: jet レベルで発展方程式 r_uv, Ω_uv, W_uv を解く | `scripts/S4/s5b.py` |
| `scripts/S4/DoubleNullFieldStrength.py` | 段階5: 二重ヌル計量 (u,v) で YM 場の強さ F を関数形で計算 | `scripts/S4/s5.py` |
| `scripts/S4/EinsteinTensorEngine.py` | 汎用 einstein(g, X): 任意計量から Einstein テンソルを計算するエンジン | `scripts/S4/curv.py` |
| `scripts/S4/ExactCapNeckSolutions.lean` | 外側の厳密解: 帽子(閉じた放射 FRW)と首(AdS₂×S²) | `scripts/S4/exact.lean` |
| `scripts/S4/GenerateCertificatesAll.py` | 全16成分の証明書(D のみ) → certall.pkl | `scripts/S4/gen4all.py` |
| `scripts/S4/GenerateCertificatesSelected.py` | 選択成分(対角+01)の証明書、D と N 両計量 → cert.pkl | `scripts/S4/gen4.py` |
| `scripts/S4/GenerateFourDimCertificates.py` | 4次元照合用の証明書(選択成分) → cert4d.pkl | `scripts/S4/gen4d.py` |
| `scripts/S4/GenerateFourDimCertificatesAll.py` | 4次元照合用の証明書(全成分) → cert4dall.pkl | `scripts/S4/gen4dall.py` |
| `scripts/S4/GenerateYMDiagonalAll.py` | 対角計量 YM 方程式の全成分 → ymdall.pkl | `scripts/S4/genYMDall.py` |
| `scripts/S4/GenerateYMDiagonalSingle.py` | 対角計量 YM 方程式の単一成分 (0,2) → ymd.pkl | `scripts/S4/genYMD.py` |
| `scripts/S4/GenerateYMFourDimUnitLapse.py` | gen4d を exec し、N=1 と置いた4次元 YM 成分を再計算 | `scripts/S4/genym4d.py` |
| `scripts/S4/GenerateYMNullEquations.py` | ヌル計量 (Om,r,W) の YM 方程式 → ym_eq.pkl | `scripts/S4/genYM.py` |
| `scripts/S4/GenerateYMStressCertificates.py` | YM 応力テンソル Tym の証明書(D と N、選択成分) → certT.pkl | `scripts/S4/genT.py` |
| `scripts/S4/GenerateYMStressCertificatesAll.py` | Tym の証明書(D、全16成分) → certTall.pkl | `scripts/S4/genTall.py` |
| `scripts/S4/GoursatFormConstraints.lean` | Goursat の形と拘束の伝播(Cu/Cv、Raychaudhuri) | `scripts/S4/goursat.lean` |
| `scripts/S4/JetSetupEngine.py` | jet 変数・微分・tolean 変換の基盤エンジン(全 gen*/cert* の土台) | `scripts/S4/gen3.py` |
| `scripts/S4/KretschmannBlowupAnalysis.lean` | kret の解析部分: 固有時での a² = ℓ² − τ²、η → π/2⁻ で K → ∞(実数版) | `scripts/S4/kret_an.lean` |
| `scripts/S4/KretschmannCapEvaluation.py` | kret.pkl に帽子の代入 (a, X, Y) を施して評価 | `scripts/S4/kret2.py` |
| `scripts/S4/KretschmannFullContraction.py` | Riemann 全成分と全縮約、帽子評価 → kret_cert.pkl, kret_cap.pkl | `scripts/S4/kret3.py` |
| `scripts/S4/KretschmannInvariant.lean` | 帽子の Kretschmann 不変量 K = 24ℓ⁴/a⁸、発散、ヌル波面の軌道 | `scripts/S4/kret.lean` |
| `scripts/S4/KretschmannJets.py` | jet 変数で Kretschmann 不変量を計算 → kret.pkl | `scripts/S4/kret.py` |
| `scripts/S4/RicciComponentsDiagonal.lean` | ricD_*: 整理済みの対角計量 Ricci 成分 | `scripts/S4/ric.lean` |
| `scripts/S4/RicciComponentsRaw.lean` | ricA_*: 未整理形の Ricci 成分(対角計量、16成分) | `scripts/S4/all.lean` |
| `scripts/S4/YangMillsEquationsDiagonal.lean` | ymD_*: 対角計量での YM 方程式成分 | `scripts/S4/ymd.lean` |
| `scripts/S4/YangMillsEquationsDoubleNull.lean` | 二重ヌル座標の YM 方程式(Z8 の W_uv 式の導出) | `scripts/S4/ymeq.lean` |
| `scripts/S4/YangMillsFieldStrengthStress.lean` | YM の場の強さと応力テンソルの定義(磁気的仮定、Tym) | `scripts/S4/ym.lean` |

## v1.1.1 で追加されたモジュール（2026-11-16、旧名なし）

| 新名 | 内容 |
|---|---|
| `CFT/Quantum/MinisuperspaceVariation.lean` | ミニスーパースペース作用の偏微分 L_a、L_b（命題1-2a） |
| `CFT/Quantum/MinisuperspaceEulerLagrange.lean` | EL方程式とハミルトン方程式の同値（ゲージ Ṅ=0、命題1-2） |
| `CFT/Foundations/WaveCharacteristicData.lean` | 特性波動方程式のモデル解（命題4-3の存在側） |
| `CFT/Quantum/ModeTimeEvolution.lean` | 単一モードの時間発展（命題7-3の中核） |
| `CFT/Foundations/PeriodicIntegrationByParts.lean` | 周期的部分積分と対称性（命題3-3の1次元部分・5-1のモデル） |
| `CFT/Spherical/WedgeEYMSystem.lean` | くさびEYM系の定式化と角条件（命題4-1） |
