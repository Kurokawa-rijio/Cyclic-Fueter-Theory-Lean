# 2026-10-21k(第 10 弾)

ベース:2026-10-21i + 外部パッチ j。この版は Lean 4.15.0 + Mathlib v4.15.0 で全体ビルド済み(build_k.log)。

## 外部パッチ j の検証(内容は正しい、コンパイル済み)
- AlphaS4_Final `null_final`:YM の表面流の結論を両側の流束 −s₂W_v,₂ − (−s₁W_v,₁) に、共通トレース `cs : s₁ = s₂` を仮定に追加。
- AlphaS3_Mass `min_mass_from_constraints`:r(s₀) = ℓ と首の EYM ハミルトン拘束から `ell_neck` で ℓ² = 4πG/g² を導く(半径² を仮定しない)。
- AlphaV_GaussMap:`zProfile`、`profileMap`、`profileMap_injective`(z が狭義単調、r ≠ 0)、`profile_immersion_data`。大域的な埋め込みの主張とは区別する。
- DepCheck.lean:証明本体の依存(`#uses`)と型の依存(`#type_uses`)を分離。

## 段階 2 の 4 次元照合(新規 AlphaS2_4DMatch、定理 82 個)
- Ricci・Einstein 16 成分(`ricA_ij`、`einA_ij`)、YM の応力 16 成分(`tymA_ij`)、YM 方程式 12 成分(`ymA_an`)を同期ゲージ N = 1 で計算。
- `sync_ij`:E₀₀ = H/2、E₀₁ = E₁₀ = −AM、E₁₁ = A²(2T + H/2)、E₂₂ = R²(X + T + H/2)、E₃₃ = s²E₂₂、他の 10 成分 0。
- `ym_sync_02`:YM(1,θ) = −s eP。`ym_sync_13`:s·YM(2,φ) = YM(1,θ)。他の 10 成分 0。
- `full_4d_iff_alpha`:4 次元の EYM の全成分(16 + 12、F = dA + A∧A)⇔ α の五つの方程式。
- `palais_free`:4 次元の EYM の全成分 ⇔ 縮約した作用の五つの EL 方程式(`el_iff_alpha` と合成)。Palais の対称臨界性は使わない。
- 生成スクリプトと証明書:aux/S4/{gen4all.py, genTall.py, genYMDall.py, gen4dall.py, mkall.py, mk4d.py}、*.pkl。

## その他
- AlphaS5_Final `wave_jump_final`:使っていない仮定 v0 ≤ v1 を外した。

## 検査
- 定理 1074 個、1061 個が [propext, Classical.choice, Quot.sound]、6 個が [propext, Quot.sound]、4 個が [propext]、3 個は公理なし。sorryAx 0、独自の axiom 0(audit.txt)。
- DepCheck(review/depcheck.txt):新しい依存はすべて true。false の 4 件は補助版で第 9 弾と同じ。
