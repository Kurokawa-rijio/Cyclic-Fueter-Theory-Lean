# GitHub への公開手順

## 推奨リポジトリ名

`Cyclic-Fueter-Theory-Lean`

## 公開前に必ず決めること

1. リポジトリを **Public** にするか **Private** にするか。
2. 再利用を許可するライセンスを付けるか。現状はライセンスを付けていないため、第三者への一般的な再利用許諾はない。

## ローカルから push する場合

1. `Cyclic-Fueter-Theory-Lean.zip` を展開する。
2. GitHub で同名の空リポジトリを作る（GitHub側でREADME、LICENSE、.gitignoreを自動生成しない）。
3. 展開したプロジェクトのルートで次を実行する。

```bash
git init
git add .
git commit -m "Initial Lean formalization snapshot (2026-10-17b)"
git branch -M main
git remote add origin https://github.com/<YOUR_GITHUB_USERNAME>/Cyclic-Fueter-Theory-Lean.git
git push -u origin main
```

`<YOUR_GITHUB_USERNAME>` は本人のGitHubユーザー名に置き換える。

## 公開後の確認

- GitHub Actions の `Lean CI` が成功することを確認する。
- `lake-manifest.json` は元ZIPに含まれたローカルパス依存を避けるため除外している。CI上で `lake update`/Mathlib依存解決が正常に行われることを確認する。
- CIが成功するまでは、公開版が新規環境で再ビルド済みだと説明しない。
