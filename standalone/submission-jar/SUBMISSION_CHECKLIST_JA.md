# 投稿チェックリスト（Journal of Automated Reasoning, Springer）

## 投稿前に自分で埋めるところ（4か所）

1. `manuscript.tex` の `EMAIL-TO-BE-ADDED`：連絡先メールアドレス（タイトルページ）
2. `manuscript.tex` の `REPOSITORY-URL-TO-BE-ADDED`：Lean 一式を置く公開リポジトリの URL（Declarations の Code availability）
3. `manuscript.tex` の `DOI-TO-BE-ADDED`：Zenodo などのアーカイブ DOI（まだなければ「and will be archived with a DOI on acceptance」に書き換え）
4. `cover_letter.tex` の `EMAIL-TO-BE-ADDED` と `REPOSITORY-URL-TO-BE-ADDED`

埋めたあと、次の順で再コンパイルします。

```
pdflatex manuscript && bibtex manuscript && pdflatex manuscript && pdflatex manuscript
pdflatex cover_letter
```

## 投稿システムで聞かれること

- 投稿先：https://submission.nature.com/new-submission/10817/3
- 論文種別：Original Paper（regular article）
- アップロードするもの：
  - `manuscript.tex`
  - `references.bib`
  - `manuscript.bbl`
  - `sn-jnl.cls`
  - `sn-mathphys-num.bst`
  - `manuscript.pdf`
  - `cover_letter.pdf`
  - LaTeX ソースは編集可能な形で出すことが求められます。
- 著者：単著、corresponding author。ORCID があれば登録します。
- 査読方式：single-blind です。本文に名前があって問題ありません。
- 推薦査読者：任意です。入れる場合は、所属機関のメールアドレスを持つ人に限られます。利害関係がなく、実在を確認した人だけにしてください。こちらでは名前を挙げていません。
- フォームで聞かれる宣言（Funding / Competing interests / Data / Code）：本文の Declarations と同じ内容を答えます。
- AI 利用：本文の Section 8 (Methods) とカバーレターに記載済みです。フォームにも同じ趣旨で答えてください。

## 確認しておくこと

- arXiv に先に出す場合は、カバーレターに「A preprint has been posted at arXiv:XXXX」の一文を加えます。分野は cs.LO を主分類にし、math-ph、gr-qc をクロスリストにする想定です。
- 本文で Lean の公開リポジトリとして挙げるのは、`standalone/` だけを独立させた新しいリポジトリにするのが自然です。親プロジェクトの用語が混ざらないためです。
- 参考文献は 17 件で、自分の著作は入っていません。DOI を確認できたものには付けてあります（Christodoulou 1993、Volkov–Gal'tsov、Peldán、Boldo ほかは DOI 未確認のため arXiv 番号か書誌情報のみ）。
- テンプレート：Springer Nature LaTeX template Version 3 (October 2023) の `sn-jnl.cls` と `sn-mathphys-num.bst` をそのまま使っています。
  - 変更点は一つだけです。冒頭に `\RequirePackage{amsthm}` を置いて、テンプレートの定理スタイル（thmstyleone ほか）が有効になるようにしました。
  - Springer のサイトに最新版 v3.1（2024年12月）があるので、差し替える場合はクラスファイルを入れ替えて再コンパイルするだけで済みます。
