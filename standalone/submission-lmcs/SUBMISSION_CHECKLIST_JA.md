# 投稿の手順（Logical Methods in Computer Science）

LMCS は「先に arXiv に出し、その arXiv 版を LMCS に投稿する」方式です。掲載料はかかりません。

## 0. 埋める空欄

- `manuscript.tex`
  - `EMAIL-TO-BE-ADDED`（著者のメールアドレス。LMCS では必須項目）
  - `DOI-TO-BE-ADDED`（Section 8 の末尾。Lean 一式の Zenodo DOI）
- `cover_letter.tex` と `cover_letter.txt`
  - `EMAIL-TO-BE-ADDED`
  - `DOI-TO-BE-ADDED`
  - `ARXIV-ID-TO-BE-ADDED`（arXiv に出したあとで埋める）

LMCS は、コードを Zenodo などの DOI 付きアーカイブに置くよう求めています。先に `standalone/` を独立したリポジトリにして Zenodo で DOI を取ると、空欄の DOI が埋まります。

再コンパイルは次の順で行います。

```
pdflatex manuscript && bibtex manuscript && pdflatex manuscript && pdflatex manuscript
```

## 1. arXiv に投稿する

- 投稿ページ：https://arxiv.org/submit （アカウント作成：https://arxiv.org/user/register ）
- 主分類は cs.LO（LMCS の必須条件）。クロスリストは math-ph と gr-qc を推奨します。
- アップロードするのは `arxiv_upload.zip` の中身です。
  - `manuscript.tex`
  - `manuscript.bbl`
  - `references.bib`
  - `lmcs.cls`
  - `alphaurl.bst`
- arXiv は BibTeX を実行しないので、`.bbl` が必要です。LMCS は `.bib` の同梱も求めているため、両方入れてあります。
- `lmcs.cls` は 2026/10/21 版（v0.95）です。LMCS のサイトから取得した最新版で、中身が公式ファイルと一致することを確認済みです。
- ライセンスは CC BY 4.0 を選びます（LMCS の標準ライセンス）。
- 注意：arXiv に初めて投稿する場合、cs.LO への投稿に「推薦（endorsement）」を求められることがあります。求められたら、案内に従って推薦者を探す必要があります。
- タイトルと要旨は、論文のものと完全に同じにしてください（LMCS の要件）。

## 2. LMCS に投稿する

- アカウント作成：https://lmcs.episciences.org/user/create
- 投稿ページ：https://lmcs.episciences.org/submit/index
  - arXiv の ID を入力すると、論文が取り込まれます。
- 担当編集者（handling editor）を 1 人だけ選びます。候補は次の二人です。
  - Assia Mahboubi（担当分野：Formalized mathematics、Interactive proof checking）。カバーレターではこの人を推しています。
  - Benedikt Ahrens（担当分野：Formalized mathematics、Interactive proof checking）
- License Agreement（LMCS の掲載許諾）に署名します。
- 編集者へのコメント欄に `cover_letter.txt` の内容を貼ります。投稿規定にカバーレターの指定はありませんが、入れておくと親切です。

## 3. 確認事項

- 「既発表ではなく、他誌で審査中でもない」ことが条件です。JAR には投稿していないので問題ありません。
- AI の利用は Section 8 とカバーレターに書いてあります。LMCS の規定には AI に関する明文がありませんが、開示しておくのが安全です。
- 参考文献は 17 件で、本人の著作は入っていません。
