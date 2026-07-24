---
id: 143
slug: blueprint-reverse-gen-from-lean
title: "Lean から blueprint を逆生成する (forward TeX は不採用のまま)"
created: 2026-07-23
---

# Lean から blueprint を逆生成する (forward TeX は不採用のまま)

## 背景

本リポは leanblueprint を**使わずに**来た。CLAUDE.md「やらないこと」で禁じているのは
**forward driver としての TeX 依存グラフ** — `\uses{}`/`\proves{}` を人手保守して形式化を
駆動する向き。edge が人間の主張ゆえ実体と drift しうる。

一方で **逆向き (Lean → blueprint 相当の成果物を抽出する)** は別物で、このリポでは
**むしろ自然**。実測 (2026-07-23):

- 教科書ラベル付き docstring **4,411 箇所 / 670 ファイル** (`**Isaacs Thm 1.4**` 形式)
- `section /- 9A: Theorem 9.7 (a) (p. 274) -/` 等、教科書構造をミラーした section ラベル
- `#print axioms` / AxiomsCheck で proved か sorry 依存かを機械判定可能
- `importGraph` パッケージは既に mathlib 依存として入っている (`.lake/packages/importGraph/`)

blueprint が提供したい情報 (何が statement 化され・何が証明済みで・何に依存し・教科書の
どこか) は**既に Lean ソース + axiom 監査の中に在る**。leanblueprint はそれを TeX で手書き
させる道具なので、本リポでは「手書きする代わりに抽出する」だけでよい。逆向き edge は
**証明項 (`getUsedConstants` / `CollectAxioms`) から取る**ので kernel 保証の ground truth に
なり、「doneness は sorry 数でなく構成可能性・`#print axioms` で検証」という本リポの哲学と
同じ側に立つ。

ユーザー方針 (2026-07-23): この方針を CLAUDE.md に明記し (済 — 「やらないこと」節を改訂)、
実装を issue 化する。

## 設計方針 (守る線)

- 逆生成物は**常に Lean から再生成**する。**手編集して第二の source of truth にしない**
  (手編集で育て始めた瞬間、forward TeX の失敗モード = 実体との drift に戻る)。
- 開発を駆動する道具にはしない。完成物の **view / progress dashboard** として使う
  (frontier map は `issues/` + AxiomsCheck と連動)。

## やること (推奨順、A+D が本命)

- [ ] **A. 宣言レベル依存 DAG のメタプログラム抽出** (本命の「逆 blueprint」)
  - `Lean.Elab` スクリプトで `env.constants` を走査、`OddOrder.*` に絞る
  - 各宣言から: statement (型を pp) + docstring (教科書ラベル+慣用名) +
    依存集合 (`value?.getUsedConstants` を **`OddOrder.*` 内 edge のみ**に filter) +
    status (`CollectAxioms` に `sorryAx` を含むか → **proved / stated-only 色分け**)
  - 可読性の鍵: ノードを**教科書ラベルを持つ宣言 (~4,411)** に絞り、無名 helper を貫く
    edge を **transitive reduction** → 教科書レベル DAG (= blueprint 本体)
  - 出力: Graphviz `.dot` / d3 用 JSON。**leanblueprint の dep-graph ビューアが食う
    node/edge JSON をそのまま吐けば TeX 抜きで同じインタラクティブグラフが得られる**
- [ ] **D. ラベル concordance (教科書番号 ⇔ Lean 名の両方向対応表)** — 安く効く補完
  - `**{Isaacs,BG,Peterfalvi} Thm N.M**` を grep して
    「各番号 → Lean 名 → ファイル → sorry 状態」の表を吐く (Lean elaboration 不要の純テキスト)
  - A の edge を D の教科書アンカーで固定すると本物の blueprint になる
  - ⚠ `three_books_full_survey_2026_07_16.md` (降格済みスナップショット) の**置き換え**に
    もなりうる (実体から生成 ⟹ drift しない coverage 表)
- [ ] **B. doc-gen4** (任意・後回し): mathlib 標準 HTML doc 生成器。全宣言を docstring・
  statement・依存リンク付きで閲覧。標準だがビルドが重く、curated DAG でなく参照サイト
- [ ] **C. importGraph** (既存・安い): `lake exe graph` で module/import 粒度 DAG。
  数学 DAG でなくファイル DAG。構造把握の sanity map として

## 完了条件 (段階的)

まず PoC → 有用なら定着。以下のいずれかで最初のマイルストーンとする:

- A を 1 名前空間 (例 `OddOrder.Peterfalvi.S16`) に限定して `.dot` を吐くメタプログラム
  が動き、proved/sorry 色分け DAG が生成できる、または
- D の対応表 (全 3 冊) が生成でき、教科書番号 ↔ Lean 名 ↔ sorry 状態が 1 hop で引ける

生成物は再生成スクリプト (`bin/` か `scripts/`) として commit し、手編集しない運用を明記。

## 注意点 (正直な限界)

- **hairball 問題**: 宣言レベル生グラフは mathlib 規模で巨大。A のラベル絞り込み +
  transitive reduction が可読性の生命線 (無ければ hairball)
- statement は **Lean の型**であって散文でない。逆生成物は形式 statement + docstring の
  慣用名を出すだけで、英語の証明概略は捏造しない (むしろ honest)
- sorry 色分けは **frontier map** として効く (statement-first spine の未証明ノードが光る)

## 参照

- CLAUDE.md「やらないこと」節 (2026-07-23 改訂: forward 不可 / reverse 推奨 / 守る線)
- `.lake/packages/importGraph/` (既存ツール), doc-gen4 (未導入)
- [issue 0139](0139-notes-meta-seibon-log-bunri.md) (survey スナップショット降格の文脈 —
  D が置き換え候補)
- `notes/meta/three_books_full_survey_2026_07_16.md` (降格済 coverage、D の置換対象)

---

## ❄ 2026-07-24 FROZEN (ユーザー裁定) — pending へ

blueprint 逆生成はユーザー裁定で凍結。実装計画 (§設計・Phase 分割) は本文に保存済み —
解凍時はそこから再開。forward TeX 不採用の方針 (CLAUDE.md「やらないこと」) は不変。
