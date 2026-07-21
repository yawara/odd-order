---
id: 140
slug: references-submodule-ka
title: "references の submodule 化検討 (gitignore 方式は版が記録されない)"
created: 2026-07-21
---

# references の submodule 化検討 (gitignore 方式は版が記録されない)

## 背景

現状の `references/` は「gitignore された別 private repo のチェックアウト」で、
本リポ側にどの版を使ったかが**一切記録されない**。iut (2026-07-21 立ち上げ) は
references を **git submodule** として持つ方式を採用し、次の利点を確認済み:

- **版の pin がコミット履歴に残る** — 「この形式化はどの抽出 text を見て書いたか」が
  再現可能 (原文照合が本質のプロジェクトでは監査可能性に直結)
- fresh clone / 別マシンでの再現が `git submodule update --init references` の 1 コマンド
- worktree 側も main を clone 元にした初期化で統一できる
  (iut `bin/setup-worktree.sh` 参照; symlink 特例が不要になる)

トレードオフ: references 更新のたびに本リポ側で gitlink bump のコミットが要る
(高頻度更新だとノイズ)。odd-order の references は整備が既に安定しているので
bump 頻度は低いはず。⚠ `references/erdos90` は references リポ側の submodule なので、
入れ子 submodule の取得手順 (`--recursive` を使うか個別 init か) の確認が要る。

## やること

- [ ] 採否の裁定 (ユーザー判断事項 — 本 issue は検討材料の整理まで)
- [ ] 採用する場合: `.gitignore` から references を外し `git submodule add`、
      CLAUDE.md / `notes/meta/worktree_setup.md` / CI 注記 (checkout に含めない) を更新
- [ ] レーン worktree の references symlink を submodule 初期化方式へ移行

## 完了条件

裁定が本 issue に記録され、採用時は fresh clone → build → 原文照合が
submodule 経由で再現すること。

## 参照

- iut 実装: `.gitmodules` + `bin/setup-worktree.sh` + `references/README.md`
  (`/home/ywr/iut/`)
- moore57 側の同型 issue: moore57 issue 0057
