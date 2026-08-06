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

---

## 🧭 HUB 推奨 (2026-07-22): 採用推奨、実施はユーザー承認 + 大区切り後 — pending へ

- 推奨 = **submodule 化を採用** (iut で利点実証済み、版が記録されない現状の欠点は本物)。
- ただし全レーン稼働中の references 構成変更は各 worktree の symlink 運用に触るため、
  実施タイミングは **FeitSibley (1054) / Theorem B (2053) いずれかの close 後の quiet
  window** を推奨。repo 構成の不可逆変更ゆえ最終 go はユーザー承認事項 → pending。

---

## 🔓 2026-08-07 REOPENED — 推奨のトリガー条件が満たされた

hub 推奨の実施タイミング条件「**FeitSibley (1054) / Theorem B (2053) いずれかの close 後の
quiet window**」が成立した: **2053 は 2026-08-07 に close**、レーン a/b/c はいずれも main へ
完全合流済で worktree 稼働なし = まさに quiet window。

⚠ 残る条件は「repo 構成の不可逆変更ゆえ最終 go はユーザー承認」の 1 点のみ。着手前に確認する。

---

## ✅ CLOSED (2026-08-07) — submodule 化を実施 (ユーザー承認)

「repo 構成の不可逆変更ゆえ最終 go はユーザー承認」の条件が満たされ、実施した。

**やったこと**:
1. `references` リポの未 push commit 1 本を push (submodule pointer が解決するように)。
2. 本リポの `.gitignore` から `references/` 行を削除。
3. **`.git/info/exclude` の `references` 行を削除** — ⚠ ここが罠。worktree 運用のために
   足してあった行 (worktree_setup.md 旧 §3) が残っていると `git submodule add` が
   「ignored by one of your .gitignore files」で失敗し、`.gitignore` だけ見ても原因が分からない。
   `git check-ignore -v references` で発見できる。
4. `git submodule add git@github.com:yawara/odd-order-references.git references`
   ⟹ `.gitmodules` に登録、gitlink `59e7b885` を記録。

**CI**: 変更不要。`lean_action_ci.yml` は `actions/checkout@v5` を submodule オプション無しで
使っており、既定で submodule を fetch しない (ユーザー指示「CI はサブモジュールは必要ない」に
一致)。意図が後から壊されないよう**理由コメントを追加**した (private repo 認証で落ちる旨)。

**worktree 運用**: `references` は submodule 化後も **main の実体を symlink で共有**する
(PDF + ページ画像で重いため)。旧 §3 の `.git/info/exclude` 手順は廃止し、`typechange` が
気になる場合の `update-index --skip-worktree` を代替として記載 (`worktree_setup.md` §3)。

⚠ **公開される情報**: 本リポは public なので、`.gitmodules` によって private リポの URL
(`yawara/odd-order-references`) が公開される。中身は clone できないので実害は無いが、存在は見える。

**波及**: `erdos90` は `references` の中の submodule なので、本リポから見ると **nested**。
取得は `git submodule update --init --recursive references`。
