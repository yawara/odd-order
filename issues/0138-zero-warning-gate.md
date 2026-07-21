---
id: 138
slug: zero-warning-gate
title: "ゼロ警告 gate (check-warnings) の導入と現存 172 lint 警告の解消"
created: 2026-07-21
---

# ゼロ警告 gate (check-warnings) の導入と現存 172 lint 警告の解消

## 背景

lint 警告は build を止めないため溜まり続け、後からの一括訂正が高くつく
(本リポでは issue 0123 = linter-warnings-cleanup が既存。moore57 では 5031 件まで
膨らんだ — moore57 issue 0056)。ユーザー方針 (2026-07-21、iut 立ち上げ時):
**警告はその commit で直す**を機械で強制する。

iut (`/home/ywr/iut/bin/check-warnings`) に実装済みの gate:
`lake build` 出力の `warning:` 行のうち **sorry 警告以外が 1 件でもあれば exit 1**
(sorry は正常系ゆえ許容; Lake の log replay により増分 build でも既存警告を検出)。

**現存警告の実測 (2026-07-21、main の no-op build)**: 総数 174 = sorry 2 +
**lint 172**。内訳の大どころ:

- `linter.flexible` 約 70 件 — ほぼ全て `OddOrder/BG/AppE_FiliformGroup.lean`
  (240/326/419/452 行の `simp ... at h1 h2 ...`)
- `open scoped Classical` 警告 9+ 件 (Peterfalvi S04/S08/S09 ほか)
- 未使用変数名・未使用仮定・`Mathlib.Tactic` 丸 import・maxHeartbeats コメント無し・
  longLine 1 件 など少数多種

## やること

- [ ] iut の `bin/check-warnings` を移植 (`OddOrder` 読み替えのみ; sorry 許容フィルタは
      issue 0137 の引用符非依存パターンで)
- [ ] 現存 172 件を解消 (AppE_FiliformGroup の flexible 集中は `simp?` 置換 or
      理由コメント付き per-decl `set_option linter.flexible false in` の裁定)
- [ ] CI (`lean_action_ci.yml`) に gate step を追加
- [ ] issue 0123 との統合 — 0123 のスコープを本 issue が包含するなら 0123 を close

## 完了条件

`bin/check-warnings` が exit 0、CI green、以後の警告は commit 時点で止まる。

## 参照

- iut 実装: `/home/ywr/iut/bin/check-warnings` + CLAUDE.md「ビルド・検証規律」
- 実測ログの取り方: main で `lake build 2>&1 | grep -E "warning: "` (replay で全件出る)
- 関連: issue 0123, 0137 / moore57 issue 0056
