---
id: 93
slug: hub-lane-b-policy-dup-superseded-by-c
title: "HUB: lane b の policy codification (47bd6a0f) は lane c 版に supersede — 次 sync で drop"
created: 2026-07-01
---

# HUB: lane b の policy codification (47bd6a0f) は lane c 版に supersede

## 経緯 (2026-07-01 hub tick)

ユーザー裁定 2026-07-01（自律 frontier 選択・shared-infra claim-before-build）を、**lane b と lane c が
両方とも独立に codify**した:

- **lane b** `47bd6a0f docs(規約)`: `CLAUDE.md` + `ft_path_policy.md §0.4` に別 wording で追加。
- **lane c** `052237b4 docs(policy)`: `CLAUDE.md` + `ft_path_policy.md §0 policy 5-6` +
  `merge_monitor.md §1.6`（shared-infra 重複検出）+ `issue_management.md`（9000 番台 claim protocol）。

両者は CLAUDE.md の**同一アンカー**（「作業順序 = 上流優先」bullet 直後）を編集しており衝突/重複。
**c 版が superset**（machinery 一式で self-consistent）ゆえ hub は **c を採用・合流**（main `f6507084`）、
**b の policy commit は不採用（保留）**とした。

## lane b への指示

- 次の `git merge main` で **CLAUDE.md / ft_path_policy.md の conflict が出る** → **main 側（= c 版）を採用**し、
  自分の `47bd6a0f` の CLAUDE.md/ft_path_policy 追加を **drop**（同じ裁定が c 版で既に landing 済、内容は失われない）。
- 具体的には `git rebase main` 中の conflict、または `git merge main` 後に CLAUDE.md/ft_path_policy を
  main の版に戻して commit。b の .lean 実作業（§7/§12 hB chain）は影響なし。
- b 版に c 版へ**追加したい nuance**（例: §0.4 の "clean-additive 判定" の明快な 3 段手順）があれば、
  c 版へ **追記する形**で notes/issue 経由提案（重複 bullet の再追加でなく)。

## hub (次 tick) への注記

- lane b が上記を反映するまで、3-dot `main...b` に `CLAUDE.md`/`ft_path_policy.md` が出て merge が
  **conflict する**。これは **superseded policy dup**（本 issue）であり novel な問題ではない → その conflict は
  `git merge --abort` して「b: policy dup 未解消（issue 0093）」と 1 行報告し、b の**他の非衝突コミット**は
  通常合流（可能なら）。**STOP（CronDelete）はしない**（build/violation でない）。b が drop したら通常合流に復帰。

## 状態

- [x] c 版 policy を main へ landing (`f6507084`)
- [ ] lane b が CLAUDE.md/ft_path_policy dup を drop（次 sync 時）
