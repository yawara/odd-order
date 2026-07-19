---
id: 130
slug: lane-b-issue-9163-collision-and-sync-drift
title: "lane b: issue 9163 番号衝突 + main 同期 drift (23 commits)"
created: 2026-07-19
---

# lane b: issue 9163 番号衝突 + main 同期 drift (23 commits)

## 背景

2026-07-19 19:5x の hub 監視で検出。

**(1) 9000 番台の番号衝突.** `issues/SEQUENCE.9000` は共有カウンタだが、
lane b (codex 駆動) が **main から 23 commits 遅れた状態**で採番したため
9163 が二重に割り当てられた:

| 側 | ファイル | 状態 |
|---|---|---|
| main (正) | `issues/9163-typepa-mssharp-rescope-for-815-typeii.md` | commit 済 (4e38043d1, 19:21) — SEQUENCE 更新は 3c90d39ee (19:15) |
| lane b | `issues/9163-frobenius-conjugate-coordinates.md` | **未 commit (staged)**, `SEQUENCE.9000` も 9162→9163 に変更済 |

内容は無関係 (前者 = Pf (8.15)/(8.18) type-P_A M_S# rescope、
後者 = Higman Lemma 5 用 Frobenius 座標基底 / issue 2048 の feeder)。

**(2) 同期 drift.** lane b は 18:25 の FF merge 以降 main を取り込んでおらず
`git rev-list --count b..main` = 23。CLAUDE.md「🔄 起動時 + 定期の main 同期」
に違反した状態で、番号衝突はその直接の帰結。lane b は codex セッションのため
Claude 側の起動時同期規律が効いていない可能性がある (要観察)。

## やること

- [ ] **裁定**: main 側 9163 (`typepa-mssharp-rescope`) を正とし、**lane b 側を
      9164 へ改番**する。lane b 側は未 commit ゆえ改番コストが小さく、main 側は
      すでに commit 済で他 issue/notes からの参照リスクがある
- [ ] 実施タイミング = **lane b が現 WIP を commit した直後 (hub の次の合流 tick)**。
      稼働中の worktree に hub が割り込んで `git mv` しない
      ([[concurrent-subagents-share-git-state]]: 同一 worktree の git 状態共有)
- [ ] 改番手順: `git mv issues/9163-frobenius-conjugate-coordinates.md
      issues/9164-frobenius-conjugate-coordinates.md` → frontmatter `id: 9164` →
      `issues/2048-pf-suzuki-lemma5.md` / `notes/peterfalvi/suzuki_ch1.md` /
      新規 Lean docstring 内の "9163" 参照を 9164 に置換 → `SEQUENCE.9000` を 9164 に
- [ ] lane b の次回起動/再開時に `git merge main` を必ず通す (23 → 0)

## 完了条件

- `ls issues/**/9163-*` が 1 件のみ (main の typepa 側)
- lane b の Frobenius 座標 issue が 9164 として main に合流し、参照も全て 9164
- `git rev-list --count b..main` = 0

## 参照

- `issues/9163-typepa-mssharp-rescope-for-815-typeii.md` (main 側, 正)
- lane b worktree: `issues/9163-frobenius-conjugate-coordinates.md` (改番対象)
- `issues/2048-pf-suzuki-lemma5.md` (consumer)
- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean` (lane b 未 commit)
- `notes/meta/issue_management.md` 「並行セッションの採番レンジ」
