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

## 追記 (2026-07-19 20:08) — lane b が自己検出、hub 介入不要

codex ログ (`~/.codex/sessions/.../rollout-2026-07-18T01-16-26-*.jsonl`, 20:08) で
lane b 自身が衝突を検出済み:

> main 側の新しい commit に issue 9163 への言及があり、こちらの stale checkout で採番した
> claim と衝突している可能性を検出しました。…こちらの claim を未使用番号へ移してから続けます。
> 今は merge 自体は行いません。

⟹ **hub は稼働中 worktree に手を入れない**。次の合流 tick で
「9163 が 1 件のみ・b 側が未使用番号へ移動済み」を検証するだけでよい。
20:10 時点では未実施 (b の WIP 継続中)。

## 追記 (2026-07-19 20:25) — 9164 で**再衝突**、根治策としてレーン別サブバンドへ

b は 9163 → **9164** へ自力で改番したが、ほぼ同時刻に a も main 取り込み済みの状態から
次番号 **9164** (`dedup-ringaut-algaut-bridge`) を引き、**同日 2 度目の衝突**が発生した。
a 側は既に main へ合流済 (`fae731ae3`)、b 側は未コミット (`AM`)。

⟹ **共有カウンタ `SEQUENCE.9000` は原理的に衝突する** (未マージ期間がある限り、
2026-07-18 の `max(SEQUENCE, 実在ファイル最大)+1` 補強でも防げない)。

### 根治策 (hub 裁定、実施済)

- **shared-infra claim をレーン別サブバンド化**: **9200=a / 9300=b / 9400=c / 9500=hub** (幅 100)。
  SEQUENCE ファイルが別なので構造的に衝突しない。9000-9199 は歴史的レンジとして凍結。
- `bin/new-issue` を **100 の倍数 base 対応**に修正 (1000 の倍数 → 幅 1000、それ以外 → 幅 100)。
  自己テスト済 (`--base 9500` → 9500 採番 / 端数 base は従来どおり reject)。
- 正本更新: `CLAUDE.md` (3 箇所) / `notes/meta/issue_management.md` / `notes/meta/merge_monitor.md`。
- **「9xxx = shared claim」の grep 規約は不変** — `ls issues/9*.md` で全レーンの open claim を走査できる。

### 実施 (2026-07-19 20:35、hub tick で完了)

b は Lemma 5 完成と同時に 9164 を **closed** にして合流したため、hub が main 側で改番した:

- `issues/closed/9164-frobenius-conjugate-coordinates.md` → **`issues/closed/9300-...`**
  (frontmatter `id: 9300`)、`issues/SEQUENCE.9300` = 9300 を作成
- 参照 1 件を追随: `issues/2048-pf-suzuki-lemma5.md:102`
- **9164 は a の `dedup-ringaut-algaut-bridge` が保持** (open、`issues/1043` から参照されており
  参照数が多い側を据え置く = 2026-07-18 の改番規則どおり)
- 検査: open+closed+pending 全体で 9163/9164 の重複なし
  (残る 1036/1037/1038・9125・9132 は改番しない歴史的 closed 衝突)

以後 b の shared-infra claim は `export ODD_ISSUE_BASE=9300`。

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
