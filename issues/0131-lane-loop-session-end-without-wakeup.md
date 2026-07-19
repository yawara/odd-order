---
id: 131
slug: lane-loop-session-end-without-wakeup
title: "レーンの /loop 自走が wakeup 未発火でセッション終了する障害 (a 05:36 / c 21:19)"
created: 2026-07-19
---

# レーンの /loop 自走が wakeup 未発火でセッション終了する障害 (a 05:36 / c 21:19)

## 背景

2026-07-19 に **同一の停止パターンが 2 回**発生した。どちらも成果損失はゼロ
(`unmerged 0` / `dirty 0` で止まる) が、レーンが黙って止まるため **hub が気づくまで
frontier が凍結**する。

| レーン | 停止時刻 | 停止までの状態 | 検出 | 空転時間 |
|---|---|---|---|---|
| a | 05:36 | ahead 0 / dirty 0 | hub tick (11:27 に自力復帰) | **5h51m** |
| c | 21:19 | unmerged 0 / dirty 0 / behind 0 (main 同期直後) | hub tick 21:57 | 38m (検出時点) |

**c の停止の形** (transcript `~/.claude/projects/-home-ywr-odd-order-c/a83a1241-*.jsonl` の末尾):

1. 21:19:19 hub が合流済みであることを確認 (`git merge-base --is-ancestor` で自作業の landing 確認)
2. 21:19:22 `git merge main` で同期 (0 behind)
3. 21:19:55 「Synced with main (0 behind), working tree clean.」+ **`## Session summary` を書いて turn 終了**

⟹ **次の iteration の `ScheduleWakeup` を呼ばずに turn を終えた**。CLAUDE.md の
「レーンの `/loop` self-pacing wakeup = 60s (最短固定)」以前に、そもそも wakeup が予約されていない。
a の 05:36 停止 (merge_monitor.md 記載、「60 秒後 wakeup が発火せずセッション終了」) と同型。

## 何が問題か

- **「区切りがついた」ことは停止理由でない**。CLAUDE.md の STOP 条件は
  (i) unsound carrier・新 axiom、(ii) signature 無断変更、(iii) build 破壊・sorry regression・
  想定外 git 状態、(iv) 真に underdetermined な設計分岐 — の 4 つのみ。
  「1 つの issue を閉じた」「main と同期して clean になった」は**継続の合図**であって停止理由ではない。
- レーンは frontier を自律決定する規約 (上流優先 + 文書順) なので、**次に何をするか分からないから止まる**
  という事態自体が規約違反 (frontier が枯渇したなら 9000 番台 HUB issue を立てて hub に問う)。
- 症状が「静かな停止」なので、hub の合流 tick (15 分) でしか検出できない。

## やること

- [ ] **hub tick の検出項目に「レーン停止」を正式に追加** — 判定は
      `~/.claude/projects/-home-ywr-odd-order-<lane>/*.jsonl` の最終更新時刻 (transcript が
      止まっていればセッションが終わっている)。`git log` の最終 commit 時刻だけでは
      「大きめのコミットを書いている最中」と区別できない (実際 c は 21:00 時点では生きていた)
- [ ] 停止を検出したら**報告する** (hub からレーンの unsupervised セッションへメッセージは送れない
      = [[cross-lane-sync-via-notes]])。再開はユーザーの操作が要る
- [ ] レーン再開プロンプトに **「turn を終えるときは必ず `ScheduleWakeup(delaySeconds: 60)` を
      呼ぶ。issue を閉じた・main と同期した・区切りがついたは停止理由にならない」**を明記する
- [ ] 2 回とも「main 同期直後の clean 状態」で止まっている点を追加調査 —
      同期完了が「タスク完了」と解釈されている可能性が高い

## 完了条件

- hub tick 手順 (`notes/meta/merge_monitor.md`) に停止検出が組み込まれ、
  レーン再開プロンプトに wakeup 必須の文言が入ること。
- 以後の停止が 1 tick (15 分) 以内に検出・報告されること。

## 参照

- `notes/meta/merge_monitor.md` (a の 05:36 停止と暫定裁定 9158 の記録)
- `CLAUDE.md`「レーンの `/loop` self-pacing wakeup = 60s (最短固定、ユーザー 2026-07-06)」
- `issues/closed/9158-*` (a 停止時の Pf 本文暫定移管 → 復帰で失効)
