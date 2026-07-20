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

## 追記 (2026-07-20): 第 2 の類型 — **理由つき停止**も同じく frontier を凍らせる

上表の「黙って止まる」型とは別に、**自己診断して報告してから止まる**型が 2 件発生した。
どちらも報告内容は正しく、成果損失もゼロだが、**再開にユーザー操作が要る点は同じ**:

| レーン | 時刻 | 停止理由 (レーン自身の言) |
|---|---|---|
| a | 22:46 | 「territory 内で取れる行動は hub issue の起票が最後。裁定を待って空転するか、他レーンの仕事を一方的に取るかになる」→ PushNotification + `ScheduleWakeup({stop:true})` |
| c | 01:41 | 「**直近 3 iteration が docs コミットのみで Lean を 1 行も landing していない**。調査偏重に逃げるパターンに当たる」→ 進捗不良を能動報告 (規約どおり) して `ScheduleWakeup({stop:true})` |

⚠ **報告は正しいが停止は規約と食い違う**。CLAUDE.md は「真に blocked でも 9000 hub issue を立てて**続行**
(報告≠停止)」であり、「調査偏重」の是正は**実装に移ること**であって停止ではない。
c の場合、次の一手 (E.3(b) 補題 (2) の実装) は自分で特定済みで、着手できる状態だった。

⟹ レーン再開プロンプトに入れる文言 (前掲の wakeup 必須と併せて):
**「進捗不良を検知したら報告し、そのうえで *実装に移って続行* する。報告は停止理由ではない」**。

## 追記 (2026-07-20 03:10): 3 例目 — a が**マイルストーン直後に黙って停止**

a は 02:38 の `ScheduleWakeup(60s)` を最後に、02:54 の「**(8.18) 全体が書籍の文に到達しました**」
という完了報告で turn を終え、**次の wakeup を予約しなかった** (`stop: true` すら呼んでいない
= 第 1 類型の黙った停止)。02:38 までは 3 回連続で正しく 60s を予約できていたので、
**「区切りがついた turn」でだけ予約が抜ける**傾向が強い。

⟹ 3 例に共通するトリガーは「**達成感のある turn の終わり**」(main 同期完了 / 完済報告 /
マイルストーン到達)。再開プロンプトでは *停止条件* を列挙するより、
**「report を書いたら、その同じ turn 内で必ず `ScheduleWakeup(60s)` を呼ぶ」**という
順序の規則として渡す方が効く見込み。

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

## 追記 (2026-07-20 16:08 JST): 4 例目 — a が**マイルストーン報告の turn で**再び黙って停止

| 項目 | 実測 |
|---|---|
| 最後の `ScheduleWakeup` | 06:42:38Z (`delaySeconds: 60`)。セッション通算 **48 回**は正しく予約できていた |
| 最終アクティビティ | 06:45:33Z (= 15:45 JST) |
| 停止時の状態 | `unmerged 0 / dirty 0 / behind 8` (成果損失ゼロ) |
| 検出 | hub tick 16:08 (**23 分**の空転で検出) |
| 最後の turn の内容 | 「**Forty commits, all build-green, tree clean and synced with main.** Checked the τ seam before writing the dispatch…」= (9.9.b) dichotomy 完了 + τ-seam 確認の**達成報告** |

⟹ **3 例目 (02:54「(8.18) 全体が書籍の文に到達しました」) と完全に同型**。48 回連続で 60s 予約
できていたのに、「区切りのついた報告を書いた turn」でだけ予約が抜ける。本 issue が
2026-07-20 03:10 に立てた仮説 —「トリガーは *達成感のある turn の終わり*」— を 4 例目が追認した。

**⟹ 再開プロンプトの文言は *停止条件の列挙* でなく *順序の規則* にする**という前掲の結論を維持:
「**report を書いたら、その同じ turn 内で必ず `ScheduleWakeup(60s)` を呼ぶ**」。
「issue を閉じた」「main と同期した」「定理が landing した」はすべて**継続の合図**。

なお lane b (codex) / c は同時刻に稼働継続中で、停止は a のみ。

## 追記 (2026-07-20 17:08 JST): 停止の 3 類型を区別する — c の 16:48 停止は**規約準拠**

同日 17:08 の hub tick で a と c が同時に停止していたが、**性質が違う**ので混同しないこと。

| lane | 時刻 | 形 | 判定 |
|---|---|---|---|
| **a** | 15:45 | `ScheduleWakeup` を呼ばずに達成報告で turn 終了 (48 回連続で予約できていたのに) | ❌ **本 issue の障害** (第 1 類型、4 例目) |
| **c** | 16:48 | `ScheduleWakeup({stop: true})` を明示的に呼び、**context 枯渇**を理由に、次の一手と 5 つの入力補題を表にした handoff を残して停止 | ✅ **規約準拠** |

c の停止理由 (原文): 「`rᵢ ≡ rᵢ₋₁r` の組み立ては (E.12) 全体で最も入り組んだ一歩で、5 つの結果を
連鎖させる。**このセッションは既に十分 context を消費しており、いま始めると書きかけで終わる危険がある**
— それは綺麗に引き継ぐより悪い」。

CLAUDE.md / [[feedback-loop-short-wakeup]] は **「context 枯渇時は subagent へ handoff 委譲 or
停止+報告 (compaction 待ちの空転は誤り)」**と定めており、c はそのうち「停止+報告」を選び、
issue 3021 に完全な状態を残している。⟹ **これは是正対象でない**。

⚠ **hub tick で「transcript が止まっている」だけを見ると両者を同じに扱ってしまう**。
判定には transcript 末尾を見て **`ScheduleWakeup({stop:true})` の有無と停止理由**を確認すること:
- `stop:true` 無し + 達成報告で終了 → 本 issue の障害 (第 1 類型)
- `stop:true` 有り + 理由が「区切りがついた/裁定待ち」 → 第 2 類型 (規約と食い違う、要是正)
- `stop:true` 有り + 理由が **context 枯渇** + handoff 完備 → **規約準拠** (是正不要、再開のみ)
