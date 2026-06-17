# レーン自律 loop ポリシー — LAUNCH.md 駆動の `/loop` 自己選択

> 横断運用ドキュメント。各 worktree の `LAUNCH.md`（git-excluded）冒頭にある
> **「▶ LOOP GATE」ブロック**から参照される正本。**ハブは他セッションに loop を注入できない**
> （`send_message` は承認必須かつ unsupervised モードで不可、[[cross-lane-sync-via-notes]]）。
> ゆえに「いつ loop に入るか」の判断を**この手順 + 各 LAUNCH.md の現在 VERDICT に外在化**し、
> **各レーンが起動時に自分で評価して `/loop` を選ぶ**。ユーザー意図 (2026-06-17):
> 「LAUNCH.md に記述があって、各レーンがタイミングに応じて自律的に loop を選択肢に入れられる」。

## 役割分担

- **各レーン（worktree セッション）**: 起動直後に自分の `LAUNCH.md` の「▶ LOOP GATE」を読み、
  下の判定で **`/loop`（自己ペース）に入るか / 単発で 1 ステップ進めて停止するか**を自律的に選ぶ。
- **ハブ（main セッション）**: merge tick ごとに各レーンの gating を実コードで見直し、
  各 LAUNCH.md の **VERDICT 行を更新**する（[`merge_monitor.md`](merge_monitor.md) の手順に統合）。
  loop に入れるのはレーン自身、入ってよいかの**判定材料を最新化するのがハブ**。

## レーンの自己判定手順（起動時に評価）

### ENTER LOOP — 次がすべて真なら `/loop`（interval 省略 = 自己ペース）に入る

1. LAUNCH.md「現在地 + 次作業」に、**ungated で leaf-build-green 判定可能な具体的 obligation**
   （sorry / named residual）が**少なくとも 1 つ**ある。
2. その obligation が **新規 `axiom` / forward-dep / 他レーン所有ファイルの編集**を要しない。
3. それが**他レーンの未 `sorry` 解消 statement / sorried interface を consume しない**
   （cite する識別子は grep して「proved（body に sorry 無し）」を確認 — 散文の楽観を信じない）。
4. 直近の自分のコミットから**同一 obligation で 3 周以上空転していない**。

→ 該当: `/loop`。外部ゲート無しの連続作業なので wakeup は短く（60s 即再開、[[feedback-loop-short-wakeup]]）。
   **各周回の型**:
   1. 次の sorry / obligation を **1 つだけ**前進させる（難所は sorry 退避でなく正面突破、[[feedback-no-avoiding-hard-parts]]）。
   2. `lake build <develop leaf>` が green（leaf-build の stale-green に注意、節目で full build、[[leaf-build-stale-green]]）。
   3. feature 単位で commit（build-green を別ステップで検証してから、[[feedback-verify-build-before-commit]]；
      記号本文は heredoc、[[git-commit-heredoc-for-lean-symbols]]）。
   4. **STOP 条件を再評価**（下記）。真なら loop を抜ける。

### STOP / 入らない — いずれか真なら loop に入らず、1 ステップだけ進めて handoff し停止

- **gate**: 次作業が他レーンの sorried statement / BG↔Pf interface に gated（このレーンでは閉じられない）。
- **depletion**: ungated leaf を出し尽くし、残るは gated assembly のみ。
- **decision**: 教科書の行間で詰まり、設計判断 or ChatGPT 相談が要る（[[feedback-ask-chatgpt-for-elided-gaps]]、
  最強モデルで [[feedback-chatgpt-use-strongest-model]]）。
- **impasse**: 同一 obligation で空転（型詰まり / API 不明）。諦めでなく原因究明へ切替の合図
  （[[feedback-no-avoiding-hard-parts]]）。それでも閉じないなら停止して報告。

→ 該当時: LAUNCH.md の現在地 + ハンドオフ note を更新し、抜けた理由を 1 行残して停止。
  ハブが merge tick で検知し、必要なら VERDICT を更新 / ユーザーに thumbs-down 報告
  （[[feedback-flag-poor-progress]]）。

## 各 LAUNCH.md に置く「▶ LOOP GATE」ブロックの形

LAUNCH.md の**最上部**（現在地ブロックの直前）に固定見出しで置く。レーンがハンドオフで本文を
書き換えても、この見出しと VERDICT 行は保つ。テンプレート:

```markdown
## ▶ LOOP GATE（起動時に自己評価 — 判定手順 = notes/meta/lane_loop_policy.md）
- **VERDICT**: <LOOP | LOOP_THEN_STOP | STOP>  （hub 更新: YYYY-MM-DD）
- **objective**: <loop で回す具体的 obligation（file:line + Lean 識別子）>
- **develop leaf**: `lake build <module>`
- **stop when**: <この loop を抜ける条件 = gate / depletion / decision / impasse の具体形>
- **gates / 注意**: <consume してはいけない sorried statement、編集禁止ファイル等>
```

VERDICT の意味:
- **LOOP** — ungated runway が明確。起動したら `/loop` に入って自走してよい。
- **LOOP_THEN_STOP** — ungated leaf は残っているが既知の gate が先にある。depletion まで loop、その後停止。
- **STOP** — 次の item が既に gated / 要判断。loop に入らず 1 ステップ進めて報告（or 待機）。

## 注意

- VERDICT は**ハブが merge tick で実コードに照らして更新**する（散文ベースでなく、cite 先の sorry 有無を grep）。
  レーンは VERDICT を**判定材料**として使い、起動時に上の手順で最終判断する（VERDICT と現場が食い違えば
  現場を優先し、抜けた理由を残す）。
- `/loop` は同一セッション内で自己 re-prompt する。**ハブはレーンの loop を開始も停止もできない**
  — できるのは VERDICT 更新と stall の検知・報告のみ。
- B の (6.8) §6 certain-type structure gap など**ユーザー直接管理のブロッカー**は STOP 扱いだが、
  merge tick での thumbs-down 対象外（[[merge_monitor]] 2026-06-17 メモ）。
