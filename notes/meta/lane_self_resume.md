# lane 自己復帰モニター — hub 判断待ち停止からの自動再開

> 導入 2026-06-23 (ユーザー裁可)。各 lane worktree の `LAUNCH.md` から参照される正本。
> main worktree (hub) = `/home/ywr/odd-order`。

## ⭐ 現行メカニズム: ScheduleWakeup ポーリング (推奨、2026-07-02 ユーザー裁可)

**hub 判断待ち / 上流 cite 待ちで停止したら、`ScheduleWakeup` で ~10 分 (600s) 間隔の自己ポーリングを
arm する** (旧 cron 方式より優先)。理由:

- **`/model` 切替に頑健** — ScheduleWakeup は harness の loop 機構でモデルを直接再起動する。cron
  ([[cron-dies-on-model-switch]]) と違い消えない (起動時 re-arm 不要)。
- **cite 待ちも対象** — 旧 cron トリガ (LAUNCH.md 変化 / issue closed) に加え、**「上流レーンの lemma
  が sorry-free 化して cite 可能になる」cite 待ち**もポーリングで拾える (旧方式は cite 待ちを除外して
  いたが、ScheduleWakeup 方式では毎発火で `git merge main` して upstream landing を確認する)。

**手順** (lane が「hub 判断待ち / 上流 cite 待ちで停止」と決めたとき):
1. `ScheduleWakeup(delaySeconds: 600, prompt: <下記テンプレ>, reason: <何を待つか>)` を arm。
2. 1 行「hub 判断待ち / cite 待ちで停止、ScheduleWakeup(600s) arm (待機対象=…)」を残して待機。
3. **発火時** (harness が prompt でモデル再起動): 下記テンプレに従い解決判定 → 解決なら engage / 未解決
   なら **同 prompt・delaySeconds=600 で ScheduleWakeup を再 arm** して待機継続。

**ScheduleWakeup prompt テンプレ**:
```
<lane> 待機ポーリング (10分間隔 wakeup, 待機対象=<hub issue N の裁定 / 上流 lemma X の sorry-free 化>)。
起動時に必ず先に cd <path> && git merge main --no-edit で同期。
解決判定: (a) 待機 issue に hub 応答/裁定が追記 or issues/closed/ へ移動、(b) LAUNCH.md 変化、
(c) 上流 leaf が landing (cite 対象が sorry-free / 新 shared-infra leaf 出現)。
いずれか成立→ 割当に従い genuine work を engage。未成立→ 無駄な churn (marginal forward-build/scaffold)
をせず、同 prompt・delaySeconds 600 で ScheduleWakeup 再 arm して待機。
```

**⚠ 限定発動は不変**: 本ポーリングも「投機的な新規作業を作らない」原則を守る (下記「限定発動」節)。
発火して未解決なら**何も作らず**再 arm するだけ。**間隔 = ~10 分 (600s)** がユーザー永続方針
(裁定・upstream landing は分〜十分オーダーで変化; prompt cache TTL=5分を跨ぐが responsiveness 優先)。

> 以下は旧 cron 方式 (2026-06-23〜、~5 分)。ScheduleWakeup が使えない状況の fallback として残置。

## 目的と適用範囲

lane が **hub に判断をあおいで停止** (= HUB 宛 issue を起票して hub の解決を待つ) したとき、
ユーザーの手動再起動を待たず、hub の解決を検知して**自動再開**する仕組み。

**⚠ 限定発動 — これは「自律 work-loop」ではない**: 2026-06-18 に停止した lane 自律 /loop
([[lane-autonomous-loop-policy]]、「frontier で投機的に仕事を作り続ける」ループ) とは**別物**。
本モニターは **(1) hub の判断が無いと進めず停止した場合のみ** arm し、**(2) 既に割当済みの仕事を
unblock 後に再開するだけ** で、**投機的な新規作業は一切作らない**。条件不成立なら何もせず idle に戻る。
通常の作業継続・次タスク選択には使わない。

## 復帰トリガ (限定、ユーザー選択 2026-06-23)

hub の解決は次のいずれかで main / worktree に現れる。**どちらか成立で「解決」**:

- **(a) 自分の `LAUNCH.md` の内容が変化** — hub の handoff / 再割当は LAUNCH.md 直接更新で行う
  (例: 2026-06-23 relane で lane-c/lane-h の LAUNCH.md を hub が書き換えた)。LAUNCH.md は
  git-excluded だが `git hash-object LAUNCH.md` で内容指紋を取れる。
- **(b) 起票した HUB issue が `issues/closed/` へ移動** — hub が issue を解決すると `git mv` で
  closed/ に移す。main ref は全 worktree 共有ゆえ `git ls-tree main issues/closed/ | grep -q "<N>-"`
  で検知 (fetch 不要)。

> cite 待ち (例: lane-c (9.8)-(9.11) が lane-b char 待ち) のような「issue を立てずに上流 lemma の
> sorry-free 化を待つ」ケースは**本トリガに含めない** (ユーザー選択は限定トリガ)。その場合は通常どおり
> STOP + notes/issue で報告し、hub が解決 = issue close すれば (b) で拾える。

## 停止時の手順 (lane が「hub issue を起票して待つ」と決めたとき)

1. baseline を控える:
   ```bash
   BASE=$(git hash-object LAUNCH.md)   # 当時の LAUNCH.md 指紋
   N=<起票した HUB issue 番号>          # 例 4007
   ```
2. resume-monitor cron を**自セッションで** arm (CronCreate, recurring, **だいたい 5 分間隔**
   `2-59/5 * * * *` = :02/:07/…/:57、:00・:30 と hub の :07/:27/:47 を概ね避ける; ユーザー指示 2026-06-23
   永続方針 = hub に判断を移譲して停止したら ~5 分 timer で素早く自動復帰)。prompt は下記テンプレに
   `<path>`/`<BASE>`/`<N>` を埋める。(注: 5 分は prompt cache TTL 境界ゆえ各発火は概ね cache-miss だが、
   hub 解決を速く拾う優先でこの間隔を採用。)
3. 1 行「hub 判断待ちで停止、自己復帰モニター arm (cron <id>, issue <N>)」を残して idle。

### resume-monitor cron prompt テンプレ
```
自己復帰チェック (hub 判断待ち, issue <N>, baseline LAUNCH.md=<BASE>, worktree=<path>)。
⛔ ガード: 既に作業再開済み (このセッションで新しい作業を始めている) なら何もせず終了。
1. cd <path>。解決判定:
   (a) `[ "$(git hash-object LAUNCH.md)" != "<BASE>" ]`  # LAUNCH.md 変化
   (b) `git ls-tree main issues/closed/ 2>/dev/null | grep -q "<N>-"`  # issue closed on main
   どちらか成立 → 「解決」。
2. 未解決 → 「hub 判断待ち継続 (issue <N>)」1 行で即終了 (何もしない、次発火を待つ)。
3. 解決 →
   (i)  `git merge main` で hub の変更を取込 (コンフリクトは自所有なら解決、他レーン由来は notes/issue で hub へ)。
   (ii) LAUNCH.md を再読し新割当・hub の指示を把握。
   (iii) `CronList` でこの resume-monitor job を特定し `CronDelete` (自己停止)。
   (iv) 新割当に従い作業再開。サマリに「自己復帰 (issue <N> 解決)」を 1 行。
```

## 起動時 re-arm

cron は session-only + `/model` 切替で消える ([[cron-dies-on-model-switch]])。セッション開始時に:
- まだ「hub 判断待ち」状態 (起票 issue が `issues/` 直下に open かつ LAUNCH.md が当時のまま) なら → **再 arm**。
- 既に解決済 (LAUNCH.md 更新済 or issue が closed/ に在る) なら → arm せず**直接再開**。

## hub 側への含意 (注記)

lane が自己復帰すると `git merge main` で hub の変更を取り込み、割当に従い作業 → commit → 次の hub
merge tick で通常合流される。**hub の合流手順は不変** (lane の自己復帰は通常の作業再開と区別不要)。
hub は単に「停止していた lane が自走で戻ってくることがある」と認識すればよい。
