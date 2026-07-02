# cron monitor — 稼働状態メモ (away 対応)

> ⚠ **STALE (注記 2026-07-02)**: 2026-06-12 away 対応メモ。現行の監視手順・ペース (7,22,37,52)・
> レーン構成 (a/b/c) は [`merge_monitor.md`](merge_monitor.md) が正本。

> このセッション (main 合流モニター) の cron/監視まわりの現状。ユーザー離席中の判断を文書化。
> 次に起きたエージェント (自己起床 / 次 tick / ユーザー復帰) はまずここを読む。

## 現況 (2026-06-12 夕方更新: 3 レーン体制 B+F+G)

- **レーン再設計 (ユーザー裁可)**: **G (`bg-s13`, BG §13 Prime Action) 新設** → 3 レーン体制。
  worktree `/home/ywr/odd-order-bg-s13` 配置済み (symlink + olean warm-start 546M コピー済み、
  LAUNCH.md 配置済み、issue base **8000**)。G は §12 未証明分 (12.13-12.16) を S12_E の sorry'd
  statement 引用で賄う (新規 forward axiom 不要; F の proof 着地で自動 unconditional 化)。
  **G は S12_E 編集禁止** (F の active ファイル) — cron ゲートにも組込み済み。
  F の LAUNCH.md から §13 を G 管轄へ付け替え済み (F は §12 完結で STOP → §14 は再判断)。
- **現役 cron = `71a627ea`** (3 レーン版: F→G→B、S12_E ガード付き)。
  ⚠ **先代 `a637e8ce` は `/model` なしでも消滅していた** (CronDelete が "No scheduled job")。
  session-only cron は /model 以外 (ユーザー interrupt?) でも死ぬ模様 — **ユーザー対話のたびに
  CronList で生存確認するのを標準動作とする**。durable 化 (CronCreate durable:true =
  scheduled_tasks.json 永続) は別セッション起動の副作用があるためユーザー判断待ち。
- **hub 凍結窓タスク ✅ 完了 (2026-06-12)**: S10_HallStructure → Core(1373)+本体(952)、
  S10_BetaRadical → Core(1177)+Global(563)+本体(1321) の prefix-split 実施
  (module 名不変・下流 import 不変、root closure は chain 経由)。BetaRadical 側は cross-file
  化した 3 補題を public 化+改名 (`exists_sylow_subgroupOf_of_le` /
  `conj_smul_eq_self_of_mem_setNormalizer` / `isUniquelyMaximal_of_le_of_lt_top` — 元名は
  他ファイルの private 複製と衝突 [LocalLemmasCore で実衝突を build が検出])。
  ⚠ 知見: 同名 private 複製が repo に多数 (例 `mem_normalizer_of_conj_smul_eq` 系 17 ファイル) —
  de-private 時は **必ず全 hit を truncation なしで** 確認し、衝突時は trio 内改名が正手。
  grep の部分文字列偽陽性 (`…_of_le_inf_…`/`…_eq_self`) にも注意 (`\b` 境界で照合)。
  (0063/0064 は完了済みを実地確認 — 下の旧記述は stale)。

## 旧現況 (2026-06-12 午前, 参考)

- **新セッション開始時、前セッションの session-only cron は消滅していた** (CronList = "No scheduled jobs.")。
  session-only cron は Claude セッション終了で死ぬので、**セッションが切れたら必ず再作成が要る**。
- **現役 session-only cron = `a637e8ce`** (`2,17,32,47 * * * *`, 15分, F→B 自動合流 +
  MERGE_HEAD ガード内蔵 + 合流時 push)。CronList で 1 本のみ確認済み。
  (歴代 job: `297aecb0` → `d87f439a` → `a8824a71` → `11a96c38` → **`a637e8ce`**。前 4 つは失効)
- **🚨 GOTCHA: `/model` 切替で session-only cron が消える (2026-06-12 15:xx 実害)**: `11a96c38` は
  多数 tick を正常発火していたが、ユーザーが `/model` を 2 往復 (Fable5⇄Opus) した直後に CronList が
  **空** ("No scheduled jobs.", output drop ではない) を返した。session-only cron は in-memory ゆえ
  `/model` のセッション再初期化でクリアされる。**対策: `/model` 切替後は必ず CronList で生存確認し、
  消えていれば即再作成**。気づかず放置すると監視が無音停止する。`11a96c38` → `a637e8ce` で再作成済み。
- **⚠ コンパクト化で監視自身が混乱しうる**: 2026-06-12 15:xx、コンパクト化で可視文脈が `d4d712f8`
  までに縮み、その後 (06-12 11:xx) の自分のマージ群 (Cor 12.10〜Thm 12.12, Pf (4.8)/(2.1)) と cron
  `11a96c38` が「見覚えのない別セッションの仕事」に見え、並行セッションを誤疑した。**教訓: HEAD が
  自分の可視履歴より先でも、まず「自分のコンパクト済み作業」を第一候補に**。git reflog の連続 merge は
  単一監視の足跡。並行を疑う前にユーザーに確認。
- **durable (scheduled-tasks) は未登録**: `list_scheduled_tasks` = 空。cloud 実行で worktree アクセス
  不明の懸念が未解消ゆえ当面 session-only で回す。真の away (セッション終了) 耐性が要るならユーザー判断で durable 化。
- **この tick の合流実績 (2026-06-12 初回)**: F (bg-s12) 2 commits (Cor 12.10 COMPLETE + 新 leaf
  S12_Corollary1210 548行) → merge `d7a0bbe5`。B (b-peterfalvi) 未マージ 0 (変化なし)。
  build 3783 jobs green / AxiomsCheck OK / 実 sorry 256→255 (−1) / 新規 axiom なし /
  root closure OK / サイズ flag なし (最大 touched = S12_E 1005行)。`git push origin main` 成功 (`d4d712f8..d7a0bbe5`)。
- **未処理 size flag（§10/§5 大型ファイル分割 backlog の集約）**: §10 凍結ファイル群が複数 1,500 行超。
  いずれも frontier でなく lane work による bloat でもない（§12 から呼ぶための private→public 昇格等の
  小改変で touch されているだけ）ので urgency 低 → 個別 issue 乱立を避け **ここに集約記録**:
  - S10_LocalLemmas 2364 行 → issue **0063**（既起票）
  - S05_NarrowPGroups 4039 行 → issue **0064**（既起票）
  - S10_HallStructure 2290 行 → 未起票（記録のみ）
  - S10_BetaRadical 3004 行 → 未起票（記録のみ、2026-06-11 tick で検出）
  ユーザーが §10/§5 分割 batch を望むなら 0063/0064 と合わせて hub が凍結境界で実施。
  S08_CoherenceCore 11659→11820 行は B 現役 (6.8) frontier ゆえ分割保留。

## 確定事実

- **session-only 系 (CronCreate / CronList / ScheduleWakeup) はこの環境で結果出力が落ちる**
  (`Tool ran without output` だが `provided no error`)。登録の確証が取れない。連打しても無駄。
- **`scheduled-tasks` MCP は結果が返る** (実績: `list` が「No scheduled tasks found」を返した)。
  → 離席中の自律監視は **`scheduled-tasks` 系に一本化**するのが正解。
- send_message はこのセッションで使用不可 (`not available in the current context`)。
  → レーンへの一押しはコピペ運用 (memory: lane-nudge-via-copypaste)。

## 試行と未確証

- `scheduled-tasks` の `create_scheduled_task` で **durable monitor タスク** を作成試行
  (schedule `9,39 * * * *` = 30分間隔, prompt = merge_monitor.md 準拠の F→B 自動合流 +
  「火事のときのみ通知」)。**結果が pending/空で成否未確証**。
  - ⚠ ツール名: ToolSearch は `create` を `list` と同名で誤ラベルした (registry の癖)。
    正式名 = `mcp__scheduled-tasks__create_scheduled_task` (deferred リストにある)。
  - ⚠ worktree アクセス: scheduled-tasks の agent が別セッション。`/home/ywr/odd-order` に
    アクセスできるか不明。タスク prompt の step1 で「アクセス不可なら無害終了」を仕込んだので、
    初回実行で判明する。cloud 実行でアクセス不可なら別手段 (ローカル session-only) が要る。

## 次に起きたときの手順 (連打禁止・1確認のみ)

1. `mcp__scheduled-tasks__list_scheduled_tasks` を **1回**呼ぶ。
   - durable monitor が登録されていれば → 正常。何もしない (火事なら imessage)。
   - 空なら → `create_scheduled_task` を **1回**で再作成 (上記 schedule/prompt)。
2. 各レーン未マージを git で1回確認: `git -C /home/ywr/odd-order rev-list --count main..b-peterfalvi`
   と `..bg-s12`。溜まっていれば merge_monitor.md 手順で F→B 自動合流。
3. ユーザー復帰時のみ一行リマインド。離席中は記録だけ、火事以外 ping しない。

## ユーザー方針 (2026-06-11, 5回強調 + away 設定)

「cron はうまく行ってるか、ときどき監視してね。きちんと『ときどき』たまにみるのがコツ。リマインドして」
= 離席中、**軽く1回・連打せず・たまに**確認し、状態を残す。質問・選択肢提示はしない。
(memory: cron-monitor-cadence-gentle)
