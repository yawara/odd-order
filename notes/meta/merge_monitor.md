# main 合流モニター — a/b/c/d レーン自動合流の運用手順

> 横断運用ドキュメント。**標準監視ペース = 15 分間隔** (cron `7,22,37,52 * * * *`、:00/:30 回避・15 分均等、ユーザー 2026-07-02; 2026-06-29〜07-02 は 30 分 `13,43`、それ以前は 15 分)。cron は session-only ([[cron-dies-on-model-switch]]; CronCreate `durable:true` は本環境で disk 永続せず session-only 扱い) ゆえ、**再作成時は必ずこのペース `7,22,37,52` で**作る。main worktree = `/home/ywr/odd-order`。
> ユーザー方針: **「検証通過は自動合流」** — build green + axiom-clean + sorry regression なし + 新 axiom なしを
> 満たすレーンを `--no-ff` で自動マージ。満たさなければ `git merge --abort` で報告。合流成立時は最後に
> `git push origin main`（変化なし/全 abort なら push しない）。
>
> **レーン配分の正本 = [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md)**
> (ゲートなし・signature contract 方式)。本ファイルは hub 側の合流手順 + gotcha 集。

> **🔀 一時 cross-lane carve-out (issue 8022, ユーザー裁可 2026-06-30)**: gate-2 の M̃-cover re-route は
> S10+S09+S14_MaximalI を build-green に一括必要な coupled 改修ゆえ、**lane d に S09/S14_MaximalI への一時
> cross-lane carve-out を付与**。⟹ step 1.5 で **lane d が `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
> (FrobeniusFamily/FamilyHypothesis71/G0) および `S14_MaximalI.lean` の `not_all_maximal_typeI`/`covers`
> を編集していても、issue 8022 の M̃-cover re-route の一環なら逸脱としない** (atomic 1 commit/branch で
> 来る前提)。hub は d のこの atomic 変更を一括合流 (S09/S14/S10 を含む大型 diff)。
> **a/b/c への要請** (notes 経由): 8022 land まで S09 FrobeniusFamily/FamilyHypothesis71・S14_MaximalI の
> `not_all_maximal_typeI` 周辺は編集を避ける (d の atomic 変更との衝突回避)。a の §9.9.b (S11)・b の §12 hB
> chain (S14 の別 decl)・c の §16 size bounds は通常継続可。8022 land 後に本 carve-out は解除。

> **✅ issue 0089 解決 (2026-06-30, ユーザー裁定 D=削除)**: `S07_RhoProjection.lean` は S09 `chiRho`
> 機構の完全重複ゆえ**削除済** (carve-out 0087 撤回)。(12.16) path は S09 `chiRho`/`Hypothesis78`/
> `NormEstimates` を cite。旧 HOLD は解除。
> ⚠ **re-sync lag**: lane b の branch には**削除前の** S07_RhoProjection がまだ残存しうる (b が
> `git merge main` で削除を取り込むまで)。⟹ 3-dot `main...b` に `S07_RhoProjection.lean` が出ても、
> それが「b が削除前から持っている残存」(= b の commit は S07 の**新規宣言追加でない**) なら**逸脱でなく
> 『b: S07 削除の re-sync 待ち』として skip**。b の non-S07 .lean 実作業のみ通常合流。b が**削除後に
> S07 を新規再作成**した場合のみ逸脱。判定: `git log main..b --no-merges` の commit が S07 への新規宣言
> 追加か (= 再作成) / 既存 S07 への追記止まり (= 残存) か。混在・不明なら skip+報告。

## レーン (2026-06-28 再配分: 4 レーン a/b/c/d)

| lane | branch | worktree | クラスタ | 主所有 .lean | issue base |
|---|---|---|---|---|---|
| **a** | `a` | `odd-order-a` | α Pf §10–13 中央指標核 (bare spine sorry 11.8) | `Peterfalvi/S(0[3-9]|1[0-3])*` + `FeitThompson.lean:426` | 1000 |
| **b** | `b` | `odd-order-b` | β Pf §12 Dade tower (12.16) | `Peterfalvi/S14_MaximalI.lean` (carve-out 0087=S07_RhoProjection は issue 0089 で削除済) | 2000 |
| **c** | `c` | `odd-order-c` | γ POLE-2 §14–16 下流 (最長 pole) | `Peterfalvi/{S15_SAndT,S16_NonExistenceG}.lean`（**S15_SAndT_Setup は 2026-07-01 に lane d へ移管, issue 0092**）| 3000 |
| **d** | `d` | `odd-order-d` | γ 上流 §15 setup (2026-07-01 再配分) + δ BG §14–16 (dormant) | `Peterfalvi/S15_SAndT_Setup.lean` (主) + `BG/**` + `FeitThompson.lean` carrier 宣言 | 4000 |

**signature-first interface (ゲートは幻)**: 上流が sorried signature を export → 下流が cite。各レーンは独立クラスタを
正面から埋め、cross-cluster は signature contract で媒介 (待たない)。詳細 = ft_lane_reallocation_2026_06_28.md。

**取り決め**: (1) 各レーンは**自所有ファイルのみ編集**、他は cite (要望は notes/issue 経由)。
(2) **新規 `axiom` 宣言は abort + ユーザー承認**。(3) **起動時 main 同期** = `git merge main` (3-way、`--ff-only` 禁止)。
`lake update` 禁止。コミットは main のみ。マージ順 = **a → b → c → d** (独立ゆえ形式的)。

**🧭 方向性・cross-lane 判断は HUB 宛 issue 起票 → hub 解決** (title に "HUB:" 冠、選択肢明記)。hub は各 tick で
新 HUB issue を別枠報告し解決 (read-only 監査 + 必要ならユーザーへ)。軽微な signature 不足通知は notes でよい
([[cross-lane-sync-via-notes]] の上位版)。**🔁 lane 自己復帰**: lane が hub 待ちで停止しても自走再開しうる
(hub の合流手順は不変、lane の自己復帰は通常の作業再開ゆえ区別不要)。

## 各イテレーションの手順

> **⛔ 問題発生時はループ停止（ユーザー方針 2026-06-22, 永続）**: 下記のいずれかが起きたら、
> 進行中マージを `git merge --abort`（**冒頭ガード = 他マージ進行中の場合を除く**）し、
> **`CronList` で監視 cron の id を確認 → `CronDelete` でその場で停止** + 問題内容を明示報告し、
> **以降のレーン処理・次 tick を行わない**（ユーザーが解消・再開指示するまで待つ）。黙って次 tick で
> 同じ問題を繰り返さない。**問題 = ** build 失敗 / 内容コンフリクト（AxiomsCheck.lean・OddOrder.lean
> の独立追記**以外**）/ sorry regression（証明済→sorry）/ 新規 `axiom` / push 失敗 / 想定外の git 状態
> / **レーン範囲逸脱（下記 step 1.5 = 自所有外の Pf/BG S-ファイルを編集; ユーザー方針 2026-06-22）**。
> **非問題（通常継続）= ** 「変化なし」/ 新 decl の faithful scaffold sorry 増 / 独立追記コンフリクトの両保持解決
> / 共有ファイル編集（AxiomsCheck.lean 追記・OddOrder.lean import・`OddOrder/GroupTheory/**`・`OddOrder/Mathlib/**` 共有 infra・notes・issues）。
>
> **♻ 問題解決後はループ自動再開（ユーザー方針 2026-06-23, 永続）**: 上記 ⛔ で停止した監視ループは、
> **問題が解決したら必ず再開する**。具体的には: (a) 停止した問題（build 失敗 / コンフリクト / sorry
> regression / 新規 axiom / push 失敗 / 想定外 git 状態 / レーン範囲逸脱）が、**ユーザーの指示か hub の
> 修正で解消したことを確認したら**、(b) **監視 cron を `CronCreate` で再作成し**（停止時に `CronDelete`
> したものを復活）、(c) 通常の tick に復帰する。「停止しっぱなし」にしない。再開時はサマリに
> 「監視ループ再開（cron id <new-id>）」を 1 行記録する。**この stop→resolve→resume サイクルが監視ループの
> 正規ライフサイクル**であり、停止は一時退避でしかない。

> **🔒 レーン所有マップ (step 1.5 範囲逸脱チェック用、2026-07-02 3 レーン再編 a/b/c、lane d 退役)**:
> 正本 = [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md)。
> | lane | クラスタ | 所有 .lean（これ以外の Pf/BG S-ファイル編集 = 逸脱→停止） |
> |---|---|---|
> | **a** | α Pf §10–13 中央指標核 + σ-theory tail | `OddOrder/Peterfalvi/S(0[3-9]|1[0-3])*` + `OddOrder/FeitThompson.lean`（:426 + 旧 d carrier 宣言群 = 全体、d 退役で fold）+ **S10 bgTheoremE carrier**（旧 carve-out 0086 解消）+ σ-theory tail (S11 imprimitivity + dup retire は S11 内、GroupTheory/** 共有で cite) |
> | **b** | β Pf §12 Dade tower + coherence infra | `OddOrder/Peterfalvi/S14_MaximalI.lean`（**全体**、旧 carve-out 0088 `exists_typeICovering` は b に解消）+ **coherence infra** = `S07_Coherence*`/`S08_PGroupReduction`（既存 coherence file、(5.7)/(6.5.c)/(6.8) case-B 系、hub authorized 2026-07-02）+ GroupTheory/** coherence leaf。⚠ これらは nominal に a の `S0[3-9]` regex に掛かるが **coherence infra ゆえ b 担当（逸脱でない）**、a の active territory は §9-13 char 核で S07/S08 coherence は非接触 |
> | **c** | γ POLE-2 §15–16 chain 一本化 | `OddOrder/Peterfalvi/{S15_SAndT_Setup, S15_SAndT, S16_NonExistenceG}.lean`（**S15_SAndT_Setup は 2026-07-02 に lane d→c、§15→16 全 chain を c が所有**）+ 構成的 Clifford (issue 9002、GroupTheory/** shared) |
> | **~~d~~ 退役** | — | **2026-07-02 退役**。σ-theory leaf (`GroupTheory/**`, sorry-free) は共有ゾーンに残置 (a が tail 完成)。BG/** は完了・共有凍結。FeitThompson carrier は a に fold。**branch `d` は git に温存 (作業は全 merge 済)、worktree セッションは停止**。 |
> | **共有（全 lane 可）** | — | `OddOrder/AxiomsCheck.lean` / `OddOrder.lean` / `OddOrder/GroupTheory/**` / `OddOrder/Mathlib/**` / `OddOrder/Algebra/**`（全 lane 加算可）/ **`OddOrder/FeitThompson.lean`**（d 退役で主に a、宣言境界で衝突回避）/ `OddOrder/BG/**`（完了・共有）/ `notes/**` / `issues/**` |
>
> **carve-out (issue 0086, ユーザー裁可 2026-06-29)**: `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` は
> 原則 lane a 所有だが、その中の `BGTheoremECoverData` 構造 + `BGTheoremETypeICovering` / `BGTheoremENonTypeICovering` +
> **`bgTheoremE_cover_data`** 定理 (BG Theorem E carrier, Pf 8.17、b/c/d 共有 consumer) は **lane d 所有**として扱う。
> ⟹ **step 1.5 の範囲逸脱チェックで、lane d が S10 のうちこれら carrier 宣言**「のみ」**を編集している場合は逸脱としない**
> （S10 のそれ以外を lane d が編集したら逸脱; lane a が carrier ブロックを編集したら逸脱）。判定が曖昧なら
> `git diff main...d -- …S10…` の hunk が line 493–570 周辺の carrier 宣言に限るか確認。恒久解（現状維持 or lane d
> ファイルへ移設）は issue 0086 で追跡。
>
> **carve-out (issue 0087, ユーザー裁可 2026-06-29) — ❌ 撤回済 (issue 0089, 2026-06-30)**:
> `OddOrder/Peterfalvi/S07_RhoProjection.lean` は lane b 所有として導入されたが、S09 `chiRho` 機構の
> 完全重複と判明し**削除済** (issue 0089, ユーザー裁定 D)。以後この carve-out は無効。lane b が
> S07_RhoProjection を再作成したら逸脱。
>
> **carve-out (issue 0088, ユーザー裁可 2026-06-29)**: `OddOrder/Peterfalvi/S14_MaximalI.lean`（原則 lane b）の
> うち **`exists_typeICovering` 定理（line 2639–2798、(8.17.a) type-I covering）の carrier-consumer 部分**は
> **lane d 所有**として扱う。理由: この定理は lane d 所有の S10 carrier `BGTheoremECoverData` /
> `BGTheoremETypeICovering`（carve-out 0086）を直接 consume するので、carrier API の変更
> （例: `thickenedA1`→`cover`, `thickenedA1_card`→`cover_card`, `cover_subset_kernels` 追加）が
> 必然的にこの定理に波及する。⟹ step 1.5 で **lane d が S14_MaximalI のうち `exists_typeICovering`
> のみ**を編集している場合は逸脱としない（S14_MaximalI のそれ以外を lane d が編集したら逸脱; lane b が
> `exists_typeICovering` の carrier-consumer 部分を編集したら逸脱）。判定が曖昧なら
> `git diff main...d -- …S14_MaximalI…` の `@@` hunk が全て `theorem exists_typeICovering` 文脈
> （line 2639–2798）に収まるか確認。恒久解（現状維持 or carrier-consumer を d ファイルへ移設）は issue 0088 で追跡。
>
> **carve-out (issue 0090, ユーザー裁可 2026-06-30)**: `OddOrder/Peterfalvi/S09_CertificateDischarge.lean`
> （lane b が新規作成、§7 (7.7.a) の CF(L,A) spanning 基盤 = S09 の opaque `chiRho_decomp` certificate を
> discharge する欠落インフラ、genuine・非重複と hub 検証済）はファイル名が lane a の S09 namespace
> パターンに掛かるが **lane b 所有**として扱う。⟹ step 1.5 で **lane b がこのファイルを編集していても
> 逸脱としない**（lane a がこのファイルを編集したら逸脱; lane b が他の S09 ファイル＝
> `S09_NonexistenceCertain.lean` 等を編集したら逸脱）。lane b は別ファイル隔離ゆえ lane a の S09 本体と
> 衝突しない。恒久解（現状維持 / `S07_*` rename / S09 統合）は issue 0090 で追跡。
1. 各レーンの未マージ確認: `git log --oneline main..<branch>`。
   **全レーン 0 なら「変化なし」1行報告で即終了**（build を走らせない）。
1.5. **レーン範囲逸脱チェック（ユーザー方針 2026-06-22, 永続）**: 未マージがあるレーンについて、
   **マージ前**に**そのレーンが実際に変更したファイル**を取得し、上記 🔒 所有マップに照らす。
   **⚠ 必ず 3-dot `main...<branch>`（merge-base からの branch 側差分）を使う** — 2-dot `main..<branch>`
   は端点差分で「レーンが main に遅れている分（他レーンの merge で main 側だけ進んだ S05/S06/S11 等）」を
   **誤検出**する（line 192 の罠と同根; 2026-06-22 実害 = lane-f/b が 2-dot で false-positive 逸脱判定）。
   **自所有でも共有でもない `.lean`（典型: 他レーンの Pf/BG S-ファイル）を含むなら範囲逸脱** → そのレーンは
   **マージせず（trial merge も開始しない）**、⛔ に従いループ停止（abort 不要 = まだ merge していない、
   `CronDelete` + 報告 + 以降の tick を行わない）。報告には逸脱ファイル名 + lane + 所有者を明記。例 (lane=$b):
   ```
   owned_re='^OddOrder/Peterfalvi/S(0[3-9]|1[0-6])|^OddOrder/BG/|^OddOrder/FeitThompson'  # 全 Pf S03-16 + BG を許容; per-lane 厳密判定は 🔒 マップ (a=S03-13/b=S14_MaximalI/c=S15-16/d=BG)
   shared_re='^OddOrder/AxiomsCheck\.lean$|^OddOrder\.lean$|^OddOrder/GroupTheory/|^OddOrder/Mathlib/|^OddOrder/Algebra/|^OddOrder/FeitThompson'  # GroupTheory/Mathlib/Algebra=汎用 infra (全 lane 加算可)、FeitThompson は a/d 共有
   git diff --name-only main...$b -- '*.lean' | grep -vE "$owned_re" | grep -vE "$shared_re" | grep . && echo "範囲逸脱 → STOP"
   ```
   逸脱なし（空）→ step 1.6 へ。共有ファイル・notes・issues のみの差分は逸脱でない。
1.6. **shared-infra 重複検出（claim-before-build 運用、ユーザー裁定 2026-07-01）**:
   `ft_path_policy.md` §0 policy 6 で、複数の gated レーンが同じ上流 shared infra
   （未所有 leaf `OddOrder/(Algebra|GroupTheory|Mathlib)/**`）を同時並行構築する重複を防ぐ。各 tick で:
   - **(a) 同一 leaf path の衝突**: 2 つ以上のレーンが**同じ新規** shared-infra `.lean` を追加していないか。
     ```
     for L in a b c d; do git diff --name-only --diff-filter=A main...$L -- \
       'OddOrder/Algebra/**' 'OddOrder/GroupTheory/**' 'OddOrder/Mathlib/**'; done | sort | uniq -d | grep . \
       && echo "shared-infra path 衝突 → STOP"
     ```
   - **(b) claim なしの新規 shared-infra leaf**: 新規追加された shared-infra `.lean` に対応する open 9000
     番台 claim issue が**無い**（`issues/9*-*.md` を grep）→ ⚠ flag（沈黙構築 = policy 6 違反の疑い）。
   - **(c) 同一 ref の 2 claim**: open 9000 番台 issue に同じ教科書 ref / 補題名の claim が 2 件 → STOP。
   検出したら **STOP + 報告**（より完成度の高い方を残し、他方を cite に rebase させる指示。浪費は ~1 tick に
   有界）。空 → step 2 へ。**grandfather**: 2026-07-01 前 landing 済 leaf（`GaloisRationalInteger.lean` 等）は対象外。
2. **a → b → c → d の順**で（独立レーンゆえ順序は形式的、上流→下流の自然順）、未マージがあれば自動合流:
   - マージ前の実 sorry 数を記録: `bin/count-sorry`
     （prose 偽陽性 [sorry-free / sorryAx / `sorry'd` / backtick 引用] を除外する判定器。
       旧 `grep '(^|[^a-zA-Z-])sorry'` は 259 と過大計上したが count-sorry は 146 ≈ 実 141。
       絶対数の ground truth は build 警告 `lake build OddOrder 2>&1 | grep -c 'uses .sorry.'`）
   - `git merge --no-ff --no-commit <branch>`
   - **コンフリクト時**:
     - `AxiomsCheck.lean` / `OddOrder.lean` の**独立追記衝突** = 両ブロック保持で解決して続行
       （A=keystone 系の `#assert_only_allowed_axioms`、B=Peterfalvi 系の同コマンドは別定理ゆえ両方有効）
     - それ以外・内容が絡む衝突 = `git merge --abort` で**報告**（自動解決しない）
   - **staged が全て `notes/` 配下なら build 省略**(Lean 不変ゆえ結果不変)し直接 commit へ。
   - **`.lean` を含む場合 — sorry 先行チェックで build 短絡**: build は重い (~3800 jobs) ので**先に**
     `bin/count-sorry` を取る。増えていれば `git diff --cached` で **regression か scaffold か**判定し、
     **regression（証明済→sorry）or 新規 axiom なら build せず即 `git merge --abort`**。
     scaffold（新 decl statement）or 不増なら `lake build OddOrder OddOrder.AxiomsCheck`(background, 完了待ち)へ。
   - **合格条件**（全て満たす）:
     - build exit 0 かつ最終行 "Build completed successfully (N jobs)"
     - AxiomsCheck OK（`#assert_only_allowed_axioms` 由来のエラーなし）
     - **sorry ポリシー（2026-06-15 改定: scaffold 許可, ユーザー裁可）**: `bin/count-sorry` の増加を即不合格にしない。
       hold するのは (a) **regression**（既存の証明済 decl が `sorry` に退化）と (b) **新規 axiom** のみ。
       **新 decl の faithful scaffold statement 追加（`theorem/lemma … := sorry`）は許可**（§13→§14→§16 interface-building の正常進行）。
       - 判定: count 増加時は `git diff --cached -- '*.lean' | grep -E '^[+-].*sorry'` を確認。
         追加 `+… sorry` が同 hunk の追加 `+theorem/+lemma`（=新 decl）に属すれば scaffold ⟹ **ALLOW**。
         既存 decl の proof が `+sorry` に置換（新 decl 行が伴わない）なら regression ⟹ **HOLD+報告**。
       - count-sorry は prose 偽陽性（sorry-free / sorryAx / `sorry'd` / backtick 引用）を除外済（残差 +5 は安定 prose）。
         絶対数 ground truth は build 警告 `uses .sorry.`。
   - 合格 → `git commit`:
     `Merge '<branch>' (<topic>): <要約>` + 本文に各単位 + 末尾
     `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
   - 不合格 → `git merge --abort` で**報告**（何が落ちたか・どのファイルか）
3. **新規 forward axiom を含む commit** (`axiom ` 宣言の追加を `git diff --cached` で確認) は
   自動合流せず abort → 報告（上記ポリシー）。
3b. **root closure 検査 (2026-06-11 追加, E の発見)**: 新規追加 `.lean` ファイル
   (`git diff --cached --name-only --diff-filter=A -- '*.lean'`) は **root closure から到達可能**
   でなければならない — `OddOrder.lean` に import 行があるか、closure 内の他 `.lean` が import
   している (例: hub の prefix-split で旧 module 名ファイルが新 Core を import する場合は追記不要)。
   どちらも無いと `lake build OddOrder` の対象外でゲートをすり抜ける (実例: S05b /
   S11_MsigmaANormal が closure 外で未検証だった)。孤立時 = hub が `OddOrder.lean` に import 行を
   追記してから build (機械的修正、abort 不要)。
4. **サイズ watch (粒度規約の enforcement, 2026-06-11)**: 合流後に
   `git diff HEAD^ --stat -- '*.lean'` で touched .lean の現在行数を `wc -l` 確認。
   **1,500 行超の既存ファイルへの追記**を検出したら: 合流は維持しつつ ⚠ flag をサマリに含め、
   分割 issue が未起票なら起票する（分割の実施 owner = hub。lane の frontier と衝突しない
   凍結境界で prefix-split する）。lane 側のデフォルト（新主結果番号 = 新 leaf）は LAUNCH.md に記載。
5. **push**: 合流 commit が 1 件以上成立していれば最後に `git push origin main` (exit 0 確認、
   失敗は報告)。変化なし/全 abort なら push しない。
6. **サマリ報告**: 各レーン {マージ済 N commits / コンフリクト abort / 待機 / 変化なし} + 未マージ残数
   + サイズ flag + push 結果。
7. **LOOP GATE VERDICT 維持 (2026-06-17 追加, [`lane_loop_policy.md`](lane_loop_policy.md))**: 各 worktree の
   `LAUNCH.md` 冒頭「▶ LOOP GATE」ブロックは各レーンが起動時に `/loop` を自己選択する判定材料。**毎 tick で
   再監査はしない** (重い)。代わりに、今 tick のマージが**他レーンの gate を解いた**ときだけ VERDICT を見直す:
   - `typeP_duality` (lane-h) が proved → G の conjunct 2/assembly + F の §16/POLE-2 が解禁 → G/F の VERDICT を
     `STOP`→`LOOP`/`LOOP_THEN_STOP` に更新しうる。
   - σ-gap (`C_M(Q)≤M_σ`, issue 8012) が proved → G の conjunct 3-5 が unconditional 化。
   - (6.8) capstone (`S08_CoherenceTheorems:59`) が閉じた → B を次タスクへ。
   判定 = マージ差分に上記 gate statement の `sorry` 除去が含まれるか。含まれれば該当レーンの LAUNCH.md VERDICT
   行を更新 (worktree LAUNCH.md は git-excluded ゆえ直接編集可・build 不要)、含まれなければ触らない。サマリに
   「VERDICT 更新: \<lane\> \<old\>→\<new\>」を 1 行。**新規レーン投入時や VERDICT が古い疑いがあれば** 単発で
   loop-readiness 監査 (read-only、frontier ファイル + cite 先 sorry 有無を grep) を回して VERDICT を引き直す。

## 注意

- A と B は `AxiomsCheck.lean` 末尾を共有 hotspot として両方追記 → **マージ毎にコンフリクトしうる**が、
  独立ブロック（別定理の axiom ガード）なので両保持で機械的に解決可。先頭 import 部も同様。
- `git merge --abort` は `--no-commit` で止めた状態でもコンフリクト状態でも有効。
- `lake update` 禁止（共有 mathlib rev を壊す）。コミットは **main のみ**。
- 各レーンの worktree (`/home/ywr/odd-order-<slug>`) には**触らない**（`git log main..<branch>` で読むだけ）。
- loop は同一セッション継続。マージ済みコミットは git が source of truth ゆえ状態ファイル不要
  （`main..<branch>` が毎回「まだ取り込んでいない分」を正しく返す）。
- **`git diff main..<branch>`（2-dot=端点差分）でマージ内容を判断しない**。各レーンは他レーンの成果を
  恒久的に持たない（例: B=b-peterfalvi は A=a-keystone の RepresentationTheory/Extraspecial 系を持たない）ので、
  端点差分は「他レーンファイルの大量削除」という**幻**を見せる（実測 4149 deletions に見えたことがある）。
  実マージは merge-base からの 3-way ゆえ、それらは「main 側のみ追加」扱いで保持される。マージ内容の確認は
  必ず `git merge --no-ff --no-commit` 後の `git diff --cached --stat`（=実際に staged される加算分）で行う。
  **step 1.5 の範囲逸脱チェックも同じ罠**: マージ前の「レーンが変更したファイル」は必ず 3-dot
  `git diff --name-only main...<branch>`（merge-base からの branch 側）で取る（2-dot だと遅れている分を誤検出）。
- **⚠ 3-dot でも "multiple merge bases" 警告時は誤検出しうる（2026-06-28 実害, lane-f が S11=lane-b 所有を逸脱と誤判定）**:
  レーンが `git merge main` を繰り返すと main↔lane 間に **merge base が複数**でき、`git diff main...<branch>` は
  その中から**1 つ（しばしば古い方）を自動選択**する（`warning: multiple merge bases, using <old-sha>` が出る）。
  古い base を選ぶと「その base 以降に main 側へ入った他レーンの成果」が branch 側差分に紛れ込み、**自所有外
  ファイル（例 S11）が逸脱判定に出る**。これは genuine 逸脱と見分けがつかないので、**即 STOP せず以下で誤検出を排除**:
  (1) **分岐元 merge-base との diff**: `git merge-base --all main <branch>` で全 base を出し、各 base に対し
     `git diff <base> <branch> -- <疑い file>` が **0 行**なら、そのレーンはそのファイルを**一切編集していない**
     （古い base 由来の見かけの差分）。(2) **疑い commit の per-commit 確認**: `git show <lane-HEAD> -- <疑い file>`
     が `+theorem/+lemma/+def` を含まない（merge で取り込んだだけ）なら自作編集でない。(3) **最終確定 = trial-merge
     staged**: `git merge --no-ff --no-commit <branch>` 後 `git diff --cached --name-only` に疑い file が
     **含まれなければ**、3-way が main 側（最新）を保持＝逸脱なし。staged に疑い file が出て内容が絡むなら genuine 逸脱で abort+STOP。
  - 要するに **3-dot の逸脱フラグは「疑い」止まり**。分岐元 base diff=0 + trial-merge staged に無し、で誤検出を排除して合流可。
- **`axiom` 判定 grep は必ず `.lean` に scope する**: `git diff --cached | grep '^\+\s*axiom '` は
  **issue/notes の markdown 中の散文（"axiom footprint = …" 等）を誤検出**する（2026-06-22 実害）。
  正しくは `git diff --cached -- '*.lean' | grep -E '^\+axiom [A-Za-z_]+ *[:({]'`（行頭 `axiom <ident>` の
  実宣言のみ; staged が markdown のみなら空）。sorry +/- 判定も同様に `-- '*.lean'` scope。
- **worktree の working-tree grep (`cd <wt> && grep -rnE … OddOrder/`) は未コミット WIP も数える** →
  sorry 増の**誤報源**。lane が draft 中の未追跡/未コミット `.lean`（実例: Thm 3.6 stub `S03f_Thm36.lean`）の
  sorry も拾うため、worktree では +N に見えても branch HEAD（コミット済）は不変なことがある。**merge が運ぶのは
  コミット済状態のみ**ゆえ、sorry ゲートの authoritative 判定は **trial merge 後に main 側で `grep -rnE … OddOrder/`**
  （= 実際に staged されるコミット済加算分）で行う。staged が notes のみ/該当 .lean を含まなければ worktree の +N は誤報。
- **lane が merge 済み commit を amend した場合** (実例 2026-06-11, `b582007f`→`9581665d`):
  ff 同期が "Diverging branches" で落ちる。対処: (1) `git log --oneline -3 <branch>` +
  `git merge-base main <branch>` で amend (親が main の merge 前 HEAD) を確認、(2) 通常の
  `--no-ff --no-commit` trial merge — 内容が上位集合なら自動解決またはファイル単位 theirs、
  (3) `git diff main <branch> -- <file>` = 0 なら実差分は付随物 (guard 等) のみ。通常ゲートで commit。
  予防 = 各 LAUNCH.md に「commit 後の amend/rebase 禁止」を明記済み。
- **前セッションがマージ途中で死んだ場合**: 新セッション開始時に `git status` が staged 変更 + `MERGE_HEAD`
  を持ち、`git merge` が `fatal: ... MERGE_HEAD exists` を返す。これは「コンフリクト解決・staged 済みだが
  build/検証/commit 前」の状態。対処: (1) `cat .git/MERGE_HEAD` がどのレーン branch HEAD と一致するか確認、
  (2) `git grep -lE '^(<<<<<<<|=======|>>>>>>>)'` でコンフリクトマーカー残存なしを確認、(3) 通常の
  build + AxiomsCheck + sorry 不増ゲートを通し、(4) 合格なら `git commit` で完結（不合格は `git merge --abort`）。
  注意: 真の pre-merge sorry 数は既にマージ適用後なので、`git show main:<file>` で touched .lean を main HEAD と比較する。
- **⚠ cron × 手動マージの競合 (2026-06-11 実害)**: cron が**並行発火**して、進行中の `--no-commit`
  trial merge を `MERGE_HEAD exists` 検出 → `git merge --abort` で**消す**事故が発生 (F の 12.18
  staged merge が tree-clean に巻き戻り、952 行の取込が消えた)。対策 2 つを cron prompt に組込み済:
  (1) **cron 冒頭ガード**: `.git/MERGE_HEAD` 存在時は「前マージ進行中, skip」で即終了、**絶対に
  abort しない**。(2) **手動マージは atomic**: merge→build→commit を 1 ターンで完結し staged のまま
  長時間放置しない (放置中に次 tick が衝突)。加えて merge 出力は `> /tmp/merge.log 2>&1` へ退避
  (S12_Lemma1218 の大量 hunk で「Auto-merging」が 100+ 行出て端末が壊れ、誤診の元になった)。
  マージ結果の正否は `git show :<file> | wc -l` で**期待行数**を実値確認するのが確実
  (索敵: theirs が取り込まれたか。base==ours で theirs 変更なら theirs 採用が正)。

## 現状メモ

- **2026-07-02 — 3 レーン再編 (ユーザー裁定): lane d 退役、a/b/c に縮約**。char endgame が密結合パイプライン
  (coherence→σ-theory→§10-13→§13-16→S16) と判明、ungated frontier 上流集中で下流 (c/d) が反復 stall →
  3 レーンに縮約。**lane d 退役** (σ-theory dichotomy sorry-free 完成、残 tail = S11 consumer=a に fold、
  δ BG/** 完了・共有凍結、carrier done)。**S15_SAndT_Setup は lane d→c** (§15→16 chain 一本化)。carve-out
  0086 (S10 carrier→a) / 0088 (S14 exists_typeICovering→b) は file owner に解消。σ-theory generic leaf は
  `GroupTheory/**` 共有残置 (a が tail 完成 + S11 dup retire→cite)。**cron は a/b/c のみ監視** (d は branch
  温存だが session 停止、未マージは常に 0)。ISSUE_BASE 4000 退役 (9000 shared-infra は継続)。詳細 =
  `ft_lane_reallocation_2026_06_28.md` の「3 レーン再編」節。⚠ 次 tick 以降 `main..d` は常に 0 (skip)、
  万一 d が新 commit を出したら (session 生存) 通常 range-check して合流可。
- **2026-07-01 — hub tick 合流 a/b/c/d (4 lane) + lane d σ-theory 再々配分 (issue 4014 hub 裁定)**:
  cron tick で全 4 レーン合流 (a=Pf 9.8.c constituent / b=Pf 5.5 L-side+12.14 horth / c=Pf 13.16 W₁-side
  conjunct 1+N_G(W₁)≤T / d=issue 4014 gating-map)。push `1144248a..aee8043f`、sorry 120→122 (全 scaffold)。
  lane d が「§15 S&T setup + δ BG §14–16 の on-spine ungated frontier 枯渇」を code-level 確証 (issue 4014)
  → **ユーザー裁定 = option (b): lane d を generic σ-theory (typeP_Galois 土台) の新 shared-infra leaf
  `OddOrder/GroupTheory/**` 構築へ再配分** (claim-first、既存 SingerField/GaloisCharacter 等を scan)。
  ⟹ cron の range-check: **lane d が `OddOrder/GroupTheory/**` に新 σ-theory leaf を追加しても共有ゾーンゆえ
  逸脱でない**。ただし step 1.6 の shared-infra dup 検出は継続 (lane a §11 typeP_Galois と衝突しないか監視;
  lane a は cite するだけの取り決め)。詳細 = issue 4014「HUB 裁定」節 + ft_lane_reallocation。
- **2026-07-01 — policy 規約化 (自律 frontier 選択 + shared-infra claim) + lane b dup 保留 (issue 0093)**:
  ユーザー裁定 2026-07-01 を lane b/c が両方 codify。**c 版 (superset: CLAUDE + ft_path_policy §0 policy
  5-6 + merge_monitor §1.6 + issue_management 9000-range) を採用・合流** (`f6507084`)。b 版
  (`47bd6a0f`、CLAUDE/ft_path_policy の別 wording) は **supersede→保留**。⚠ 次 tick で `main...b` に
  CLAUDE.md/ft_path_policy が出て merge conflict しても **superseded policy dup (issue 0093)** ゆえ
  abort + 「b: policy dup 未解消」1 行報告に留め **STOP しない**。b が drop したら通常復帰。
- **2026-07-01 — lane d 再配分 (issue 0092, ユーザー裁定)**: lane d の旧クラスタ δ (BG §14–16) の FT
  deliverable は実質完成 (spine 消費 endpoint 全 sorry-free) と監査確定。**lane d の主焦点を binding pole
  γ の import-上流最上流 `S15_SAndT_Setup.lean` (16 sorry) へ移管**。lane c は下流 `S15_SAndT` +
  `S16_NonExistenceG` を保持。以後 range-check: lane c が S15_SAndT_Setup 編集=逸脱 / lane d が S15_SAndT・
  S16_NonExistenceG 編集=逸脱。lane d は BG/** 所有を dormant 保持。cron 所有マップも更新済。
- **2026-07-01 — hub 監視再開 + lane b cross-lane 裁定 (issue 0091)**: 第1 tick で lane a 合流
  (Pf 9.8.c propagation + S11 build-red 修正, issue 1014 CLOSED, `2eb5389f`, push 済)。lane b は
  `Hypothesis78.nu_isometry` を global→family に弱める **範囲逸脱 (S09_NonexistenceCertain=lane a 所有) +
  signature contract 改変 + issue 1013 charter 違反** で STOP → **ユーザー裁定=受理** (family 版が Peterfalvi
  忠実版, full build green で下流無破壊確認)。詳細 = issue 0091。⚠ **standing carve-out ではない**:
  以後 lane b が S09_NonexistenceCertain を編集したら通常通り逸脱。
- **2026-06-28 — レーン再配分 (a/b/c/d) + 監視再開**: ゲートなし・signature contract 方式へ全面再配分
  (正本 `ft_lane_reallocation_2026_06_28.md`)。worktree を `odd-order-{a,b,c,d}` に rename (`git worktree move`/
  repair、`.lake/build` cache 流用、coq submodule back-pointer 修復済)。全 4 レーン main `5f1c0be2` に同期・
  **0 unmerged** で監視開始。旧 relane #1-#12 / lane f/b/h/c の詳細履歴は `ft_frontier_remap_2026_06_25.md`
  + git log に温存 (本ファイルからは除去してクリーン化)。
