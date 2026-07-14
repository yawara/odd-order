# main 合流モニター — a/b/c レーン自動合流の運用手順

> 横断運用ドキュメント。**監視ペースは hub のモデルで決まる (ユーザー 2026-07-09 明文化)**: **Fable 使用中 = 30 分間隔 `13,43 * * * *`** (速度考慮) / **Opus 使用中 = 15 分間隔 `7,22,37,52 * * * *`** (:00/:30 回避・均等割り)。履歴: 2026-07-12 Fable で 30 分 (ユーザー再確認・規約化再指示)、2026-07-05 Fable で 30 分 `13,43` → Opus 切替で 15 分復帰、2026-07-09 Fable で 30 分 (ユーザー指示)、2026-07-02〜07-05 は 15 分、2026-06-29〜07-02 は 30 分、それ以前は 15 分。cron は session-only ([[cron-dies-on-model-switch]]; CronCreate `durable:true` は本環境で disk 永続せず session-only 扱い) ゆえ、**再作成時は現行モデルに対応するペースで**作る。main worktree = `/home/ywr/odd-order`。
> ユーザー方針: **「検証通過は自動合流」** — build green + axiom-clean + sorry regression なし + 新 axiom なしを
> 満たすレーンを `--no-ff` で自動マージ。満たさなければ `git merge --abort` で報告。合流成立時は最後に
> `git push origin main`（変化なし/全 abort なら push しない）。
>
> **レーン配分の正本 = [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md)**
> (ゲートなし・signature contract 方式)。本ファイルは hub 側の合流手順 + gotcha 集。

> **🔀 一時 cross-lane carve-out (issue 8022) — ❌ 失効 (2026-07-02 lane d 退役)**: lane d への
> S09/S14_MaximalI 一時編集権、および a/b/c への「S09 FrobeniusFamily/FamilyHypothesis71・
> S14_MaximalI `not_all_maximal_typeI` 周辺の編集回避」要請は**解除**。route B の残作業と owner は
> issue 8022「🧾 状態整理」節 (per-rep §8 Dade-support 8.15 = lane b、carve-out 0096 経由)。

> **✅ issue 0089 解決 (2026-06-30, ユーザー裁定 D=削除)**: `S07_RhoProjection.lean` は S09 `chiRho`
> 機構の完全重複ゆえ**削除済** (carve-out 0087 撤回)。(12.16) path は S09 `chiRho`/`Hypothesis78`/
> `NormEstimates` を cite。旧 HOLD は解除。
> ⚠ **re-sync lag**: lane b の branch には**削除前の** S07_RhoProjection がまだ残存しうる (b が
> `git merge main` で削除を取り込むまで)。⟹ 3-dot `main...b` に `S07_RhoProjection.lean` が出ても、
> それが「b が削除前から持っている残存」(= b の commit は S07 の**新規宣言追加でない**) なら**逸脱でなく
> 『b: S07 削除の re-sync 待ち』として skip**。b の non-S07 .lean 実作業のみ通常合流。b が**削除後に
> S07 を新規再作成**した場合のみ逸脱。判定: `git log main..b --no-merges` の commit が S07 への新規宣言
> 追加か (= 再作成) / 既存 S07 への追記止まり (= 残存) か。混在・不明なら skip+報告。

## レーン (2026-07-07 current: a/b/c — ⚰ lane d 退役)

| lane | branch | worktree | クラスタ | 主所有 .lean | issue base |
|---|---|---|---|---|---|
| **a** | `a` | `odd-order-a` | α **S12 (11.8) unique feitThompson sorry** + §7 on-path norm (2026-07-04 再々編) | `Peterfalvi/S(0[3-9]|1[0-3])*` + `FeitThompson.lean` (全体) | 1000 |
| **b** | `b` | `odd-order-b` | β **§16 endgame char cascade = S15 (13.9)-(13.19)** (2026-07-04 再々編; §12 Dade は完遂・cite-only) | `Peterfalvi/{S15_SAndT_Setup, S15_SAndT}.lean` (c→b, 2026-07-04) + `S14_MaximalI.lean` + coherence file 群 + carve-out 0090/0096 | 2000 |
| **c** | `c` | `odd-order-c` | γ 🤖 **codex 5.6 運用 (2026-07-10, issue 0105)** · **S16 非存在 + ♻ 2026-07-07 REACTIVATE (issue 0098 パッケージ 5 件)**: typeP_pair port (§8 新 shared leaf) / semilinear (9.7.b) field-model leaf / S-side βₛ bridge carve-out (S15_SAndT.lean:3616 BetaData 領域) / §14 Γ-bridge assembly / hcard2 verify | `Peterfalvi/S16_NonExistenceG.lean` + 構成的 Clifford (9002 完了) + carve-out: reconciled_typePData_T 残 field (S15_SAndT_Setup:4520/:4590) ・BetaData 領域 (S15_SAndT:3616) + 新 shared leaf (claim-before-build) | 3000 |
| ~~**d**~~ | — | — | ⚰ **退役 (2026-07-07, ユーザー裁定)** — codex 運用 shared-infra レーン。worktree/branch 削除済 | — | — |

> **🤖 lane c = codex 5.6 (GPT-5.6) 運用 (2026-07-10, ユーザー裁定, issue 0105)**: lane c の operator を
> Claude から codex 5.6 に切替 (trial)。**所有・issue base (3000)・合流ゲートは不変** (build green /
> AxiomsCheck / sorry regression / 範囲逸脱チェックはモデル非依存)。handoff・kickoff prompt の正本 =
> [`lane_c_codex_handoff_2026_07_10.md`](lane_c_codex_handoff_2026_07_10.md)。旧 lane d 再活性化トリガー (i)
> 「S-side landing → T-side mirror」は 8ff313b1 で成立したが、d 再作成でなく c の operator 切替で対応
> (T-side mirror = c territory)。**hub 追加チェック (最初の ~5 tick 重点)**: c の合流 tick で
> `git diff main...c -- '*.lean' | grep -E '^\+\s*(theorem|lemma|def) '` の新規宣言に対し既存 API との
> dup を spot-grep (旧 lane d の失敗モード = 既存 S01/GroupTheory 補題の複製 churn)。**dup 主体の tick は
> merge せず abort** + issue 0105 に記録 + notes/issue で c に de-dup (cite 置換) を差し戻す — これは
> ⛔ STOP でなく**通常継続** (ループは止めない、ユーザー escalation 不要)。数 tick (~2 日) で
> keep / swap-back を hub が裁定 (評価軸 = genuine landing、sorry 数でない)。裁定は issue 0105 に記録。

> **⚰ 2026-07-07 — lane d (codex) 退役 (ユーザー裁定)**: 徹底調査で **FT frontier (Peterfalvi 72 + BG 15 実 sorry) に codex 単独で閉じられる genuine・on-path・非衝突・非gated な実 sorry は存在しない**と確定 (Peterfalvi=全て gated/深いchar/a-b-c衝突/偽/off-path; BG 非b分=AppD/AppE 全て consumer 0・unimported の off-path scaffold)。構造的理由: FT 残 frontier は深く密結合な char/local-analysis で「切り出せる mechanical leaf」がほぼ無く、codex に軽タスクを与えると dup relocation の churn に流れる (直近 2 tick = 計 14 補題が全て既存 S01 補題の複製、net-genuine 0)。⟹ 3 レーン (a/b/c) に集約。worktree `/home/ywr/odd-order-d` + branch `d` 削除 (churn は net-zero、reflog 復元可)。**♻ 再活性化トリガー (将来)**: (i) proven S-side の **T-side dual** (`V_inf_centralizer_Q_eq_bot` 等) の gate ((14.9) T-typeII 構造) が a/b で landing → codex が template を mirror; (ii) a/b/c が特定 group-theory helper を明示 pull-request。いずれか発生時に `git worktree add /home/ywr/odd-order-d -b d` で再作成 (issue base 4000)。**⚠ ユーザーは codex の /loop セッションを停止すること** (worktree 消失後は codex が git エラーで空転)。

> **⏸ SUPERSEDED→temporary-hold (2026-07-09, issue 9077 HUB RULING #2)**: 下記 (B) の 9078 は **完遂**
> (`SemilinearFieldModel.lean` leaf + T-side `tFieldModelData_of_repr` producer、全 sorry-free、`t_side_frobenius_kernel`
> 構造 discharge)。c は独立 frontier 再枯渇を surface → hub が **3-probe workflow (wf_52474eb0、high-conf)** で裁定 =
> **(A-mod) temporary-hold**。全 probe が「c-buildable ungated non-dup target 無し」を確認: 残 gate (V_inf/13.15 =
> b の active (13.4) `lambda_forces_T_caseB` / t_side field-data = a の active 9000 char body) は全て他レーンの
> **ACTIVE work で降りると policy-8 dup** (9013 案 B は却下済)、GroupTheory/Mathlib shared-infra は real sorry 0。
> c は全 non-dup slice を sorried-cite endpoint 化済 ⟹ **gated-endpoint pattern で self-resume 待機** (lazy idle でない、
> 2026-07-06 DORMANT とは別)。**hub フォロー: a の 9000 / b の (13.4) landing 監視 → landing tick で 9077 に「c 再 engage 可」flag**。詳細 = 9077 RULING #2。
>
> **♻♻ RE-CONFIRMED (2026-07-08, issue 9077 HUB RULING (B))**: lane c が「S16 全 13 sorry は a/b gated、
> 独立 frontier 枯渇」を全数検証で surface (ユーザー「ハブに聞くべき」)。hub が subagent 調査+自己検証で裁定 =
> **c は DORMANT でなく `SemilinearFieldModel.lean` shared leaf + T-side `TFieldModelData` producer を build**
> (= 0098 item 2 の再活性、genuine 未着手 gap、a の Singer と cleanly-separable = dup でない、a は未着手で
> `main..a`=0)。着手 claim = **issue 9078** 起票済。gated-endpoint skeleton パターン (V-abelian を hypothesis 化)。
> 分担境界: c=field-model realization (a の Singer cite) / a=§9 block-decomp + (11.9) char body。詳細 = 9077/9078。
>
> **♻ SUPERSEDED (2026-07-07, issue 0098)**: 下記 DORMANT 化は解除 — 4-agent 再調査 (wf_d4994964) で
> ungated genuine work 5 件 (typeP_pair port / semilinear field-model leaf / βₛ bridge carve-out / §14 Γ-assembly /
> hcard2 verify) を確定し c を REACTIVATE。9013 item (i) mᵀ は c へ de-scope。9000 claim は a 保持 (scope 注記済)。
>
> **⚠ 2026-07-06 夕 — lane c DORMANT cite-sink 化 (hub 裁定, 4-agent 調査 wf_00a0db07)**: c の S16 領域は枯渇
> (0 ahead、S16_NonExistenceG の 10 bare sorry は**全て true carrier gate** = a の typeP_Galois (9000) or b の
> §13/§15/§16 char cascade に gated、sorried-cite assemblable はゼロ; Clifford 9002 完了; reconciled_typePData_T
> は U-side 済・残 W2_le/centralizer_W1 = b territory)。ungated 行き先も無し (shared leaf 全 sorry-free、d が
> shared-infra slot を占有)。⟹ 07-02 教訓どおり **c を DORMANT cite-sink 化** (idle lane を busywork させない)。
> **reactivation trigger** (いずれか landing で c 自動再開 → S16 W-side norm cascade + parity 矛盾を assemble):
> **a: typeP_Galois (9000, root gate)** / **b: §13 v-value lower-bound export (9013) / §15-16 W-factor σ-structure
> (9017) / S-T partner parity (3002)**。c の成果は全 in-place 保全 (revert しない)。⚠ **b は依然 OVERLOADED** ゆえ
> a が 9000 を landing 後に b→c 再配分の余地を再検討。
>
> 例外・共有・凍結の正確な判定は下の 🔒 所有マップが正。**lane d は 2026-07-06 復活** (2026-07-02〜07-06 退役、
旧 branch `d` は削除済ゆえ `git worktree add /home/ywr/odd-order-d -b d` で新規作成)。**d = codex 運用**の
最軽量レーンとして復活した 9006 Hall-lemma relocation は完了済み (closed/9006)。続く 9007 induced-conjugation
hoist も完了済み (closed/9007)。2026-07-06 lane-d audit では shared foundation
(`OddOrder/GroupTheory/**`, `OddOrder/Mathlib/**`, `OddOrder/Algebra/**`, `OddOrder/Isaacs/**`) に bare
`sorry` は無く、残る bare `sorry` は a/b/c 所有の Peterfalvi frontier に集中している。従って d は新しい
open shared claim が立つまで **issue/notes hygiene + open-9000 scan** に限定し、Peterfalvi/BG S-file へは
新 carve-out なしで入らない。

> **♻ 2026-07-06 夕 — lane d DORMANT→再活性化 (hub 裁定)**: DORMANT 化後、d は 4 tick 連続で **genuine な
> shared 群論 API を sorry-free additive に生産** (claim 9018-9031: normal Hall uniqueness / mulAut invariance /
> complementary Hall / **MinimalInvariantNormal** / minimal invariant p-group・commutativity / π-group disjoint /
> Hall action / invariant conjugation 等、Isaacs/GroupTheory/Mathlib)。内容は **coprime-action / minimal-invariant
> subgroup = FT local analysis (typeP_Galois 9000 の σ-theory 基盤含む) が使う foundational 群論**で、chore-churn
> busywork ではない。⟹ 「DORMANT / idle 待機」判定は実態と乖離ゆえ撤回、**d = codex 運用の active shared-infra
> レーン**に再活性化。claim-before-build 継続。**⚠ make-work 化防止**: hub は d の新 API が FT 経路 (特に 9000 /
> BG local analysis) に接続するかを定期確認する (0-consumer 自体は off-path 根拠にしないが、FT-relevance の追跡は
> 続ける)。正本 = 本ブロック + ft_lane_reallocation「lane d 再活性化」節。

> **🔀 2026-07-14 レーン再設計 (issue 0115、ユーザー発議 + hub 3 並列監査 wf_525303b8)**:
> (1) **c 再起動 GO** — 5 endpoint 中 4 workable (07-05 の「c-unreachable」は STALE; campaign A =
> ComparingLM 3-field bridge 配線、campaign B = T-side Singer field model)。operator はユーザー起動待ち。
> (2) **`S15_SAndT_Setup/OrderDetermination.lean` の所有 b→a 移管** (4 sorry; (13.11)/(13.12) は un-gated、
> (13.13)/(13.15) は de-opacify 要)。以後 range-check: a の同 file 編集 = 非逸脱 / b の同 file 編集 = 逸脱。
> (3) **4 レーン目見送り** — Pf Appendices 15 sorry は off-path 確定 (Part II scaffold)。
> (4) NormEstimates/CountingLayer/SAndTBasic の残 5 sorry = layer-inversion 問題、hub relayer (issue 0116)。

**signature-first interface (ゲートは幻)**: 上流が sorried signature を export → 下流が cite。各レーンは独立クラスタを
正面から埋め、cross-cluster は signature contract で媒介 (待たない)。詳細 = ft_lane_reallocation_2026_06_28.md。

**取り決め**: (1) 各レーンは**自所有ファイルのみ編集**、他は cite (要望は notes/issue 経由)。
(2) **新規 `axiom` 宣言は abort + ユーザー承認**。(3) **起動時 main 同期** = `git merge main` (3-way、`--ff-only` 禁止)。
`lake update` 禁止。コミットは main のみ。マージ順 = **a → b → c** (独立ゆえ形式的)。

**🧭 方向性・cross-lane 判断は HUB が自律裁定する (ユーザーに聞きに来ない、ユーザー 2026-07-06)**。
レーンが frontier を自律判断するのと対称に、hub は **(a) レーン間の診断の食い違い** (「X は repo に在るか」
「どちらの grep/診断が正しいか」等) と **(b) レーン方針・cross-lane 設計判断** (carve-out 付与・ファイルの
keep/delete・所有/優先順位・重複解消) を、**hub 自身が必要な調査 (code-level grep・`coq/` の Coq trace・
subagent fan-out) を行って裁定し**、結果を issue (HUB 宛 issue / 該当 shared-infra issue) と notes に記録する。
**この種の裁定に AskUserQuestion を使わない** — 「食い違いがある / 方針が割れている」自体は escalation 理由でなく、
**調査して裁定する**のが hub の仕事。調査もユーザーに投げない。
- **ユーザー escalation は narrow に予約**: (i) 新 `axiom` 宣言、(ii) unsound carrier・signature 無断変更、
  (iii) build 破壊・sorry regression・想定外 git 状態 = **merge-safety STOP** (下記 ⛔、halt+報告)、
  (iv) 既存規約+徹底調査を尽くしてなお真に underdetermined かつ不可逆・影響大の戦略選択 (稀)。
- **先例 (2026-07-06)**: lane-a/lane-b の prime-TI 診断食い違いを hub が 2 subagent + Coq trace で調査し
  「PrimeTIResidue KEEP + 9014 OPEN」を裁定 (issue 9014 HUB RULING)。当初 hub は AskUserQuestion で
  keep/delete を聞いたが、**既存規約 (CLAUDE.md の prime-TI port must-build) + 調査結果で "keep" は既に
  determined** ゆえ聞くべきでなかった — 以後この種は自律裁定 ([[hub-arbitrates-cross-lane-autonomously]])。
- lane が HUB 宛 issue を起票してもよい (title に "HUB:" 冠、選択肢明記) が、hub は待たず各 tick で拾って裁定。
  軽微な signature 不足通知は notes でよい ([[cross-lane-sync-via-notes]] の上位版)。

**🔁 lane 自己復帰**: lane が hub 待ちで停止しても自走再開しうる
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
> / 共有ファイル編集（AxiomsCheck.lean 追記・OddOrder.lean import・`OddOrder/GroupTheory/**`・`OddOrder/Mathlib/**` 共有 infra・notes・issues）
> / **上流 signature 変更への機械的 call-site 追従**（下記 🔩）/ **自所有 sorried decl の不要化削除** (sorry 減、
> 上流再配線で obligation 自体が消える型 — 先例 = b の `witness_psi_degree` 削除 49607ba9)。
>
> **🔩 機械的 call-site 追従は非逸脱 (hub 裁定 2026-07-10 tick、一般ルール化)**: レーンが**自所有 upstream 宣言の
> signature を変更** (引数追加・仮説引数化・リネーム) したとき、その **consumer call-site の機械的追従編集**は
> 他レーン所有 file 内であっても範囲逸脱としない。条件 (全て): (i) 追従は引数供給/名前置換のみで対象宣言の
> statement・証明内容を変えない、(ii) 数行規模、(iii) commit message で self-flag、(iv) build green。
> 根拠 = 0096 拡張 (proof-only de-gate) ・「S08_CaseBCoherence2 1 行追従」と同系の先例統合。逸脱判定は
> 「他レーンの active 数学に触ったか」であり「diff が他レーン file に掛かったか」ではない。
> 先例 = b の `witness_L_hzeta0nu` hAH 仮説引数化に伴う S16 下流 2 file × 1 行追従 (49607ba9、
> c は codex 運用中の active file だったが hunk 非交差で問題なし)。
>
> **🔧 範囲逸脱の是正 = 成果を無駄にせず軌道修正（ユーザー方針 2026-07-06）**: レーン範囲逸脱で halt+flag した後、
> その逸脱に **genuine output（実証明・実構成・sorry-free work）が含まれるなら discard/revert せず、hub が軌道修正で
> 保全する** — 正しい file/leaf へ移設 / carve-out 付与 / owner 再割当 / 下流再配線。「軌道修正できれば十分」で、
> genuine math を破棄しない（territorial ルールは coordination 保護であって成果 gate-keep でない）。先例 = lane b の
> `S07_Subcoherent`=carve-out / `mu2Grid`=S05→PrimeTIResidue 移設 / `PrimeTIResidue` 削除=撤回（全て保全）。
> ⚠ 保全対象は **genuine output のみ**; unsound carrier・新 axiom・sorry regression・signature 無断改変 は
> 別カテゴリ（保全すべき成果でない、halt のまま）。正本 = CLAUDE.md「進捗の測り方」の該当 bullet。
>
> **♻ 問題解決後はループ自動再開（ユーザー方針 2026-06-23, 永続）**: 上記 ⛔ で停止した監視ループは、
> **問題が解決したら必ず再開する**。具体的には: (a) 停止した問題（build 失敗 / コンフリクト / sorry
> regression / 新規 axiom / push 失敗 / 想定外 git 状態 / レーン範囲逸脱）が、**ユーザーの指示か hub の
> 修正で解消したことを確認したら**、(b) **監視 cron を `CronCreate` で再作成し**（停止時に `CronDelete`
> したものを復活）、(c) 通常の tick に復帰する。「停止しっぱなし」にしない。再開時はサマリに
> 「監視ループ再開（cron id <new-id>）」を 1 行記録する。**この stop→resolve→resume サイクルが監視ループの
> 正規ライフサイクル**であり、停止は一時退避でしかない。

> **🔒 レーン所有マップ (step 1.5 範囲逸脱チェック用、2026-07-06 lane d 復活を反映)**:
> 正本 = [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md)。
> | lane | クラスタ | 所有 .lean（これ以外の Pf/BG S-ファイル編集 = 逸脱→停止） |
> |---|---|---|
> | **a** | α Pf §10–13 中央指標核 + σ-theory tail **+ S07 ν-constructor carve-out (2026-07-06)** | `OddOrder/Peterfalvi/S(0[3-9]|1[0-3])*` + `OddOrder/FeitThompson.lean`（`card_kappaHall_lt_of_isTypeIIIorIV` (行番号は drift するため decl 名で参照) + 旧 d carrier 宣言群 = 全体、d 退役で fold）+ **S10 bgTheoremE carrier**（旧 carve-out 0086 解消）+ σ-theory tail (S11 imprimitivity + dup retire は S11 内、GroupTheory/** 共有で cite)。**+ carve-out (issue 9016, hub 裁定 2026-07-06 夕・ユーザー裁可)**: gate-2 obligation-2 = **non-orthonormal S₂ 用 `τ₃`/`ν` glue-map constructor** を a が `S07_*` へ **新規 additive 宣言**として build (b の orthonormal glue `S07:3196/3229` 系には非接触)。これが a の唯一 ungated head-on target (a の唯一 bare feitThompson sorry を gate)。obligation-1 hY は b の S07_Subcoherent が producer (sorried-cite) |
> | **b** | β Pf §12 Dade tower + coherence infra **+ BG §15/§16 (2026-07-06 追認)** | `OddOrder/Peterfalvi/S14_MaximalI.lean`（**全体**、旧 carve-out 0088 `exists_typeICovering` は b に解消）+ **coherence infra** = `S07_Coherence*`/`S08_PGroupReduction`（既存 coherence file、(5.7)/(6.5.c)/(6.8) case-B 系、hub authorized 2026-07-02）+ GroupTheory/** coherence leaf。⚠ これらは nominal に a の `S0[3-9]` regex に掛かるが **coherence infra ゆえ b 担当（逸脱でない）**、a の active territory は §9-13 char 核で S07/S08 coherence は非接触。**⚠ b の例外 glob は正確に `S07_Coherence*` + `S08_PGroupReduction` の 2 つのみ** (正本 ft_lane_reallocation §レーン表): `S08_CaseB*`/`S08_CoherenceTheorems` 等その他の S07/S08 file は **lane a 所有** — 2026-07-03 tick で a の `S08_CaseBCoherence2` 1 行追従を「b 所有では」と誤読しかけた (glob 照合で解消、逸脱でない)。**+ BG §15/§16 node (issue 9017, hub 裁定 2026-07-06 夕・ユーザー裁可「drift 追認」)**: `OddOrder/BG/Ch4_FamilyOfMaximal/{S15_MF.lean (§15.8 tau2_transfer_constraint / §15.9 centralizer_escape_final_local), S16_MainResults.lean, S14_TypePCounting.lean (Cor 14.12 `typeP2_neighbor_is_typeF*`、Thm 15.8 の prereq — carve-out 拡張 2026-07-06 tick、signature 保持・他 owner なし)}` の残 bare sorry は **b の active territory** (共有凍結から除外)。Thm 15.8 signature 訂正 (unsound→Coq準拠, consumer 0) + `typeF_frobenius_of_tau2_prime_free` の S16→S15 hoist を承認済 (9017 RULING)。lane c の Peterfalvi `S16_NonExistenceG.lean` には跨らない (別 file) |
> | **c** | γ **S16 非存在 — ⚠ 2026-07-06 夕 DORMANT cite-sink** (領域枯渇の hub 裁定、reactivation trigger は下記) | `OddOrder/Peterfalvi/S16_NonExistenceG.lean`（**2026-07-04 再々編: S15_SAndT_Setup + S15_SAndT は c→b 移管**、c は S16 に集約し S15 を import cite）+ 構成的 Clifford (issue 9002、**完了**) + **carve-out (2026-07-06, hub 裁定, issue 9013)**: `S15_SAndT_Setup.lean` 内の `reconciled_typePData_T` T-side carrier ブロック（現 S15:~4018–4260、`isNilpotent_V` 等の T-side type-P data field discharge）は **c 所有**（退役解除 — c の (14.9) T-side type-IV 排除が本 carrier を要求すると 884a52e0 airtight 分析で確定、on-path 復活）。⟹ step-1.5 で c が S15 の**この T-side 領域のみ**を編集しても逸脱でない（c が S15 の char-family 領域 = b の active `cprimeSharpS`/(C')# 系 ~845 を触ったら逸脱）。b は逆に T-side 領域を触らない。恒久解（reconciled_typePData_T を c-owned/shared T-side leaf へ移設し S15 二重所有を解消）は issue 9013 で追跡 |
> | **b 追加所有 (2026-07-04)** | β §16 char cascade | `OddOrder/Peterfalvi/{S15_SAndT_Setup, S15_SAndT}.lean`（c→b 移管、(13.9)-(13.19) on-path parity/構造/norm を b が担当; off-path S-side cascade 13.5-13.10 は退役）|
> | **d** | δ codex shared-infra hygiene — **2026-07-06 夕: DORMANT** | **2026-07-06 復活 → 同日夕 dormant 化 (分担監査 + ユーザー裁可)**。9006 Hall relocation / 9007 induced-conjugation hoist は完了済み。BG §15/§16 node は **b が owner を追認**したため d の rescue frontier にならず、他に unclaimed shared leaf も監査で発見されず (9014/1017-arith は build 済)。⟹ d は charter どおり **停止 (stop+報告)、checklist/notes の busywork を作らない** (直近 `chore: refresh issue checklist` 連発は CLAUDE.md 禁止の busywork ゆえ即停止)。新しい genuine shared claim が立てば再起動。worktree は保持 (idle 継続なら retire 検討、可逆)。`OddOrder/GroupTheory/**` 等 shared leaf は claim 後のみ。**Peterfalvi/BG S-file は fresh issue/carve-out なしに編集しない**。 |
> | **共有（全 lane 可）** | — | `OddOrder/AxiomsCheck.lean` / `OddOrder.lean` / `OddOrder/GroupTheory/**` / `OddOrder/Mathlib/**` / `OddOrder/Algebra/**` / **`OddOrder/Isaacs/**`**（全 lane 加算可）/ `OddOrder/BG/**`（**大部分は完了・共有凍結。⚠ 例外 = BG §15/§16 node = lane b 所有** (issue 9017, 2026-07-06 追認): `S15_MF.lean` §15.8/15.9 部 + `S16_MainResults.lean` の残 4 bare sorry は共有凍結でなく b active。それ以外の BG/** は従来どおり凍結）/ `notes/**` / `issues/**`。**⚠ Isaacs 追加 (2026-07-04 hub 裁定)**: `OddOrder/Isaacs/**` は基盤 finite-group-theory ライブラリで**どのレーンの active territory でもない**ゆえ shared foundation として扱う (consumer が proven 補題を additive に加算可、GroupTheory/Algebra 同格)。precedent = c の Isaacs 6.11 使用 / a の (7.8.b) 用 `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` 追加 (commit 9f41b6f7)。既存 Isaacs 宣言の statement 改変は要 hub flag (additive のみ非逸脱)。|
> | **凍結 scaffold** | — | `OddOrder/Peterfalvi/Appendices/**`（off-path・consumer 0、2026-07-02 census 検証済: Huppert 1 / NearFields 2 / Suzuki 5 / Suzuki2Groups 4 / FeitSibley 3 sorry。**どのレーンも編集しない**。σ-theory near-field 等が App B/C を cite する必要が生じたら、その時点で hub が owner 割当 — 自然候補 = a の σ-theory tail 系）|
>
> ⚠ `FeitThompson.lean` は**共有ではなく lane a 所有** (d 退役で carrier 宣言群ごと fold)。他レーンが
> carrier 宣言 (`Section16Inputs` 等) に field を追加する必要があるときは hub/issue 経由で承認合流
> (先例: lane c の `S_U_commutative`/`Sdata_W2_eq` 追加 = 構成子供給付き、hub 承認)。
>
> **carve-out (issue 0086, ユーザー裁可 2026-06-29) — ❌ 解消 (2026-07-02 lane d 退役)**: bgTheoremE
> carrier は **file owner = lane a に fold** (issues/closed/0086)。以下は履歴:
> `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` は
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
> **carve-out (issue 0088, ユーザー裁可 2026-06-29) — ❌ 解消 (2026-07-02 lane d 退役)**: S14_MaximalI は
> **全体 lane b** (issues/closed/0088)。以下は履歴:
> `OddOrder/Peterfalvi/S14_MaximalI.lean`（原則 lane b）の
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
>
> **carve-out (issue 0096, hub 裁定 2026-07-02 ユーザー委任レビュー)**:
> `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean`（原則 lane a）のうち **§8 Dade-support 宣言群**
> — `typeII_A_sets_TI` / `typeII_A_sets_normalizer` / `dadeSupportHypotheses_typeI` /
> `dadeSupportHypotheses_typeP` / `support_mutual_exclusion`（+ これらの直接 helper 新設）— は
> **lane b 所有**として扱う（(8.18.c)→(12.3)→(12.14–16) chain + issue 8022 route B の前提 = β 主題;
> b による `support_mutual_exclusion` の実証明 `65a2be52` は false-statement 修正として受理済 =
> issue 9003 裁定）。`S10_BGInterface.lean` への A₁/σ♯/M̃ bridge 補題の**追加**も b 許容
> (既存宣言の変更は要 hub flag)。⟹ **step 1.5 で lane b の S10/S10_BGInterface 編集は、hunk が
> 上記宣言 (+新 helper) の文脈に収まる場合は逸脱としない**。S10 のそれ以外（bgTheoremE carrier・
> `hall_*`・type-classification structural）を b が編集したら従来通り逸脱; lane a は上記 5 宣言を
> 編集しない。恒久解 = §8 support theory 完成後に dedicated leaf（例 `S10_DadeSupport.lean`）へ
> hub prefix-split（issue 0096 で追跡）。
> **⟹ 2026-07-04 拡張 (ユーザー承認)**: 上記 5 宣言に加え、**§8-support consumer の proof-only
> de-gate** も b 許容 — b が上流 (BG Theorem B 系) を sorry-free 化したとき、consumer 宣言
> (例 `typeI_centralizer_le_and_unique` :1728, Pf 8.12.b) の **証明本体のみ**を now-sorry-free
> upstream cite に差し替える編集は逸脱としない (条件: signature 不変 + sorry/axiom regression なし
> + self-flag)。**statement 改変は依然 out-of-scope** (要 hub flag)。実例 = commit 94a34018 の
> S10 de-gate (B4 full-Theorem-B → `typeP_hall_small_subgroup_cyclic_tau2`)。
> **carve-out (3002 供給編集権, ユーザー裁定 2026-07-05 — 監視 tick で明文化)**: 2026-07-05 hub 裁定
> (9009 選択肢 2 = b への `FeitThompson.lean` `Section16Inputs`/constructor block 一時編集権) を
> **「issue 3002 供給 chain に必要な lane-a 所有ファイルへの additive helper 追加」まで拡張**する。
> 実例 = b の `S05_TICyclic.lean` `omega_inner` (+11、既存 proven `omega_inner_self`/`omega_inner_ne`
> の Kronecker 形合成、`omegaS_inner` 供給用、issue 3002 で self-flag 済) — 本 tick でユーザー受理。
> 条件: (i) 純 additive (既存宣言の statement/proof 改変は従来どおり逸脱)、(ii) proven (sorry 追加なし)、
> (iii) 用途が 3002/9009 供給 chain、(iv) issue/notes で self-flag。**3002 供給完了で失効**
> (以後の b の S05 等 lane-a ファイル編集は通常どおり逸脱)。
>
> **carve-out (issue 0101, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S11_NineElevenCoherence.lean`
> (lane b が新規作成、(9.11) Ptype_core_coherence port の Dade-pair パラメータ化 leaf) は名目上 lane a の
> S11 namespace パターンに掛かるが **lane b 所有**として扱う (9016 hY-producer 裁定の実施 + 1017 G1)。
> ⟹ step 1.5 で b がこのファイルを編集しても逸脱でない (a が編集したら逸脱; b が他の S11 ファイルを
> 編集したら従来どおり逸脱)。**分担境界: caseA (9.7.a) maximality 帰納 = b (本 leaf) / caseB (9.7.b)
> 一様 route = a (S13 landed 済、b は再構築禁止) / full assembly = a (S12/S13 側で S11 leaf を import)**。
> 詳細 = issues/0101。
>
> **carve-out 拡張 (issue 0101, hub 裁定 2026-07-08 監視 tick #4)**: `OddOrder/Peterfalvi/S11_NineElevenCaseA.lean`
> (lane b が新規作成、caseA (9.7.a) entry point `caseA_coherent_sOf_H0Cprime_of_refuter` = caseA coherence を
> maximality-refuter 節へ reduction、namespace は `OddOrder.Peterfalvi.S13`・S13_MaximalIII_IV import) も
> **lane b 所有** carve-out として扱う (S11_NineElevenCoherence と同型 = 内容で割当)。根拠 (hub 自律裁定):
> (1) genuine caseA work = 0101 が b に割当てた caseA territory そのもの、**sorry-free・新 axiom なし**;
> (2) a の base case `sOf_degreeSubfamily_isCoherent` (S13) + b の skeleton `coherent_of_maximal_coherent_pair_refuted`
> (S07_Subcoherent) を signature contract で cite (所有衝突でなく consumer 関係); (3) **lane a は S11/S13 の
> 当該 file を一切編集していない** (`git diff main...a -- 'S11*'` 空、a の active S13 = S13_MaximalIII_IV/
> S13_CoreStructure とは別 file 隔離); (4) merge-safety 全通過 (build green 3941 jobs / AxiomsCheck OK /
> sorry 不変 87 / 新 axiom なし)。⟹ step 1.5 で b が S11_NineElevenCaseA を編集しても逸脱でない
> (a が編集したら逸脱; b は a の S13_MaximalIII_IV/S13_CoreStructure 等 active S13 file には従来どおり
> 触れない = import cite のみ)。詳細 = issues/0101「2026-07-08 追加 carve-out」節。
>
> **⟹ HUB RECONCILIATION (issue 0101, hub 裁定 2026-07-12 監視 tick — merge a85869eb)**: 上記
> 「a が編集したら逸脱」を **(10.8) 閉包 (issue 1025) 期間中に限り緩和**。**ユーザー 2026-07-12「Aで」+
> HUB RULING (9087) が (10.8) knot 閉包を authorize し、その threading target に S11_NineElevenCaseA が
> 明記**されている。⟹ step 1.5 で **a が S11_NineElevenCaseA の 9083 Phase E caseA machinery 宣言**
> (`caseA_two_summand_inertia_inputs`/`NineElevenNormBound`/`C_eq_cSub` 系の signature/proof threading)
> **を編集しても逸脱でない** (b の entry point `caseA_coherent_sOf_H0Cprime_of_refuter` を a が触ったら
> 逸脱; b はこの entry point を専有維持)。判定 = decl 単位 (混在 leaf)。merge-safety 全通過確認済
> (build green 4177 / sorry 65→65 / 新 axiom なし / b entry point preserved decl 16→16 / b 非 ahead で
> collision なし)。**(10.8) 閉包 landing で失効**。詳細 = issues/0101「HUB RECONCILIATION」節。
> **carve-out (issue 2035, hub 裁定 2026-07-14 監視 tick 20 — merge 側で記録)**:
> `OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHom.lean` の **caseB-Xi / `CliffordCaseBData`
> reverse-characterization 系宣言** (`caseB_xiOf_H0C_eq_induce_hcPsi` / `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair` /
> `isIndHC_of_source_eq_induce_hcPsiPair` 等、S11 (9.11) caseB Clifford 対応) は名目上 lane a の S11 regex
> (`S(0[3-9]|1[0-3])`) に掛かるが **lane b 所有**として扱う (carve-out 0101/9076/9014 と同型 = 名目 regex でなく
> 内容で割当; 0101 の S11 (9.11) caseB coherence carve-out の同ディレクトリ拡張)。根拠 (hub 自律裁定):
> (1) genuine b content — `CliffordCaseBData` (b の landed 9094 vocabulary) は同 dir の `ChiefFactorCore.lean`
> で定義、本 file は `CaseBXi` を import する caseB-exhaustion 機械 = b の 9094/2035 char cascade;
> (2) **lane a は本 file 非接触** (a 現 0 ahead、`InnerCompHom.lean` の非-refactor 履歴は b の commit のみ;
> dir 内の唯一の a feature commit 30a256cf (11.9.c) は別 file `ThetaCountAssembly.lean` で main 既 merge の
> past work); (3) **a の S13 (9.7.b) 一様 route の dup でない** (3 宣言とも S13/S11_NineEleven の main に不在 =
> 0101「b は (9.7.b) 再構築禁止」に抵触せず — これは 9094 CliffordCaseBData の caseB であって (9.7.b) route でない);
> (4) sorry-free・純 additive (+328/-0)・build green 4197 / AxiomsCheck OK 2399 / 新 axiom なし。b は S15 caseB
> wiring (set-artifact) を自ら revert し InnerCompHom lemma のみ保持 (2035 #34 self-flag) = 「軌道修正で保全」自己適用。
> ⟹ step 1.5 で b が InnerCompHom の caseB-Xi/CliffordCaseBData 宣言を編集しても逸脱でない (a が編集したら逸脱;
> dir の (11.9.c) `ThetaCountAssembly` 系は従来どおり decl-unit で a 領域)。詳細 = issues/2035 #34。
> **carve-out (issue 9076, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S05_GridRigidity.lean`
> (lane c が新規作成、Pf (3.8) abstract norm-2 rigidity engine `orthonormalGrid_diff_rigidity` = S05 σ-image
> と S15 η-grid を de-dup する module-generic 核) は名目上 lane a の S05 regex に掛かるが、issue 9076
> (lane c shared-infra claim、§3 cyclicTI rigidity、claim-before-build 準拠) の abstract engine ゆえ
> **lane c 所有**として扱う (carve-out 0090/0096/0101 と同型 = 名目 regex でなく内容で割当)。根拠: lane a は
> S05 系を一切編集していない (active 衝突なし)、依存 `S05_GridTrichotomy` は既存 grid-rigidity infra、
> 9076 の「§10-13 と重なる可能性」は a が rigidity を **cite** する consumer 関係 (signature contract) で
> 所有衝突でない。⟹ step 1.5 で c が S05_GridRigidity (+ grid-rigidity S05_Grid* 系・S16_GridExpansion)
> を編集しても逸脱でない (lane a が S05_Grid* を編集したら逸脱; c が S05 の char-核 file = S05_TICyclic 等を
> 編集したら従来どおり逸脱)。詳細 = issues/9076。
>
> **carve-out (issue 9014/2038, hub 裁定 2026-07-11 監視 tick — merge 側で記録)**:
> `OddOrder/Peterfalvi/S05_OmegaSpanning.lean` (lane b が新規作成、Pf (3.3)/(1.3) ω-grid spanning +
> Fourier 展開 = (13.18) B(iii) port chain の底、9014 claim の port 対象 `equiv_restrict_compl_ortho`
> 系) は名目上 lane a の S05 regex に掛かるが **lane b 所有**として扱う (carve-out 0090/0101/9076 と
> 同型 = 名目 regex でなく内容で割当)。根拠: (1) sorry-free の genuine port (153 行、汎用核は共有
> `GroupTheory/RepresentationTheory/SupportedSpanOrthogonality.lean` に分離済 = 配置規律も正)、
> (2) 新規宣言に main との dup なし (hub 確認済)、(3) lane a は本 file 非接触 (S05_TICyclic を import
> cite する consumer 関係のみ)、(4) claim = open 9014 (claim-before-build 準拠)。⟹ step 1.5 で b が
> S05_OmegaSpanning を編集しても逸脱でない (a が編集したら逸脱; b が他の S05 char-核 file を編集したら
> 従来どおり逸脱)。⚠ 合流時に root closure 欠落 (どこからも import されず) を hub が検出 →
> OddOrder.lean に import 追記で修正 (step 3b 機械的修正)。b は今後新 leaf 作成時に OddOrder.lean
> 追記まで込みで commit すること。
>
> **carve-out 拡張 (issue 9076 piece 4c, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean`
> (lane c が新規作成、Pf (8.10)/(8.15) honest `'A0(S) = 'A(S) ∪ V^S` 定義 + set-level facts) は名目上
> S15 = **lane b 領域**だが、issue 9076 の piece 4c (A0-Dade correctness fix — 現 (13.18) は 'A(S)-Dade
> だが μ差 support は P^#∪V_S ゆえ A0 化必須) infra ゆえ **lane c 所有**として扱う (S05_GridRigidity と
> 同型 = 内容で割当)。根拠: 新 leaf (b の `S15_SAndT` を編集せず `honestTypeP2ASet` (b の
> `S15_SAndT_Setup:552`) を cite して拡張)、b は S15 を触っていない (衝突なし)。⟹ step 1.5 で c が
> S15_HonestTypeP2A0 を編集しても逸脱でない (b が編集したら逸脱)。
> **⟹ 相互 carve-out 追記 (hub 裁定 2026-07-11 監視 tick)**: 上記「b が編集したら逸脱」を
> **def-層 (語彙) に限り緩和**する。b は自所有 `S15.Hypothesis` carrier の field 追加に必要な
> **上流語彙 def の移設・機械的追従** (実例 = `honestTypeP2A0Set` を SubcoherenceInputs へ移設、
> def 本体は namespace 修飾以外不変、iter32-34 で self-flag) を行ってよい (🔩 + 9014 相互
> carve-out と同型)。条件: (i) def/statement の意味不変、(ii) c の set-level facts・A0-Dade
> content (theorem/lemma) には非接触、(iii) issue self-flag、(iv) build green。c の theorem 層は
> 従来どおり c 専有 (b が触ったら逸脱)。移設後の def-層の恒久所有 = b (SubcoherenceInputs 内)。
> **⟹ 相互 carve-out 拡張 #2 (hub 裁定 2026-07-13 監視 tick — merge 12123d9d)**: def-層に加え、b は
> **自所有 `Hypothesis.*` char-cascade 定理の *additive* 追加**も S15_HonestTypeP2A0 で行ってよい (実例 =
> `Hypothesis.tauS_mu_diff_support`/`tauS_mu_vanish_on_V` = (4.8) full-grid μ差 support/V-value、c の
> `honestTypeP2A0Set` を **cite** して 1017 caseB R-family を閉じる)。条件: (i) **純 additive** (c の
> set-level facts・A0-Dade theorem/lemma の改変・削除は依然逸脱)、(ii) 追加定理は b の `Hypothesis` char
> 系で c の A0 def は cite のみ、(iii) issue self-flag、(iv) build green。根拠: genuine b char output・
> c content 非接触 (merge 検証: `-theorem` 皆無)・c 非 ale ゆえ「軌道修正で保全」policy で受理。⟹ step 1.5 で
> b が S15_HonestTypeP2A0 に additive `Hypothesis.*` char 定理を追加しても逸脱でない (c の A0-Dade
> theorem/lemma 改変は逸脱)。同様に **S15_BridgeCharacter は混在 leaf で decl 単位判定** (b の (13.18/19)
> char 系 = `tauS_mu_cross` 等の追加は b 領域、c の BetaData/tauS_mu_row0 系は c 専有 — tick 9 の decl-unit
> ルール継続)。
>
> **✅ coordination 点 解決 = carve-out 拡張 #2 付与 (issue 9076 piece 4c-3, hub 裁定 2026-07-08 監視 tick)**:
> 上記注記の「⚠ 将来 coordination 点 (`tauS_mu_row0_cross` の A0-Dade 化 statement 変更 = b territory、
> b+c 調整要)」は**解決**。lane c が piece 4c-3 で `S15_SAndT.lean` の **(13.18) S-side A0-rewire ブロック**
> (`tauSbetaGrid` / `tauS_mu_row0_cross` / `gammaGrid_defGamma` の τ_S を `dadeHypS`→`dadeHypS0` に差し替え)
> を直接編集。carve-out 申請より先に着手したが、hub 監視 tick で **「軌道修正で保全」ポリシー**に従い
> **retroactive に carve-out 拡張を付与**して保全: **この (13.18) rewire ブロックは lane c 所有**。
> 根拠 (自律裁定): (1) genuine correctness fix — 旧 `dadeHypS` ('A(S)-Dade) では μ差 support の V_S-part が
> arbitrary-extension 領域に落ち statement が provable でなかった; A0 化が唯一の sound route (issue 9076 4c)。
> (2) **下流 blast radius = ゼロ** — `tauS_mu_row0_cross`/`gammaGrid_defGamma`/`tauSbetaGrid` を cite する
> consumer は S15_SAndT.lean 外に存在しない (grep 確認、S15_HonestTypeP2A0 docstring 言及のみ)。
> (3) **b は S15_SAndT に一切触れていない** (`git diff main...b` 確認) → 調整点の懸念 (b+c 同時編集で衝突) は
> 実際には未発生。(4) merge-safety 全通過: build green (3940 jobs) / AxiomsCheck OK / 新 axiom なし /
> sorry +1 = 新 decl `not_isConj_honestTypeP2ASet_typePV` deep-pin scaffold (regression でない)。
> ⟹ step 1.5 で c が S15_SAndT の **(13.18) S-side rewire ブロックのみ**を編集しても逸脱でない
> (c が S15_SAndT の他領域 = b の char-family/(C')# 系を触ったら従来どおり逸脱; b はこの (13.18) ブロックを
> 触らない)。**b は次回 main sync で c の rewire を取り込むこと、`tauS_mu_row0_cross` を再構築しない。**
> 詳細 = issues/9076 piece 4c-3。
> **⟹ 所在地更新 (2026-07-12 tick 9)**: b の 0103 系 prefix-split (merge 16bd816d) で、この c 所有
> ブロック (BetaData 領域 + tauSbetaGrid/GammaGrid/tauS_mu_row0_cross/gammaGrid_defGamma) は
> **バイト同一のまま `S15_BridgeCharacter.lean` へ移動** (hub 機械検証: 移設 1413 行中 1405 行同一、
> 差分 8 行は b 自身の (13.19) producer 分解のみ)。以後 **c の carve-out はファイル追従 =
> S15_BridgeCharacter.lean 内の当該宣言群** (c がそこを編集しても逸脱でない; b は同 file 内の自分の
> (13.19) producer 系のみ編集し c 宣言に触らない — 混在 leaf につき step 1.5 は decl 単位で判定)。
>
> **carve-out (issue 9014/9076, hub 裁定 2026-07-08 監視 tick — merge 216b605d)**:
> `OddOrder/Peterfalvi/S13_PrimeTIResidueBridge.lean` (lane b が新規作成、86 行、**namespace は
> `OddOrder.Peterfalvi.S15`** = ファイル名 S13_* だが宣言は S15 領域) は名目上 lane a の S1[0-6] regex に
> 掛かるが **lane b 所有**として扱う (carve-out 0090/0101/9076 と同型 = 名目 regex でなく内容で割当)。
> 内容 = (13.18) μ-carrier の honest source (`Hypothesis.s06S`/`residueS` = prime-TI residue grid を
> type-uniform な S06.Hypothesis + sorry-free `PrimeTIResidueData.ofS06Hypothesis` で構成、IsTypeP1 不要;
> §12 muGrid は type-P2 obstruction で dead)。根拠 (自律裁定): (1) genuine b content — (13.18) = §13 char
> cascade = b の S15_SAndT territory; (2) **lane a は S13/S15 活動ゼロ** (0 unmerged、`git diff main...a --
> 'S13_PrimeTIResidueBridge*'` 空) で active 衝突なし; (3) a の S12/S14/shared `PrimeTIResidue` を **cite する
> だけ** (編集せず); (4) merge-safety 全通過 (build green 3942 jobs / AxiomsCheck OK / sorry 86→86 / 新 axiom
> なし / 衝突なし)。⟹ step 1.5 で b が S13_PrimeTIResidueBridge を編集しても逸脱でない (a が編集したら逸脱;
> b が a の active S13 = S13_MaximalIII_IV/S13_CoreStructure 等を触ったら従来どおり逸脱)。⚠ **minor**:
> ファイル名 (S13_*) と namespace (S15) の不一致 — 内容が S15 ゆえ将来 `S15_PrimeTIResidueBridge.lean` への
> rename が自然 (b の裁量、非緊急・非 blocking)。詳細 = issues/9014・9076。
>
> **carve-out 拡張 (issue 9014, hub 裁定 2026-07-09 監視 tick — merge dd18fdc5)**: 上記 b 所有の
> `S13_PrimeTIResidueBridge.lean` のうち **`Hypothesis.residueS` 周辺 (c の (13.18) engine が consume する
> S-side bridge 宣言) は lane c も編集可** (retroactive 保全、9076 4c-3 と同型)。実例 = c の instance-plumbing
> refactor (binder → scoped FiniteInduce 統一、whnf timeout 解消、consumer 0・数学的内容不変)。b の
> (13.18) μ-carrier honest source 側 (`Hypothesis.s06S` 等) は従来どおり b 専有。b は main sync で
> 本 refactor を取り込み、binder 供給へ再変更しない。詳細 = issues/9014 「HUB carve-out 追記 2026-07-09」節。
>
> **carve-out (issue 2038 供給編集権, hub 裁定 2026-07-09 監視 tick — merge 03fd8474)**: 3002 供給編集権
> (上記、失効済) と同型の期限付き編集権を **issue 2038 の (12.14) chiRho 供給 chain** に付与: b は
> **a 所有 S09 chiRho 機構ファイル** (`S09_Building78C.lean`・`S09_NonexistenceCertain/*` 等) への
> **純 additive・proven な helper theorem 追加**を行ってよい (条件 = 3002 先例と同一: (i) additive のみ、
> (ii) proven (sorry 追加なし)、(iii) 用途 = 2038 (12.14) 供給、(iv) issue で self-flag)。既存宣言の
> statement/proof 改変は従来どおり逸脱。**(12.14) 供給完了で失効**。詳細 = issues/2038 「HUB carve-out」節。
>
> **carve-out (issue 9092 供給編集権, hub 裁定 2026-07-13 監視 tick — merge a6fa0ca5)**: 3002/2038 供給編集権と
> 同型の期限付き編集権を **issue 9092 の `mu_isColumnFamily` 供給** に付与: b は **`Hypothesis` (SubcoherenceInputs,
> b territory) への field 追加 + 全 producer 同時放電を 1 coordinated commit** で行ってよく、その放電のうち
> **a 所有 `FeitThompson.lean` の Hypothesis producer (:1392/+1556/1686) への `mu_isColumnFamily` near-definitional
> 供給行の追加**を許容 (`mu:=muS:=columnFamily.mu` ゆえ near-definitional)。条件: (i) FeitThompson は当該 field の
> near-definitional 供給行のみ (他 statement/math 不変)、(ii) **field+全 producer 放電を 1 commit** (build 破壊回避)、
> (iii) issue 9092 で self-flag、(iv) build green。⟹ step 1.5 で b が FeitThompson の当該供給行を編集していても
> 逸脱でない (他の FeitThompson 編集は従来どおり逸脱)。**mu_isColumnFamily 供給完了で失効**。詳細 = issues/9092。
>
> **carve-out (issue 9094 供給編集権, hub 裁定 2026-07-13 監視 tick 4 — merge c14d8a01)**: 3002/2038/9092 と
> 同型の期限付き proof-only 編集権を **issue 9094 の λ-cluster restructure (案 A)** に付与: b は
> **c 所有 `S16_NonExistenceG/TTypeII.lean` の `T_side_caseB_facts` (:191-196) の proof 差し替え**
> (旧 `character_degree_analysis` obtain → 新 dichotomy-split export cite) を行ってよい。statement は
> 無条件のまま正しい (Coq PFsection14 `ltqp`+(13.12)/(13.13)-on-T 準拠、hub 検証済) ゆえ **proof のみ**。
> 条件: (i) statement 不変、(ii) c の A0-Dade/BetaData 領域非接触、(iii) issue 9094+commit self-flag、
> (iv) build green。**移行完了で失効**。NormEstimates 5 定理の dichotomy thread は b 自所有で通常作業。
> 詳細 = issues/9094 HUB RULING (案 A = λ-free Core 分割、右分岐は landed CliffordCaseBData vocabulary、
> 非破壊移行手順つき)。
> **⟹ 拡張 (hub 裁定 2026-07-14 tick 8 — merge 78193bad)**: b の **a 所有 S09 Hypothesis76/chiRho
> 機構ファイル (S09_Building78C 等) への純 additive・proven helper 追加 (用途 = 9094/2035 供給)** を
> retroactive 受理し本編集権に統合 (実例 = `hypothesis76OfDadeBase` (7.7) 任意 base builder +57 行、
> 2035 #24 self-flag 済; 2038 供給編集権 (用途 (12.14)) と同型の 9094 用途版)。条件は 2038 と同一:
> (i) additive のみ、(ii) proven、(iii) 用途 9094/2035、(iv) self-flag。a の active S09
> (S09_FrobeniusParity (7.10) 系) と非交差確認済。**9094 供給完了で失効**。
>
> **carve-out (issue 9087 RULING #4, hub 裁定 2026-07-13 監視 tick 2 — merge da032e55)**: newly-ungated
> 3 decl — `card_LF_coprime_pq` (`S15_Gate3.lean:157`) / `allTypeI_fittingIsTI` (`S14_MaximalI/
> TypeICovering.lean:68`, private) / `not_nonTypeICovering_of_all_typeI` (同 `:95`, private) — を
> **lane a へ decl 単位 carve-out** (両 file は本来 b territory)。根拠: a 自領域 genuine 候補ゼロ
> (census #print axioms 確定) / b は 2035 active で 3 target と非交差 (機械検証済) / ungated genuine
> on-path math ((13.17.b) B2 + (12.17) all-type-I chain) を idle 化しない / unblock 元 = a で文脈鮮度。
> 条件: (i) signature 不変 (statement 改変は要 hub flag、proof 供給 + stale docstring 訂正のみ)、
> (ii) 新規 helper は additive のみ (既存 b 宣言の改変・削除は逸脱)、(iii) 9087+commit で self-flag、
> (iv) build green。**3 decl の sorry-free 化で失効** (完全 b 所有へ復帰)。b は当該 3 decl を再証明
> しない。⟹ step 1.5 で a が S15_Gate3 / TypeICovering の**当該 decl 文脈のみ**を編集しても逸脱で
> ない (a が両 file の他領域 = b の既存宣言を触ったら従来どおり逸脱)。詳細 = issues/9087 RULING #4。
> **⟹ ❌ 失効 (2026-07-14 監視 tick — merge 004be7f0)**: 3 decl 全て sorry-free 化で失効条件充足。
> S15_Gate3 / S14_MaximalI/TypeICovering は完全 b 所有へ復帰。3/3 `not_nonTypeICovering_of_all_typeI`
> の signature 変更 (provenance 引数化) は self-flag → hub 受理 (as-stated は carrier provenance
> 非記録による in-file 循環で証明不能 — producer `bgTheoremE_cover_data` (a 所有 S10) の教科書
> (8.8.b) 準拠強化とセットの honest fix; 他 consumer 無影響を機械検証済)。b は次回 main sync で
> 新 signature を取り込む (再 restate しない)。
>
> **⟹ 拡張 #2 (ユーザー裁定 2026-07-05 tick(3) — Hypothesis76 (7.6) 忠実化 field の包括許可)**:
> 同型逸脱 3 連発 (issue 0091 Hypothesis78 / zeta_induced / zeta_injective、各回ユーザー受理) の
> 反復解消として、**issue 2034/3002 の (13.5) 供給作業中に限り、b による `S09_NonexistenceCertain`
> `structure Hypothesis76` への Pf (7.6) 忠実な field 追加を包括許可**する。条件: (i) field **追加**のみ
> (既存 field の改変・削除は逸脱)、(ii) 教科書 (7.6) に忠実な内容、(iii) 供給 (構築子/consumer 更新)
> 込みで build green、(iv) issue 2034/3002 で self-flag。**2034/3002 完了で失効**。Hypothesis76 以外の
> S09_NonexistenceCertain 編集は従来どおり逸脱。

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
   owned_re='^OddOrder/Peterfalvi/S(0[3-9]|1[0-6])|^OddOrder/BG/|^OddOrder/FeitThompson'  # 全 Pf S03-16 + BG を許容; per-lane 厳密判定は 🔒 マップ (a=S03-13+FeitThompson+S07 ν-constructor carve-out 9016 / b=S14_MaximalI+coherence+carve-out 0090/0096+BG §15/§16 node 9017 / c=S15-16; BG は大部分共有凍結だが §15/§16 node = b active 9017)
   shared_re='^OddOrder/AxiomsCheck\.lean$|^OddOrder\.lean$|^OddOrder/GroupTheory/|^OddOrder/Mathlib/|^OddOrder/Algebra/|^OddOrder/Isaacs/|^OddOrder/FeitThompson'  # GroupTheory/Mathlib/Algebra/Isaacs=汎用/基盤 infra (全 lane 加算可; Isaacs は 2026-07-04 hub 裁定で shared foundation、additive のみ)。FeitThompson は regex 互換で残すが実際は lane a 所有 — a 以外の FT 編集は 🔒 マップ注記どおり hub flag
   git diff --name-only main...$b -- '*.lean' | grep -vE "$owned_re" | grep -vE "$shared_re" | grep . && echo "範囲逸脱 → STOP"
   ```
   逸脱なし（空）→ step 1.6 へ。共有ファイル・notes・issues のみの差分は逸脱でない。
1.6. **shared-infra 重複検出（claim-before-build 運用、ユーザー裁定 2026-07-01）**:
   `ft_path_policy.md` §0 policy 6 で、複数の gated レーンが同じ上流 shared infra
   （未所有 leaf `OddOrder/(Algebra|GroupTheory|Mathlib)/**`）を同時並行構築する重複を防ぐ。各 tick で:
   - **(a) 同一 leaf path の衝突**: 2 つ以上のレーンが**同じ新規** shared-infra `.lean` を追加していないか。
     ```
     for L in a b c; do git diff --name-only --diff-filter=A main...$L -- \
       'OddOrder/Algebra/**' 'OddOrder/GroupTheory/**' 'OddOrder/Mathlib/**'; done | sort | uniq -d | grep . \
       && echo "shared-infra path 衝突 → STOP"
     ```
   - **(b) claim なしの新規 shared-infra leaf**: 新規追加された shared-infra `.lean` に対応する open 9000
     番台 claim issue が**無い**（`issues/9*-*.md` を grep）→ ⚠ flag（沈黙構築 = policy 6 違反の疑い）。
   - **(c) 同一 ref の 2 claim**: open 9000 番台 issue に同じ教科書 ref / 補題名の claim が 2 件 → STOP。
   検出したら **STOP + 報告**（より完成度の高い方を残し、他方を cite に rebase させる指示。浪費は ~1 tick に
   有界）。空 → step 2 へ。**grandfather**: 2026-07-01 前 landing 済 leaf（`GaloisRationalInteger.lean` 等）は対象外。
2. **a → b → c の順**で（独立レーンゆえ順序は形式的、上流→下流の自然順）、未マージがあれば自動合流:
   - マージ前の実 sorry 数を記録: `bin/count-sorry`
     （prose 偽陽性 [sorry-free / sorryAx / `sorry'd` / backtick 引用] を除外する判定器。
       旧 `grep '(^|[^a-zA-Z-])sorry'` は 259 と過大計上したが count-sorry は 146 ≈ 実 141。
       絶対数の ground truth は build 警告 `lake build OddOrder 2>&1 | grep -c 'uses .sorry.'`）
   - `git merge --no-ff --no-commit <branch>`
   - **コンフリクト時**:
     - `AxiomsCheck.lean` / `OddOrder.lean` の**独立追記衝突** = 両ブロック保持で解決して続行
       （A=keystone 系の `#assert_only_allowed_axioms`、B=Peterfalvi 系の同コマンドは別定理ゆえ両方有効）
     - **`issues/**`・`notes/**` (.md) の独立追記衝突も同様に両ブロック保持で続行** (hub 裁定
       2026-07-10 tick で明文化: hub の裁定追記と lane の進捗追記が同一 issue 末尾に付く型は
       AxiomsCheck 独立追記と同じ良性クラス、build 影響なし。実例 = issues/2038 の
       carve-out 記録 vs whnf-wall 診断、merge 68dd36ca)。**同一行・同一節をどちらも書き換える
       絡み衝突は従来どおり abort+報告**
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
     `Merge '<branch>' (<topic>): <要約>` + 本文に各単位 + 末尾に
     現行モデルの trailer (harness 既定; 2026-07-02 現在 Claude Fable 5)
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
7. **❄ FROZEN 2026-06-18 — LOOP GATE VERDICT 維持 (2026-06-17 追加, [`lane_loop_policy.md`](lane_loop_policy.md); LOOP GATE 機構停止中。⚠ 以下の例中のレーン名 h/G/F/B は 2026-06-28 改名前の旧名 = 履歴。現行レーンは a/b/c)**: 各 worktree の
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

- **⚠ live-branch merge race (2026-07-12 tick 15 実害 → 手順化)**: レーンは 60s wakeup で数分おきに
  commit するため、hub の step 1.5 scope-check と `git merge <branch>` の**間**に新 commit が積まれると、
  merge は check していない commit まで取り込む (実例: a@29b08747 を check → merge 時に a が 700ba71f を
  積んでおり merge 38df2e1d の第 2 親が 700ba71f になった; 遡及チェックで clean を確認・build/AxiomsCheck は
  merged tree に対して有効だったので実害なし)。**防止: step 1 で各レーンの tip SHA を pin し
  (`tip=$(git rev-parse <branch>)`)、以後の 1.5/1.6 diff も merge も全て `$tip` に対して行う**
  (`git merge --no-ff --no-commit $tip`)。merge 後に branch が進んでいても pinned SHA 分だけが対象になり、
  超過分は次 tick に自然に回る。commit message の `@<sha>` も pin した SHA を書く。
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
- **⚠ 「空 sync merge」判定は stale になる (2026-07-11 実害)**: tick 冒頭で `git diff main <lane>` が
  空 (= sync のみ) でも、a/b の merge・build を待つ間に lane が新 commit を push しうる。空と判断して
  `git merge --no-ff <lane>` を **--no-commit なし + push 連鎖**で実行した結果、未検証 .lean (新 leaf
  74 行) が build 前に main に載った (事後検証で green・実害なし)。対策: (1) **merge 直前に
  `git rev-list main..<lane>` を再確認** (tick 冒頭の値を使い回さない)、(2) sync-only でも
  **常に `--no-commit` で trial merge** し staged を見てから commit、(3) **push は全レーン検証完了後の
  単独コマンド** (merge と同一 bash に連鎖させない)。
  - **⚠⚠ 再発 (2026-07-11 同日 2 度目、今回は実害 = red main push) → SHA 固定を必須化**: 上記 (1)-(3) が
    advice 止まりで再度素通りした (検査は `0a128d16` 時点、merge が未検査の新 tip `5f2e11cb` を取り込み、
    その中の AxiomsCheck assert 5 本が sorryAx 依存で red — c は codex 運用で push が速く、检査→merge の
    数分の窓でも stale 化する)。**以後必須の手順**: tick 冒頭で `TIP=$(git rev-parse <lane>)` を採取し、
    範囲逸脱・axiom・sorry の全検査を **その $TIP に対して**行い、merge も **`git merge --no-ff $TIP`**
    (branch 名でなく **SHA を merge**) で行う。これで検査対象と取り込み対象が構造的に一致し、stale-tip
    混入は不可能になる。tick 中に lane が進んでいれば差分は次 tick に自然に回る。
  - **⚠ `lake build … | tail` は exit code を隠蔽する (2026-07-11 実害の相方)**: pipe の最終コマンド
    (tail/grep) の exit 0 が build 失敗を上書きし、後続の `git push` 連鎖が red を通した。**build は
    `> log 2>&1` リダイレクト + `echo EXIT=$?` で exit code を明示確認**し、push は green 確認を
    **読んだ後の別 bash** で行う (上記 (3) の強化; [[lean-build-discipline]] の「build 検証と commit は
    別 bash」は push にも適用)。
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

- **2026-07-14 (tick 48) — ★ a (13.15) 実証明 = OrderDetermination 移管 4 sorry 完遂 + b refuter-T campaign 開始**:
  **a=1** (`a6c9bb3f` = ★ **(13.15) caseB_order_u 実証明** — 数値エンジンを S16_CaseBOrder →
  新 Setup leaf `CaseBOrder.lean` (399 行) へ自己 relayer し honest 入力で実証明。旧 opaque 版削除、
  下流互換 bridge `caseB_order_u_data` のみ faithful scaffold +1。S16_CaseBOrder は deprecated
  redirect 化 (下流不変、内容ベースで a 域 = 非逸脱)。**0115 移管 4 本 ((13.11)-(13.15)) 全て実証明
  完了、OrderDetermination.lean 実 sorry 0** — 0116 sequencing 条件 (ii) の対象 cluster が close。
  残 = CaseBOrder:394 bridge 1 本 (CliffordCaseBData certificate 化が次 obligation)。merge)。
  **b=5** (`825ebdd9`〜`aa5ecb5a` = **refuter-T campaign 開始** — #74 4-obligation の refuter-T
  (S15_TSetMemberRFamily:1017) mirror。新 leaf 3 本 sorry-free: NineElevenPairBoundT 641 /
  NineElevenStepsT 677 / NineElevenSevenEightT 656、OddOrder.lean 配線済。NuRowPin 微修正。
  issues/2035 で hub #75 vs b #75 の独立追記衝突 → 両保持 + b 側 #76 振り直し。merge)。c=0。
  build green **4210→4213 jobs** (+4 = 新 leaf 実 elaborate) / AxiomsCheck OK / census **40 不変**
  (a: −1 実 discharge +1 scaffold) / 新 axiom なし / 逸脱なし / orphan なし。push 済。
  **0116 追跡**: 条件 (ii) は「a の OrderDetermination cluster quiet 化」→ 移管 4 本完遂で実質成立に
  接近 (a の次 frontier が同 file 群を離れるか次 tick で確認)。条件 (i) = b の hT2 弱化裁定は未応答
  (b は 2035 #75 未読の可能性 — 今 tick で main 経由配達済、b の refuter-T campaign は #75 の弱化と
  独立に進行可能なので block しない)。
- **2026-07-14 (監視再開、tick 48〜) — ユーザー指示で監視ループ再開**:
  cron `a51a9e3d` を再作成 (Fable=30分 `13,43`)。再開時点: `main..{a,b,c}` = 0・全 worktree clean・
  レーン operator 未稼働 (ユーザーが順次起動予定)。tick 47 記録の再開時 hub TODO 処理:
  (1) 合流対象なし。(2) **0116 relayer = トリガー成立と判断** — 2035 #74 で b の θ-package 本体組立完了、
  T-side campaign の残りは 4 named obligation (refuter-T / nuGridSupply / T_isTypeP2_gate / no_lambda) に
  collapse = (13.4)/(13.3) cluster close の節目。かつ全レーン quiet の今が衝突最小 window ⟹ hub が着手
  (issue 0116 に実施記録)。(3) NuRowPin 1261 行 (<1500) = watch 継続、対処不要。
  **⟹ 0116 調査完了・HUB RULING 記録 (同日)**: 5-agent workflow (wf_746d2ebb) + hub 自前検証で
  設計確定 — (a) SAndTBasic:841 は c の 9077 #3 carve-out ゆえ scope 外 (かつ c の route は
  DAG-blocked → 9077 に HOLD+item-2-first を追記)、(b) 「NormEstimates 沈降」は c_eq_one の
  (13.10) 依存 + mid-layer 実 cite で cycle = 不可能、(c) **T_isTypeP2_gate は layer-inversion
  でなく証明循環** (T_isTypeP2 → … → gate を hub が TTypeII 読解 + Coq PFsection13 対照で確認)
  → honest fix = hT2 弱化 (b の math、2035 #75 で通知)、(d) 実施 = Route T (threading、新
  discharge leaf) で確定だが **sequencing = b の hT2 弱化裁定 + a の OrderDetermination cluster
  quiet 化の後** (threading が a の active decl 群 numeric_bounds/c_eq_one/caseA_parameters の
  signature を編集するため — 0116 トリガー節と同じ anti-collision 原則、コスト理由でない)。
  hub は毎 tick で両条件を追跡し、成立 tick で Route T 実施。size flags: CDS 2239 行 (b へ flag
  済 2035 #75) / CountingLayer 2001 行 (Route T step 3 で解消予定)。
- **2026-07-14 (tick 47、最終 sweep) — 監視停止 (ユーザー「いったん区切ります」) + 9077 RULING #3**:
  cron `88a50cb0` を CronDelete。⛔ 停止 (問題起因) ではないので**自動再開しない** — 次回はユーザー指示で
  現行モデル対応ペース (Fable=30分 `13,43`) で再作成。最終 sweep: **a=1** (`0a75fb65` = ★ **(13.13)
  caseA parameter determination 実証明** — opaque Prop を real CliffordCaseAData に置換、9098 の
  divisibility 算術 engine で q=3 ∧ u=(p−1)²/4。OrderDetermination 3/4 本目)。**b=3** (`83da2170` 系 =
  ★ **(13.4) theta-package assembly — monolithic sorry を faithful restate + bricks で置換**)。
  **c=6** (`3d4e4eee` (14.14) producer → `078402d7` **自己検出 revert** (census 誤り: 既存 landed の重複。
  consumer 側から遡らない grep の失敗と自己分析) + 9077 **reallocation 要請 #2**)。
  0115 で a/c の追記が append-append conflict → 両報告保持で解決。build green **4209 jobs** /
  AxiomsCheck OK / census **41→40 (実 −1)** / 新 axiom なし / orphan clean。push 済。
  ★ **9077 HUB RULING #3**: c の次 = b quiet file 2 宣言の proof-only carve-out
  (`V_inf_centralizer_Q_eq_bot` + `sibleyTarget_frobI`)。候補 (ii) は a の (13.15) 宣言と衝突ゆえ却下。
  **停止時点**: main = 本 commit (push 済・tree clean)、`main..{a,b,c}` = 0 (sweep 完了、以後の
  レーン新 commit は次回 hub 再開時に合流)、census 40 (朝 49 → 実 −9 の 1 日)。
  再開時の hub TODO: (1) レーン新 commit の合流、(2) 0116 relayer の実施判断 (b の (13.4) cluster
  close 後トリガー — theta-package assembly 済みにつき近い)、(3) NuRowPin 1261 行の size watch。
- **2026-07-14 (tick 46) — ★★ c Campaign B も完了 (0115 両 campaign 当日完遂)。3 レーン合流、census 42→41**:
  **a=4** (`9b5c33ba`〜`c1a3f72e` = claim 9098 (block-scalar divisibility infra、claim-before-build ✓) →
  case A block bound の divisibility 強化 + two-primary factor 除去。新 leaf S11_CaseAOddPartBound +
  GroupTheory 2 file。b-owned HypothesisBasics への touch は**自 leaf の import 1 行のみ** (mechanical、
  受理)。sorry 0/0。merge)。
  **b=3** (`cd621023`〜`e11e4aa5` = **tau1T_ofHonest bundling (#41 step 5 前半)** + (1.5.a)-T membership
  layer + theta-package conjunct 2-4 producers complete。新 leaf S15_Tau1T +700 (配線済)、AxiomsCheck
  追従。sorry 0/0。merge)。
  **c=4** (`13fe64d5` = ★ **0115 Campaign B 完了 — T-side (9.7.b) field model を 9097 adapter
  (a の ConjugationFieldModel) で discharge、`t_side_caseB_fieldModel` 実証明 (SubgroupM 2→1)**。
  + docs 3: Campaign B 完了記録・次 frontier = (14.14) OrthogonalitySwitchData producer (Coq LM_cases
  port) の組立設計 census・b 宛 V_inf_centralizer_Q_eq_bot discharge note。merge)。
  build green **4209 jobs** (+2 = S15_Tau1T/S11_CaseAOddPartBound 実 elaborate) / AxiomsCheck OK /
  census **42→41 (実 −1)** / 新 axiom なし / 逸脱なし (a の cross-touch は import-only) / orphan clean。
  push 済。**0115 の c 両 campaign が再起動当日に完遂** — c は自律的に次 frontier ((14.14)) を設計済み。
  SubgroupM 残 1 (hu_full) は a の (13.15) landing 待ち = 既知 pipeline。
- **2026-07-14 (tick 45) — ★★ 3 レーン同時 landing: census 46→42 (実 −4)。c Campaign A 完了**:
  **a=1** (`6f6e3414` = **(13.12) PC Hall obligation 実証明** (OrderDetermination 移管 4 sorry の 2 本目、
  実 discharge −1、残 = (13.13)/(13.15) の de-opacify 2 本)。merge)。
  **b=2** (`29ef27bf`/`13cb3f34` = **(13.3.c)-T ν-row pin dichotomy 完成** + pinned (9.11)-T coherence
  carrier = 2035 #41 step 4 complete。S15_NuRowPin +994 (現 1261 行 — ⚠ 1500 接近 watch)、AxiomsCheck
  assert 11 本自発追記、sorry 0/0。merge)。
  **c=3** (`e357717d`/`3fe31b7f`/`567e2866` = ★ **0115 Campaign A 完了**: L-side off-principal grid
  parities を (13.19.c) dichotomies から実証明 + honest (14.11.2) L-side Y=0 + chi classification
  (grid_mem overclaim は除去し producer sorry-free 化)。**ComparingLM の実 sorry 3→0**。0115 に実施
  報告。再起動当日に campaign 1 本完遂。merge)。
  build green **4207 jobs** / AxiomsCheck OK / census **46→42 (実 −4: a 1 + c 3)** / 新 axiom なし /
  逸脱なし / orphan clean。push 済。S16 残 = SubgroupM 2 (Campaign B 進行中)、OrderDetermination 残 2。
- **2026-07-14 (tick 44、ミニ — c 初 commit) — c 再稼働後の first landing: hu_full statement 修正**:
  **c=1** (`3450746f` = **0115 監査 caveat への即応**: SubgroupM `hu_full` の statement バグ
  (p ≡ 1 (mod q) 枝と矛盾する無条件 u-値主張) を branch-independent な (9.7.b) gate に修正
  (+63/−48、faithfulness 修正)。operator = Claude session (Fable、15:57 起動、issue 0105 の codex
  運用から変更 — 0105 に注記要)。merge)。a=0 / b=0 (両者稼働中)。
  build green **4207 jobs** / AxiomsCheck OK / census **46 不変** (統計 +1/−2 は restate に伴う
  移動、comment-strip net 0) / 新 axiom なし / 逸脱なし。push 済。c は続けて Campaign A
  (ComparingLM) を編集中。**3 レーン + hub の full pipeline が完全稼働**。
- **2026-07-14 (tick 43) — ★ 再設計後の初 tick: 3 レーン全て稼働状態に復帰。a (13.11) 実証明 + b caseA-T (9.11) 本体**:
  **a=1** (`e775eced` = ★ **(13.11) numeric_bounds 実証明** — issue 0115 の OrderDetermination b→a
  移管を a が即消化した初 landing (sorry 実 discharge −1)。同 file 編集は移管済みゆえ非逸脱。merge)。
  **b=3** (`5054d391`/`5d9e8a36`/`6af94346` = **caseA-T (9.11) base coherence on Ind_T^G** +
  assembly/dispatch `sSet_coherent_indT_A` + 新 leaf `S15_NuRowPin` +267 (ν-row pin machinery layer 1、
  配線済・faithful pin scaffold +1)。merge)。
  **c=再稼働確認**: live process (16:21〜) が `SubgroupM.lean` を編集中 = **0115 Campaign B に着手**。
  dirty は稼働中につき非接触。main 同期済 (behind 0)。
  build green **4207 jobs** (+1 = NuRowPin 実 elaborate) / AxiomsCheck OK / census **46 不変**
  (a −1 実証明 + b +1 scaffold) / 新 axiom なし / 逸脱なし / orphan clean。push 済。
  ⟹ 0115 再設計が 1 tick で全面稼働: a=OrderDetermination / b=2035 T-side / c=Campaign B。
- **2026-07-14 (tick 42) — a+b 合流: (9.7.b) conjugation field model (shared leaf) + caseA-T base-cut coherence**:
  **a=1** (`fcb25e47` = ★ **norm-one conjugation field model 構築** — (9.7.b) faithful carrier の新
  shared leaf `GroupTheory/RepresentationTheory/ConjugationFieldModel.lean` +199 (sorry 0)。
  **claim 9097 起票→close・OddOrder.lean 配線・AxiomsCheck assert 13 本まで 1 commit 内で完備**
  (手順の模範実施)。c の 0115 Campaign B (T-side Singer field model) の上流部品。merge)。
  **b=3** (`b8ce4654`/`f98a61ea`/`5da34f33` = caseA-T 設計監査 #62 + sSetIrrDegT uniform-degree cut +
  **caseA-T base-cut coherence (subcoherent + (5.7) producer)**。S15_TSetMemberRFamily +202、実 sorry 0。
  merge)。c=0 (operator 起動待ち)。b は追加 3 file 編集中 (稼働中、非接触)。
  build green **4206 jobs** (+1 = ConjugationFieldModel 実 elaborate) / AxiomsCheck OK / census **46 不変** /
  新 axiom なし / 逸脱なし / orphan clean。push 済。
- **2026-07-14 (tick 41) — ★ b 合流 (caseB-T (9.11) coherence) + レーン再設計裁定 (issue 0115/0116)**:
  **b=6** (`4ae89c31`/`d8ec3e45`/`fd2c0675`/`cc3fa98a` = ★ **caseB-T (9.11) coherence
  `sSet_coherent_dade_caseB_T`** + (5.2.e) cross-orthogonality + dadeT0 regular-set vanishing +
  dispatcher reductions。S15_TSetMemberRFamily +506、実 sorry 0。merge)。a=0 / c=0。
  build green **4205 jobs** / AxiomsCheck OK / census **46 不変** / 新 axiom なし / 逸脱なし / orphan clean。
  ★ **レーン再設計 (ユーザー発議「c 停止・レーン増設?」→ hub 3 並列監査 wf_525303b8 → issue 0115)**:
  c 再起動 GO (4/5 workable、独立 2 campaign 定義済、hu_full statement mismatch の caveat 付き) /
  OrderDetermination b→a 移管 (4 sorry、a の 9000 材料の自然な consumer、b active set と非交差) /
  4 レーン目は Appendices off-path 確定につき見送り (3 レーン飽和が正解) / NormEstimates 系
  layer-inversion は hub relayer issue 0116 で追跡。push 済。**c の operator 起動はユーザー操作待ち**。
- **2026-07-14 (tick 40) — a+b 合流: T-side prime-TI Dade cross-relation ほか / ⚠ orphan 1 件を hub 配線で修正**:
  **a=1** (`132a1dbf` = section16 capstone boundary の docstring 訂正 (−6 hit は全て prose 内 `sorry` 言及、
  comment-strip で両版 real 0 確認)。merge)。
  **b=6** (`7439926c` = T-side A0-Dade vanish quartet `tauT_nu_vanish_on_V`、`320b7dd8` = ★ **tauT_nu_cross
  (T-side prime-TI Dade cross-relation)**、`732a2573` = dade=Ind bridge chain、`6d7ef716` = reducible
  T-member row distinctness + row-sum Dade image、`e7e0bd00` = 新 leaf `S15_TSetMemberRFamily` +169、
  #52 依存監査。全 +642 additive、実 sorry 0。merge)。c=0。
  ⚠ **orphan 検出→即修正**: 新 leaf `S15_TSetMemberRFamily` が root closure 外 (初回 build 4204 jobs =
  未 elaborate)。gotcha 手順どおり hub が OddOrder.lean へ import 追加 (sanctioned) → **再 build green
  4205 jobs** (+1 = 実 elaborate 確認)・orphan re-scan clean。b への申し送り: 新 leaf は作成 commit 内で
  root 配線まで含めること (TSideDegrees の hub import は同 commit で実施済みだった — R-family leaf のみ漏れ)。
  AxiomsCheck OK / census **46 不変** / 新 axiom なし / 逸脱なし。push 済。
- **2026-07-14 (tick 39) — ★ b 合流: 9086 差し戻しに模範対応 + T-side 2035 campaign 大幅前進 / a docs**:
  **b=de-dup 済 tip `d5d6f0d2` を合流** (b は 9086 裁定を同期 merge `8675a186` 内で即消化 — dup leaf
  drop、cite 発生前に解消。net diff は TSideDegrees +314 (実 sorry 0) + issues のみで dup-free 確認済。
  数学: `6f84ff33` = **(13.2.a)-at-T `isMulCommutative_V` 無条件化** ((14.9) 入力なし — type-II/III
  witness + SZ transport、type-IV は (11.9.c) 排除、type-V は (10.10))、`6a6db61d` = caseB-T uniform
  degree p·v、`999e8c47` = (4.7)-at-T member support trio、`6c4fbb7b` = dadeHypT (A(T)-Dade datum、
  hT2-parametric) + oddCardT、`d5d6f0d2` = (5.3.a)-at-T conjugate-diff support pair。#43-#49 記録)。
  **a=1** (`b48ada04` = superseded T-side TypePData issue close。dirty 2 file は稼働中につき非接触)。c=0。
  build green **4204 jobs** / AxiomsCheck OK / census **46 不変** (+1 hit は docstring「sorry-free」、
  comment-strip で実 0 確認) / 新 axiom なし / 逸脱なし / orphan clean。push 済。
  ⚠ 注記: `main..b` 履歴に dup SHA (2ca52edf) は残るが tree は dup-free (drop 済) — 以後の tick は
  net diff で判定。**isMulCommutative_V 無条件化は c の旧 hold gate の 1 つ (V abelian 系) に波及する
  可能性** — c 再開判定の材料として次 tick で確認。
- **2026-07-14 (tick 38) — a 合流 (AxiomsCheck guard 登録) + b **partial** 合流 (step 1 genuine / ⚠ dup leaf 差し戻し = 9086 裁定)**:
  **a=4** (`07787735`/`5907e03a` = tick 37 follow-up: **section16 producer chain 12 宣言 + type-P2 Dade
  bundle の AxiomsCheck assert 登録** (+29)、`fd980c5b`/`887ef16d` = 9087 記録 + stale spine-root 診断
  issue 2 件 close (9090/9091)。merge)。
  **b=4 中 2 のみ合流** (`02a4f916` = 2035 #41 step 1 `sSet_reducible_eq_nuRowSum` 実証明 (TSideDegrees
  +44 sorry-free) + `c3892668` = #42 D-abelian route 記録。merge `e68658ad`)。⚠ **b `2ca52edf`
  (新 leaf NilpotentCyclicAbelianization +120) は a の既存 9086 leaf `NilpotentAbelianization` の
  真部分複製 + consumer-0 orphan と hub 照合で確定 → `e1dea754` (#43、dup 前提 docs) と共に未合流・
  差し戻し** (9086 HUB RULING + 2035 に cite 先回答を記録。route #43 自体は genuine 評価 — supply 元の
  差し替えのみ)。次 tick 以降 `main..b` に両 SHA が残るのは既知状態 (盲目的 merge 禁止)。c=0。
  build green **4204 jobs** / AxiomsCheck OK (a の新 guard 込み) / census **46 不変** / 新 axiom なし /
  orphan scan clean。push 済。⚠ hub 手順スリップ 1 件 (裁定 issue 編集を staged のまま merge 実行 →
  exit 2、commit 後に再 merge で解消。「手動マージは atomic」gotcha の再確認)。
- **2026-07-14 (tick 37) — ★★★ a 合流: 9087 carve-out 実施 landing = FT spine Section 16 named input producer chain が axiom-clean 化**:
  **a=2** (`abac8ca9` = carve-out 実施 (裁定条件 4 点全遵守: 3 cite 置換のみ / 単独 commit / message
  self-flag / 9087 実測記録)。`58f0f533` = landing 記録: **12 宣言が `[propext, Classical.choice,
  Quot.sound]` のみに** — BG §16 `theoremII_tame_embedding{,_of_inputs}` / Pf §10 type-I Dade 2 本 /
  Pf §14 4 本 (`not_all_maximal_typeI`/`theorem88_caseB_holds` 含む) / **FT spine inputs 4 本
  (`section16MaximalPair`→`section16Inputs`→`sectionSixteenHypothesis_of_isMinimalSimpleOdd`)**。
  merge)。b=0 / c=0。build green **4204 jobs** (7m01s、rewire の下流再 elaboration) / census **46 不変** /
  新 axiom なし / 逸脱なし (carve-out 範囲内)。**hub 独立実測**: flagship 2 宣言の `#print axioms` を
  scratch probe で再確認 = clean 一致。push 済。carve-out は landing で失効 (9087 記録どおり)。
  ⟹ named Section 16 input producer の**実構成が clean 化** = carrier 構成可能性の実進捗 (doneness 基準)。
  follow-up 候補: (i) 12 clean 宣言の AxiomsCheck assert 登録 (a)、(ii) consumer-0 化した legacy
  `theoremA_maximal_structure` (OVERSTATEMENT 明記、TheoremsAE の残 sorry) の retirement 検討 (b territory)。
- **2026-07-14 (tick 36) — a 合流 (docs) + ★ 9087 HUB RULING: TaxonomyOutput 3-cite rewire carve-out を a に付与**:
  **a=1** (`0df692bb` = 9087 追記: Section 16 producer chain の `#print axioms` 実測で dirty root を
  **旧 `theoremA_maximal_structure` の 3 cite (TaxonomyOutput.lean:1265/1292/1359) に局所化**。
  faithful 版は既に axiom-clean、置換は mechanical proof-only。merge)。b=0 / c=0。
  build green **4204 jobs** (docs-only、warm 確認) / census 46 不変 / 新 axiom なし。
  ★ **HUB RULING (9087 記録)**: hub が 3 site + faithful 宣言 + b ファイル非交差を検証 → **a に当該
  3 cite 置換限定の proof-only carve-out 付与** (b queue 却下 — 上流優先、b は 2035 #41 続行)。条件 =
  置換以外の編集禁止 / 単独 commit self-flag / landing で失効 / clean 化を #print axioms 実測で 9087 に記録。
  landing すれば mp producer の legacy sorryAx が除去され、named Section 16 input producer の実構成が
  clean 化する見込み (FT spine root 直結)。
- **2026-07-14 (tick 35) — a+b 合流: a unsound-route 撤去 (soundness cleanup) + b T-side (13.4) support estimate 実証明**:
  **a=1** (`f2cb4ff2` = **(6.8)-TI 依存の unsound subtree 撤去**: `S11.sibleyTarget_H0C` + 唯一 consumer
  `coherent_H0C_commutator` + wrapper `S12.typeII_section11_coherence`、および consumer-0 legacy obligation
  `S12.coherent_Sset_diff_SHCSet` を削除。live spine は S15 honest route (`sSet_coherent_indS_A`/
  `coherent_H0Cprime_S`) が既に担う。9087 に authoritative 記録 (issue 7001/1017)。hub 検証: 残参照は
  docstring のみ + build green で code-level 無参照確定。merge `3860a802`)。
  **b=2** (`c975fec2` = **(13.4)-at-T support estimate 実証明** (TSideDegrees +68 sorry-free)、`e4509630` =
  2035 #41 T-side coherence construction plan。merge `c40721fa`)。c=0。
  build green **4204 jobs** / AxiomsCheck OK / count-sorry **48→46** (両減とも a の unsound/dead sorried
  obligation 削除による census 減 — 実証明 discharge でなく soundness cleanup、開示済み) / 新 axiom なし /
  逸脱なし / orphan scan clean。push 済。**a-owned S03–S13/FeitThompson の literal sorry = 0 に到達**
  (a 注記どおり FT 完了指標ではない — 9096 ν pins の cross-lane explicit 配線が genuine frontier)。
- **2026-07-14 (tick 34) — ★★ a+b 合流: 9096 ν-carrier campaign 完結 (a threading + b T-side (13.2.b)/(13.3.a,b)) + sorry 実 discharge 49→48**:
  **a=4** (`bef0c054` = 9096 item 3 / issue 1030 完了: `sectionSixteenNuGridSupplyData_of_inputs` 構成
  (10 pure grid fields → NuGridSupplyData、`#print axioms` clean、AxiomsCheck assert 追加)。generic
  `nuGridSupply` は row-translation gap で証明不能のまま = 下流は explicit-pins rewiring (9096 記録) が正。
  + issue hygiene 3 commits: **9000 σ-theory claim close (完遂)** ・1012/1019/1029/1030/9079 close。
  merge `6d4a4fd5`)。
  **b=3** (`214bf3b5`/`4ce9e84c`/`78506664` = T-side (13.2.b) `card_Q_eq_qp` **無条件証明** + (13.3.a)
  `nu_apply_one_eq_v` **実証明** (tick 33 の scaffold discharge、TSideDegrees 現在 sorry-free) +
  (13.3.b)-at-T theta-witness dichotomy。issue 2035 記録。merge `02485e6a`)。c=0。
  build green **4204 jobs** (統合状態 1m09s) / AxiomsCheck OK (a の新 assert 込み) / count-sorry
  **49→48 (実 discharge)** / 新 axiom なし (diff の 'axiom' hit は doc 文字列のみ確認済) / 逸脱なし /
  orphan scan clean。push 済。
  ⟹ **9096 の裁定チェーン (b split → a threading → b T-side 再開) が同日中に全 landing**。b の次 =
  explicit-pins 消費で T-side (13.3.c)/(13.4) 続行。⚠ c 再開トリガー関連: a が 9000 を完遂 close —
  ただし c の直近 gate (昨夜自己評価) は b-side (`caseB_order_u`/`character_degree_analysis`/parity+grid)
  ゆえ hold 継続、b の T-side landing 波及を監視。
- **2026-07-14 (tick 33) — ★ b 合流: 9096 RULING 実施 = NuGridSupplyData pure grid 化 + T-side (13.3.c) δ'=1 assembly**:
  **b=2** (`701fb8f4` = bundle split 手術: `V_commutative` field 削除・`Hypothesis.swap` に明示引数 `hV`
  追加 (hT2 直後)・consumer 2 箇所は既存 hT2 から (14.9) 系 theorem 経由で内部導出 = signature 不変。
  `98fb5a14` = T-side (13.3.c) `deltaPrime_eq_one_T` **sorry 実 discharge** + 新 leaf
  `S15_SAndT_Setup/TSideDegrees.lean` +343 (nu identity-value scaffold 1 本 = a の 1030 threading が
  埋める前提、faithful)。9096 に実施報告 + 新 signature の a 宛通知を自己記録)。a=0 / c=0。
  build green **4204 jobs** (2m31s) / AxiomsCheck OK / count-sorry **49→49 不変** (S15 内で −1 実証明
  +1 新 scaffold) / 新 axiom なし / 逸脱なし (全 b-owned S15 cluster) / orphan scan clean (TSideDegrees
  は S15_CharacterDegreeSupply が import)。merge `8e83c01a`、push 済。
  ⟹ **9096 ruling item 2 完了 → a の producer thread (item 3, issue 1030) が un-gate**。a は現在
  probe 作業中 (未コミット) — 次 tick 以降で 1030 landing を監視。
- **2026-07-14 — 監視再開 (ユーザー指示「監視を再開して」)**: cron `88a50cb0` を Fable 規定ペース
  `13,43 * * * *` (30 分間隔) で再作成。再開時点: main = `4fdf38ce` (push 済・tree clean・full build
  green 4203 jobs)、`main..{a,b,c}` = 0、lane a は main 同期済 tree clean (codex 再開待ち)、b/c は
  session 停止中 (b は 9096 RULING の bundle split 待ち、c は hold 継続)。
- **2026-07-14 (tick 32、手動 — ユーザー指示「各レーンの進捗を統合」) — a 未コミット diff 回収 + ★ 9096 HUB RULING + c hold 継続**:
  cron 停止中 (session 新規)。**a=1** (`1f4c3ef9` = **lane-a codex session の残置 3-file diff を hub が回収 commit**:
  AxiomsCheck ν-grid assert 13 本 + issue 1029 完了記録 (checklist 全 [x]、V_commutative は意図的除外) +
  9096 A-lane ν-carrier audit。codex session は task_complete 正常終了・作業中でないことを jsonl + proc で
  確認の上で回収。merge `87fa792b`)。b=0 / c=0。build green **4203 jobs** (warm 7.4s、AxiomsCheck 再 elab
  3.7s exit 0 = 新 13 assert 全通過) / count-sorry **49→49 不変** (comment-strip census) / 新 axiom なし /
  逸脱なし (AxiomsCheck=shared sanctioned additive + issues のみ) / orphan scan N/A (新 .lean なし)。
  a は merge 後 main 同期済 (ahead 0 / behind 0、tree clean = codex 再開可能状態)。
  ★ **9096 HUB RULING 記録 = (A)-modified**: a の ν-grid canonical package landing 承認 (audit 2 主張を
  hub code-level 検証) → **b の次 work = `NuGridSupplyData` 分割手術 (b-owned HypothesisSwap.lean、
  V_commutative 除去 + hT2 以後供給へ再配線) → T-side (13.3)/(13.4) 再開**。a は split 後に producer thread。
  詳細 = issue 9096 🧭 節。
  ★ **c 再開可否 (ユーザー質問) = hold 継続が正**: 昨夜の c-codex 自己評価 (23:31 JST session、main 同期のみ)
  と hub 検証が一致 — T1 `hVcomm` は a が解消済 (TTypeII 現在 sorry-free、census 確認)、残 5 endpoint は
  b-side (`caseB_order_u` / `character_degree_analysis` / parity+grid) gated。re-engage トリガー = 本 tick の
  9096 ruling 経由で b の T-side landing 波及。⚠ 備考: c worktree に 7/1 からの stale lean プロセス
  (PID 113472、S11_MaximalII_III_IV elaborate) が残存 — 実害なし、c 再開時に自然消滅か手動 kill。
- **2026-07-14 (tick 31) — a 合流: ν-grid T-side nu conjugation (issue 1029 継続)**:
  **a=1** (`9d221886` = T-side nu conjugation。`FeitThompsonNuGrid.lean` +52 (0 sorry、計 587))。b=0 / c=0。
  build green **4203 jobs** / AxiomsCheck OK (**2416** 全 allowlist) / count-sorry **49→49 不変** / 新 axiom なし / 逸脱なし。
  ★ 9096 ν-carrier build 継続 (conjugation API 追加)。
- **2026-07-14 (tick 30) — a 合流: ν-grid T-side row sum dichotomy / value identity / difference support (issue 1029 継続)**:
  **a=3 実 commit** (`83d63b79`/`d0d3e9ca`/`6e106fdd` = T-side nu row sum dichotomy + value identity +
  difference support。`FeitThompsonNuGrid.lean` +236 (0 sorry、計 535) + `FeitThompsonSetup.lean` +6 (0 sorry)。
  全 a-owned ν-carrier files)。b=0 / c=0。build green **4203 jobs** / AxiomsCheck OK (**2416** 全 allowlist) /
  count-sorry **49→49 不変** / 新 axiom なし / 逸脱なし。sizes: NuGrid 535 / FeitThompsonSetup 1568。
  ★ 9096 ν-carrier build 継続中 (a が row-sum/value/support の T-side ν-grid API を積み上げ = b の T-side gate 前提)。
- **2026-07-14 (tick 29) — a 合流: canonical T-side ν-grid core 構築 (issue 1029) — ★ 9096 の ν-carrier gate を a が自律着手**:
  **a=1** (`bb959962` = **ν-carrier 着手**。ν-grid decls (nuT/deltaPrimeT/omegaS_inner/eTS/colT 等) を
  `FeitThompson.lean`→新 leaf `FeitThompsonNuGrid.lean` +299 へ抽出 (clean relocation、-185/+1) +
  canonical T-side nu grid core を sorry-free 構築。issue 1029 新規。全 a-owned files)。b=0 / c=0。
  build green **4203 jobs** / AxiomsCheck OK (**2416** 全 allowlist) / count-sorry **49→49 不変**
  (relocation sorry-neutral + 新 core sorry-free) / 新 axiom なし / 逸脱なし。size: NuGrid 299 / FeitThompson 1674。
  ★ **9096 進展**: b の T-side gate (`tSide_theta_package`/`deltaPrime_eq_one_T`) が要求する **ν-carrier を a が
  自律的に build 開始** (option A が organic に成立)。a の ν-grid が完成すれば b の T-side が un-gate される見込み。
  ⟹ hub は 9096 direction ruling を急がず、a の ν landing を監視 → landing tick で b に「T-side 再開可」を flag。
- **2026-07-14 (tick 28) — ★ a 合流: Peterfalvi Frobenius-family lower bound 実証明 (sorry 実 discharge 50→49)**:
  **a=1** (`463983d5` = §9 char に復帰。`card_G0_lower_bound`/`not_trivial_G0` を新 leaf
  `S09_FrobeniusCardG0LowerBound.lean` +142 へ移設 + **genuine 証明 → FrobeniusFamily.lean の sorry 1→0 discharge**。
  issue 0044 closed。not_trivial_G0 に nilpotency 仮説 `hnilp` 追加 (a-owned signature 変更))。c=0 / b=0。
  build green **4202 jobs** / AxiomsCheck OK (**2416** 全 allowlist) / **count-sorry 50→49 (実 discharge、
  FrobeniusFamily 1→0、他 file 増なし = clean、hub 検証済)** / 新 axiom なし。
  🔩 **mechanical follow (非逸脱, hub 裁定)**: a の `not_trivial_G0` signature 変更 (hnilp 追加) に伴い
  **b-owned `S14_MaximalI/TypeICovering.lean` の `not_all_maximal_typeI` proof に +11/-1 の call-site 追従**
  (hnilp witness = `maxNilpotentNormalHall_isNilpotent` 供給、statement 不変)。判定 = b active math 非接触
  (b 0 ahead、not_all_maximal_typeI は 9087 RULING #4 で既 landed・b 現 frontier でない) → 🔩 rule 該当。
  ⚠ **a は commit で self-flag し忘れ (🔩 cond iii)** — hub が merge log + 本 note で traceability 補完。
  a への申し送り: 自 upstream signature 変更で他レーン file を追従する時は commit self-flag すること。
  ⚠ issue 9096 (b frontier direction) 依然 保留。
- **2026-07-14 (tick 27) — ★ a 合流: Isaacs Thm 7.1 (Thompson normal p-complement) COMPLETE + issue 0031 close**:
  **a=1** (`cb7faf68` = ★ **Isaacs Theorem 7.1 完成** — capstone `thompson_normal_p_complement_of_local_hypotheses`
  を新 leaf `S7C_ThompsonPComplementFinal.lean` +105 で **sorry-free 証明**、AxiomsCheck で「3 axiom 全 allowlist =
  sorryAx 非依存」確認。issue 0031 → closed/ (git mv)。root closure = S7D1 import)。scope Isaacs shared-foundation
  additive ✓。b=0 / c=0。build green **4201 jobs** / AxiomsCheck OK (**2413** 全 allowlist) / count-sorry **50→50 不変** /
  新 axiom なし / 逸脱なし。**a の tick15-27 Ch07 build-out (Step1-6 + final、全 sorry-free) が Thm 7.1 で完結**。
  ⚠ issue 9096 (b frontier direction) 依然 保留。
- **2026-07-14 (tick 26) — a 合流: Isaacs Ch07 Step6 abelian Sylow-2 input (新 leaf S7C_AbelianQuotientComplement)**:
  **a=1** (`5e0c7b43` = Isaacs Ch07 issue 0031。新 leaf `S7C_AbelianQuotientComplement.lean` +322 (0 sorry、
  root closure = S7D1 import) + Basic/S7D1 import 追従 + AxiomsCheck)。scope Isaacs shared-foundation additive ✓。
  b=0 / c=0。build green **4200 jobs** / AxiomsCheck OK (**2412** 全 allowlist) / count-sorry **50→50 不変** /
  新 axiom なし / 逸脱なし。⚠ issue 9096 (b frontier direction) 依然 保留。
- **2026-07-14 (tick 25) — a 合流: Isaacs Ch07 Step5 Sylow-center centralizer (新 leaf S7C_CentralizerCenter)**:
  **a=1** (`ec2cebff` = Isaacs Ch07 issue 0031。新 leaf `S7C_CentralizerCenter.lean` +73 (0 sorry、root closure
  = S7D1 import) + Basic/S7D1 import 追従 + AxiomsCheck)。scope Isaacs shared-foundation additive ✓。b=0 / c=0。
  build green **4199 jobs** / AxiomsCheck OK (**2410** 全 allowlist) / count-sorry **50→50 不変** / 新 axiom なし / 逸脱なし。
  ⚠ issue 9096 (b frontier direction) 依然 保留。
- **2026-07-14 (tick 24) — a 合流: Isaacs Ch07 Step4 Sylow maximality (新 leaf S7C_SylowMaximal)**:
  **a=1** (`c02156ee` = Isaacs Ch07 issue 0031。**新 leaf `S7C_SylowMaximal.lean` +120 (0 sorry、root closure
  = S7D1 が import)** + Basic/S7B2/S7D1 の import 追従 (decl 削除ゼロ) + AxiomsCheck +6)。scope Isaacs
  shared-foundation additive ✓。b=0 / c=0。build green **4198 jobs** / AxiomsCheck OK (**2409** 全 allowlist) /
  count-sorry **50→50 不変** / 新 axiom なし / 逸脱なし。
  ⚠ **issue 9096 (b frontier direction) 依然 保留** — ユーザー裁定待ち (tick 23 参照)。
- **2026-07-14 (tick 23) — a+b 合流: a=Isaacs Ch07 Step3 p-prime core trivial + b=docs (frontier assessment, issue 9096)**:
  **a=1** (`58c67f17` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement` +227、0 sorry、計 1223 行 + AxiomsCheck +4)。
  **b=1 docs-only** (`b3ca00fb` = frontier assessment。issue **9096 新規 (HUB direction 依頼)**: b の S15-solo 9094
  char-degree S-side は完了 (`S_caseB_facts_no_lambda` proven, tick22)、残 3 gate は全て cross-lane gated —
  `tSide_theta_package_of_not_caseB_core`/`deltaPrime_eq_one_T` = ν-carrier (a-territory) 依存、
  `T_caseB_facts_no_lambda` = S16-gated、NormEstimates 移行 = c-owned S16_GridExpansion relayer。.lean 非接触)。c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2406** assertion 全 allowlist) / count-sorry **50→50 不変** /
  新 axiom なし / 逸脱なし。size watch: S7C 1223 (2000 未満)。
  ⚠ **HUB direction 保留 (issue 9096)**: b の cluster 完了 + frontier cross-lane gated。**a は ν-carrier でなく
  Isaacs Ch07 (Thm 7.1) を自律進行中**ゆえ b の default「a-ν landing 待ち」は自然発火しない。本セッションは
  merge-only scope (cron「hub は合流のみ・frontier 選択に介入しない」) ゆえ hub direction ruling は保留し、
  ユーザーへ surface (推奨 = b に ν-carrier discharge の proof-only carve-out (option B) or ungated T-instance
  hbridge (option E)。詳細 = 本 summary + issues/9096)。
- **2026-07-14 (tick 22) — a+b 合流: a=Isaacs Ch07 p-separability + ★b=S_caseB_facts_no_lambda 完全証明 (sorry 実 discharge)**:
  **a=1** (`455a310b` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement` +144、0 sorry、計 996 行 + AxiomsCheck +2)。
  **b=1** (`a8b777b6` = ★ **hbridge 完全 CLOSE — `S_caseB_facts_no_lambda` を完全証明** (sorry→proven)。
  S15_CharacterDegreeSupply +259/-107 (proof restructure、decl 削除ゼロ、b 所有 leaf))。c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2404** assertion 全 allowlist) / **count-sorry 51→50 (実 discharge、
  regression でなく前進)** — S15 sorry 4→3、残 3 = `deltaPrime_eq_one_T`/`tSide_theta_package_of_not_caseB_core`/
  `T_caseB_facts_no_lambda` (原 4 の subset、新 regress なし hub 検証済) / 新 axiom なし / 逸脱なし。
  size watch: S15 1566 / S7C 996 (共に 2000 未満)。9094 残 = T_caseB_facts_no_lambda 側 + NormEstimates 移行 (import DAG 制約)。
- **2026-07-14 (tick 21) — a 合流: Isaacs Ch07 quotient normal complement in Step 2 (Thm 7.1 継続)**:
  **a=1** (`fc6fb9a1` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement.lean` +215 (自 file 継続、0→0 sorry、
  計 852 行) + AxiomsCheck +8)。scope Isaacs shared-foundation additive ✓。b=0 / c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2403** assertion 全 allowlist) / **count-sorry 51→51 不変** /
  新 axiom なし / 逸脱なし。(間に「変化なし」tick 2 本、番号なし)。
- **2026-07-14 (tick 20) — a+b 合流: a=Isaacs Ch07 maximal-bad-subgroup=p-core + b=S11 (9.11) caseB reverse-characterization (hub carve-out)**:
  **a=1** (`6036cc4f` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement` +271/`Basic` -30 + AxiomsCheck +10。
  ⚠ diff に `-theorem lt_normalizer_inf_sylow_of_lt` が出たが **removed@Basic + re-added@S7C の byte-identical
  relocation** (statement 保持、consumer Main.lean 685/756 無傷、build green で確認) = 削除でなく自 file 間移設。
  scope Isaacs shared-foundation additive ✓)。**b=1** (`6bfd6b38` = S11 (9.11) caseB reverse-characterization
  Clifford 機械 `caseB_xiOf_H0Cprime_eq_induce_hcPsiPair` 等を `S11_MaximalII_III_IV/InnerCompHom.lean` に
  +328/-0 sorry-free。**hub 自律裁定で carve-out 付与** (上記 carve-out 節、= 内容で b 割当・a 非接触・a の
  (9.7.b) route dup でない・(11.9.c) 別 file、0101 の同 dir 拡張)。b は S15 caseB wiring を自ら revert し
  lemma のみ保持 (2035 #34) = 軌道修正で保全の自己適用)。c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2399** assertion 全 allowlist) / **count-sorry 51→51 不変** /
  新 axiom なし / 逸脱なし (b は carve-out で in-scope 化)。size watch: InnerCompHom **1678** (2000 未満だが
  +328 で成長 — 次追記で prefix-split 検討)、S7C 637。
- **2026-07-14 (tick 19) — a 合流: Isaacs Ch07 descend Thompson local hypotheses (Thm 7.1 継続)**:
  **a=1** (`fc19d7e7` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement.lean` +77 (自 file 継続、0→0 sorry、
  計 366 行) + AxiomsCheck +6)。scope: Isaacs/** shared foundation additive ✓。b=0 / c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2394** assertion 全 allowlist) / **count-sorry 51→51 不変** /
  新 axiom なし / 逸脱なし。
- **2026-07-14 (tick 18) — a 合流: Isaacs Ch07 select maximal bad normalizer subgroup (Thm 7.1 継続)**:
  **a=1** (`0304119b` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement.lean` +100 (自 file 継続、decl 削除ゼロ、
  0→0 sorry、計 289 行) + AxiomsCheck +8)。scope: Isaacs/** shared foundation additive ✓。b=0 / c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2391** assertion 全 allowlist) / **count-sorry 51→51 不変** /
  新 axiom なし / 逸脱なし。S7C は DAG 深部ゆえ大規模再コンパイル継続。
- **2026-07-14 (tick 17) — a 合流: Isaacs Ch07 transport Thompson local hypotheses (Thm 7.1 継続)**:
  **a=1** (`5e7b477d` = Isaacs Ch07 issue 0031。`S7C_ThompsonPComplement.lean` +133/-20 (a 自身が tick15 で作った
  file の継続、decl 削除ゼロ = 既存 statement 非改変) + `S7B2_NormalJ_PComplement.lean` +1/-1 (import 追従) +
  AxiomsCheck +5)。scope: Isaacs/** shared foundation additive ✓。b=0 / c=0。
  build green **4197 jobs** / AxiomsCheck OK (**2387** assertion 全 allowlist、Ch07 新補題 5 本追加) /
  **count-sorry 51→51 不変** (全 Ch07 file sorry-free) / 新 axiom なし / 逸脱なし。
  ⚠ S7C も DAG 深部 (S03g_Thm310→S7D1→S7C) ゆえ full build 大規模再コンパイル (tick15 同様、background 完走)。
- **2026-07-14 (tick 16) — b 合流: hbridge caseA branch を genuine に証明 (9094/2035)**:
  **b=1 実 commit** (`f553eae6` = `S15_CharacterDegreeSupply.lean` +173、hbridge の caseA 分岐を genuine 証明 =
  "subtlety" は red herring と判明。b 所有 leaf ✓)。a=0 / c=0。
  build green **4197 jobs** / AxiomsCheck OK (2382 assertion 全 allowlist) / **count-sorry 51→51 不変**
  (S15 file 4→4、4 sorried decl set 不変 = `deltaPrime_eq_one_T`/`tSide_theta_package_of_not_caseB_core`/
  `T_caseB_facts_no_lambda`/`S_caseB_facts_no_lambda`、proven→sorry swap なし。+173 は caseA 内部証明機械 =
  S_caseB_facts_no_lambda discharge へ向かう sub-lemma) / 新 axiom なし / 逸脱なし。
  size watch: S15_CharacterDegreeSupply 1436 (tick12 1240 → +196、2000 未満だが成長中 — watch)。
- **2026-07-14 (tick 15) — a 合流: Isaacs Ch07 Thm 7.1 (Thompson normal p-complement) — Sylow centers via p-prime quotients**:
  **a=1** (`e2772ae0` = Isaacs Ch07 Thompson subgroup work、issue 0031。**新 leaf `S7C_ThompsonPComplement.lean` +76**
  (sorry-free) + `Basic.lean` +3/-2・`S7D1_BurnsideSetup.lean` +1/-1 (import 追加 + 微修正、**decl 削除ゼロ = 既存
  Isaacs statement 非改変**) + AxiomsCheck +2)。**scope**: Isaacs/** = shared foundation ゆえ additive 追加は
  全 lane 可・逸脱でない ✓ (2026-07-04 hub 裁定)。新 S7C は root closure OK (`OddOrder.lean → S03g_Thm310 →
  S7D1_BurnsideSetup → S7C`、a が S7D1 に import 配線)。b=0 / c=0。
  build green **4197 jobs** / AxiomsCheck OK (2382 assertion 全 allowlist) / **count-sorry 51→51 不変** (全 Ch07 file
  sorry-free) / 新 axiom なし / 逸脱なし。size watch: S7C 76 OK。
  ⚠ **build 所要時間の注意**: a が `S7D1_BurnsideSetup` (BG §3 `S03g_Thm310` の依存元 = DAG 深部) を触ったため、
  .olean 無効化が下流 Peterfalvi spine 全体にカスケードし **full build が 10 分超** (通常の leaf 変更は cached ~10-40s)。
  失敗でなく大規模再コンパイル (background で完走)。深部 foundation を触る tick では build 時間増を見込む。
- **2026-07-14 (tick 14) — a 合流: S09 canonical Frobenius selected bound (実証明)**:
  **a=1** (`eb1e4920` = `S09_FrobeniusSelectedEstimate.lean` +240、canonical selected bound を **sorry-free で実証明**、
  AxiomsCheck +11、OddOrder.lean import 自追記 ✓、issue 0044 更新。scope=S09 territory ✓)。b=0 / c=0。
  build green **4196 jobs** / AxiomsCheck OK (2381 assertion 全 allowlist) / **count-sorry 51→51 不変** (新 leaf sorry-free) /
  新 axiom なし / 逸脱なし。size watch: 240 OK。a は §9 concrete norm 評価群 (γ-norm/B-sum/good-index/selected) を継続 build。
- **2026-07-14 (tick 13) — a+b 合流: a=S09 concrete Frobenius good-index bound (実証明) + b=S_caseB_facts_no_lambda de-opacify**:
  **a=1** (`9b7b9c79` = `S09_FrobeniusGoodIndexEstimate.lean` +215、concrete good-index bound を **sorry-free で実証明**、
  AxiomsCheck +11、OddOrder.lean import 自追記 ✓、issue 0044 更新。scope=S09 territory ✓)。**b=1** (`3ca01cef` =
  `S_caseB_facts_no_lambda` を de-opacify (構造化 + translation lemmas) — S15_CharacterDegreeSupply +29/-2 に
  proof 再構造化 + `HypothesisBasics.lean` に **additive translation lemma 3 本** (`toTypesIIIIIIVSetupS_q_eq`/
  `chiefFactorS_p_eq`/`mkSection11CharacterDataS_u_eq`、+51/-0、c 所有 decl 非接触 ✓ = b の S15_SAndT_Setup territory))。c=0。
  build green **4195 jobs** / AxiomsCheck OK (2380 assertion 全 allowlist) / **count-sorry 51→51 不変**
  (de-opacify は S_caseB_facts_no_lambda の 1 sorry を構造化しただけ、4 sorried decl set は tick11-13 で不変 =
  proven→sorry swap なし、hub diff 検証済) / 新 axiom なし / 逸脱なし。size watch: a leaf 215 OK。
- **2026-07-14 (tick 12) — a+b 合流: a=S09 concrete Frobenius γ-norm/B-sum bound (実証明 2 leaf) + b=docs (NormEstimates 移行の architecture 発見)**:
  **a=2** (`c1f8402b` gamma norm bound + `64c01243` B-sum bound = `S09_FrobeniusGammaNormEstimate.lean` +252 /
  `S09_FrobeniusBsumEstimate.lean` +72、いずれも **sorry-free の concrete 評価**、AxiomsCheck +23、**a が
  OddOrder.lean import を自分で追記** (tick10 申し送りを反映) ✓、issue 0044 更新。scope=S09 territory ✓)。
  **b=1 docs-only** (`a6c43531` issue 2035 #29 = ⚠ architecture 発見: NormEstimates 5 定理の Core+dichotomy
  移行が **import DAG でブロック** — NormEstimates は Machinery135 (legacy `character_degree_analysis` 定義元) を
  import する層にあり、新 producer への切替が循環 import を生む旨。.lean 非接触)。c=0。
  build green **4194 jobs** / AxiomsCheck OK (2379 assertion 全 allowlist、exit 0) / **count-sorry 51→51 不変**
  (a leaf sorry-free・b docs-only) / 新 axiom なし / 逸脱なし。size watch: a leaf 72/252 OK。
  9094 残 = NormEstimates 5 定理移行 (b が import DAG 制約を issue 化 = 次の設計判断待ち) + dichotomy scaffold 実証明。
- **2026-07-14 (tick 11) — a+b 合流: a=S09 family-wide weighted Γ 分解 (実証明) + b=9094 ⑤ flip 1-2/N (TTypeII endpoint→Core+dichotomy)**:
  **a=1** (`c023f3cc` = `S09_FrobeniusGammaDecomposition.lean` +585 で family-wide weighted gamma
  decomposition を **sorry-free で構成** (0→0)、AxiomsCheck +18 (新 decl assertion)、issue 0044 更新。
  scope=S09 territory ✓)。**b=2** (`eb9a7364` TTypeII endpoint を Core+dichotomy へ移行 = ⑤ flip 1/N +
  `21769869` general S-side dichotomy producer landed = ⑤ flip 2/N; S15_CharacterDegreeSupply +90 に
  新 producer `T_caseB_facts_unconditional` 等、**c 所有 TTypeII.lean は 9094 供給編集権の proof-only
  差替え** = `T_side_caseB_facts` の statement 不変・`character_degree_analysis`(uninhabitable)→
  `T_caseB_facts_unconditional` cite + import 1 行、self-flag 済・c の A0-Dade/BetaData 非接触 ✓)。c=0。
  build green **4192 jobs** / AxiomsCheck OK (2377 assertion 全 allowlist、exit 0) /
  **count-sorry 49→51 = +2 新 decl scaffold** (`T_caseB_facts_no_lambda`@1180 + `S_caseB_facts_no_lambda`@1219、
  いずれも b の新規 dichotomy scaffold。pre-existing 2 本 (`deltaPrime_eq_one_T`/`tSide_theta_package_of_not_caseB_core`)
  不変 = regression でない、全 +2 が新 decl で説明済) / 新 axiom なし / 逸脱なし。size watch: S09 902 / S15 1240 /
  TTypeII 965 全て 2000 未満 OK。9094 残 = NormEstimates 5 定理移行 (:454/:570 が legacy `character_degree_analysis`
  を依然 cite) + dichotomy scaffold の実証明。
- **2026-07-14 (tick 10) — a 合流: S09 (7.9) local degree-ratio reality + coherence agreement (Γ 分解)**:
  **a=1** (`3b6382d4` = `S09_FrobeniusGammaDecomposition.lean` **新 leaf +317**、(7.9) Γ 分解の
  local degree-ratio reality + coherence agreement を実証明、**sorry-free**)。b=0 / c=0。
  build green **4192 jobs** / AxiomsCheck OK (2374 assertion 全て allowlist 内、lake exit 0 —
  `linter.style.header` の `#assert_only_allowed_axioms` 未パース error は既知の pre-existing false-positive) /
  **count-sorry 49→49** (新 file sorry-free) / 新 axiom なし / 逸脱なし。
  ⚠ **2-dot 幻の phantom deletion**: `git diff main..a` は a が 7 behind ゆえ main の tick8/9 内容
  (b の 3 λ-cluster 定理 + 本 note の tick8/9 entry) を「削除」と誤表示したが、a の実 commit
  `3b6382d4` は **S09_FrobeniusGammaDecomposition.lean のみ +317** (`git show --stat` で確認) →
  3-way merge で main 版が保持され b の定理・note は intact (merge 後 grep で確認済)。
  🔧 **hub 機械修正**: 新 leaf が **どこからも import されず** (orphan、root closure 欠落) →
  `OddOrder.lean` に import 追記 (9014 先例と同じ step 3b)。**a は今後新 leaf 作成時に OddOrder.lean
  追記まで込みで commit すること**。size watch: 新 file 317 行 OK。
- **2026-07-14 (tick 9) — a+b 合流: a=S09 family-wide Frobenius 直交 (実証明) + b=9094 案 A 3/3 部分 (λ-cluster Core 版)**:
  **a=1** (`fa68a784` = `S09_FrobeniusFamilyOrthogonality.lean` 新 leaf +575、family-wide Frobenius
  orthogonality を **sorry-free で実証明** — AxiomsCheck に hypothesis79/78 系 6 決定を追加、全て
  「3 axiom, all in allowlist」= sorryAx 非依存の clean landing。issue 0044 更新。scope = a の S09
  territory ✓・新 axiom なし) を merge 53243b88 で合流。**b=3 実 commit** (`lambda_forces_T_caseB_core`
  (13.4) の Core/λ-cluster 版 = ④ 完了 + `lambda_tau1_apply_eq_of_not_mem_H_sat_core` (13.9.a) 第一段
  Core 版、いずれも S15_CharacterDegreeSupply.lean +167、b 所有 leaf) を merge 2ae545d6 で合流。
  build green **4191 jobs** (10.8s) / AxiomsCheck OK (2367+/0、新 S09 FrobeniusFamily 6 決定 clean) /
  **count-sorry 48→49 = +1 新 decl scaffold** (`tSide_theta_package_of_not_caseB_core` = b の新規、tick8
  で既 sorried の `deltaPrime_eq_one_T` は不変 = regression でない、hub 検証済) / 新 axiom なし / 逸脱なし。
  c=0 (40 behind、DORMANT 継続)。9094 残 = 3/3 の dichotomy producer + NormEstimates 5 定理移行 +
  TTypeII proof-only 差替え。⚠ **size watch**: `S15_SAndT_Setup/CountingLayer.lean` = **2001 行**
  (2000 gate を +1 超、0094 dir 化分割以来 6+ tick 安定・本 tick 非接触ゆえ pre-existing)。**次に b が
  本 file へ追記したら prefix-split 必須** (今回は非成長ゆえ split issue 起票せず watch のみ)。
- **2026-07-14 (tick 8) — a+b 合流: 9094 案 A 実装 2/3 (LambdaClusterData + conditional producer)**:
  **a=5** (実質 issues のみ: 9095 duplicate claim close = issue hygiene) を merge 3bec4cfa
  (build 省略)。**b=6** (LambdaClusterData + conditional producer + cCoeff guarded restate 2 本
  ((13.5) λ-係数 / (13.7) η₁₀-係数) + `hypothesis76OfDadeBase` (7.7) 任意 base builder =
  S09_Building78C への additive 追加 → **9094 供給編集権を S09 additive に拡張して受理** (上記
  ⟹ 拡張)) を merge 78193bad で合流 (build green 4190 / count-sorry 48→48 / 新 axiom なし)。
  c=0。9094 残 = 3/3 (dichotomy producer + NormEstimates 5 定理移行 + TTypeII proof-only 差替え)。
- **2026-07-14 (tick 7) — b 合流: ★ 9094 案 A 実装 1/3 (CharacterDegreeCore + 無条件 producer)**:
  **b=5** (CharacterDegreeCore = Machinery135 に guard 付き λ-free structure (+126) + 無条件
  producer `characterDegreeCore_nonempty` = 新 leaf S15_CharacterDegreeSupply (+255、landed engine
  で全 field discharge、残 sorry = `deltaPrime_eq_one_T` 1 本 = nuGridSupply a-所有 carrier gated
  scaffold)。τ₁ field guarded supply 5 本完備 (2035 #23)。producer 置き場は import 制約で新 leaf
  = RULING 裁量条項内・self-flag 済 → hub 追認) を merge a0659a8a で合流 (build green 4190 /
  count-sorry 47→48 scaffold ALLOW / 新 axiom なし)。**a=sync-only** (3 sync merge、実差分ゼロ →
  skip、次の実 commit とまとめて合流)。c=0。9094 残 = 2/3 conditional producer + 3/3 dichotomy
  producer + consumer 移行。b が言及する将来 coordination = nuGridSupply の FeitThompson carrier
  field 追加 (9081 pattern) — b が必要時に claim してくる想定。
- **2026-07-14 (tick 6) — a+b 合流: (7.9) family conclusion sorry-free (a) + S1cases irr-branch 供給 leaf (b)**:
  **a=3** (0044 再開 cont.49-51: 新 leaf `S09_FrobeniusParity` 146 行 = `hypothesis79_conclusion`
  sorry-free ((7.9) family-level: Sibley Δ + delta-reality + parity)、(7.10) 定量 assembly の原文
  blueprint 記録。残 S09-side sorry root = `hypothesis79_delta_even`) を merge 06681cf1 で合流
  (build green 4189 / count-sorry 47→47 / 3-dot の merge_monitor.md 差分は古い base 幻 =
  per-commit 確認で排除)。**b=2** (2035: 新 leaf `S15_CharacterDegreeSupply` 327 行 sorry-free
  3 定理 = Coq S1cases irr-branch 対応の tau1S_induce_inner_eta 供給 + private→public 化 1 箇所、
  OddOrder.lean import 追記済で root closure 自己完結 — 先 tick の指導が定着) を merge eef40a78 で
  合流 (build green 4190 / count-sorry 47→47)。c=0。9094 実装は b が Core 供給部品を順調に蓄積中。
- **2026-07-14 (tick 5) — a+b 合流: ★ 9087 carve-out 完遂・失効 (a) + 9094 案 A 実装開始 (b)**:
  **a=3** (9087 RULING #4 2/3 `allTypeI_fittingIsTI` + 3/3 `not_nonTypeICovering_of_all_typeI` 実証明
  landing = carve-out 3 decl 全 sorry-free 化 → **失効・b 所有復帰** (上記 ❌ 追記)。3/3 は as-stated
  証明不能 (carrier provenance 非記録) → producer `bgTheoremE_cover_data` (a 所有) の (8.8.b) 準拠
  強化 + signature 変更 self-flag = hub 受理。Isaacs 側 `normal_pGroup_le_kernel` 等 additive 追加。
  (12.17) chain 残 dirty root = (7.10) card_G0_lower_bound + (12.6)(c1) sibleyTarget_frobI の 2 本に
  localize、(7.10) OFF-PATH label は stale 化 → a は 0044 再開) を merge 004be7f0 で合流
  (build green 4188 / AxiomsCheck OK / count-sorry 49→47 実証明減 / 新 axiom なし)。
  **b=2** (2035 τ₁ honest supply (zSpan 支持 + guarded (13.2.e))、9094 RULING 受領 + Core 設計入力
  = τ₁ field 3 本の P ⊄ Ker guard 化 (第 5 overstatement)) を merge df9c0f7d で合流
  (build green 4188 / count-sorry 47→47)。c=0。**ユーザー相談**: a/b どちらを codex に任せるか
  → hub 回答 = a 推奨 (cross-lane 調整ゼロ + frontier localize 済み 2 本 vs b は 9094 restructure
  実装中で供給編集権・混在 leaf の条件密度が高く d 退役教訓の弱点領域)。
- **2026-07-13 (tick 4) — b 合流 + ★ 9094 HUB RULING (λ-cluster 案 A)**: **b=8** (feat(2035, 13.3.a+c):
  `tau1S_ofHonest_mu_col_eta_col_one` sorry-free + issue 9094 起票 + docs 2035 #20/#21) を検証合流
  (merge c14d8a01: build green 4188 jobs / AxiomsCheck OK / count-sorry 49→49 / 新 axiom なし / scope
  clean)。a=0 / c=0。**9094 裁定 (f94eb232)**: `CharacterDegreeData` λ-cluster の no-λ uninhabitability
  (carrier bug 第 3 例) に対し **案 A = λ-free `CharacterDegreeCore` 分割**を採用 — Coq PFsection13 の
  Section factoring (Variable lambda :961-962、(13.4) 非 export、無条件 (13.12)/(13.13) は dichotomy
  case-split) と 1:1 対応が根拠。no-λ 分岐 = landed `caseB_of_no_irreducible_sOf_H0Cprime` vocabulary
  (新 structure なし)。TTypeII `T_side_caseB_facts` は statement 正 (Coq §14 ltqp 準拠) → b に
  proof-only 供給編集権 carve-out (上記)。consumer 6 箇所は全て statement 正・proof route のみ修正。
- **2026-07-13 (tick 3) — a+b 合流: ★ carve-out 1/3 `card_LF_coprime_pq` 実証明 (a) + (13.3.c) pin bundle 完成 + carrier 健全化 (b)**:
  **a=5** (feat(9087 RULING #4 1/3): `card_LF_coprime_pq` (S15_Gate3 carve-out decl) **実証明 landing** =
  §15 gate-4 B2 axiom-clean — carve-out 条件遵守確認済 (当該 decl 文脈のみ・signature 型不変)、
  σ-uniqueness 補題を a 所有 S10 に factor (+40、0096 宣言非接触)、allTypeI_fittingIsTI 設計 recon =
  残 2/3 へ) / **b=6** (feat(2035, 13.3.c): has-irr μ-column pin dichotomy + pin bundle 完成
  (MuColumnPin rewrite +573/−88 sorry-free); **fix: CharacterDegreeData.tau1S_induce_inner_eta
  uninhabitability 修正** — 旧 field が mu_col_tau1_eta_col_one と矛盾し structure uninhabited だった
  のを honest scope 化 = b 自所有 carrier の健全化・self-flag 済で受理) / c=0。build green ×2
  (4187/4188 jobs)・AxiomsCheck OK (2367/0)・**count-sorry 51→50→49** (B2 + pin 両 discharge、
  regression なし)・新 axiom なし・size watch 全 <1500 (CaseACoherence 1140 / Machinery135 1166 /
  MuColumnPin 550 / Gate3 930)。push `b3836d70..4f36cc7c` (fef8c18a + 4f36cc7c)。
- **2026-07-13 (tick 2) — a+b 合流: ★ 9077-T1 閉包 (a、c 所有 file への proof-only de-gate 受理) + 9087 RULING #4**:
  **a=3** (feat(9077 T1): TTypeII `T_not_isTypeIV_of_isTypeP1` の (11.9)-gated `hVcomm` bare sorry を
  landed 済 `not_isTypeIV_of_mem_maximalSubgroups` (S13_NonGaloisExclusion) 直 cite で閉包 —
  **c 所有 TTypeII.lean への編集は proof-only de-gate (signature 不変・新規宣言なし・self-flag・c 停止中)
  = 0096 拡張と同型で非逸脱と裁定** + AxiomsCheck assert 3 本 + docs 9087/9077 + sync) /
  **b=1** (docs 2035 #17 のみ、build 省略) / c=0。build green (4187 jobs)・AxiomsCheck OK (2364/0, +3)・
  **count-sorry 52→51** (hVcomm discharge)・新 axiom なし・size watch OK。push `ddba2593..`(da032e55+df8d2d62+裁定 docs)。
  **HUB RULING #4 (9087)**: newly-ungated 3 decl (`card_LF_coprime_pq`/`allTypeI_fittingIsTI`/
  `not_nonTypeICovering_of_all_typeI`) を lane a へ decl 単位 carve-out (所有マップに entry 追記済)。
- **2026-07-13 (新セッション tick 1 — Fable 5 hub; 監視対象 = a/b、c はユーザー指示で明示停止中) — b 合流**:
  **b=3** (feat(2035, 13.3.c) all-reducible pinned coherence glue `coherentImageMap` = pin bundle core、
  S15_CaseBReducibleCoherence +266 全 proven + sync merge + docs(2035) pin architecture 訂正 #15/#16) /
  a=0 / c=0。tip SHA pin (27cf1336) で検査・merge を一致させ実行。build green (4187 jobs)・
  AxiomsCheck OK (2361/0)・count-sorry 52→52・新 axiom なし・逸脱なし・size watch OK
  (S15_CaseBReducibleCoherence 973 <1500)。push `e94f6265..ddba2593`。
  **監視ペース**: Fable ゆえ 30 分 `13,43` で cron 再作成 (id b64b7309、session-only)。
- **2026-07-13 (tick 1, セッション再開初回 — Fable 5 hub; 監視対象 = a/b のみ、c 未稼働 ユーザー指示) — b 合流**:
  **b=4** ((9.11.6) S-instance `nineElevenNormBoundS` dichotomy closed (1017) + **0114 再分割実施**:
  S15_CaseBReducibleCoherence 1829→697、新 leaf S15_CaseACoherence 1031 + S15_NineElevenSteps 523、
  OddOrder.lean import 追記済) / a=0 / c=0。build green (4183 jobs)・AxiomsCheck OK・count-sorry 61→61・
  新 axiom なし・逸脱なし・size watch 全 <1500 (**0114 closed**)。push `31c519fd..47cafdc2`。
  **監視ペース**: Fable ゆえ 30 分 `13,43` で cron 再作成 (id 66211cac、session-only)。
- **2026-07-12 (tick 16, セッション再開初回 — Opus 4.8 hub) — a+b 合流**:
  **a=1 genuine + 2 sync** ((11.9.c) `not_isTypeIV_of_mem_maximalSubgroups` = 全 maximal subgroup M の
  per-M 普遍 Type-IV 排除、issue 1024 納品記録→pending; 残 2 commit は main sync merge、自所有
  S13_NonGaloisExclusion のみ) / **b=2** ((13.19.c) `col_constant` + `caseC_dual` を `Hypothesis.swap`
  (S↔T 再 instantiate) transport で完遂、義務 3→1、**sorry 2 本 discharge**; swap phase 2 = `Hypothesis.swap`
  constructor 完成 (HypothesisSwap leaf modify)) / **c=0** (未マージなし)。
  **⚠ live-branch race 実例**: tick 冒頭で a tip=a8eebe9e を観測したが SHA pin 前に a が 2ba76a5b (sync merge)
  まで進行 → pin した 2ba76a5b に対し全検査+merge を実行 (「注意」節の手順どおり、実害なし)。
  build green (4177 jobs)・AxiomsCheck OK (2352 OK/0 fail)・**count-sorry 68→66** (b 実証明 discharge、
  regression でない)・新 axiom なし・size watch 超過なし (S13_NonGaloisExclusion 1017 / S15_SAndT 1160 /
  HypothesisSwap 283)。push `182d489f..f0d6f494`。
  **監視ペース遷移**: 前セッションは Fable 30分 → 本セッション Opus 4.8 ゆえ **15分 `7,22,37,52`** で
  cron 再作成 (id ce8170c7、session-only)。
- **2026-07-12 (tick 15) — 全 3 レーン合流: ★ (11.9.c) U cyclic + Type III 完結 (a) / (13.19.c) row constancy (b) / (3.9.a) rigidity port (c)**:
  **a=4** ((11.9.c) `U_isCyclic_of_hypothesis` + `not_cliffordCaseA_of_hypothesis` (非Galois 完全排除) +
  新 shared leaf `GroupTheory/NilpotentAbelianization` (9086 claim 済、nilpotent+cyclic abelianization ⟹
  cyclic) + **race 分 `700ba71f` = P3 完結 `isTypeIII_of_hypothesis`/`no_typeIV_maximal` +131** — merge
  38df2e1d は message 上 @29b08747 だが実第 2 親 = 700ba71f (scope-check 後にレーンが積んだ; 遡及チェック
  clean = a 自所有 file のみ・axiom/sorry 変化なし、build/AxiomsCheck は merged tree で有効。以後は tip SHA
  pin 手順 — 「注意」節参照)) / **b=3** ((13.19.c) `betaL_eta0_row_constant` 完全証明 (義務 4→3、Coq
  betaLeta 忠実移植) + swap phase 1 新 leaf `HypothesisSwap` +124 (NuGridSupplyData bundle、producer
  `nuGridSupply` = 新 decl faithful scaffold sorry +1)) / **c=3** ((3.9.a) `eq_in_cycTIiso` port =
  `eta_eq_of_norm_one_regular_value_eq` + `alignedOmegaSigmaGrid_eq_alignedOmegaEtaGrid` (global grid
  equality) + (11.8.2) concrete hclassify — TGapGridAlignment 975→1263)。build green ×3 (4176/4177/4177
  jobs)・AxiomsCheck OK・count-sorry 68→68 (b: −1 実証明 +1 scaffold)・新 axiom なし・size watch: 超過なし
  (S13_NonGaloisExclusion 847 / TGapGridAlignment 1263 ⚠ 1500 接近 watch)。
- **2026-07-12 (tick 14, セッション再開初回) — 全 3 レーン合流: ★ (11.9.c) u=a pin (a) + (13.19.b) 完全証明 + junk-τφ soundness 修正 (b)**:
  **a=1** ((11.9.c) 非Galois u=a pin keystone `caseA_u_eq_a_of_residual_not_orthogonal` —
  新 leaf S13_NonGaloisExclusion +716 sorry-free、conj-対合 + (11.9.a) 行0射影 + Dade pin;
  S12 helper 2 件 AxiomsCheck 登録) / **b=2** (★ (13.19.b) `coherent_extension_orthogonal_eta_of_mem_Sset`
  完全証明、義務 5→4。**soundness 核**: 旧義務 `tau_apply_orthogonal_eta_of_mem_Sset` は junk-τφ
  (非 supported CF への任意拡張) で**証明不可能な obligation だった** → (13.19) 層を
  TypeICoherent78Data τ₁ = coh.extension ベースに restate。S16 下流 2 file × 1 行は機械的 signature
  追従 = 🔩 非逸脱 (commit self-flag 済)。⚠ b 自己 flag: 同種 junk-τφ 主張の audit 価値 → 2038 に記録済) /
  **c=1** (0105 docs のみ: codex ホスト mid-turn 切断 (VS Code リロード、作業損失なし) → ユーザー裁定で
  一時 Claude 交代、trial 評価 26/26 不変)。build green ×2 (4175 jobs)・AxiomsCheck OK・
  **count-sorry 69→68** (unprovable 義務の削除、regression でない)・新 axiom なし・size watch 超過なし
  (S13_NonGaloisExclusion 716 / S15_SAndT 1071)。
- **2026-07-12 (tick 13) — c のみ合流**: **c=1** ((11.8) transposed eta grid align —
  TGapGridAlignment 256→975 行 +719 全 proven、AxiomsCheck +73)。a=0 / b=0。build green
  (4174 jobs)・AxiomsCheck OK (2342/0)・count-sorry 69→69・新 axiom なし。push `7fe28d44..1be17740`。
- **2026-07-12 (tick 12, セッション再開初回) — 全 3 レーン合流**: **a=3** ((11.9.a)/1024 J0/J2:
  R(μ)-family conj-対合公式 `certainTypeRImage_conj` + `rowInv_zero` (S06 +43 全 proven) +
  t=0 退化排除 = conj-対合 route 設計 docs) / **b=7** (docs のみ: 2038 iter20-24 記録 —
  (13.19.a) 完・(13.19.b) 戦略 = field (B) 形 + FT discharge; CLAUDE.md /loop 自動自走明文化
  (ユーザー 2026-07-12) — .lean 変更なし build 省略) / **c=2** ((11.8) aligned source grid
  factor 化 — 新 leaf `S16_NonExistenceG/TGapGridAlignment.lean` +256、TTypeII import で root
  closure OK、AxiomsCheck +23)。build green ×2 (4173/4174 jobs)・AxiomsCheck OK・
  count-sorry 69→69・新 axiom なし・size watch 超過なし。push `5c092591..dc3c2eaa`。
- **2026-07-12 (tick 11) — 全 3 レーン合流: ★ (11.9.a) 行0射影 完全証明 (a) + (13.19.a) L1-L2 (b)**:
  **a=3** (★ `inner_tau_muColumnZero_sub_zeta_rowZero_of_residual_not_orthogonal` **完全証明**
  ((11.9.a) 行0射影) + ZIrrFourier Bessel 不等式 (shared additive +70) + S11 λ 存在/a∣u 部品) /
  **b=8** ((13.19.a) 5 段設計の L1-L2 完遂: `typeIBetaL_betaS_disjoint_support` **完全証明**
  (Ã(L)∩(P∪W)^G=∅、義務 6→5)、S04 に Pf 2.2 位数補題 純 additive +44 = 先例承認) /
  **c=1** ((11.8) aligned grid source characters expose +91)。build green ×3 (4173 jobs;
  9m08s/9m10s/1m16s)・AxiomsCheck OK・**count-sorry 70→69**・build 警告 68→67・新 axiom なし。
  push `d6b2681e..afac044f`。
- **2026-07-12 (tick 10) — 全 3 レーン合流: (11.9.a) Galois C-層完成 (a) + 義務 8→6 (b)**:
  **a=4** ((11.9.a) Galois 補正層 C-層完成 — 新 leaf `S13_TypeIIIGalois.lean` +289 全 proven +
  S05_SigmaIsometry chiFam pair-move +151、残り = (11.9.a) 最終組立のみ) / **b=6** ((13.19) 義務
  8→6: φ 存在 `exists_Sset_apply_one_eq_index` 実証明 + `tauTbetaGrid` honest 実装。**T-side 'A0
  Dade instance `dadeHypT0`/`_hconj` を c leaf S15_HonestTypeP2A0 に純 additive・proven 新設** =
  c の generic producer を T で instantiate (c 宣言非改変、additive-supply 先例で hub 承認)。
  SubgroupL/BetaVanishing は IsTypeP2 T 引数供給の 🔩 追従のみ) / **c=5** (PF 3.3 omega-grid
  exhaustion + (11.8) eta rigidity 連結、TGapNonorthogonality +628 全 proven)。build green ×3
  (4173 jobs; 7m48s/2m24s/1m16s)・AxiomsCheck OK・**count-sorry 72→70** (b 義務 2 discharge)・
  build 警告 70→68・新 axiom なし。push `5de854c0..e369e559`。⚠ size watch:
  **TGapNonorthogonality.lean 1553 行 (>1500) → issue 0109 起票** (c frontier 尊重、凍結境界で split)。
- **2026-07-12 (tick 9, レーン再開後初) — b/c 合流: (13.19) producer 分解 (b) + h114 一般化 (c)**:
  tick 6-8 = 変化なし×3 (レーン停止をユーザーに flag → ユーザーが全レーン再起動)。**b=2**
  ((13.19) producer monolith sorry を **Tier-A 実構成 + 明示義務 8 本**に分解 (net sorry +7 全て
  faithful scaffold); S15_SAndT 再 prefix-split → 新 leaf `S15_BridgeCharacter.lean` 1479 行。
  ⚠ **c carve-out (9076 4c-3 BetaData/(13.18) rewire) がバイト同一で新 leaf へ移動** — hub 機械検証
  (1413 行中 1405 同一、差分 = b 自身の producer 分解のみ) で承認、所有マップに所在地更新を追記。
  S15_SAndT は 649 行に縮小) / **c=1** ((11.8) h114 refuter の arbitrary-grid 一般化、
  TGapNonorthogonality +410 全 proven) / a=0。build green ×2 (4172 jobs; 2m11s/1m14s)・AxiomsCheck OK・
  count-sorry 65→72 (+7 義務化)・build 警告 63→70・新 axiom なし。push `080f9392..4fc7a99a`。
- **2026-07-12 (tick 5) — a のみ合流**: **a=2** ((11.9.a) G1 部品 `mapRingEquiv_muColumnZero_sum`
  μ₀ 列和の Galois 固定性、S12_Prop109 +58 全 proven + 1024 G3 narrow 化設計) / b=0 / c=0。
  build green (4171 jobs, 4m24s)・AxiomsCheck OK・sorry 65→65・新 axiom なし。push `2b2a73e9..802c540c`。
- **2026-07-12 (tick 4) — 全 3 レーン合流: ★ (13.17.c) over-claim 修正 = E⊄Q faithful 化 (b)**:
  **a=2** (新 shared leaf `GaloisInnerTransport.lean` +99 全 proven、**claim-before-build 完全準拠**
  (9085 起票 + OddOrder.lean 配線込み); S12 `inducedFamily_closedUnderMapRingEquiv` +30) /
  **b=3** (★ **健全化**: (13.17.c) 無条件 E⊄Q は over-claim (原文・Coq FTtypeII_support_facts とも
  disjunction 保持) と断定 → `complement_not_le_Q` を (14.5) 形 signature に faithful 化して
  **完全実証明**; 3 定理を S15_ComplementStructure→S15_SAndT TAIL 移設 (b 所有内); **c file
  SubgroupL.lean への 🔩 機械的追従** = exists_LHypothesis 引数供給 + P_inf_U_eq_bot バイト同一
  file 内移動 — self-flag 済・c の active TGap 系非接触で hub 承認、**c は次回 sync で取り込み・
  再移動しない**) / **c=3** (Pf (11.8) T-side residual image 同定 + column assembly grid の
  arbitrary-sigma 一般化、TGapNonorthogonality +134 / TGapPrimeTI +45 全 proven)。
  build green ×3 (4171 jobs; 5m00s/2m08s/1m28s)・AxiomsCheck OK・**count-sorry 66→65**
  (complement_not_le_Q 実 discharge)・build 警告 64→63・新 axiom なし。push `067cac9d..214693bd`。
  ⚠ 運用メモ: 本 tick 中に cron prompt が 7 件 queue (build 待ち中の idle-fire 累積) — 進行中 tick の
  重複 wake-up として無視 (MERGE_HEAD ガードの精神どおり、staged merge は保護された)。
- **2026-07-12 (tick 3) — 全 3 レーン合流: gammaGrid_Y_norm_bound 完全証明 (b) ほか全レーン実証明**:
  **a=2** (Pf (11.9.c) 部品 `card_uActionHom_range_modEq_one` W₁-orbit 合同 u≡1 mod q、S11 +126 全 proven
  + 1024 に (11.9.a) 実装計画確定) / **b=1** (★ **gammaGrid_Y_norm_bound (Pf 13.18d) 完全証明** — Coq leqif
  鎖の Lean 化、S15_SAndT +256; IsReal に swap 形 conj-inner API 4 本 — 既存 ZIrrFourier star 形と別
  statement・相互参照済で dup でない) / **c=2** (Pf (11.8) canonical T-side anchor 整列 — 新 leaf
  `TGapNonorthogonality.lean` +381 全 proven、a の S12/S13 API cite の consumer 構成、TTypeII が import で
  root closure OK)。build green ×3 (4169-4170 jobs; 10s/9m13s/1m12s)・AxiomsCheck OK・
  **count-sorry 67→66** (gammaGrid_Y_norm_bound discharge)・build 警告 65→64・新 axiom なし・逸脱なし。
  push `0831fde0..90c8509d`。
- **2026-07-12 (tick 2, cron 初発火) — 全 3 レーン合流: ★ gammaGrid_real 完全証明 (b) + S15 分割 0102 完遂**:
  a=1 (docs: issue 1024 = Pf (11.9) typeP_Galois/Type-III material survey + 証明計画、build 省略) /
  **b=3** (★ **gammaGrid_real (Pf 13.18c, Coq GammaReal) 完全証明** — mu_conj/eta_conj fields 3 層追加+
  producer discharge+assembly、2038 iter 8 完遂; **S15_SAndT prefix-split** → 新 leaf
  `S15_ComplementStructure.lean` (597 行、sorried 6 decl 移動、S15_SAndT 1486 行に復帰 <1500)、
  issue 0102 closed) / **c=2** (Pf (11.8): zero-row 排除 obligation を inline sorry から明示 statement
  `hnotZeroRowProjection` (Coq `FTtype34_not_ortho_cycTIiso`) へ isolate + TGapProjectionRigidity
  refuter infra +59)。⚠ c は multiple merge bases (2) — 3-dot が前 tick 済み FeitThompson 等を幻影表示、
  per-commit 確認 + trial-merge staged で誤検出排除 (手順どおり)。build green ×2 (4169 jobs; 3m04s/1m25s)・
  AxiomsCheck OK・count-sorry 68→67 (gammaGrid_real discharge −1、移動/isolate は ±対)・build 警告 66→65・
  新 axiom なし。push `bb955e43..0641db84`。size watch: FeitThompson 1850/Setup 1650 (>1500、0079 既知・
  co-edit hotspot 継続)、S15_SAndT は 0102 で解消。
- **2026-07-12 — 監視再開 (ユーザー「各レーンを監視します」+ Fable 30 分規約化再指示) + b/c 合流**:
  cron `1363241e` を Fable 規定 30 分 `13,43` で作成。CLAUDE.md・memory の残存「15分」固定表記を
  モデル依存規約 (正本 = 本ファイル冒頭) に統一 (`0f61c418`)。初回 tick (SHA 固定手順): a=0 /
  **b=3 commits** (Pf 3.9a/4.9a CF-level conj-pair producer 3 本 `omegaS_conj`/`muS_conj`/
  `tau3W_omegaS_conj` + IsReal bridge; FeitThompson.lean への純 additive proven 追記 = 2038 供給、
  先例 7dcbd371 と同型で merge 時 hub 承認、2038 self-flag 済) / **c=6 commits** (Pf 3.9b
  `eta_row/column_galois_orbit` を忠実 field として S15.Hypothesis→Section16Inputs→cd→構成子の
  全 chain に配線 — producer は main 既存 proven ⟹ 供給付き field 追加 = `S_U_commutative` 先例で
  hub 承認; Pf 11.9a T-side projection dichotomy assemble = (11.9) 一枚岩 sorry を case split し
  zero-column 側実証明・残 = zero-row 排除 (Coq 11.8) に narrowing)。build green ×2 (4168 jobs;
  b 後 8m52s / c 後 2m58s)・AxiomsCheck OK・count-sorry 68→68 (build 警告 66 不変)・新 axiom なし・
  0105 dup spot-check 清 (自前 TGap 系列拡張のみ)。push `cb479f50..0341a433`。⚠ size watch:
  FeitThompson.lean 1844 / FeitThompsonSetup.lean 1630 (>1500) — 既存 issue 0079 に現況注記
  (両者とも b/c の carrier 供給 co-edit hotspot ゆえ「idle 時に hub 分割」方針維持)。
- **2026-07-07 (夜) — FT endgame 計画制定 (ユーザー依頼の総ざらい)**: 6-agent workflow (wf_4d2d6126) で
  sorry census (87 = on-path 64 / 凍結 23) / opacity (free carrier 残 = TFieldModelData のみ、axiom 0) /
  frontier 幅 (現在 8–9 → 終盤 S16 直列 spine に収束) / velocity / issues を総点検し、
  **[`ft_endgame_plan_2026_07_07.md`](ft_endgame_plan_2026_07_07.md)** を制定。骨子: **3 レーン維持・拡張なし
  (E1 条件付き)** / R1 = W2 (9000 instance tail) 直列化解消 (trigger = a の (9.11) 組立 landing or c の 0098
  消化の早い方、基本線 a pivot + W9 を c へ) / R2 = b は 3002 unsound fix を 9013 gate より先に /
  縮小トリガー C2 (幅≤2 で 3→2)・C3 (Wave 3 で実質 1)。issue close: 0099・9017。9071 は d 退役で moot
  (branch/worktree 削除確認済)。
- **2026-07-07 (夕) — レーン役割再点検 (ユーザー提起) → HUB 裁定 issue 0098: c REACTIVATE + b de-scope**:
  4 並列調査 (wf_d4994964) で a=1019 収束中だが queue 深/9000 instance tail は a territory (1017 計画と一体、
  再配分は dup 再演ゆえ棄却)、b=velocity 高いが 9 クラスタ保有+c の gate 7 本で overload 継続、c=遊休は gate 形状
  だが ungated genuine 5 件存在 (うち S-side βₛ bridge は未 claim の ownership gap = 隠れ long-pole) と確定。
  裁定 (判断軸 = レーン等価 + 価値×独立性のみ、適性レトリック禁止を memory 追記): **a 変更なし / b active 変更なし
  + 9013(i) mᵀ を c へ de-scope + βₛ bridge を c へ carve-out / c REACTIVATE (0098 パッケージ 5 件)**。
  shared leaf の interface guard (module-level generic・singerAdapter 再利用・claim-before-build) を 9000/0098 に明記。
  レーン表 c 行更新、9013/9000 に転記。⚠ aSets_support_slice (BG S16_MainResults:2123) は UNDERSPECIFIED —
  restatement が証明に先行 (どのレーンも as-is で証明しない)。cron は Fable 切替に伴い 30 分 `13,43` (d38bcde8) に
  再ペース (前例 2026-07-05)。本日 a 追加合流 1 件 (S(HC)⊆SHCSet sorry-free, S13 +15, build green 3934・push 済
  `06838f6c..5dc355ab`)。
- **2026-07-07 (tick 7) — a/b/c 統合 (cron tick, 全レーン自走分)**: 全レーン merge-base==main HEAD の clean 先行、
  conflict 皆無・新 axiom なし。
  - **a** (`f31df00d`, genuine): Pf (11.8) `coherent(S(HC))` を **sorry-free** に landing — `coherent(S(M''))` の
    subset-restriction + conjDiff witness (S13 +106/−38)。a 領域。
  - **b** (`943e55ed`, genuine ★milestone): **9017 Keystone A 完了** — sAFL の `hWnorm` (W M-normal) を実証明し
    前 tick の残 1 sorry を discharge ⟹ **BG Thm 15.8 `tau2_transfer_constraint` 完全 sorry-free**
    (`#print axioms` = [propext, Classical.choice, Quot.sound])。残 = Cor 15.9 のみ (S15_MF +108/−20)。9017 claim。
  - **c** (`918ad873`+`255148aa`, bookkeeping): issue 9072 CLOSE (Pf 14.9 horth carrier discharged 記録) +
    post-horth gate 状態を lane-a (9000) / lane-b (9013,3002) に cross-lane 共有 (append のみ、.lean 不変)。
  - **build/sorry**: full build green **3934 jobs** (3m21s)、AxiomsCheck OK、新 axiom なし。census **88→87**
    (b Keystone A discharge −1、a sorry-free additive、c issue のみ)。push 済。
- **2026-07-07 (tick 6) — 監視再開 (ユーザー「各レーンを監視します」) + a/b/c 第3次統合**: tick5 (夜) 以降 cron
  unset だった (session-only ゆえ前回停止で消滅) → 規定ペース `7,22,37,52` で cron `984c2a22` 再作成。tick5 後に
  3 レーンが自走して出した新規分を合流。全レーン merge-base==main HEAD (`80d1655a`) の clean な先行、conflict 皆無・
  新 axiom なし。
  - **a** (`550985df`, genuine): Pf (11.8.6) redesign — world-bridge decomposition `SOf(H0C)=SOf(HC)∪sOf(H0C)`
    を **sorry-free** に landing (`f3d93d1a`、S13_MaximalIII_IV +165) + capstone gate 構造確定・`coherent(SOf(HC))`
    sorry-free path (issue 1019)。a 領域。
  - **b** (`5d25e42e`, genuine): BG 15.8/15.9 **Keystone A** — `sylQ`/`uniqQ` (`opiCore_isUniquelyMaximal_of_isSylow`)
    を実証明 + non-nil sAFL を pure minimality-lifting (hLift) に reduce (S15_MF +398/−5)。外側 bare sorry を閉じ
    内側 `hWnorm` (W M-normal) 1 本に精緻化 = net sorry 0 (regression でない)。issue 9017 (shared-infra claim, BG §15)。
  - **c** (`142df918`, genuine): Pf 14.9 **T-side type-P Dade isometry foundation** (S16_NonExistenceG +99)。
    main HEAD `80d1655a` の hub-verdict (9072) = 「T-side coherence route は SOUND, 4001 dead-end でない、C が build」
    に沿った landing。c reactivation trigger の一つが発火した形。c 領域。
  - **build/sorry**: full build green **3934 jobs** (3m25s)、AxiomsCheck OK (全 axiom allowlist 内、新 axiom なし)。
    real sorry census (comment-strip) **87 不変** (on-path 64 / off-path 凍結 23)、regression なし。push 済
    (`80d1655a..8ff14bd9`)。
  - **follow-up 合流 (c 自走分)**: build/merge 中に c が 2 commit 追加 (`c8875eb2` = Pf 14.9 の T-side `horth`
    coherence carrier を **discharge** — `calT1` を `T_typeIII_calT1_family` で構成 + `hcount` を
    `T_typeIII_calT1_card` で proven 化 + `horth` を T-side `S07.Hypothesis` Dade package で discharge、S16 +634/−17)。
    従来 opaque な多-carrier `obtain … := sorry` を **de-opacify** し、残 sorry は lane-b §13/§15 に真に gated な
    S-side βₛ bridge 1 本のみ。regression (証明済→sorry) でなく genuine 構成。合流 (`0e…` merge)、full build green
    3934 jobs (46s、S16+下流のみ)、AxiomsCheck OK。census **87→88** (de-opacify で露出した residual、指標でない)。
- **2026-07-07 (tick 5) — a/b/c 第2次統合 (ユーザー「いますぐ取り込みましょう」)**: tick3 統合後にレーンが
  自走して出した新規分を合流。3 レーン体制 (d 退役後) の初統合。
  - **a** (`7a6190bf`): issue 1019 (11.8.6) soundness refinement + Coq 精読で Route 1 確定 (docs のみ、Lean 不変)。
  - **b** (`b245d446`, genuine): BG Thm 15.8/15.9 **Keystone C** を実証明で close — `signalizer_msigma_sup_inf_partner_eq`
    (H_σ⊔(H∩M*)=H) + Coq `snK_sMst` port (S14_TypePCounting)。**S15_MF real sorry 3→2**。b 領域 (S14/S15)。
  - **c** (`7c1f06e4`, genuine): Pf (13.15) case-B order dichotomy 完成 (p≡1 branch) + (14.4) T-side v-value を
    proven engine に wire (S16_CaseBOrder/S16_NonExistenceG)。Main.lean は c 未編集ゆえ tick4 の清掃済み版を保持
    (dup 再導入なし = 3-way merge で検証)。
  - **build/sorry**: full build green **3934 jobs**、AxiomsCheck OK、新 axiom なし。real sorry **88→87**
    (b Keystone C 分 -1、c は sorry-free)。Main.lean dup 清掃も維持 (6286 行、再導入なし)。push 済。
  ユーザーが d の genuine 席を探索 (Peterfalvi 内 sorry 指定 → BG 側探索) した結果、hub 徹底調査で
  **FT frontier に codex 単独 closeable な genuine sorry 不在**と確定 → 退役裁定。詳細 = 上記レーン表 ⚰ 節。
  - **退役実施**: worktree `/home/ywr/odd-order-d` remove + branch `d` 削除 (was `e4c6ec3c`、churn net-zero・
    reflog 復元可)。a/b/c 3 レーンに集約。ユーザーは codex `/loop` 停止予定。
  - **dup 清掃**: d 前 tick batch (`2826cac1` 経由の 7 commit、Isaacs Ch04 Main.lean +350) の **全 10 decl が
    既存 S01/GroupTheory 補題の dup (defs≥2、genuine 0)** と確定 → 7 commit の Main.lean 追加を reverse-patch で
    除去 (`git apply -R`、−350)。full build green 検証後 commit。消費者は S01/GroupTheory 版に解決 (Isaacs 内
    生存 decl の巻き込みは batch 内で完結)。issue bookkeeping (9061-9067 closed) は保持。
  - **♻ 再活性化トリガー**: (i) T-side dual (`V_inf_centralizer_Q_eq_bot` 等) の gate ((14.9) T-typeII) が
    a/b で landing → codex が proven S-side を mirror; (ii) a/b/c の helper pull-request。→ base 4000 で worktree 再作成。
- **2026-07-07 (tick 3) — 統合 tick (ユーザー「各レーンを統合します」): a/b/c 合流 = 3 genuine landing、d = net-zero churn ゆえ非合流**:
  - **a 合流** (`6cdefc8e`, in-progress merge の完了): Pf (9.5)/(4.5.b) reducible S-member = μ-column を
    S06 residue theory で実証明 (`0969af79`)、**S12 real sorry 8→7**。+ issue 1019 (11.8.6 uniform-degree
    足場が非Galois type III/IV で over-strong と検証確定 → bounded-coherence redesign、scope 済)。
    merge_monitor コンフリクトは両側 07-07 ログ append-both で解決。
  - **b 合流** (`1fe64571`, クリーン): BG Thm 15.8 `tau2_transfer_constraint` を 3 keystone に分解、
    keystone B を実証明で close して assemble (`5020dad7`)。S15_MF.lean のみ (disjoint)。残 A/C は
    honest named-keystone skeleton (gated-endpoint pattern、regression でない)。S15 real sorry = 3。
  - **c 合流** (`a2b2de98`, クリーン): Pf (13.15) case-B order side-agnostic numeric-elimination engine を
    新 leaf `S16_CaseBOrder.lean` に landing (`65e90bd8`、202 行・**sorry-free**)、OddOrder.lean 登録。
    c は S12/Main.lean 未編集 (`git log main..c -- <file>` 空) = main 版保持、取りこぼし無し。
  - **⛔ d = 非合流 (churn、genuine output ゼロ ゆえ trajectory 保全対象でない)**: d の tick 中 10 commit
    (5 feat + 2 main-merge + drop-all `e089f6b4` + 2 chore) は **net Lean diff = 0**。追加 6 theorem 全てが
    既存 sorry-free 補題の重複と確定: 5 件が S01 逐語コピー (9071 既裁定) + p-group `coprime_pgroup_acts_
    trivially_of_order_p_fixed_centralizer` (86e4684b、"BG Cor 1.12") も **`S01:2039 corollary_1_12` と署名・
    証明とも逐語一致** (corollary_1_12 は S06:1414 に実消費者あり)。d の blanket-drop は結果的に正しい。
    **d をマージする価値ゼロ + issue bookkeeping (9071 renumber) の衝突コストのみ** ゆえ非合流。
    d branch は統合後 main へ re-sync 推奨 (churn 履歴は net-zero ゆえ reset で失うもの無し)。
  - **build**: full build green **3934 jobs**、AxiomsCheck OK (全 allowlist 内、新 axiom 無し)。**real sorry = 88** (bin/count-sorry)。
    a:S12 −、b:15.8 gap を named keystone に分割 +、c:+0。proven spine の regression 無し。
  - **push 済** (`c13d2a24`, origin ahead=0): 滞留 15 commits を push。**★ユーザー方針 (2026-07-07)**:
    「push も自己判断してほしい、毎回でなくても要所で」= hub は verified 統合後 (build green + AxiomsCheck OK)
    の `git push origin main` を**自己判断で実行してよい (毎回認可を聞かない)**。前 tick の classifier block は解消。
  - **d = 現状維持 (ユーザー裁定 2026-07-07)**: d branch は reset せず。次 tick で d 自身が `git merge main`
    (churn 履歴 + 9071 issue 衝突は d/hub が合流時に解決)。guardrails (repo全体 dup-scan + commit前 full build)
    は 9071 に記録済、次 shared-infra 追加前に適用。
- **2026-07-07 (tick 2) — a 合流 (progress) + ⛔ d REJECT (BG S01 dup relocation で full-build break) → 監視 HALT**:
  a=2 (Pf 11.8.6 capstone ψ₀ column-witness、hgen algebra sorry-free 化 = **-1 sorry**) を合流 `a8474c50`、
  build green 3933、push 済 (origin 同期)。**d=3 commits を REJECT** (issue 9071 HUB RULING): d の
  `ForwardFromCh03.lean` 追加 5 theorem が**全て BG `S01_Solvable.lean` の逐語コピー**
  (`coprime_actsTrivially_of_normal_and_quotient`=S01:1771 / `coprime_stabilizes_chain_trivial`=S01:1803 /
  `coprime_nilpotent_acts_trivially_of_centralizer_self`=S01:1895 / `burnside_operator`=S01:1720 /
  `mulAut_eq_one_of_coprime_orderOf_of_frattini`=S01:1735)。d の意図は "Move to Isaacs Ch04" relocation だが
  **追加半分だけ・S01 原本削除せず・caller rewire せず** → `S04e_GorThm37.lean:183` Ambiguous term で
  **full build FAIL**。d の dup-scan が frozen BG を除外 + leaf build のみで検証 → 見落とし。**churn (新数学 0)
  + claim-before-build 違反 + build-break** ゆえ hub 裁定 = REJECT (trajectory 保全対象でない = genuine output
  でなく dup)。trial merge を abort、main は a の green 状態を保持。**⚠ d は live で tick 中に 3→6 commit に進行**
  (main-merge b8931593 + nilpotent[=S01:1895 dup] + p-group[86e4684b, **同名 repo 無 = genuine 可能性**]) →
  blanket-drop でなく**選別**: dup 5 除去 + p-group は content 検証し genuine なら S01 cite で保全。unmerged base
  = **e21db660** (`949d5e27` でない = 前 tick batch 中間)。**build failure STOP ゆえ監視 cron を CronDelete して HALT**
  (次 tick で同 break を繰り返さない)。d が branch を fix したら stop→resolve→resume で cron 再作成。
  再発防止 (9071): d の重複 scan は repo 全体 grep + shared-infra 追加は commit 前 full build。sorry = 88 (a -1)。
- **2026-07-07 — 監視再開 (ユーザー「各レーンを監視します」) + tick d 合流 + ⚠ push 18-commit drift 露見**:
  cron 死亡確認 (CronList 空) → 新 cron `c50d5c72` を規定ペース `7,22,37,52` で作成。初回 tick:
  a/b/c=0 (b/c は main に**遅れ** = lane 側の `git merge main` 待ち、逸脱でない)、**d=7 commits**
  (Isaacs Ch04 commutator/Fitting/Frattini action 補題 = claim 9061-9067、全 closed)。step1.5 clean
  (Isaacs shared foundation の Main.lean のみ + issue hygiene)、step1.6 dup なし、新 axiom なし、
  **sorry 変化なし (pure proven additive +350)**。合流 `2826cac1`、full build green **3933 jobs**、
  AxiomsCheck OK。**⚠ サイズ watch: `Isaacs/Ch04_Commutators/Main.lean` = 6636 行 → 分割 issue 0097
  起票** (hub owner、優先度中・shared foundation ゆえ非緊急)。
  **⛔ push blocked (STOP でない)**: auto-mode classifier が `git push origin main` を拒否 (hub 標準
  auto-push policy を classifier が認識しない)。**main が origin より 18 commits 先行** — 直近数 tick の
  a/b/c/d merge が全て local-only で滞留。merge は全て検証済・保持。**ユーザーに push 認可を確認中**
  (merge 保持・監視は継続、STOP しない)。sorry = 89 (tick 前後不変)。
- **2026-07-07 — 📢 lane-a → hub 伝達 (ユーザー指示「ハブにも伝達」)**: lane-a が (11.8) endgame を精査中に
  **landed spine の設計問題を発見・検証確定** — hub 認識用の heads-up (裁定不要、lane-a 自律 frontier)。
  - **成果 (2 landing、axiom-clean、真の定理)**: (11.8.6) ψ₀ column-witness (commit `18344eb5`) +
    **(9.5)/(4.5.b) reducible-inclusion** (`0969af79`、reducible S-member = μ-column を S06 residue theory で
    実証明; note の「repo 不在 major §9」評価を覆した)。S12 real sorry **9→7**。full build green。
  - **★ finding (検証済、独立3角度)**: `Sset_diff_SHCSet_apply_one_eq_qu` (= (11.8.6) capstone が使う
    uniform-degree qu on inducedFamily\SHCSet) は **非Galois type III/IV で偽** (Coq (9.8)(d) の degree-qa
    既約、qa≠qu)。決め手 = **Coq §11 が `S_1` を `subcoherent` 扱いし `bounded_seqIndD_coherence` を使用
    (uniform-degree 不採用)**。→ 偽の足場4件 (`Sset_diff_SHCSet_apply_one_eq_qu`/`hgen_of_S2_uniform_degree`/
    capstone/`coherent_Sset_diff_SHCSet`) に ⚠️ over-strong マーク済 (`dd50be6e`、docstring のみ・build 不変)。
  - **redesign (issue 1019、scope 済)**: 正しい機構 `bounded_seqIndD_coherence` (Pf 6.2/6.3) は
    **既に repo にあり sorry-free** (`S08.six_three_of_six_two_oracle`)、`coherent_S_of_coherent_SH0C` (S13) も
    配線済 → 大 port 不要、redesign は capstone を **S(H₀C) 族に re-target** する 1–2 session の作業。
  - **⚠ hub が次 tick で注視すべき点 (merge/scope)**: redesign は **(11.8) endgame
    (`exists_zeta_residual_not_orthogonal` / `w2_lt_w1_of_residual_not_orthogonal` / `w2_lt_w1_of_hypothesis`)
    を S12 → S13 へ移設 + `FeitThompson.lean:649` の consumer を `S13.w2_lt_w1_of_hypothesis` に更新**する予定
    (import 制約: S12 は下流 S13 の bounded-coherence を呼べないため)。file-move + FT consumer 更新ゆえ
    scope 判定に関わる — 実施時に lane-a から予告する。他レーンは uniform-degree lemma に非依存 (lane-a 内部)。
  - **現状**: 全 commit 済 (`3ee78238..5bf2ab7b`、8 commits)・working tree clean・build green。
    redesign コード実装 (S13 移設 + narrow union-glue) が次 focused work。

- **2026-07-05 (夜) — 監視停止 (ユーザー指示「loopを停止して」)**: cron ad5e5815 を CronDelete。
  ⛔ 停止 (問題起因) ではないので**自動再開しない** — 次の監視再開はユーザー指示を待って
  `7,22,37,52 * * * *` で再作成する。停止時点: main = `334e0bf2` (push 済・tree clean・origin 同期)、
  実 sorry = 101。**未マージ残 (次回再開時にまず合流): `main..a` = 0, `main..b` = 0, `main..c` = 3**
  (c は S16 consumer wiring 系の見込み、範囲は再開 tick で通常判定)。
  **⚠ 再開時の重点 open item (POLE-2 coordination 進行中)**:
  (1) **b の (3.9.a) unsound-carrier fix** — Step-D fallback で landing した `eta_pair_of_coprime` の
      finNeg 形が likely-FALSE ゆえ、次回 A (honest rowInv/colInv 反転形へ書換 + S06 chiColumn_conj から
      sorry-free 証明 + `section16CharacterData_of_isMinimalSimpleOdd` の AxiomsCheck assert 再有効化) or
      B (field 完全撤去) で解消 = **spine axiom-clean 回復の条件** (issue 3002)。b が A/B fix を実 commit で
      landing するか注視。
  (2) **issue 1017 (§5 coherence) = 着手 lane a** (hub 裁定): a が新規 §5 leaf (uniform_degree_coherence +
      subcoherence) を新設し (10.7)→(10.8) char capstone を閉じる。b の S07_Coherence* 非接触。
  (3) **3 レーン並行 deep-engage 中** (a=§5 coherence / b=§13 η-grid keystone [(3.9.a) fix 含む] /
      c=S16 consumer wiring)、lane 数 3 維持。本セッション成果: sorry 104→101、a が gate-1 CLOSED
      (11.8.1 count 全 threading) + 群論 ungated frontier 完遂、b が §13 η-grid (3.9) fields landing
      (Step-D)、c が S16 (13.19) を precise carrier まで de-scaffold + POLE-2 stall の coupled 構造を確定。
- **2026-07-05 (3) — tick: b の §13 η-grid keystone Step-D fallback (spine axiom 表明無効化) を STOP→ユーザー受理 + issue 1017 (§5 coherence) hub 裁定**:
  HUB 裁定 (POLE-2) どおり b が §13 η-grid keystone に着手 (issue 3002): Section16Inputs/CharacterData に
  Pf (3.9) η-grid Dade fields を threading。**副作用で spine producer `section16CharacterData_of_isMinimalSimpleOdd`
  が sorryAx transit → `#assert_only_allowed_axioms` を一時無効化** (3.9.a `eta_pair_of_coprime` =
  finNeg 組合せ転置 ≠ rowInv 指標反転 の documented gate; 3.9.c/3.9 は sorry-free 供給)。[[scaffold-sorry-free-not-done]]
  「従来 sorry-free spine への sorry 混入=HOLD」に該当し **b の合流を abort → ユーザー裁定 = 受理 (Step-D
  fallback 承認、field land で c の EtaGenericData wiring 即 unblock を優先)**。**axiom 表明再有効化条件 =
  b が (3.9.a) を honest close (rowInv/colInv restatement、one_le_norm_signed_paired_sum が support) した時点**
  (issue 3002 で追跡)。⟹ 以後、spine の `#assert_only_allowed_axioms` 無効化は本 (3.9.a) gate 由来の 1 件のみ
  許容 (他 spine 表明の無効化は依然 HOLD+flag)。a/c は本 tick clean 合流 (a=gate-1 threading docs+issue /
  c=bessel field close −1)。**issue 1017 (§5 uniform_degree_coherence + subcoherence 欠落 = a の 10.8 char
  capstone prereq) hub 裁定 = 着手 lane a** (free + 診断済 + consumer、新規 §5 leaf 新設、b の S07_Coherence*
  非接触)。⟹ 3 レーンが char endgame の別 keystone を並行 deep-engage (a=§5 coherence / b=§13 η-grid /
  c=S16 wiring)。full build green 3929 / sorry 101→101 (a −1 gate-1 系, c −1 bessel, b +1 3.9.a gate = 差引 −1
  だが c 合流時 100 → b 合流時 101)。push 完了。
- **2026-07-05 (2) — tick: b の Hypothesis76 zeta_induced (S09_NonexistenceCertain) STOP→ユーザー裁定受理 + 38-commit burst 合流**:
  b が a 所有 `S09_NonexistenceCertain` の `structure Hypothesis76` に field `zeta_induced` (Pf (7.6)
  忠実、(13.5.a) 整数性の供給) を追加 = 3002 供給編集権 (additive helper 限定) の外 → 手順どおり
  a 合流後に cron f05f294d を CronDelete して STOP → **ユーザー裁定 = 受理 (0091 同型の一回限り、
  standing でない。以後の b の同 file 編集は通常どおり逸脱)**。裁定待ち中に b が 2→38 commits に
  drift (3002/2033/2034 の (13.5)-package real 化 burst) → staged 全数監査 (FeitThompson hunks =
  3002 zone 内 / 共有 3 file 純 additive / S09 +22 additive のみ) で clean 確認後合流 `6679c4db`。
  build green 3924 jobs (261.1s) / AxiomsCheck OK / sorry 118→119 (+5 scaffold −4 discharge)。
  cron 再作成で監視復帰 (stop→resolve→resume)。
- **2026-07-05 — 監視再開 (ユーザー指示「各レーンを監視します」) + tick 合流 a/b/c 全レーン + b S05 裁定 (供給編集権明文化)**:
  cron 死亡確認 (CronList 空) → 初回 tick で a=2 / b=3 / c=1 commits を合流。**a** = Pf 11.8.1
  `charParam_d_modEq_one` 実証明 (d≡1 mod q 閉、S12_Section9Counts 新 leaf 分離、sorry 115→114)。
  **c** = shared 9010 `InducedDegreeSum` (sorry-free、claim 携行; root closure 外 → 手順 3b で
  OddOrder.lean に import 追記)。**b** = 3002 grid threading 両半分 (7 property fields 供給込み
  sorry ゼロ、2026-07-05 裁定選択肢 2 の実施) + (13.10) atom 4 producer 分解 (sorry 114→117、
  +4 は全て新 decl scaffold で ALLOW)。**b の S05_TICyclic `omega_inner` (+11) を step 1.5 逸脱として
  保留 → ユーザー裁定 = 受理 + 3002 供給編集権として明文化** (上記 carve-out ブロック参照、3002 供給
  完了で失効)。処理順は a→c 先行合流 → b 裁定後合流 (2026-07-04 夜 tick と同型)。検証: full build
  green 3918/3919/3919 jobs (174.5s / 5.5s 増分 / 289.8s)、AxiomsCheck OK、新 axiom なし。push は
  a+c 分で**前セッション滞留 21 commits も解消** (`50315e70..1a99f4f4`)、b+docs 分は本 commit 後。
  ⚠ 教訓: tick 処理中に b の tip が 2→3 commits に進行 (lane セッション稼働中) — merge 直前の range
  再確認 (2026-07-04 教訓) が実際に効いた。
- **2026-07-04 (朝) — tick: b の S12→S10 relocation を STOP→ユーザー裁定受理 + 大 drift 検出 (cron 4db07909 再作成)**:
  b が lane-a authored の `typePData_V_ti`(Pf 4.6.b)/`typePData_typePV_not_mem_derived`(Pf 10.5) を
  **S12_Core(lane a)→S10 へ upstream relocation** (b の type-P Dade engine `typePA0_isConj` が cite 用、
  S10<S12 の import 依存で必須) + a の S12 call site 2 箇所更新 → **S12_Core 編集 = 0096 protocol の都度裁定
  逸脱** で STOP (cron 541028bc CronDelete)。**ユーザー裁定 = 受理 (build 検証後合流、standing でない)**。
  ⚠ **大 drift 教訓**: AskUserQuestion 回答まで ~6h gap があり、その間 b が loop¹²⁰→¹⁵⁵ の ~38 commit
  ((12.14) SORRY-FREE 完成・(12.16) cyclotomic 等の Dade tower endgame、全 S14=b 所有 + S10 carve-out +
  GroupTheory 共有) を進行 → `git merge b` が range-check 済 2-commit tip でなく現 tip を取り込んだ。
  **post-merge 監査で全 clean 確認**: S10 out-of-scope decl 非接触 / S12 変更は承認済 relocation の 2 decl のみ
  (他 decl 削除なし) / 新 axiom なし / 全ファイル owned(S14)・shared(GroupTheory)・carve-out(S10)・承認済(S12)
  ゾーン内 / **build green 3912 / AxiomsCheck OK / sorry 113→112 (−1, b の 12.14 系 discharge)**。push
  `042c2d05..316d818e`。**⟹ cron prompt に「長 gap 後は merge 直前に range 再確認」を追加** (step 5)。
  S12_Core 編集は今後も 0096 protocol で都度裁定 (受理は standing carve-out でない)。
- **2026-07-04 (夜) — tick: a(RepTheory induce_inner_trivial)/b(Pf 8.12.b faithful) 合流 + b の S10 (8.12.b) landing を hub 裁定受理 (carve-out 0096 拡張 #2) + 9006 relocate 裁定**:
  a=`692a8ba4` (`induce_inner_trivial` = ⟨Ind_H^G θ,1_G⟩=⟨θ,1_H⟩、GroupTheory/InducedCharacter 共有、
  grandfather leaf、build green 3906) +`a04539e4`(docs) → 合流 `69f8858b`。**b** = `7f863d33`
  (Pf (8.12.b) faithful `typeI_or_typeII_centralizer_unique_hall` を S10 に landing = Hall 仮説付き
  完全証明・axiom-clean; 旧 false-as-stated `typeI_or_typeII_centralizer_unique`/`escapingCentralizers_control`/
  vestigial-false `typeII_A_sets_*` に **docstring-only 注記**) +`10377c82`(docs §8 type-II 監査)。b の S10
  (8.12.b) 所有は 2026-07-04 拡張#1 (proof-only de-gate) を超える → **step 1.5 逸脱検出 STOP → ユーザー裁定
  受理**: carve-out 0096 を「(8.12.b) faithful form の S10 landing + 旧 decl の docstring 注記 (statement/
  proof 不変)」に拡張#2 (旧 decl の削除/statement 改変は依然要 flag)。**issue 9006 (b 起票, FeitThompson から
  3 Hall 補題 relocate) = ユーザー裁定「owner 固定せず issue+LAUNCH で全レーン awareness を保てば誰でも可」**
  → 9006 に運用記載 + lane a LAUNCH.md に周知行。b 合流 `73a66959`。検証: **full build green 3906 jobs /
  AxiomsCheck OK / sorry 112→112 (新 faithful decl は proven ゆえ中立) / 新 axiom なし**。push
  `8f0dcd73..73a66959` (a+b)。監視 cron を `a718b710` で再作成。c 本 tick 未マージ 0。
  ⚠ b の loop¹¹⁰ docs (`9fcf5af5`) が「レーン b tractable 作業枯渇 — S07/S08 完成, S09 は 7.9 gated」を
  記録 (次 tick 以降 b の frontier 状況を注視; 停滞なら能動報告)。
- **2026-07-04 — tick: a(docs)/b(BG Theorem B COMPLETE) 合流 + b の S10 de-gate を hub 裁定受理 (carve-out 0096 拡張)**:
  tick で a=`160ffec9` (docs, issue 0044 = (7.8.a) blocker 解消) → 即合流 (`9c3110b0`)。**b** = `94a34018`
  (BG Theorem B **全 5 conjunct 完成・axiom-clean**: `theoremB_A_minus_Msigma_isTISubset` B(5) +
  `uniqueMaximal_of_kappaSigmaCompl_element` Lemma15.1(c)一般形 + `theoremB_U_and_A_tame` faithful化
  [conjunct1 を `p.Prime` 制限 = 旧 `∀p:ℕ` の latent unsoundness 是正] → Theorem B の standing sorry 除去)
  +`d8e107a5` (docs)。b は consumer un-gate の一環で **S10 `typeI_centralizer_le_and_unique` (Pf 8.12.b,
  :1728, lane-a 所有・carve-out 0096 外) の proof body を de-gate** (B4 full-Theorem-B cite →
  `typeP_hall_small_subgroup_cyclic_tau2` 直接 cite; signature 不変・sorry/axiom regression なし・9003 で
  self-flag)。⟹ **step 1.5 範囲逸脱を検出し STOP** (cron `c8419068` CronDelete) → **ユーザー裁定 =
  受理 + carve-out 0096 拡張** (§8-support consumer の proof-only de-gate を b 許容、statement 改変は
  依然 out-of-scope; 2026-07-03 の同型 S10 edit 受理と整合)。b 合流 `40cf07a9`。検証: **full build green
  3906 jobs / AxiomsCheck OK / sorry 113→112 (−1, Theorem B gate 除去) / 新 axiom なし**。push
  `842a1a2f..40cf07a9` (a+b)。carve-out 拡張を issue 0096 + 本マップ note に反映。**監視 cron を
  `5801a228` で再作成し tick 復帰** (stop→resolve→resume 正規サイクル)。c は本 tick 未マージ 0。
- **2026-07-04 (未明) — 監視ループ再開 (ユーザー指示「各レーンを監視します」) + 再開初 tick 合流 a/c**:
  停止時 cron 死亡を確認 (`CronList` = 空)、**新 cron `c8419068` を規定ペース `7,22,37,52 * * * *` で再作成**。
  再開初 tick で停止時の未マージ残を合流 (stop 時見込み a:2/c:3 は lane が `git merge main` 再同期で
  a:1/c:2 に再編、内容同一)。**a** = `f6533c86` refactor(Pf 11.8.5 prep): SHC 機構の isometry 核を
  reusable `IsCoherent` API (inner_extension_self_eq_one / inner_extension_eq_zero_of_ne) に抽出 (S12、
  callers 不変・sorry 不変)。**b** = 0 (変化なし)。**c** = `5e81d626`+`d319c0f1` Pf 1.7(b) cont.: type-I
  Clifford の Hall coprimality input + coprimality COMPLETE (Ito in-repo、CliffordDecomposition.lean =
  9002 shared infra)。範囲逸脱なし (a→S12 所有 / c→GroupTheory 共有)、新 axiom なし、**sorry 113→113 不変**。
  merge `3868c3f9`(a)+`eabcbde2`(c)、**full build green 3906 jobs** (3898→3906 = +8, 新 decl 相当)、
  AxiomsCheck OK、`git push origin main` 成功 (`fab4a354..eabcbde2`)。新規 HUB issue なし
  (9000 の 2 HUB 項は共に stale: dup 裁定は解決済 = lane d leaf、"lane d 次 target" 項は lane d 退役で moot、
  stop 記録どおり「lane a 承継・対応不要」)。次 tick 以降 `7,22,37,52` で通常監視。
- **2026-07-03 (夜) — 監視停止 (ユーザー指示「いったん区切ります」)**: cron a8af8c6a を CronDelete。
  ⛔ 停止 (問題起因) ではないので**自動再開しない** — 次の監視再開はユーザー指示を待って
  `7,22,37,52 * * * *` で再作成する。停止時点: main = `e9119393` (push 済・tree clean・origin 同期)。
  **未マージ残 (次回再開時にまず合流): `main..a` = 2, `main..b` = 0, `main..c` = 3** (いずれも lane
  セッション継続中の新 commit; a=11.8 系, c=Pf 1.7(b) 系の見込み、範囲は再開 tick で通常判定)。
  本セッションの成果 (再開〜停止): sorry 120→113、a/b/c 全レーンが実証明で前進。特筆:
  (1) **Pf §8 Dade-support クラスタ type-I 側完結** — (8.12.b)/(8.13.a/b/c)/(8.14)/(8.15) を
  BG bridge で実証明、supply 元の **BG Lemma 14.13(a) (`non_disjoint_signalizer_frobenius`) が
  完全証明・axiom-clean** (新 leaf `S16_Lemma1413.lean`)。type-II 系のみ残 (BG Theorem B に gated)。
  (2) **issue 9004 全完了** (Hypothesis46 small-V + typePA0 M-共役の unsound 是正 → toHypothesis46
  §10 instantiation + 4.8/4.10 aligned-grid thread discharge、axiom-clean)。(3) **issue 9005 (hub
  prefix-split)** — S08 generic char 3 補題を `InducedTransport.lean` へ分離、c の Isaacs 6.11
  Clifford correspondence を unblock。(4) c は **Isaacs 6.11 + Pf 1.7(b) constructive Clifford
  (mult-one packaging + conj-distinctness + non-reality) COMPLETE** (issue 9002)。
- **2026-07-03 — 監視再開 (ユーザー指示「各レーンの監視を再開します」) + 初回 tick 全レーン合流**:
  cron a8af8c6a を規定ペース `7,22,37,52 * * * *` で再作成。初回 tick: a=5 / b=8 / c=10 commits を
  a→b→c で合流 (`9aca52bf` / `55e46f1f` / `4847abc3`)、全ゲート green (build 3898/3898/3901 jobs、
  AxiomsCheck OK、sorry 115→120 = 全て新 decl faithful scaffold pin、新 axiom なし)、push 済。
  特記: (1) **b の S12_Core cross-lane 2-hunk (S10 (8.15) carrier faithful 化の機械的追従、issue
  0096 flag 済) はユーザー裁定 2026-07-03 で受理** — 65a2be52 と同型の statement-soundness 改善。
  standing carve-out ではない (以後の b の S12_Core 編集は通常どおり逸脱)。(2) c の新規 3 file
  (CyclicCharacterExtension 系) が root closure 外 → 手順 3b で OddOrder.lean に import 追記。
  (3) サイズ watch: S10 が 905→1703 行で 1500 超え (分割は issue 0096 の恒久解 = S10_DadeSupport
  prefix-split で追跡済; S12=0076 / S14=0084 も既存)。(4) a の issue 9004 追加発見 2 (typePA0
  G-共役 unsound) は b 所有の `dadeSupportHypotheses_typeP` (S10:566) の statement 偽を含意 —
  0096/9004 に相互注記で b へ通知。 cron 943218a9 を規定ペース
  `7,22,37,52 * * * *` で再作成。再開時点: main = 停止時と同一系 (tree clean・origin 同期済)、
  `main..{a,b,c}` = 0 (変化なし)。新規 HUB issue なし (open の 9000 claim は lane a 承継注記済で対応不要)。
- **2026-07-02 (夜) — 監視停止 (ユーザー指示「監視はとめます。一区切りにします」)**: cron 1af200eb を
  CronDelete。⛔ 停止 (問題起因) ではないので**自動再開しない** — 次の監視再開はユーザー指示を待って
  `7,22,37,52 * * * *` で再作成する。停止時点: main = e0d9bcb5 (push 済・tree clean・full build green
  3898 jobs)、`main..{a,b,c}` = 0、全レーン本日夕方以降 無 commit (lane セッション停止中とみられる)。
- **2026-07-02 (夕) — hub 全体レビュー (ユーザー委任) + 再編 follow-through 完遂**: lane-role review
  (5 並列 agent) で a/b/c とも on-role・honest 進捗を確認 (b のみ partial = S10 edit 1 件 → 受理)。実施:
  (1) issue 整理 — 0086/0088/0092/0093/4014 close (supersede/解消注記)、8022 の d-carve-out 失効注記、
  9000 claim を lane a へ承継注記。(2) 裁定 (issue 9003) — b の `65a2be52` (S10 `support_mutual_exclusion`
  実証明 = false-statement 修正) を**受理 (keep in S10)**、**§8 Dade-support 宣言群を lane b に carve-out
  (issue 0096)**、当時の (6.5.c) 未処理 claim (2026-07-06 D audit で landed 済み/stale) と b の main 17 遅れをリマインド。(3) 本ファイル +
  ft_lane_reallocation + ft_path_policy の 3 レーン整合化 (旧 4 レーン operative 記述を修正/履歴化)。
  検証: on-path unowned sorry = 0、`FeitThompson.lean` 0 sorry、共有ゾーン 0 sorry (comment-strip census
  103 sorry: a 28 / b 13 / c 32 / BG 凍結 15 / Pf Appendices 凍結 15)。
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

- **⚠ orphan module は「build green」をすり抜ける (2026-07-11 実害、hub 配線で修正)**: `lake build OddOrder`
  が検証するのは **root `OddOrder.lean` からの推移 import closure のみ**。新 leaf を merge しても
  OddOrder.lean (または既存 consumer) への import 配線が無ければ**一度も elaborate されずに
  "Build completed successfully"** になる (実例: a の `S12_Noncoherence` — ★★★★
  `no_typeV_maximal_unconditional` 本体 — と `S12_TypeVCaseC`、07-06 の
  `GroupTheory/RepresentationTheory{,.SubrepresentationKernel}` の計 4 module が orphan、
  うち Noncoherence は AxiomsCheck の assert も無く un-tripwired だった)。**対策 (tick 手順に追加)**:
  新規 .lean file を含む merge の後は **orphan scan** — `OddOrder/**/*.lean` の module 集合と
  `.lake/build/lib/lean/OddOrder/**/*.olean` の集合を突合し、差分があれば OddOrder.lean へ import を
  追加 (共有ファイルの sanctioned 編集) してから build green を判定する。加えて lane 側は新 leaf 作成時に
  OddOrder.lean 配線 + (flagship 級なら) AxiomsCheck assert 追加までを 1 commit に含めるのが正
  (c は TTypeII が import する形で遵守済みの先例)。
