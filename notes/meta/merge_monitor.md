# main 合流モニター — a/b/c レーン自動合流の運用手順

> 横断運用ドキュメント。**監視ペースは hub のモデルで決まる (ユーザー 2026-07-09 明文化)**: **Fable 使用中 = 30 分間隔 `13,43 * * * *`** (速度考慮) / **Opus 使用中 = 15 分間隔 `7,22,37,52 * * * *`** (:00/:30 回避・均等割り)。履歴: 2026-07-05 Fable で 30 分 `13,43` → Opus 切替で 15 分復帰、2026-07-09 Fable で 30 分 (ユーザー指示)、2026-07-02〜07-05 は 15 分、2026-06-29〜07-02 は 30 分、それ以前は 15 分。cron は session-only ([[cron-dies-on-model-switch]]; CronCreate `durable:true` は本環境で disk 永続せず session-only 扱い) ゆえ、**再作成時は現行モデルに対応するペースで**作る。main worktree = `/home/ywr/odd-order`。
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
| **c** | `c` | `odd-order-c` | γ **S16 非存在 + ♻ 2026-07-07 REACTIVATE (issue 0098 パッケージ 5 件)**: typeP_pair port (§8 新 shared leaf) / semilinear (9.7.b) field-model leaf / S-side βₛ bridge carve-out (S15_SAndT.lean:3616 BetaData 領域) / §14 Γ-bridge assembly / hcard2 verify | `Peterfalvi/S16_NonExistenceG.lean` + 構成的 Clifford (9002 完了) + carve-out: reconciled_typePData_T 残 field (S15_SAndT_Setup:4520/:4590) ・BetaData 領域 (S15_SAndT:3616) + 新 shared leaf (claim-before-build) | 3000 |
| ~~**d**~~ | — | — | ⚰ **退役 (2026-07-07, ユーザー裁定)** — codex 運用 shared-infra レーン。worktree/branch 削除済 | — | — |

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
> / 共有ファイル編集（AxiomsCheck.lean 追記・OddOrder.lean import・`OddOrder/GroupTheory/**`・`OddOrder/Mathlib/**` 共有 infra・notes・issues）。
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
> **carve-out 拡張 (issue 9076 piece 4c, hub 裁定 2026-07-08 監視 tick)**: `OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean`
> (lane c が新規作成、Pf (8.10)/(8.15) honest `'A0(S) = 'A(S) ∪ V^S` 定義 + set-level facts) は名目上
> S15 = **lane b 領域**だが、issue 9076 の piece 4c (A0-Dade correctness fix — 現 (13.18) は 'A(S)-Dade
> だが μ差 support は P^#∪V_S ゆえ A0 化必須) infra ゆえ **lane c 所有**として扱う (S05_GridRigidity と
> 同型 = 内容で割当)。根拠: 新 leaf (b の `S15_SAndT` を編集せず `honestTypeP2ASet` (b の
> `S15_SAndT_Setup:552`) を cite して拡張)、b は S15 を触っていない (衝突なし)。⟹ step 1.5 で c が
> S15_HonestTypeP2A0 を編集しても逸脱でない (b が編集したら逸脱)。
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
