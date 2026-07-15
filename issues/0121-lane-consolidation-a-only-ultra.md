---
id: 121
slug: lane-consolidation-a-only-ultra
title: "HUB: A 単独 (codex 5.6 ultra) へ集約 + 監視レーン維持 (2026-07-15)"
created: 2026-07-15
---

# HUB: A 単独 (codex 5.6 ultra) へ集約 + 監視レーン維持

## 背景 (ユーザー裁定 2026-07-15)

FT endgame の parallelism が事実上枯渇した:
- **flip が唯一のボトルネックで serial** (0118 で単一レーン a に割当済、signature churn ゆえ分割不可)。
  4 root (#1 exists_muT_index / #2 exists_etaT_alphaFun_one_int / #3 character_degree_analysis /
  #7 tSide_theta_package+lambda_forces_T_caseB) は ~14 tick 全て sorried のまま、census 32 固定
  (a の作業は全て additive + compat-entry、まだ 1 root も落ちていない = large-but-convergent grinding)。
- **b/c は ungated work 0** (tick #8 の 4-agent 監査 + 以降で確認): b-5 pt2 / b-2 / 9103 Ph2 / c-3 / c-4 は
  全て flip landing 待ち。直近 b/c は main-sync のみで genuine 0 ahead。
- **c の pins rewrite が a の flip cut-over と同 S16 file で毎 tick 衝突** (hub 解決 = throughput 0 の純コスト)。

⟹ ユーザー裁定: **A を codex 5.6 ultra の単独作業レーンに集約し、b/c を退役。監視レーン (hub) は残す。**
A を選ぶ根拠 = flip の live context (uncommitted WIP + 全 flip 履歴) を保持するレーンだから (handoff リスク最小)。

## 集約後の構成

- **A** (branch `a`, worktree `/home/ywr/odd-order-a`, **codex 5.6 ultra**): 残り FT 作業を**全て serial に**実行。
- **hub** (main worktree): A のみを監視・合流 (green gate 維持)。cross-lane 調整は消滅。
- **b / c**: 退役 (worktree + branch 削除、reflog 復元可)。退役時 genuine 未マージ work = 0 で確認済 (下記)。

## 所有権の集約 (単一オーナー → scope 逸脱概念が消滅)

A が**全 Pf/BG S-file + FeitThompson + 旧 b/c carve-out を含む全領域**を所有。per-lane territory / carve-out
群は無効化 (単一レーンゆえ逸脱不可能)。旧 b/c の残タスクは A の serial queue へ fold:

| 由来 | タスク | 状態 |
|---|---|---|
| a (flip) | S16 残 5 legacy c_eq_one cut-over → NormEstimates atom `_core` cite 置換 (#1/#2) → root #3/#7 legacy retire | 進行中 |
| a (flip) | root #4: OrderRelayer/Eta10Correction を honest SwappedNuGridSupply へ (tick #14 infra landed) | 進行中 |
| b-5 pt2 | generic `Hypothesis.nuGridSupply` (HypothesisSwap:133) 削除 → root #4 除去 + census −1 | root #4 の a 側完了後 |
| b-2 / 9103 Ph2 | `S_typeP2` field + `T_isTypeP2_gate` (root #7 前半) 削除 | flip landing 後 |
| c-3 | `V_inf_centralizer_Q_eq_bot` (root #5) discharge — 単一オーナーゆえ producer↔consumer の DAG-collision 懸念消滅 | flip landing 後 |
| c-4 | `feitThompson` の #print axioms 最終 trace → FT axiom-clean 判定 + AxiomsCheck assert | 全 root 除去後 |

doneness は sorry 数でなく carrier 構成可能性 ([[scaffold-sorry-free-not-done]]) — census が動くのは root retire 時。

## hub tick の簡素化 (監視レーン維持)

- A のみ訪問。green gate = build green + AxiomsCheck OK + sorry regression なし + 新 axiom なし。
- **scope-check / carve-out 裁定 / shared-infra dedup / cross-lane conflict 解決は不要** (単一オーナー)。
- A は branch `a` に commit、hub が `--no-ff` で main へ合流 (ultra の大 commit も独立 build gate を通す価値あり)。
- cron 継続 (現行 15 分 `7,22,37,52`)。全レーン 0 なら変化なし 1 行。

## 退役の安全性 (2026-07-15 確認済)

`main..{b,c}` の genuine .lean tree diff = **0** (b=main-sync merge のみ、c=main 同位置)、
uncommitted WIP も無し ⟹ **b/c 退役で genuine 成果の損失なし**。

## 実行手順 (ゲート = ユーザーのセッション操作)

1. **[ユーザー]** b と c の codex `/loop` セッションを**停止** (⚠ worktree 削除後は codex が git エラーで空転
   するため先に停止必須。lane-d 退役の教訓)。
2. **[ユーザー]** A の codex セッションを **codex 5.6 ultra** に切替。
3. **[hub、1-2 確認後]** `git worktree remove /home/ywr/odd-order-{b,c}` + `git branch -D b c`
   (reflog 復元可)。所有マップ (merge_monitor 🔒 / ft_lane_reallocation / 0118) を「A 単独」へ更新。
4. **[A]** `git merge main` → issue 0116 の残手順を serial 実行 (上表の fold タスク込み)。
5. **[hub]** 以後 A のみ簡素 tick で監視・合流。

## 再展開トリガー (reversible)

flip landing 後、post-flip 並列 work (c-3/b-2/9103/c-4 は別 file で並列可) の量が単一レーンで律速するなら、
`git worktree add` で 2-3 レーンへ再展開。集約は可逆。

## 完了条件

- [x] b/c 退役 (worktree+branch 削除済 tick #17、tips reflog b=b14d552a/c=eeda401a; 所有マップ = merge_monitor 冒頭バナーで A 単独へ更新)
- [x] A = codex 5.6 ultra 単独レーンで稼働 (ユーザー切替済)、hub 簡素 tick で監視 (tick #17〜)
- [x] (最終) ✅ 達成 tick #22 (merge f5ab3129): flip landing (roots #1/2/3/7) → root #4 (9096) → #7-half (9103) → #5 V_inf (9077) 全除去、`#print axioms feitThompson` = 標準3公理のみ (c-4 axiom-clean PASS)

## 参照

- issue 0118 (3 レーン再設計、本 issue で A 単独へ集約 = 部分 supersede)、0116 (flip 設計)、9096 (root #4)、
  merge_monitor tick #8-#14。lane-d 退役 (merge_monitor ⚰ 2026-07-07) = 退役手順の先例。
