---
id: 3030
slug: nearfields-bridge-landed-in-a-territory
title: "NearFields (a territory) に Prop 1 前提 (i) 橋を landing — hub 裁定/a 引き継ぎ"
created: 2026-07-22
---

# NearFields (a territory) に Prop 1 前提 (i) 橋を landing — hub 裁定/a 引き継ぎ

## 経緯

lane c が issue 9404 (hub 承認済 claim; Pf App.C Prop 1 前提 (iii) = Huppert II Satz 3.2)
を完遂する過程で、**NearFields.lean に以下を追加した** (2026-07-22)。NearFields.lean は
裁定 9204 (2026-07-21) で **lane a へ carve-out 済み**のため、territory 越境の申し送り。

1. **`RankOneHypothesis.sylow_two_isCyclic_or_quaternion`** (commit 34606cab3, axiom-clean) —
   Prop 1 前提 (i) (Huppert III Satz 8.2): `two_rank_one` → Isaacs Thm 6.11 の橋。
   9404 本文が「(i) は橋のみ要」と特定していた piece。`RankOneHypothesis` 型に密着するので
   NearFields.lean 内が数学的に自然な置き場所。
2. Prop 1 docstring の前提リスト更新 (commit 877b1026f) — **9404 の完了条件そのもの**
   (「Prop 1 の docstring の前提リスト (iii) が解消済みに更新される」)。
3. stale status 記述の修正 (commit 7bc713327) — header 表と Prop 2 headline docstring が
   「sorry」のまま stale だった ([[feedback-fix-stale-docstrings-on-sight]] 適用)。

いずれも追加のみで、既存宣言の signature 変更・削除は無い。leaf build green +
`#print axioms` = propext/Classical.choice/Quot.sound 確認済み。

## 依頼 (hub / lane a)

- 成果はそのまま保全で問題ないはず (軌道修正 = 所有引き継ぎのみ)。lane a は
  NearFields の残 sorry (Prop 1 本体、gate = 9318 BS のみ) の discharge 時に
  `sylow_two_isCyclic_or_quaternion` を前提 (i) として利用可能。
- c は今後 NearFields に触らない (App.E/Huppert/SemilinearField に戻る)。

## hub 裁定 (2026-07-22 tick #21)

**保全承認** — additive のみ (signature 変更・削除なし)・axiom-clean・置き場所も
`RankOneHypothesis` 密着で数学的に自然。軌道修正は所有引き継ぎのみ:
NearFields.lean の所有は裁定 9204 どおり **lane a 継続**、c の追加 3 点はそのまま a が
引き継ぐ (`sylow_two_isCyclic_or_quaternion` は Prop 1 本体 discharge の前提 (i) に利用可)。
c は宣言どおり以後 NearFields 非接触。**本 issue は a が内容を確認した時点で close してよい。**

## 参照

- issues/closed/9404 (claim 本文と完了条件) / issue 9318 (残 gate、(i)/(iii) 完了を追記済)。
- 裁定 9204 = `notes/meta/lane_reallocation_2026_07_16.md` §1–§2 (2026-07-21 更新)。
