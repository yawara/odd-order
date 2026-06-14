---
id: 67
slug: s13-transition-split
title: "S13_PrimeActionTransition 分割 (1921行>1500, F frontier 凍結後)"
created: 2026-06-14
---

# S13_PrimeActionTransition 分割 (1921行>1500, F frontier 凍結後)

## 背景

`OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeActionTransition.lean` が **1921 行** に到達
(2026-06-14, Lemma 13.8 (3a) 合流 `d60d576b` 時点で検出)。ファイル粒度規約の 1,500 行上限超過。

ただしこのファイルは **Lane F (bg-s12) の active frontier** — F が現在 13.7/13.8 を書き、
続けて 13.9-13.13 を埋める予定。分割を今やると F の作業と衝突する (前方参照は構文上不可ゆえ
任意の宣言境界で安全だが、active に追記中の領域に prefix-split 境界を引けない)。

merge_monitor.md「サイズ watch」手順 + [[feedback-record-deferred-hub-tasks-as-issues]] に基づく
deferred hub タスクとして起票。分割の実施 owner = hub。

## やること

- [ ] **トリガー**: F が §13 transition (13.7-13.13) を landing し終え、ファイルが凍結したら着手
      (または途中でも、F の active 領域と衝突しない明確な凍結境界が定まったら部分実施可)。
- [ ] 凍結境界で prefix-split: 先頭 K 宣言 (定義 + 13.7/13.8 等の確定済クラスタ) を上流ファイルへ、
      残り (active frontier) が import する形に。前方参照不可ゆえ任意の宣言境界で安全。
- [ ] 新 leaf を `OddOrder.lean` + `AxiomsCheck.lean` の両方に import (root closure 検査)。
- [ ] 下流 (hub `S13_PrimeAction` 系 / §14 cite) は import だけで不変なことを確認。

## 完了条件

- S13_PrimeActionTransition.lean (および分割後の各ファイル) がいずれも 1,500 行未満。
- `lake build OddOrder OddOrder.AxiomsCheck` build-green、実 sorry 不増。

## 参照

- merge_monitor.md「4. サイズ watch」 / CLAUDE.md「分割の owner と trigger」
- 先例: issue 0063 (S10_LocalLemmas split) / 0064 (S05_NarrowPGroups split) — 同じく active frontier ゆえ凍結待ち
- 検出コミット: `d60d576b` (Merge bg-s12, Lemma 13.8 (3a))
