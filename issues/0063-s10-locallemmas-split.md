---
id: 63
slug: s10-locallemmas-split
title: "S10_LocalLemmas (2,363 行) の topic-split — 10.13 着地で全凍結、優先度低"
created: 2026-06-11
---

# S10_LocalLemmas (2,363 行) の topic-split — 10.13 着地で全凍結、優先度低

## 背景

粒度規約のサイズ watch (merge_monitor 手順 4) が merge `b5e0f541` (Lane E, Lemma 10.13
COMPLETE) で発火: `S10_LocalLemmas.lean` が +1,108 行で **2,363 行** (閾値 1,500 超)。
E は LAUNCH.md の新 leaf デフォルト (10.13 → `S10_RankTwoStructure.lean` 新設推奨) に
従わず同一ファイルへ追記した。

ただし 10.13 着地で **§10 は全結果 sorry-free・unconditional = 本ファイルは完全凍結**。
編集ループのコストはもう発生しない (凍結ファイルは上流変更時の full build でのみ再 elaboration)
ため、分割の価値は DAG 衛生・可読性・upstream 適性のみ。**優先度低** — hub の手隙ウィンドウで実施。

## やること

- [ ] topic 境界の特定 (候補: Lemma 10.13 cluster ~1,108 行を `S10_RankTwoStructure.lean` へ
      suffix-split; 10.3/10.4 は既に E が `S10_LocalCriteria.lean` へ移動済みなので残部の結束を確認)
- [ ] prefix/suffix-split 実施 (手順 = CLAUDE.md「分割の owner と trigger」; 前例 = S08/S12_E/S05
      split commits `1c03ec60`/`b2416203`/`954408b2` の python 境界 assert パターン)
- [ ] OddOrder.lean 登録 + full build + AxiomsCheck green
- [ ] 下流 import / AxiomsCheck guard 名の不変確認

## 完了条件

S10_LocalLemmas 系の各ファイルが ≤1,500 行で、full build 3631+ green / AxiomsCheck 全 OK /
実 sorry 数不変。

## 参照

- merge `b5e0f541` (発火元), CLAUDE.md「ファイル粒度 — 分割の owner と trigger」
- notes/meta/merge_monitor.md 手順 4 (サイズ watch)
- 分割前例: `1c03ec60` (S08) / `b2416203` (S12_E) / `954408b2` (S05)
