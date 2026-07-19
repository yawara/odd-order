---
id: 129
slug: cngroupstructure-second-split
title: "CNGroupStructure.lean 1585 行 (>1500) — Thm 1.5 証明クラスタの追加分割"
created: 2026-07-19
---

# CNGroupStructure.lean の 2 回目分割

## 背景

2026-07-19 監視 tick (merge `33e2c794a`) のサイズ watch で検出。lane c は同 push 内で
3-step 定義群を `ThreeStepGroup.lean` (337 行) へ prefix-split 済みだが、Gorenstein
Thm 1.5 の完全証明 (+~600 行 gross) が上回り、`OddOrder/GroupTheory/CNGroupStructure.lean`
は 1302 → **1585 行 (> 1500 trigger)**。

9133 の残作業 (Cor 1.6 の consumer 配線等) が続くとさらに伸びる見込み。

## やること

- [ ] c の 9133 frontier と衝突しない凍結境界で prefix-split (実施 owner = hub、
      lane c が自主分割するならそれで可)。候補: Thm 1.5 の帰納 helper 群を
      `CNGroupStructure/` dir 化 or 先頭凍結クラスタを sibling へ
- [ ] 分割後 root closure 確認 (OddOrder.lean / importer)

## 完了条件

CNGroupStructure.lean が ~1500 行未満、build green、下流 import 無変更。

## 参照

- merge `33e2c794a`、issue 9133 (CN 3-step dichotomy)
- CLAUDE.md「ファイル粒度」(leaf ≈ 300–1500 行、2000 超は必須分割)
