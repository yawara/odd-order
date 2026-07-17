---
id: 1036
slug: ch05-basic-split
title: "Ch05_Transfer/Basic.lean (1657 行) の prefix-split (1500 行閾値超過)"
created: 2026-07-17
---

# Ch05_Transfer/Basic.lean (1657 行) の prefix-split (1500 行閾値超過)

## 背景

lane a が Cor 5.4 商版 (+42 行) の追加で Basic.lean が 1657 行となり 1500 行閾値を
超過したため flag (CLAUDE.md「ファイル粒度」、分割の実施 owner = hub)。
Basic.lean 自体が issue 0103 第 2 パスで Main.lean から prefix-split された leaf。

## やること

- [x] 分割境界の決定: §5A+§5B (90–353 行) = 中心 transfer クラスタ (Thm 5.3 / Cor 5.4 ×2 /
      Lem 5.8 / Thm 5.7 Schur / Cor 5.9) を先頭クラスタとして切り出し。
      `HasNormalPComplement` def は 5C 以降の共通語彙ゆえ Basic に残す。
      private lemma `cyclic_finite_unique_order_two` は 5C 内で使用完結 (ファイル跨ぎなし)。
- [x] `CentralTransfer.lean` 新設 (299 行、flat 兄弟 prefix-split、記述的英語名)。
      preamble (copyright/imports/namespace/opens/variable) 再現。
- [x] Basic.lean 1657→1394 行 (< 1500)。module 名不変ゆえ下流 import
      (Main/Dietzmann/SylowTwoDirectFactor) は無変更。CentralTransfer を import。
- [x] build green + AxiomsCheck OK 検証。

## 完了条件

Basic.lean が 1500 行未満・build green・下流 import 無変更で合流。→ **達成 (2026-07-17 hub)**

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-09 mathlib 準拠節)
- issues/closed/0103-split-phase-directory-first.md (分割手順の正本)
- notes/meta/merge_monitor.md tick #21-22 (実施記録)
