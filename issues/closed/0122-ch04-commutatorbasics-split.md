---
id: 122
slug: ch04-commutatorbasics-split
title: "Ch04 Main/CommutatorBasics.lean (1552 行) の prefix-split (1500 行閾値超過)"
created: 2026-07-17
---

# Ch04 Main/CommutatorBasics.lean (1552 行) の prefix-split (1500 行閾値超過)

## 背景

tick #22 の size watch で検出 (a の Lem 4.6 一般化追記時点で 1552 行 > 1500 閾値)。
分割の実施 owner = hub (CLAUDE.md「ファイル粒度」)。a の Ch04 frontier は 4.6/4.29
一般化で完了済 (次は Ch06) ゆえ安全窓で即実施。

## やること

- [x] 境界決定: 単一 section 4A 内の topic 副見出し `### Thm 4.7: maximal class p-群`
      (旧 1048 行目) を境界に採用。private 跨ぎ解析で
      `commutatorElement_pow_left_of_class_le_two` (def 255 / last use 1517) のみが
      境界を跨ぐ → 規約 (ファイル跨ぎ private 禁止) に従い public 化。
- [x] `CommutatorIdentities.lean` 新設 (1022 行) = §4A 前半: commutator identities +
      coatom/p-群補題 + Lem 4.5/4.6 クラスタ。
- [x] `CommutatorBasics.lean` 1552→567 行 = §4A 後半: Thm 4.7/4.8 (maximal class p-群, Ω_r)。
      module 名不変ゆえ下流 (Main.lean / ThreeSubgroups.lean) 無変更。
- [x] build green + AxiomsCheck OK 検証。

## 完了条件

CommutatorBasics.lean が 1500 行未満・build green・下流 import 無変更で合流。
→ **達成 (2026-07-17 hub、tick #22 直後)**

## 参照

- issues/closed/1036-ch05-basic-split.md (直前の同型 split)
- issues/closed/0103-split-phase-directory-first.md (分割手順の正本)
- notes/meta/merge_monitor.md tick #22 記録
