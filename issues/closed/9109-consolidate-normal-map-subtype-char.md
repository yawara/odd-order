---
id: 9109
slug: consolidate-normal-map-subtype-char
title: "Consolidate normal_map_subtype_of_characteristic into GroupTheory/SubgroupInAmbient"
created: 2026-07-17
---

# Consolidate normal_map_subtype_of_characteristic into GroupTheory/SubgroupInAmbient

## 背景

「`N ⊴ G`, `L` char `↥N` ⇒ `(L.map N.subtype).Normal`」の補題が現在 2 箇所に存在する:

- `OddOrder.BG.Ch3.normal_map_subtype_of_characteristic`
  (`OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean:409`, public, c 所有 tree)
- `OddOrder/Isaacs/Ch10_MoreTransfer/TransferIndexPrime.lean:382` の private copy
  (docstring 自体が「candidate for consolidation into `OddOrder/GroupTheory/`」と明記)

Isaacs Ch.9 (§9A, Lemma 9.6 の Fitting/center 押し出し) でも同じ補題が必要になった
(3 消費者目)。BG leaf は Isaacs より下流なので Isaacs 側から import できない。

**2026-07-18 追記**: BG Lem 1.21(d) の `PLengthPComplement.lean` (private `normal_map_subtype_of_char`)
で **5 site 目の複製**が発生 (Ch3 が下流ゆえ import 不可)。consolidation 時にこの site も切替対象。

## ⚠ 2026-07-17 判明: 同名 public 化は build を壊す (naive 追加不可)

`OddOrder.GroupTheory.normal_map_subtype_of_characteristic` を
`SubgroupInAmbient.lean` に public 追加したところ、**`OddOrder/Peterfalvi/Appendices/Huppert.lean`
(c 所有) が build 破壊**した (`776:6`, `802:6` "Ambiguous term")。原因: Huppert は
`normal_map_subtype_of_characteristic` を**無修飾**で参照しており、`BG.Ch3.S10` 版と
`GroupTheory` 版の両名前空間を open しているため衝突する。

⇒ **consolidation は「shared 版追加 → 全消費者 cite 切替 → 旧 copy 削除」を 1 つの
atomic な変更**として、Huppert の無修飾参照の修飾化を含めて所有レーン (c) 込みで行う必要。
naive に GroupTheory 版だけ足すと壊れる。lane a は当面 Ch09 内 private copy を使用
(`Semisimple.lean` `normal_map_subtype_of_char`; Ch10 と同じ回避)。

## やること (consolidation の atomic 手順; c 所有 file 込みゆえ hub/c で実施)

- [x] 9000 番台 issue で claim (本 issue)
- [ ] `OddOrder/GroupTheory/SubgroupInAmbient.lean` に public 版追加
- [ ] **同一変更内で** 全消費者を shared 版 cite に置換 + 旧 copy 削除:
  - Ch09 `Semisimple.lean` private `normal_map_subtype_of_char` → shared cite (a 所有)
  - BG.Ch3.S10 `normal_map_subtype_of_characteristic` 削除 → shared cite (c 所有)
  - Ch10 `TransferIndexPrime` private copy 削除 → shared cite (c 所有)
  - **Huppert.lean `776`/`802` の無修飾参照を修飾化** (c 所有; これを忘れると壊れる)
- [ ] full build green で完了

## 完了条件

shared 版が存在し 4 消費者 (Ch09 / BG Ch3 / Ch10 / Huppert) が曖昧さなく単一 declaration を
cite し、full build green。**部分適用 (shared 追加のみ) は build を壊すので不可**。

## 参照

- `OddOrder/GroupTheory/SubgroupInAmbient.lean` (issue 0052)
