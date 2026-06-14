---
id: 68
slug: s08-casebcoherence2-split
title: "S08_CaseBCoherence2.lean 分割 (1561>1500, B frontier 凍結後)"
created: 2026-06-15
---

# S08_CaseBCoherence2.lean 分割 (1561>1500, B frontier 凍結後)

## 背景

`OddOrder/Peterfalvi/S08_CaseBCoherence2.lean` が **1561 行**(粒度規約の 1,500 行閾値超)。
merge monitor のサイズ watch で検出(2026-06-15、Lane B の Pf (6.8.2.3) seam-1 直交補題群
合流 `7c55fae1` で 1436→1561)。これは **Lane B (lane-b) の active frontier**(case-B
coherence の disjointness machine を継続実装中)なので、F の `S13_PrimeActionTransition`
(issue 0067)と同型 = **frontier が動いている間は分割しない**(凍結境界が定まらないため)。

## やること

- [ ] **トリガー条件**: Lane B が (6.8.2.3) disjointness/seam クラスタを landing し、
      S08_CaseBCoherence2 への追記が止まったら(= frontier 凍結)実施。
- [ ] **分割 owner = hub**(prefix-split)。B の frontier と衝突しない凍結境界(先頭 K 宣言)を
      上流 leaf へ押し出し、残りがそれを import。前方参照は構文上不可ゆえ任意の宣言境界で安全。
- [ ] 分割後 `lake build OddOrder OddOrder.AxiomsCheck` 緑 + 実 sorry 不変を確認。
- [ ] 新 leaf を `OddOrder.lean` の root closure に登録(import 行)。

## 完了条件

S08_CaseBCoherence2.lean(と派生 leaf)がいずれも 1,500 行以下、build 緑、sorry 不変。

## 参照

- 手順: [`notes/meta/merge_monitor.md`](../notes/meta/merge_monitor.md) サイズ watch + 分割メカニズム
- 同型先行例: issue 0067 (`S13_PrimeActionTransition` 2357 行, Lane F frontier)
- 検出コミット: `7c55fae1` (Merge 'lane-b' seam-1 orthogonality)
