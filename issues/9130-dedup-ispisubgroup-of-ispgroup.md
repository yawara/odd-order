---
id: 9130
slug: dedup-ispisubgroup-of-ispgroup
title: "isPiSubgroup_of_isPGroup_of_mem を GroupTheory へ集約 (BG の重複を削除)"
created: 2026-07-18
---

# isPiSubgroup_of_isPGroup_of_mem を GroupTheory へ集約 (BG の重複を削除)

## 採番の経緯

当初 9128 で採番したが、並行レーンが同じ 9128 (`9128-psu-simplicity`) を先に main へ
merge していたため 9130 に振り直した (SEQUENCE.9000 の merge conflict で発覚)。
先行 commit `b00ad49f3` のメッセージは旧番号 9128 を参照している。

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

`isPiSubgroup_of_isPGroup_of_mem` (`p`-群 + `p ∈ π` ⇒ `π`-部分群) を
**`OddOrder/GroupTheory/OpResidual.lean`** (= `Subgroup.IsPiSubgroup` の定義元、
import graph の最下層) に追加した (2026-07-18, lane a)。

理由: Isaacs Ch09 の Thm 9.23 で必要になったが、既存の実装は
`OddOrder/BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean:129` にあり、
**BG は Isaacs の下流**なので import できなかった。3 つ目のコピーを作るより
canonical home に置く方が正しいと判断。

新規 import は不要 (`Mathlib.GroupTheory.Sylow` が既に `IsPGroup` を供給)。

## やること

- [ ] `BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean:129` の
      `isPiSubgroup_of_isPGroup_of_mem` を削除し、`Subgroup.` 版を使うよう
      呼び出し側 (S12_Lemma128 / S12_Corollary129 / S12_Theorem127 の 4 箇所ほか) を更新。
- [ ] 名前空間の差 (`BG.Ch3.S12.` vs `Subgroup.`) に注意 — 呼び出しは
      `Subgroup.isPiSubgroup_of_isPGroup_of_mem` になる。
- [ ] full build + AxiomsCheck で回帰なしを確認。

## 注意

BG レーンの所有ファイルなので、実施は BG 担当レーン (または hub) が行う。
lane a は canonical 版を追加するところまで。
