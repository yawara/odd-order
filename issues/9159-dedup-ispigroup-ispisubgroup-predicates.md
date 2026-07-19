---
id: 9159
slug: dedup-ispigroup-ispisubgroup-predicates
title: "shared infra: Subgroup.IsPiGroup と Subgroup.IsPiSubgroup が同一定義の重複 — defeq 依存の解消"
created: 2026-07-19
---

# shared infra: Subgroup.IsPiGroup と Subgroup.IsPiSubgroup が同一定義の重複 — defeq 依存の解消

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 事実 (2026-07-19、BG Thm 6.4 wave 4 で発見)

**同一概念に対する定義が 2 つ、どちらも `Subgroup` 名前空間に在る**:

| 名前 | 所在 | 本体 |
|---|---|---|
| `Subgroup.IsPiGroup` | `OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean:298` (`Ch03` 配下) | `∀ p ∈ (Nat.card ·).primeFactors, p ∈ π` |
| `Subgroup.IsPiSubgroup` | `OddOrder/GroupTheory/OpResidual.lean:39` (root) | **byte-identical** |

⚠ **既に defeq 依存のコードが入っている**。BG Thm 6.4 の `thm64_of_le_proper_subgroup`
(`S06_Thm64.lean:524`) は、`isPiGroup_subgroupOf` が返す `Ch03` 綴りを
`Subgroup.IsPiSubgroup` が期待される場所で 3 箇所そのまま消費している。**現状 compile は通る**が、
これは定義の透明性に依存した silent な defeq 濫用で、どちらかに `@[irreducible]` が付いたり
定義が構造体化されたりすると壊れる。

## やること

- [ ] どちらを正本にするか決める。**`OpResidual` 側 (`IsPiSubgroup`) の名前と配置が適切**
      (root `Subgroup` 名前空間、`GroupTheory/` 配下、BG 側が主に使う)。ただし raw grep では
      `Ch03` 版の方が使用箇所が多いので、移行量は要実測。
- [ ] 片方を他方の `abbrev` にするか、全面置換して一方を削除する。
- [ ] 置換後、`S06_Thm64.lean` の 3 箇所の defeq 依存が明示的な cite に変わることを確認。
- [ ] `lake build OddOrder` + AxiomsCheck green を確認。

## 注意

- issue 9130 (`isPiSubgroup_of_isPGroup_of_mem` の集約) とは**別件**。あちらは補題 1 件の重複、
  こちらは**述語定義そのもの**の重複。
- 着手前に open 9000 issue を scan すること (claim-before-build)。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S06_Thm64.lean:524` (defeq 依存の実例)。
- issue 3026 (BG Thm 6.4)。
