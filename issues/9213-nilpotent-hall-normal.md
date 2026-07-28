---
id: 9213
slug: nilpotent-hall-normal
title: "有限冪零群の Hall 部分群は正規 (3C.7 の前提)"
created: 2026-07-28
---

# 有限冪零群の Hall 部分群は正規 (3C.7 の前提)

## claim

**lane a** が build する (shared infra claim, 2026-07-28)。消費点は
[issue 1055](1055-isaacs-problems-campaign.md) の **Isaacs Problem 3C.7 (Carter 部分群)**
共役性 step 4b。他レーンは重複着手しないこと。

## やること

- [ ] `C` 有限冪零, `Q` が `C` の Hall `π`-部分群 ⟹ `Q ⊴ C`。
- [ ] 系: `C` 冪零, `S` = Sylow `p`, `Q` = Hall `p'` ⟹ `[S, Q] = 1`
      (`Q ⊴ C` + `S ⊴ C` + `S ⊓ Q = ⊥` に `Subgroup.commute_of_normal_of_disjoint`
      = mathlib `Mathlib/Algebra/Group/Subgroup/Basic.lean:1002`)。

## 実測した既存状況 (2026-07-28)

* mathlib: 冪零群の Sylow 分解は `Sylow.directProductOfNormal`
  (`Mathlib/GroupTheory/Sylow.lean:812`)、冪零の TFAE は
  `Mathlib/GroupTheory/Nilpotent.lean:1235`。**Hall 部分群についての主張は無い**
  (mathlib は一般 Hall 部分群の概念自体を持たない)。
* 本 repo: `OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean` に
  `IsHallSubgroup` / `hall_E_exists` / `hall_C` / `hall_D`。
  `OddOrder/GroupTheory/NormalHallHeredity.lean` は「正規 Hall 条件の遺伝」で別物。
  **「冪零 ⟹ Hall が正規」は無い**。

## 証明経路 (確定済、実装待ち)

1. **正規 Hall 部分群は一意**: `Q ⊴ M`, `Q` が `M` の Hall `π`, `Q'` も `M` の Hall `π`
   なら `Q'Q/Q ≅ Q'/(Q' ⊓ Q)` は `M/Q` (= `π'`-群) の中の `π`-群 ⟹ 自明
   ⟹ `Q' ≤ Q`, 位数が等しいので `Q' = Q`。
2. `M := N_C(Q)` は自己正規化: `g ∈ N_C(M)` なら `Q^g` も `M` の Hall `π` で,
   1 の一意性から `Q^g = Q`, つまり `g ∈ M`。
3. `C` 冪零の**正規化条件**
   (`Group.normalizerCondition_of_isNilpotent` +
   `normalizerCondition_iff_only_full_group_self_normalizing`) より `M = C`,
   すなわち `Q ⊴ C`。

## 完了条件

新 leaf `OddOrder/GroupTheory/NilpotentHall.lean` が build-green・axiom-clean で
`OddOrder.lean` に配線され、1055 の 3C.7 step 4b から呼べる。

⚠ 置き場は `GroupTheory/` 配下だが `IsHallSubgroup` の定義が
`OddOrder.Isaacs.Ch03_SplitExtensions.Basic` にあるのでそこを import する形になる。

## 参照

- [issue 1055](1055-isaacs-problems-campaign.md) — Isaacs Problems campaign (3C.7 の設計節)
- `OddOrder/Isaacs/Ch03_SplitExtensions/Carter/` — 3C.7 の実装ディレクトリ
