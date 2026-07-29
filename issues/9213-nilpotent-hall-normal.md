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

- [x] `C` 有限冪零, `Q` が `C` の Hall `π`-部分群 ⟹ `Q ⊴ C`。
- [x] 系: `C` 冪零, `S` = Sylow `p`, `Q` = Hall `p'` ⟹ `[S, Q] = 1`
      (`Q ⊴ C` + `S ⊴ C` + `S ⊓ Q = ⊥` に `Subgroup.commute_of_normal_of_disjoint`
      = mathlib `Mathlib/Algebra/Group/Subgroup/Basic.lean:1002`)。

## ✅ 完了 (2026-07-29)

置き場は **`OddOrder/Isaacs/Ch03_SplitExtensions/HallNilpotent.lean`** (下記「完了条件」で
予定した `GroupTheory/NilpotentHall.lean` から変更)。理由: `IsHallSubgroup` /
`Subgroup.IsPiGroup` / `IsHallSubgroup.card_dvd_of_isPiGroup` はすべて
`OddOrder.Isaacs.Ch03` 名前空間にあり、(i) `GroupTheory/` に置くと Ch03 → GroupTheory の
逆向き import になる、(ii) 主定理は `hH.normal_of_isNilpotent` と dot-notation で呼びたいので
宣言が `OddOrder.Isaacs.Ch03` 名前空間に居る必要がある。`OddOrder.lean` 配線済・
build green・4 定理すべて axiom-clean (`propext`/`Classical.choice`/`Quot.sound` のみ)。

内容 (4 定理):

* `isPiSubgroup_le_of_isHallSubgroup_of_le_normalizer` — **`π`-Hall `H` を正規化する
  `π`-部分群 `N` は `H` に含まれる** (冪零性不要)。`N ≤ N_G(H)` から
  `↑(N ⊔ H) = ↑N · ↑H` (mathlib `Subgroup.coe_mul_of_left_le_normalizer_right`)、
  `|N ⊔ H| · |N ⊓ H| = |N| · |H|` で `N ⊔ H` が `π`-群、Hall の極大性
  (`IsHallSubgroup.card_dvd_of_isPiGroup`) で `N ⊔ H = H`。
  ⟹ 既存の `OddOrder.BG.Ch3.S12.isPiSubgroup_le_of_normal_isHall` (`[H.Normal]` 版) の
  **一般化** (仮説を `N ≤ N_G(H)` に弱めた)。
* `IsHallSubgroup.normalizer_normalizer` — `N_G(N_G(H)) = N_G(H)` (冪零性不要)。
  mathlib `Sylow.normalizer_normalizer` の Hall 版。
* `IsHallSubgroup.normal_of_isNilpotent` — **本題**。`Group.normalizerCondition_of_isNilpotent`
  + `normalizerCondition_iff_only_full_group_self_normalizing` で `N_G(H) = ⊤`。
* `commute_of_isHallSubgroup_of_isHallSubgroup_compl` — `π`-Hall と `π'`-Hall は
  元ごとに可換 (両方正規 + 位数互いに素 + `Subgroup.commute_of_normal_of_disjoint`)。

⚠ 実装の罠: `H.map (MulAut.conj g)` は `Subgroup.map` が `G →* N` を取るため、
**codomain が期待型から決まらない位置では coercion が挿入されない** (`Nat.card ↥(H.map …)` や
`Subgroup.IsPiGroup π (H.map …)` の中)。`(H.map (MulAut.conj g) : Subgroup G)` と
型注釈を付けて `N := G` を強制する。

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
