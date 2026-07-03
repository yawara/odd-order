---
id: 9006
slug: feitthompson-hall-lemmas-relocate
title: "Relocate 3 misplaced Hall lemmas from FeitThompson upstream (un-gate S11 (8.12.b) migration)"
created: 2026-07-03
---

# Relocate 3 misplaced Hall lemmas from FeitThompson upstream

## 背景 (loop¹⁰⁵、lane b)

Pf (8.12.b) の faithful 版 `typeI_or_typeII_centralizer_unique_hall` (S10、axiom-clean) を
landing 済 (commit chain loop¹⁰⁵、issue 9003)。旧 false-as-stated 版は S11 caller
`typeII_centralizer_U_eq_bot` のため残置。**S11 を `_hall` に migrate するには `data.U`
(TypePData complement) を (κ∪σ)ᶜ-Hall として供給**する必要があるが、その witness が downstream の
`FeitThompson.lean` に誤配置されており、§11 (上流) から import 不可 (cycle)。

## 誤配置されている 3 補題 (全て §11 上流の依存のみ使用)

`OddOrder/FeitThompson.lean`:
- **`isHallSubgroup_of_card_eq`** (:563) — 順序で Hall 判定。依存 = `Ch03.IsHallSubgroup` +
  `Subgroup.card_mul_index` (mathlib)。→ **GroupTheory base** (例 `OddOrder/Mathlib/Subgroup.lean`
  or Ch03 隣接) へ。
- **`card_mul_card_of_complement_normal`** (:575) — `N⋊V` の位数積。依存 = mathlib
  (`isComplement'_of_disjoint_and_mul_eq_univ` 等)。→ 同上。
- **`isHall_kappaSigmaCompl_of_isTypeP2_complement`** (:588) — type-P₂ complement は (κ∪σ)ᶜ-Hall。
  依存 = 上記 card 2 本 + `S16.typeP_exists_hall_derived_eq` + `S14.msigma_isNilpotent_of_isTypeP2`
  + `S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`。→ **`S10_BGInterface`**
  (S16 を import 済、`isTypeII_iff_isTypeP2` 等の同種 interface 補題の隣)。

## やること

1. card 2 本を GroupTheory base へ relocate、`isHall_kappaSigmaCompl_of_isTypeP2_complement` を
   S10_BGInterface へ relocate。
2. `FeitThompson.lean:897` の使用箇所を新 namespace に更新。
3. **`TypePData.fitting_inf_U_eq_bot`** を `MaximalSubgroupType.lean` に追加
   (`TypePData.derivedInG_eq_fitting_sup_U` の sibling、`derived_complement.disjoint` から)。
4. S11 `typeII_centralizer_U_eq_bot` を `_hall` に migrate:
   ```
   have hP2 := (isTypeII_iff_isTypeP2 hG hM).mp ⟨dataII⟩
   have hUhall := isHall_kappaSigmaCompl_of_isTypeP2_complement hG hM hP2 hUleM
     data.derivedInG_eq_fitting_sup_U data.fitting_inf_U_eq_bot
   ... typeI_or_typeII_centralizer_unique_hall hG hM (Or.inr ⟨dataII⟩) hUleM hUhall ...
   ```
5. 旧 `typeI_or_typeII_centralizer_unique` (false-as-stated, sorry) を S10 から削除。

## cross-lane 判断が要る点 (hub 裁定)

`FeitThompson.lean` は **lane a 全体所有**。3 補題の relocate は lane a のファイルからの削除を伴う。
generic 補題の proper placement 是正なので lane b が実施してよいか、lane a に委ねるか hub 裁定。
(補題自体は §11 上流依存のみなので relocate は sound; merge conflict risk は低い。)

### ✅ HUB 裁定 (2026-07-04, ユーザー承認)

**owner は強制しない — 「issue 経由 / LAUNCH.md で全レーンが自覚できていれば誰が実施してもよい」** (ユーザー
2026-07-04)。⟹ 運用: (1) 本 issue が relocate 計画 + FeitThompson からの削除箇所を追跡 (source of truth)。
(2) 実施レーン (b or a) は着手前に本 issue を open のまま更新し、**lane a の LAUNCH.md にも 1 行周知**
(FeitThompson.lean から 3 Hall 補題が上流 relocate され得る旨) を残す。(3) FeitThompson からの削除を伴う
commit が出たら hub は本 issue を根拠に**逸脱でなく shared-infra hygiene として合流** (通常の range-check は
FeitThompson=lane a 所有ゆえ flag するが、本裁定で当該 relocate は例外)。(4) 完了で本 issue close + LAUNCH
周知行を除去。**要点はレーン間の awareness (issue+LAUNCH) であり、owner の固定ではない。**

## 参照

- issue 9003「loop¹⁰⁵」節 (finding + landing 詳細)
- S10:398 旧 (sorry) / `_hall` (proven) / S14 caller migrate 済
