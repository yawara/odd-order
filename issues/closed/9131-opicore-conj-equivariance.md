---
id: 9131
slug: opicore-conj-equivariance
title: "oPiCore/opiCoreInG の同型・共役同変性 (Thm 9.23 V-branch 用)"
created: 2026-07-18
---

# oPiCore/opiCoreInG の同型・共役同変性 (Thm 9.23 V-branch 用)

## 背景

Isaacs Thm 9.23 (issue 1038) の `V`-branch で `K = H^g` について
`|K : O_p(K)| = |H : O_p(H)|` に読み替える必要があり、`O_π` の同型同変性が要る。

## やること

- [x] `Ch03.oPiCore` の同型不変性 — **既存だった** (`oPiCore.map_eq_of_mulEquiv`,
      `Ch03_SplitExtensions/Theorem315.lean`)。ただし `[Finite G] [Finite H]` 付き。
- [x] **一般化**: `[Finite]` を除去。証明を `map_le_of_surjective` (Finite 必須) から
      単射性ベース (`Subgroup.equivMapOfInjective` で位数不変 → `IsPiGroup` 移送) に
      差し替えた。private helper `oPiCore.map_le_of_mulEquiv` を新設。
      既存 8 箇所の call site は instance 引数が減るだけなので無変更で通る。
- [x] **重複の解消**: 前 session (commit 37b8f3043) が `SubgroupInAmbient.lean` に
      作った `map_oPiCore_mulEquiv` は上記既存補題の重複だったので削除。
      ⚠ claim-before-build の検索漏れ (CLAUDE.md「既存を再構築しない」)。
- [x] **ambient 版**: `GroupTheory.map_opiCoreInG_mulEquiv` を `SubgroupInAmbient.lean` に新設。
      `(opiCoreInG π H).map e = opiCoreInG π (H.map e)` (`e : G ≃* G'`)。
- [x] 消費側: `Ch09.opiCoreInG_relIndex_map_conj` (`|K:O_π(K)| = |H:O_π(H)|`, `K = H^g`)
      → `thompsonCorefreeBound` (Thm 9.23) で使用。

## 残: `opiCoreInG_pointwise_smul` との重複可能性 (別 issue 候補)

`GroupTheory/MaximalSubgroupTypeConj.lean:231` に `opiCoreInG_pointwise_smul`
(`φ • O_π(H) = O_π(φ • H)`, `φ : MulAut G`, `[Finite G]`) がある。これは今回新設した
`map_opiCoreInG_mulEquiv` の **`MulAut` + pointwise-smul 特殊化**であり、
`pointwise_mulAut_smul_eq_map` を挟めば導出できる (証明も同じ構造の写経)。

`MaximalSubgroupTypeConj.lean` は BG 側の重い closure (FrobeniusGroup 等) を引くので
Ch09 からは import せず、今回は ambient 版を canonical home
(`SubgroupInAmbient.lean` = `opiCoreInG` の定義元) に置いた。
`opiCoreInG_pointwise_smul` を新補題からの導出に置き換える consolidation は
[[9109]]/[[3005]] 系と同種の掃除として別途。

## 完了条件

Thm 9.23 の `V`-branch が閉じ、重複が解消され、full build green + AxiomsCheck OK。
→ **達成 (2026-07-18)**。

## 参照

- issue 1038 (Thm 9.24 / 9.23)
- OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean (`oPiCore.map_eq_of_mulEquiv`)
- OddOrder/GroupTheory/SubgroupInAmbient.lean (`map_opiCoreInG_mulEquiv`)
- OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean (`opiCoreInG_pointwise_smul`, 重複候補)
