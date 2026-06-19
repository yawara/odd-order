---
id: 2012
slug: kappahall-complement-derived
title: "Discharge kappaHall_isComplement_derived (BG↔Pf 対応: κ-Hall = Peterfalvi W₁ = BG §14 typeP_duality)"
created: 2026-06-19
---

# Discharge kappaHall_isComplement_derived (BG↔Peterfalvi 対応)

## ✅ RESOLVED (2026-06-19, commit `64472a63`) — 既に形式化済だった

この対応は **既に証明済(axiom-clean)** = `OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall`
(`S14_TypePCounting.lean:8008`、BG Thm 14.7(h)、AxiomsCheck 登録)。私が原文/既存機構を確認せず sorry'd 重複
`kappaHall_isComplement_derived` を切り出したのが誤り。**対応**: 重複を削除し consumer(FeitThompson.lean)で
既存定理を直接 cite([IsCyclic ↥K] を caseB 前へ hoist)→ **(10.11) 完全 unconditional 化**(sorry 136→135)。
教訓 = 「gap/obligation と決める前に grep + AxiomsCheck を確認」([[feedback-dont-mislabel-formalization-as-research]])。

---

**Owner**: lane-f (BG §14)。lane-h が (10.11) `theorem88_caseB_prime_orders` を sorry-free 化する際に
切り出した唯一の residual(commit `daa62d7e`)。

**性質(重要、用語訂正)**: これは**書籍の gap ではない**。BG と Peterfalvi は別々の本で、同じ極大部分群 M を
異なる記法(BG=κ/σ、Pf=W₁/W₂)で記述している。本 lemma は両者の記法を繋ぐ**対応**(BG の κ(M)-Hall =
Peterfalvi の W₁(M))で、BG §14 の type-P 構造論から従う**形式化労力**(Peterfalvi §8 が BG の局所解析を
自分の記法へ翻訳する層に相当)。

**Where**: `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` `kappaHall_isComplement_derived`(sorry）。
§16 consumer `OddOrder/FeitThompson.lean`(caseB 構成 `S_compl`/`T_compl`)が cite。

**Statement**:
```
theorem kappaHall_isComplement_derived {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hMP : BG.Ch4.S14.IsTypeP M) (hKle : K ≤ M)
    (hKhall : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)
```
= **κ(M)-Hall subgroup が M' = [M,M] を M 内で complement する**(`M = M' ⋊ K`)。
`TypePData.card_W1_eq_derived_index`（`MaximalSubgroupType.lean:167`）の docstring が「any Hall
κ(M)-subgroup K of M complement M', so they share this order」と明言する事実。

## やること

- [ ] κ-Hall が derived を complement することを BG §14 の type-P 構造(`M = M_F ⋊ ...`、κ ⊆ τ₁∪τ₃、
      W₁ = κ-Hall 等)から証明。lane-f の `typeP_duality`/`Section16TypePStructure` の機構が土台。
- [ ] 証明後、`kappaHall_isComplement_derived` を BG §14 (`S14_*`) へ移設するか S12 のまま実証明化。

## 完了条件

`kappaHall_isComplement_derived` の sorry が消える / full build green / (10.11) が完全 unconditional 化。

## 参照

- commit `daa62d7e`（10.11 sorry-free + 対応 lemma 切り出し）
- `MaximalSubgroupType.lean:162-170`（`card_W1_eq_derived_index` + docstring の対応主張）
- `Section16MaximalPair.K_hall`/`Kstar_hall`（FeitThompson.lean、consumer）
- BG↔Pf reconciliation = [[s16-typep-producer-unfillable]] の pairing 系
