---
id: 2012
slug: kappahall-complement-derived
title: "Discharge kappaHall_isComplement_derived (gap B: κ-Hall complements derived = BG §14 typeP_duality)"
created: 2026-06-19
---

# Discharge kappaHall_isComplement_derived (gap B)

**Owner**: lane-f (BG §14)。lane-h が (10.11) `theorem88_caseB_prime_orders` を sorry-free 化する際に
切り出した唯一の residual(commit `daa62d7e`)。

**Where**: `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` `kappaHall_isComplement_derived`(sorry)。
§16 consumer `OddOrder/FeitThompson.lean`(caseB 構成 `S_compl`/`T_compl`)が cite。

**Statement**:
```
theorem kappaHall_isComplement_derived {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hMP : BG.Ch4.S14.IsTypeP M) (hKle : K ≤ M)
    (hKhall : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)
```
= **κ(M)-Hall subgroup が M' = [M,M] を M 内で complement する**(`M = M' ⋊ K`)。これは BG §14
`typeP_duality` の bridge で、`TypePData.card_W1_eq_derived_index`(`MaximalSubgroupType.lean:167`)の
docstring が「any Hall κ(M)-subgroup K of M complement M', so they share this order」と明言する fact
(= BG の κ(M)-Hall を Peterfalvi の W₁(M) と同定 = **gap B**)。

## やること

- [ ] κ-Hall が derived を complement することを BG §14 の type-P 構造(`M = M_F ⋊ ...`、κ ⊆ τ₁∪τ₃、
      W₁ = κ-Hall 等)から証明。lane-f の `typeP_duality`/`Section16TypePStructure` の機構が土台。
- [ ] 証明後、`kappaHall_isComplement_derived` を BG §14 (`S14_*`) へ移設するか S12 のまま実証明化。

## 完了条件

`kappaHall_isComplement_derived` の sorry が消える / full build green / (10.11) が完全 unconditional 化。

## 参照

- commit `daa62d7e`(10.11 sorry-free + bridge 切り出し)
- `MaximalSubgroupType.lean:162-170`(`card_W1_eq_derived_index` + docstring の bridge 主張)
- `Section16MaximalPair.K_hall`/`Kstar_hall`(FeitThompson.lean、consumer)
- gap B = [[s16-typep-producer-unfillable]] の pairing reconciliation 系
